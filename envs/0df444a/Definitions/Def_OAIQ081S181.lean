-- Prove2me | Definitions.Def_OAIQ081S181
-- name    : OAIQ081S181
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T23:26:34.603571+00:00
-- url     : https://prove2.me/theorems/96950163-d6a0-4f4c-aa5d-82c96716923a
-- title:
--   Definitions bundle OAIQ081S181 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 22 declarations of OpenAI's Lean: 14 definitions and 8 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.AssignmentConcrete.sourceJets`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.Semantics.hashValue`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.Semantics.markedValue`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.Spec.value`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.factorJet`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete.baseline`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete.binaryTarget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete.completedRows`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete.residualJet`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete.specTarget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource.nativeSpecOfInputs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Query.Ring.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Interpolation.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.sourceIncidenceJet`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_LayoutDenominatorProgramQuery`, `SubexponentialSAT_SqrtLog_LayoutDenominatorProgramQueryRun`, `SubexponentialSAT_SqrtLog_LeafProgramAssignmentConcrete`, `SubexponentialSAT_SqrtLog_LeafProgramFactorJet`, `SubexponentialSAT_SqrtLog_LeafProgramFactorSemantics`, `SubexponentialSAT_SqrtLog_LeafProgramFactorSpec`, `SubexponentialSAT_SqrtLog_LeafProgramNodeConcreteCode`, `SubexponentialSAT_SqrtLog_LeafProgramNodeConcreteResidual`, `SubexponentialSAT_SqrtLog_LeafProgramNodeConcreteRows`, `SubexponentialSAT_SqrtLog_LeafProgramNodeConcreteSpecTarget`, `SubexponentialSAT_SqrtLog_LeafProgramNodeConcreteTarget`, `SubexponentialSAT_SqrtLog_LeafProgramPreparedFactorBase`, `SubexponentialSAT_SqrtLog_LeafProgramPreparedSource`, `SubexponentialSAT_SqrtLog_LeafProgramQueryRing`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramInterpolation`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramNative`, `SubexponentialSAT_SqrtLog_PerturbationAssemblySourceStored`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S173`, `OAIQ081S174` and `OAIQ081S175` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S186`, `OAIQ081S187` and `OAIQ081S188`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.Input.payload_correct`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.Input.staged_factorJet`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.hash_step_value`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.marked_step_value`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryJetSemantics.colored_residual_target_dense_shift`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryJetSemantics.residual_group_diagonal_dense`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.prepare_native_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTargetMetadata.native_count`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTargetMetadata.native_count_le` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete.completedRows_origin`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.Input.payload_correct`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.Input.staged_factorJet`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.hash_step_value`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.marked_step_value`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryJetSemantics.colored_residual_target_dense_shift`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryJetSemantics.residual_group_diagonal_dense`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.prepare_native_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTargetMetadata.native_count`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTargetMetadata.native_count_le` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete.completedRows_origin`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S173
import Definitions.Def_OAIQ081S174
import Definitions.Def_OAIQ081S175

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutDenominatorProgramQueryRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutDenominatorProgramQuery
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage
open SubexpLiftRing SubexpQuarticRing IntegerRingLiftProgram

theorem localCommand_eval (a : LocalData) (t : ℕ) {d : ℕ} (model : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (zero one minusOne : ModelCode t d) (u : RingProgram.ScalarCode 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (hready : CachedReady t model M cache zero one minusOne (localInput a))
    (hu : a.stacks 253=u.val) (hc : ∀i∈bank,a.stacks i=[])
    (hout : a.stacks 728=[]) (W : ℕ) (hw : WordBound W a) (hsize : d*baseWidth 3 t ≤ W) :
    ∃ n ≤ LayoutDenominatorProgram.budget (a.stacks 740).length t d + 589*W+824,
      ∃ out : LocalData, Eval localCommand n a out ∧
        out.stacks=Function.update a.stacks 728 (RingProgram.flat
          (LayoutDenominatorProgram.value t model M cache zero one minusOne u.val (a.stacks 740).length)) := by
  let bits := RingProgram.flat (LayoutDenominatorProgram.value t model M cache
    zero one minusOne u.val (a.stacks 740).length)
  have hs := staged_view a hc
  have hr : CachedReady t model M cache zero one minusOne (view (staged a)).stacks := by
    rw [hs]; exact hready
  have hu' : (view (staged a)).stacks 253=u.val := by rw [hs]; simpa [localInput] using hu
  have h254 : (view (staged a)).stacks 254=[] := by rw [hs]; simp [localInput]
  have h252 : (view (staged a)).stacks 252=[] := by rw [hs]; simp [localInput]
  have hR : (view (staged a)).stacks 239=a.stacks 740 := by rw [hs]; simp [localInput]
  obtain ⟨n,r,hn,he⟩ := LayoutDenominatorProgram.command_run t model M cache hz
    zero one minusOne (view (staged a)).stacks hr u hu' h254 h252 (view (staged a)).regs
  rw [hR] at hn he
  let b : LocalData := embedState id port (staged a)
    (⟨r,Function.update (view (staged a)).stacks 252 bits⟩ : SubexpConvolutionControl.Data)
  have he' : Eval nativeCall (n+1) (staged a) b :=
    eval_liftCommand_from_state _ 239 252 id port (staged a) Function.injective_id port_injective he
  have hbs : b.stacks=Function.update (staged a).stacks 592 bits := by
    change Function.extend port (Function.update (view (staged a)).stacks 252 bits)
      (staged a).stacks = _
    rw [ProgramLinking.extend_update port_injective]
    have hh := congrArg StructuredProgram.State.stacks
      (embedState_project id port (staged a) Function.injective_id port_injective)
    exact congrArg (fun s => Function.update s 592 bits) hh
  have hb728 : b.stacks 728=[] := by
    rw [hbs,Function.update_of_ne (by decide : (728:Fin 768)≠592)]
    exact (staged_outside a 728 (by rw [mem_bank]; decide)).trans hout
  have hb460 : b.stacks 460=[] := by
    rw [hbs,Function.update_of_ne (by decide : (460:Fin 768)≠592)]
    change (view (staged a)).stacks 120=[]
    rw [hs]; simp [localInput]
  have hb592 : b.stacks 592=bits := by rw [hbs]; simp
  let c := copyState 592 728 b
  have hcs : c.stacks=Function.update b.stacks 728 bits := by
    simp only [c,copyState_stack,hb592,hb728,List.append_nil]
  let out := clearManyState bank c
  have hfinal : out.stacks=Function.update a.stacks 728 bits := by
    funext i
    change (clearManyState bank c).stacks i=_
    rw [clearMany_stacks,hcs,hbs]
    by_cases hi : i∈bank
    · rw [ite_eq_left hi]
      have hn : i≠728 := by intro he; subst i; rw [mem_bank] at hi; omega
      rw [Function.update_of_ne hn,hc i hi]
    · rw [ite_eq_right hi]
      by_cases h728 : i=728
      · subst i; simp
      · rw [Function.update_of_ne h728,Function.update_of_ne h728]
        have h592 : i≠592 := by intro he; subst i; exact hi ((mem_bank _).mpr (by omega))
        rw [Function.update_of_ne h592]
        exact staged_outside a i hi
  have hstage : Eval (copyMany 460 pairs) (copyManyCost pairs a) a (staged a) :=
    copyMany_eval _ _ _ pairs_valid (hc 460 ((mem_bank _).mpr (by omega)))
  have hcopy := copy_eval (592:Fin 768) 728 460 b (by decide) (by decide) (by decide) hb460
  have hclear := clearMany_eval bank c
  have hbits : bits.length ≤ W := by
    dsimp [bits]; rw [RingProgram.flat_length]; exact hsize
  have hstageW : WordBound W (staged a) := copyMany_wordBound pairs a W pairs_distinct
    (fun p hp => hc p.2 (pairs_destination p hp)) pairs_separated hw
  have hbW : WordBound W b := by
    intro i; rw [hbs]; by_cases hi : i=592
    · subst i; simp only [Function.update_self]; exact hbits
    · rw [Function.update_of_ne hi]; exact hstageW i
  have hcW : WordBound W c := by
    intro i; rw [hcs]; by_cases hi : i=728
    · subst i; simp only [Function.update_self]; exact hbits
    · rw [Function.update_of_ne hi]; exact hbW i
  have hcost1 := copyManyCost_le pairs a W pairs_separated (fun p _ => hw p.1)
  have hcost3 := clearManyCost_le bank c W hcW
  have hlen : bank.length=256 := by simp [bank]
  simp only [hlen] at hcost3
  have hlenP : pairs.length=10 := rfl
  rw [hlenP] at hcost1
  refine ⟨copyManyCost pairs a+((n+1)+(7*(b.stacks 592).length+5+clearManyCost bank c)),?_,out,?_,hfinal⟩
  · rw [hb592]; omega
  · exact hstage.seq (he'.seq (hcopy.seq hclear))

/-- The ambient wrapper preserves every stack except its persistent output,
and every register outside the local sixteen-register arithmetic bank. -/
theorem command_eval (a : Data) (t : ℕ) {d : ℕ} (model : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (zero one minusOne : ModelCode t d) (u : RingProgram.ScalarCode 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (hready : CachedReady t model M cache zero one minusOne
      (localInput (projectState registers id a)))
    (hu : a.stacks 253=u.val) (hc : ∀i∈bank,a.stacks i=[])
    (hout : a.stacks 728=[]) (W : ℕ) (hw : WordBound W a) (hsize : d*baseWidth 3 t ≤ W) :
    ∃ n ≤ budget (a.stacks 740).length t d W, ∃ out : Data,
      Eval command n a out ∧
      out.stacks=Function.update a.stacks 728 (RingProgram.flat
        (LayoutDenominatorProgram.value t model M cache zero one minusOne u.val (a.stacks 740).length)) ∧
      (∀i : Fin 40,16 ≤ i.val → out.regs i=a.regs i) := by
  obtain ⟨n,hn,b,he,hb⟩ := localCommand_eval (projectState registers id a) t model M cache
    zero one minusOne u hz hready hu hc hout W hw hsize
  refine ⟨n+1,?_,embedState registers id a b,?_,?_,?_⟩
  · unfold budget
    simp only [projectState,Function.comp_apply,id_eq] at hn
    omega
  · exact eval_liftCommand_from_state _ 740 728 registers id a registers_injective Function.injective_id he
  · funext i
    rw [show (embedState registers id a b).stacks i=b.stacks i from
      embedState_stack _ _ _ _ Function.injective_id i]
    exact congrFun hb i
  · intro i hi
    apply embedState_register_frame
    rintro ⟨j,hj⟩
    have hv := congrArg Fin.val hj
    dsimp [registers] at hv
    omega

end SubexponentialSAT.SqrtLog.LayoutDenominatorProgramQuery

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafRingSetupProgramNative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram
open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing

theorem idempotentCall_eval (a : Data) (bits : List Bool) (t : ℕ)
    (hv : CounterPrograms.value bits=t) (ht : 0 < t)
    (ha : projectState (registers 8 (by decide)) idempotent a =
      IdempotentPreparationProgram.inputData bits) :
    ∃ n ≤ IdempotentProgram.completeBudget t bits.length,
      ∃ out : IdempotentProgram.RegisterData,
      ∃ (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
        (u : RingProgram.ScalarCode 3 t),
      Eval idempotentCall n a (embedState (registers 8 (by decide)) idempotent a out) ∧
      out.stacks 32=RingProgram.flat (IdempotentProgram.binaryLiftWords t M cache u) ∧
      (2 : ZMod (3^t))*wordValue 3 t u=1 := by
  obtain ⟨out,M,cache,u,⟨n,hn,he⟩,hout,hu⟩ :=
    IdempotentProgram.completeProgram_runs bits t hv ht
  exact ⟨n,hn,out,M,cache,u,eval_call_from_state IdempotentProgram.completeProgram
    (registers 8 (by decide)) idempotent a (registers_injective 8 (by decide))
    idempotent_injective (ha.symm ▸ he),hout,hu⟩

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

/- Component: LeafRingSetupProgramCode.lean -/

/-! The fixed executable preparation pipeline.  Its input is the actual
numerical bank emitted by `LeafParametersProgram`; no field polynomial,
modulus, multiplication table, nodes, or idempotent coefficients are inputs.
The stage-by-stage execution theorem is separate from this code definition.
-/


/-! Arithmetic consumers use the same bytes generated by the preceding
stages.  These are structural handoff lemmas; the complete production
trace must establish `NativeBytes` before invoking them. -/

namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram
open BitProgram StructuredCalls SubexpQuarticRing SubexpLiftRing StackRoutines

/-- A fresh private Newton execution produces the persistent coefficient
master.  Its modulus/cache witnesses are generated, not supplied inputs. -/
theorem idempotentPhase_eval (a : Data) (t W : ℕ) (ht : 0 < t)
    (hv : CounterPrograms.value (a.stacks 373)=t)
    (hw : ∀ i,(a.stacks i).length ≤ W) :
    ∃ n ≤ idempotentBudget t W, ∃ e : Data,
      ∃ (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
        (u : RingProgram.ScalarCode 3 t),
      Eval idempotentPhase n a e ∧
      e.stacks 281=RingProgram.flat (IdempotentProgram.binaryLiftWords t M cache u) ∧
      (2 : ZMod (3^t))*wordValue 3 t u=1 ∧
      (∀ i, i∉idempotentStartPorts → e.stacks i=a.stacks i) := by
  let a0 := clearedPorts idempotentStartPorts a
  have hc := clearPorts_eval idempotentStartPorts a
  have h373 : a0.stacks 373=a.stacks 373 := by
    have hnot : (373 : Fin 640)∉idempotentStartPorts := by decide
    simp [a0,clearedPorts_stacks,hnot]
  have h511 : a0.stacks 511=[] := by
    simp only [a0,clearedPorts_stacks]
    have hm : (511 : Fin 640)∈idempotentStartPorts := by decide
    simp [hm]
  have h639 : a0.stacks 639=[] := by
    simp [a0,clearedPorts_stacks,idempotentStartPorts]
  let a1 : Data := ⟨readRegs a0.regs 30 31 none,
    Function.update a0.stacks 511 (a0.stacks 373)⟩
  have hcopy : Eval (overwrite 373 511) (7*(a.stacks 373).length+8) a0 a1 := by
    simpa [a1,h511,h373] using overwrite_eval 373 511 a0 (by decide) (by decide) (by decide) h639
  let a2 := RegisterResetProgram.zeroed a1
  have hr := RegisterResetProgram.all_eval a1
  have hin : projectState (registers 8 (by decide)) idempotent a2=
      IdempotentPreparationProgram.inputData (a.stacks 373) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j
      change Function.update a0.stacks 511 (a0.stacks 373) (idempotent j)=_
      by_cases hj : j=31
      · subst j
        change Function.update a0.stacks 511 (a0.stacks 373) 511=a.stacks 373
        simp [h373]
      · have hn : idempotent j≠511 := by
          intro he
          exact hj (idempotent_injective he)
        have hm : idempotent j∈idempotentStartPorts := by
          simp [idempotentStartPorts,idempotentPorts]
        simp [hn,a0,clearedPorts_stacks,hm,hj]
  obtain ⟨ni,hni,raw,M,cache,u,hi,ho,hu⟩ := idempotentCall_eval a2 (a.stacks 373) t hv ht hin
  let a3 := embedState (registers 8 (by decide)) idempotent a2 raw
  have h512 : a3.stacks 512=RingProgram.flat (IdempotentProgram.binaryLiftWords t M cache u) :=
    (embedState_stack _ _ _ _ idempotent_injective 32).trans ho
  have h281 : a3.stacks 281=[] := by
    rw [show a3.stacks 281=a2.stacks 281 from embedState_stack_frame _ _ _ _ _ (by decide)]
    simp [a2,a1,a0,clearedPorts_stacks,idempotentStartPorts]
  have h639' : a3.stacks 639=[] := by
    rw [show a3.stacks 639=a2.stacks 639 from embedState_stack_frame _ _ _ _ _ (by decide)]
    simpa [a2,a1,RegisterResetProgram.zeroed] using h639
  let e : Data := ⟨readRegs a3.regs 30 31 none,
    Function.update a3.stacks 281 (a3.stacks 512)⟩
  have hp : Eval (overwrite 512 281) (7*(6*t^2)+8) a3 e := by
    simpa only [e,h281,List.length_nil,Nat.mul_zero,Nat.zero_add,h512,IdempotentProgram.completeProgram_output_length] using
      overwrite_eval 512 281 a3 (by decide) (by decide) (by decide) h639'
  have hnc := clearPortsCost_bound idempotentStartPorts a W (fun i _ => hw i)
  have hmono : IdempotentProgram.completeBudget t (a.stacks 373).length ≤
      IdempotentProgram.completeBudget t W := by
    unfold IdempotentProgram.completeBudget IdempotentPreparationProgram.preparationBudget
      IdempotentPreparationProgram.finishBudget IdempotentPreparationProgram.Scan.tableBudget
      IdempotentPreparationProgram.Scan.scanBudget IdempotentProgram.nativeLiftBudget
    gcongr
    all_goals exact hw 373
  refine ⟨clearPortsCost idempotentStartPorts a+(7*(a.stacks 373).length+8)+32+ni+(7*(6*t^2)+8),
    ?_,e,M,cache,u,?_,?_,hu,?_⟩
  · have hn := hni.trans hmono
    have hb := hw 373
    unfold idempotentBudget
    omega
  · simpa only [idempotentPhase,Nat.add_assoc] using hc.seq (hcopy.seq (hr.seq (hi.seq hp)))
  · simpa [e] using h512
  · intro i hi'
    have hn281 : i≠281 := by intro he; subst i; exact hi' (by simp [idempotentStartPorts])
    have hn511 : i≠511 := by intro he; subst i; exact hi' (by decide)
    have hn : ¬∃ j,idempotent j=i := by
      rintro ⟨j,rfl⟩
      exact hi' (by simp [idempotentStartPorts,idempotentPorts])
    simp only [e,Function.update_of_ne hn281]
    rw [show a3.stacks i=a2.stacks i from embedState_stack_frame _ _ _ _ _ hn]
    simp [a2,a1,hn511,a0,clearedPorts_stacks,hi']

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

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

/-- The actual per-query call after ring setup and interpolation. No
inverse-denominator word is an input: stack 728 starts empty and is filled by
an executed binary-to-ring lift followed by R-1 native multiplications. -/
theorem produced_command_eval (a : Data) (m : LeafParametersProgram.Circuit.Model)
    (ht : 0 < m.val 33) (hd : 0 < m.val 34)
    (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
    (cache : RingProgram.ScalarCache 3 (m.val 33))
    (u : RingProgram.ScalarCode 3 (m.val 33)) (e : LeafRingSetupProgram.Data)
    (hp : LeafRingSetupProgram.Produced m hd M cache u e)
    (hf : ∀i : Fin 640,i.val < 340 → a.stacks (LeafRingSetupProgram.wideStacks i)=e.stacks i)
    (hc : ∀i : Fin 768,340 ≤ i.val → i.val < 596 → a.stacks i=[])
    (hout : a.stacks 728=[]) (W : ℕ) (hw : WordBound W a) :
    ∃ n ≤ budget (a.stacks 740).length (m.val 33) (m.val 34) W, ∃ out : Data,
      Eval command n a out ∧
      out.stacks=Function.update a.stacks 728 (RingProgram.flat
        (value (m.val 33) (IrreducibleSearch.data hd) M cache u (a.stacks 740).length)) ∧
      (RingProgram.modelRing (m.val 33) ht hd (IrreducibleSearch.data hd) M cache).decode
        (value (m.val 33) (IrreducibleSearch.data hd) M cache u (a.stacks 740).length) *
        (2 : (IrreducibleSearch.data hd).O (m.val 33)) ^ ((a.stacks 740).length-1)=1 ∧
      (∀i : Fin 40,16 ≤ i.val → out.regs i=a.regs i) := by
  have hready := ready_of_caches (projectState registers id a) (m.val 33) (m.val 34)
    (IrreducibleSearch.data hd) M cache u e hp.caches hf
  have hu : a.stacks 253=u.val := (hf 253 (by decide)).trans hp.caches.half
  have hsize : m.val 34*baseWidth 3 (m.val 33) ≤ W := by
    have hh := hw 280
    have he : a.stacks 280=RingProgram.flat
        (LeafProgram.Constants.constantCode (m.val 34) cache.zero cache.zero) := by
      rw [LeafProgram.Constants.constantCode_flat]
      exact (hf 280 (by decide)).trans hp.caches.fullZero
    rw [he,RingProgram.flat_length] at hh
    exact hh
  obtain ⟨n,hn,out,he,hout',hr⟩ := command_eval a (m.val 33) (IrreducibleSearch.data hd) M cache
    _ _ _ u hp.caches.canonical hready hu
    (fun i hi => hc i ((mem_bank i).mp hi).1 ((mem_bank i).mp hi).2) hout W hw hsize
  refine ⟨n,hn,out,he,hout',?_,hr⟩
  exact LayoutDenominatorProgram.value_inverse (m.val 33) ht hd (IrreducibleSearch.data hd)
    M cache _ _ _
    (LeafProgram.Constants.zero_decode _ ht hd _ M cache)
    (LeafProgram.Constants.one_decode _ ht hd _ M cache)
    (LeafProgram.Constants.minusOne_decode _ ht hd _ M cache)
    u hp.caches.inverse _

end SubexponentialSAT.SqrtLog.LayoutDenominatorProgramQuery

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblySourceStored
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The executed source predicate determines the incidence jet independently
of the particular coefficient-array witness returned by each source call. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT DensePolynomialProgram
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
open LayoutSourceRowsProgram LeafProgram.NativeSemantics
open scoped BigOperators

/-- Witness-free intended jet: the low branch uses the fixed source family;
the high branch is exactly the current fixed Boolean assignment. -/
noncomputable def sourceIncidenceJet {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (n f j : ℕ) (theta : Coeff (baseWidth 3 p.t) d) (s : OuterStore) :
    Squarefree.Jet (Fin n) (p.model.O p.t) :=
  if (s 574).getD j false then
    Squarefree.Sparse.atom Squarefree.Index.origin (if (s 575).getD j false then 1 else 0)
  else Moments.incidenceJet (fixedSourceRow p ps P n f j) (p.ops.decode theta)
    (∑ v : Fin n, (fixedSourceRow p ps P n f j v).eval (p.ops.decode theta) *
      (if (s 546).getD v.val false then 1 else 0))

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramFactorJet
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The incidence meaning depends only on the merged assignment and the
fixed-high context. Parser and accumulator contents do not enter it. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Factor
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
open PerturbationAssembly DensePolynomialProgram

noncomputable def factorJet {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (n f j : ℕ) (theta : Coeff (baseWidth 3 p.t) d) (s : Fin 768 → List Bool) :=
  sourceIncidenceJet p ps P n f j theta (choiceStore s)

end SubexponentialSAT.SqrtLog.LeafProgram.Factor

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramFactorSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One executed factor step, specialized to the actual source ring, its
computed multiplication table, and the three physical assignment masters. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Factor.Semantics
open SubexponentialSAT SubexpLiftRing SubexpQuarticRing
open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
open HashCircuitProgram HashCircuitProgram.Native
open LeafProgram.NativeSemantics LeafProgram.AssignmentSemantics
open scoped BigOperators

variable {r Q d n : ℕ}

noncomputable def hashValue (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (u J f : ℕ) (width : List Bool) (hw : width.length=baseWidth 3 p.t)
    (theta : DensePolynomialProgram.Coeff (baseWidth 3 p.t) d) (s : Fin 768 → List Bool)
    (source : List (List (SAT.Literal (Fin n))))
    (terms : List (Fin (HashInputProgram.Expansion.encodedClauses source).length × ZMod 3))
    (code : RingProgram.Code (RingProgram.ScalarCode 3 p.t) (3*p.t)) :
    Squarefree.Jet (Fin n) (p.model.O p.t) :=
  letI : CommRing (Squarefree.Poly (Fin n) (p.model.O p.t)) := inferInstance
  letI : CommRing (Squarefree.ZJet (Fin n) (p.model.O p.t)) := inferInstance
  letI : CommRing (Squarefree.Jet (Fin n) (p.model.O p.t)) := inferInstance
  indicatorPolynomial (sourceContext p n u J width hw) (LiftRing.of (p.model.F p.t)) code
    (MvPolynomial.eval (fun v : Fin n => factorJet p ps P n f v.val theta s)
      (rowPolynomial (scalarJet (V:=Fin n)) (sourceTerms p.ops.decode
        (HashInputProgram.Expansion.weightedRow p.t d source terms))))

noncomputable def markedValue (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (f : ℕ) (theta : DensePolynomialProgram.Coeff (baseWidth 3 p.t) d)
    (s : Fin 768 → List Bool) (ls : List (SAT.Literal (Fin n))) :
    Squarefree.Jet (Fin n) (p.model.O p.t) :=
  letI : CommRing (Squarefree.Poly (Fin n) (p.model.O p.t)) := inferInstance
  letI : CommRing (Squarefree.ZJet (Fin n) (p.model.O p.t)) := inferInstance
  letI : CommRing (Squarefree.Jet (Fin n) (p.model.O p.t)) := inferInstance
  MvPolynomial.eval (fun v : Fin n => factorJet p ps P n f v.val theta s)
    (clausePolynomial (R:=Squarefree.Jet (Fin n) (p.model.O p.t)) ls)

end SubexponentialSAT.SqrtLog.LeafProgram.Factor.Semantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramFactorSpec
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Source data and physical premises for the concrete factor callback.
The records below contain no execution hypotheses. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Factor
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram HashCircuitProgram.Native
open IdempotentApplyProgram.Steps MomentsProgram
open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
open PerturbationAssembly DensePolynomialProgram NativeSemantics SubexpSetupStorage

namespace Spec
variable {r Q n d : ℕ} (q : Spec r Q n d)
noncomputable def value (s : Fin 768 → List Bool) (f : ℕ) : Squarefree.Jet (Fin n) (q.p.model.O q.p.t) :=
  if h : f < q.rows.length then
    Semantics.hashValue q.p q.ps q.packing q.u q.J f q.width q.widthLength q.theta s q.source q.rows[f] q.code
  else if q.marked && decide (f=q.rows.length) then
    Semantics.markedValue q.p q.ps q.packing f q.theta s q.markedClause
  else 1
end Spec

end SubexponentialSAT.SqrtLog.LeafProgram.Factor

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramAssignmentConcrete
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The relational, actually executed assignment fold has the same value as
the selected-factor expression used by the node proof.  This bridge chooses
no raw representative and retains the shared U and T truncations. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.AssignmentConcrete

open SubexponentialSAT SubexpLiftRing SubexpQuarticRing MomentsProgram MomentsAssembly
open HashCircuitProgram HashCircuitProgram.Native
open scoped BigOperators

variable {r Q n d : ℕ}

def sourceJets (q : Factor.Spec r Q n d) (s : Fin 768 → List Bool) :
    ℕ → Fin n → Squarefree.Jet (Fin n) (q.p.model.O q.p.t) :=
  fun id v => Factor.factorJet q.p q.ps q.packing n id v.val q.theta s

end SubexponentialSAT.SqrtLog.LeafProgram.AssignmentConcrete

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramNodeConcreteRows
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The source rows used by the native factor callback retain their concrete
origin, degree, and original-coordinate support after incidence pullback. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking
open LayoutProgram LayoutSourceRowsProgram PerturbationAssembly

variable {r Q d : ℕ}

theorem fixedSourceRow_zero (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (n f j : ℕ) (v : Fin n) (hv : ∀ a ∈ ps, a.1 ≠ v.val) :
    fixedSourceRow p ps P n f j v = 0 := by
  unfold fixedSourceRow sourceRowFamily
  split_ifs
  · exact ownerSum_zero ps v.val _ hv
  · rfl

end SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramNodeConcreteTarget
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A total source target with the original variable IDs. Missing incidences
are filled by identity rows only in this mathematical totalization; scoped
factor evaluation never reads those rows. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking
open LayoutProgram PerturbationAssembly

variable {r Q d n : ℕ}

def completedRows (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (H : Finset (Fin n)) (f : ℕ) (j : Fin n) (v : ResidualEmbedding.Free H) :
    Polynomial (p.model.O p.t) :=
  if (j.val,n+f) ∈ ps then fixedSourceRow p ps P n f j.val v.val
  else Polynomial.C (if v.val=j then 1 else 0)

end SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramNodeConcreteCode
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The target uses the actual binary Newton coefficient array. Its constant
and degree statements do not replace it by a separate coefficient algorithm. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete
open scoped BigOperators
open Polynomial
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking
open LayoutProgram PerturbationAssembly

variable {r Q d n : ℕ}

def binaryTarget (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (M : SubexpPreparedQuartic.Modulus 3 p.t) (cache : RingProgram.ScalarCache 3 p.t)
    (half : RingProgram.ScalarCode 3 p.t) (H : Finset (Fin n)) (high : H → Bool)
    (hashes : List (SparseRow (Fin n) (ZMod 3))) (marked : Bool)
    (clause : List (SAT.Literal (Fin n))) : Polynomial (p.model.O p.t) :=
  NodeSemantics.target H p.t (binaryDigits p M cache half)
    (NodeSemantics.liftedHashes p.model p.t hashes) marked clause
    (NodeSemantics.branchPath H high (completedRows p ps P H))

end SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramNodeConcreteResidual
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Source jets live in the free-coordinate squarefree algebra even though
the runtime stores every key at its original ambient ID. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open DensePolynomialProgram LayoutProgram PerturbationAssembly Polynomial

variable {r Q d n : ℕ}

def baseline (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (theta : Coeff (baseWidth 3 p.t) d) (s : Fin 768 → List Bool) (f j : ℕ) :=
  ∑ v : Fin n, (fixedSourceRow p ps P n f j v).eval (p.ops.decode theta)*
    (if (s 145).getD v.val false then 1 else 0)

def residualJet (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (H : Finset (Fin n)) (high : H → Bool)
    (theta : Coeff (baseWidth 3 p.t) d) (s : Fin 768 → List Bool)
    (f : ℕ) (j : Fin n) : Squarefree.Jet (ResidualEmbedding.Free H) (p.model.O p.t) :=
  if hj : j∈H then Moments.ringScalar (HashInput.boolValue (high ⟨j,hj⟩))
  else Moments.incidenceJet (fun v : ResidualEmbedding.Free H => fixedSourceRow p ps P n f j.val v.val)
    (p.ops.decode theta) (baseline (n:=n) p ps P theta s f j.val)

end SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramNodeConcreteSpecTarget
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One source target is attached to the concrete factor specification. It
retains raw term multiplicity, optional marked violation, and shared U order. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete
open scoped BigOperators
open Polynomial
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open HashCircuitProgram HashCircuitProgram.Native

variable {r Q d n : ℕ}

def specTarget (q : Factor.Spec r Q n d) (H : Finset (Fin n)) (high : H → Bool) :
    Polynomial (q.p.model.O q.p.t) :=
  NodeSemantics.target H q.p.t (NodeSemantics.codeDigits q.ctx (q.p.model.base q.p.t) q.code)
    (decodedHashes q) q.marked q.markedClause
    (NodeSemantics.branchPath H high (completedRows q.p q.ps q.packing H))

end SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramPreparedSource
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The source parameter object is derived from the executed query's numeric
bank, ring setup, and native head cache. Source order and jet order remain distinct. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open LeafParametersProgram MulticolorTypes Subexp LayoutProgram
open HashCircuitProgram HashCircuitProgram.Native NativeSemantics
noncomputable section

theorem numeric_d (q : LeafQueryFrontend.Query) (k : ℕ) (l : Fin 8 → ℕ)
    (hg : Guard (q.input k)) : (numeric q k l).val 34=(produce (q.input k)).d := by
  apply Execute.guardedModel_degree
  have h := hg.2.2.2.2.2.2.1
  omega

theorem numeric_J (q : LeafQueryFrontend.Query) (k : ℕ) (l : Fin 8 → ℕ)
    (hg : Guard (q.input k)) : (numeric q k l).val 42=(produce (q.input k)).J := by
  apply (Execute.guardedModel_public (q.input k) l 11).trans
  apply Layout.model_jet _ _ (Nat.ne_of_gt hg.2.2.1)
  have h := hg.2.2.2.2.2.2.1
  omega

end
end SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramPreparedFactorBase
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The factor specification uses the actual generated idempotent code and
native node word. The existential scalar preparation of the code is retained
as a witness; no canonical-byte assumption is needed. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open LeafParametersProgram MulticolorTypes Subexp LayoutProgram
open HashCircuitProgram HashCircuitProgram.Native NativeSemantics
noncomputable section

def nativeSpecOfInputs (s : LeafHeadSetupProgram.Native.Inputs)
    (m : Circuit.Model) (ht : 0 < m.val 33) (hd : 0 < m.val 34)
    (words : List (List Bool))
    (hc : LeafHeadSetupProgram.CacheCorrect s.height (LeafHeadSetupProgram.unary s.R) s.width words)
    (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
    (cache : RingProgram.ScalarCache 3 (m.val 33)) (half : RingProgram.ScalarCode 3 (m.val 33))
    (e : LeafRingSetupProgram.Data) (hp : LeafRingSetupProgram.Produced m hd M cache half e)
    (hfield : s.Q < 3^(m.val 34)) (q : LeafQueryFrontend.Query) (hv : q.Valid)
    (J : ℕ) (hJ : 0 < J) (source : List (List (SAT.Literal (Fin s.n))))
    (hsource : q.clauses=HashInputProgram.Expansion.encodedClauses source) :
    Factor.Spec s.r s.Q s.n (m.val 34) :=
  factorSpec (SourceBank.Parameters.ofProduced s words hc m ht hd M cache half e hp hfield)
    s.plans (PackingIncidenceInput.reindexPacking s.plans_length.symm s.packing)
    q hv J hJ source hsource (RingNodeProgram.nodeCode (m.val 33) (m.val 34) (s.node.val+1))
    (e.stacks 202) hp.caches.width (generatedCode hp).code

end
end SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafRingSetupProgramInterpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! Paid staging of the native interpolation-cache producer in the wide
leaf machine. The private 320-tape bank is disjoint from all ring and
collector masters. Native table computation is followed by paid extraction
of all five outputs; the entire staging bank is then cleared. -/
namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Interpolation
open BitProgram StructuredCalls StackRoutines SubexpLiftRing SubexpQuarticRing

abbrev command : Cmd 40 768 :=
  .seq (clearPorts (699::privatePorts)) (.seq (copyPlan inputPlan)
    (.seq coreCall (.seq (copyPlan outputPlan) (clearPorts privatePorts))))

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Interpolation

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramQueryRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Ring and interpolation setup are performed once per marked query. All
arithmetic objects in the conclusion are generated by the two native programs. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query.Ring
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram
open LeafRingSetupProgram

def command : Query.Code := .seq producerWideCall Interpolation.command

end SubexponentialSAT.SqrtLog.LeafProgram.Query.Ring

end OAI.Algorithms
end


