-- Prove2me | Definitions.Def_OAIQ081S176
-- name    : OAIQ081S176
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T23:24:56.335994+00:00
-- url     : https://prove2.me/theorems/aeda80c1-23fb-4834-9c13-de9ac9333c0d
-- title:
--   Definitions bundle OAIQ081S176 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 30 declarations of OpenAI's Lean: 15 definitions and 15 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Query.markedFrontend`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Source.nativeSourceWorkPolynomial`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.coreCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.frontend`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.parameterCall`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.budget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.compute`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.core`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.coreProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.middle`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.result`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgram.loop`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.Lower`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLogSpace_HighQueryCorrect`, `SubexponentialSAT_SqrtLogSpace_HighQuerySetup`, `SubexponentialSAT_SqrtLog_LeafProgramQueryFrontend`, `SubexponentialSAT_SqrtLog_LeafProgramQueryPackingEmpty`, `SubexponentialSAT_SqrtLog_LeafProgramQueryPackingInput`, `SubexponentialSAT_SqrtLog_LeafProgramQueryWidthArithmetic`, `SubexponentialSAT_SqrtLog_LeafProgramSourceNativeCost`, `SubexponentialSAT_SqrtLog_LeafQueryFrontendCalls`, `SubexponentialSAT_SqrtLog_LeafQueryFrontendCore`, `SubexponentialSAT_SqrtLog_LeafQueryFrontendOutput`, `SubexponentialSAT_SqrtLog_LeafQueryFrontendRun`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramReplay`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramTableBridge`, `SubexponentialSAT_SqrtLog_PackingCallerProgram`, `SubexponentialSAT_SqrtLog_PackingCallerProgramCore`, `SubexponentialSAT_SqrtLog_PackingCallerProgramCost`, `SubexponentialSAT_SqrtLog_PackingCallerProgramJoin`, `SubexponentialSAT_SqrtLog_PackingCallerProgramOutput`, `SubexponentialSAT_SqrtLog_PackingCallerProgramReplay`, `SubexponentialSAT_SqrtLog_PackingCallerProgramState`, `SubexponentialSAT_SqrtLog_PackingIncidenceInputNative`, `SubexponentialSAT_SqrtLog_PerturbationBetaProgram`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S166`, `OAIQ081S168`, `OAIQ081S169`, `OAIQ081S170` and `OAIQ081S171` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S182`, `OAIQ081S183` and `OAIQ081S184`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect.NodeBoundary.sourceBank` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.parameterCall_eval`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.accepted`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.marked`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.accepted_replay`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.marked_replay`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedHeads.query_max_bound_rat`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.parameterCall_eval` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResources.rank_budget`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S166
import Definitions.Def_OAIQ081S168
import Definitions.Def_OAIQ081S169
import Definitions.Def_OAIQ081S170
import Definitions.Def_OAIQ081S171

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendCalls
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The frontend calls only concrete finite machines. All state embeddings
below are specifications of actual calls, never free data transformations. -/
namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls

def parameterCall : Code := .call (ProgramLinking.liftProgram LeafParametersProgram.Execute.program r9 bank)

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Joined per-query core. Mathematical values below describe physical input
words and computed outputs; they are not extra machine inputs. -/
namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod

def coreCommand (k : ℕ) : Code := .seq rawCommand (.seq highCommand
  (.seq measureCommand (.seq (numericStage k) parameterCall)))

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod
open LeafParametersProgram

def frontend (k : ℕ) : Code := .seq countHashes (.seq (coreCommand k) postCommand)

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramQueryFrontend
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native frontend entry from an actual marked-reference reader state. All
computed-size witnesses remain explicit in the paid budget. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram

def markedFrontend (k : ℕ) : Code := .seq markInput (LeafQueryFrontend.frontend k)

end SubexponentialSAT.SqrtLog.LeafProgram.Query

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafRingSetupProgramTableBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Physical table-input projection and the exact native table-call bridge. -/
namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram
open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing RingProgramTable

attribute [local instance] OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.instFactPrimeOfNatNat_solutions_3
/-- No table is supplied to this call. It runs native power recurrence and
layout on the actual runtime coefficient array. -/
theorem tableCall_produces (t : ℕ) {d : ℕ} (hd : 0 < d) (model : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (ho : BinaryArithmetic.toNat cache.one.val < 3^t)
    (a : LeafRingSetupProgram.Data) (h : TableInput t d model M cache a) :
    ∃ n ≤ 208000*(d+1)^5*(t+1)^2, ∃ e : LeafRingSetupProgram.Data,
      Eval tableCall n a e ∧ e.stacks 201=modelTable t model M cache ∧
      e.stacks 194=a.stacks 194 ∧ e.stacks 202=a.stacks 202 ∧
      e.stacks 203=cache.zero.val ∧ e.stacks 204=a.stacks 204 ∧
      e.stacks 508=cache.minusOne.val ∧
      (∀ i, (¬ ∃ j, LeafRingSetupProgram.table j=i) → e.stacks i=a.stacks i) := by
  obtain ⟨rf,n,hn,he⟩ := table_program_run t hd model M cache hz ho
    (tableInputStore a) (a.regs ∘ registers 8 (by decide)) h.modulus h.width h.degree
  let out := Machine.state rf
    (preparedStore 3 t M cache (modelCoefficients t model) (tableInputStore a))
    (modelTable t model M cache)
  let e := embedState (registers 8 (by decide)) LeafRingSetupProgram.table a out
  have he' : Eval tableCall n a e :=
    eval_call_from_state Machine.program (registers 8 (by decide)) LeafRingSetupProgram.table
      a (registers_injective 8 (by decide)) table_injective (h.project.symm ▸ he)
  have hp (i : Fin 42) : e.stacks (LeafRingSetupProgram.table i)=out.stacks i :=
    embedState_stack _ _ _ _ table_injective i
  refine ⟨n,hn,e,he',?_,?_,?_,?_,?_,?_,?_⟩
  · simpa [LeafRingSetupProgram.table,out,Machine.state] using hp 27
  · simpa [LeafRingSetupProgram.table,out,Machine.state,preparedStore,ready,tapes,tableInputStore] using hp 5
  · simpa [LeafRingSetupProgram.table,out,Machine.state,preparedStore,ready,tapes,tableInputStore] using hp 12
  · simpa [LeafRingSetupProgram.table,out,Machine.state,preparedStore,ready,tapes,tableInputStore] using hp 24
  · simpa [LeafRingSetupProgram.table,out,Machine.state,preparedStore,ready,tapes,tableInputStore] using hp 22
  · simpa [LeafRingSetupProgram.table,out,Machine.state,preparedStore,ready,tapes,tableInputStore] using hp 17
  · intro i hi
    exact embedState_stack_frame _ _ _ _ _ hi


end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramQueryWidthArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed ordinary polynomial bounds the literal ring, interpolation and
layout-denominator setup budgets, including their staging copies. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query.Width
open SubexponentialSAT LeafParametersProgram SubexpLiftRing CostAssembly.Polynomial

theorem interpolation_bound (t d Q S : ℕ) (ht : t ≤ S) (hd : d ≤ S) (hQ : Q ≤ S)
    (hf : 3^d ≤ 16*(Q+1)^2) :
    InterpolationCacheProgram.budget t d Q ≤ interpolationEnvelope S := by
  have hi := InterpolationCacheProgram.budget_polynomial t d Q
  have hm := HornerProgram.Services.mulBudget_polynomial (baseWidth 3 t) d
  have ha := HornerProgram.Services.addBudget_polynomial (baseWidth 3 t) d
  simp only [RingProgram.ternary_baseWidth] at hm ha hi
  have hb : HornerProgram.Services.mulBudget (2*t) d+
      HornerProgram.Services.addBudget (2*t) d+d*(2*t)+1 ≤
      100000*(S+1)^3*(2*S+1)^2+2*S*S+1 := by
    have hm' : HornerProgram.Services.mulBudget (2*t) d ≤ 50000*(S+1)^3*(2*S+1)^2 :=
      hm.trans (by gcongr)
    have ha' : HornerProgram.Services.addBudget (2*t) d ≤ 50000*(S+1)^3*(2*S+1)^2 :=
      ha.trans (by gcongr)
    have hdt : d*(2*t) ≤ 2*S*S := by nlinarith [Nat.mul_le_mul hd ht]
    nlinarith only [hm',ha',hdt]
  unfold interpolationEnvelope
  exact (Nat.le_of_succ_le hi).trans (by gcongr; exact hf.trans (by gcongr))

theorem arithmetic_budget_polynomial : ∃ C e : ℕ, ∀ (m : Circuit.Model) (W V L R S : ℕ),
    W ≤ S → V ≤ S → L ≤ S → R ≤ S → (∀i,m.len i ≤ S) → (∀i,m.val i ≤ S) →
    3^(m.val 34) ≤ 16*(m.val 21+1)^2 → arithmeticBudget m W V L R ≤ C*(S+1)^e := by
  obtain ⟨C,e,hp⟩ := CostAssembly.RingSetup.producerBudget_ordinary
  obtain ⟨A,d,had⟩ := arithmeticEnvelope_ordinary C e
  refine ⟨A,d,?_⟩
  intro m W V L R S hW hV hL hR hl hv hf
  have hprod := hp m W V L S hW hV hL hl (hv 33) (hv 34) (hv 21) hf
  have hi := interpolation_bound (m.val 33) (m.val 34) (m.val 21) S (hv 33) (hv 34) (hv 21) hf
  have hr : Ring.budget m W V L ≤ ringEnvelope C e S := by
    dsimp only [Ring.budget,ringEnvelope]
    omega
  have hd := LayoutDenominatorProgramQuery.budget_polynomial R (m.val 33) (m.val 34)
    (W+Ring.budget m W V L+1)
  simp only [RingProgram.ternary_baseWidth] at hd
  have hpoly : LayoutDenominatorProgram.polynomialBudget R (2*m.val 33) (m.val 34) ≤
      LayoutDenominatorProgram.polynomialBudget S (2*S) S := by
    unfold LayoutDenominatorProgram.polynomialBudget
    gcongr <;> first | exact hv 33 | exact hv 34
  apply le_trans _ (had S)
  unfold arithmeticBudget arithmeticEnvelope
  omega

end SubexponentialSAT.SqrtLog.LeafProgram.Query.Width

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendOutput
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls
open LeafParametersProgram

/-- Direct input-statistic values in the persistent metadata bank. -/
theorem exported_input_values (x : Input) (l : Fin 8 → ℕ) (a : Data)
    (h : Exported (Execute.guardedModel x l) a) :
    a.stacks 128=List.replicate x.ambient true ∧
    a.stacks 129=List.replicate x.factors true ∧
    BinaryArithmetic.toNat (a.stacks 723)=x.incidences ∧
    BinaryArithmetic.toNat (a.stacks 724)=x.freeCount ∧
    BinaryArithmetic.toNat (a.stacks 725)=x.occurrence ∧
    BinaryArithmetic.toNat (a.stacks 726)=x.factors := by
  have h0 : (Execute.guardedModel x l).val 0=x.ambient := Execute.guardedModel_input x l 0
  have h1 : (Execute.guardedModel x l).val 1=x.freeCount := Execute.guardedModel_input x l 1
  have h3 : (Execute.guardedModel x l).val 3=x.occurrence := Execute.guardedModel_input x l 3
  have h5 : (Execute.guardedModel x l).val 5=x.factors := Execute.guardedModel_input x l 5
  have h7 : (Execute.guardedModel x l).val 7=x.incidences := Execute.guardedModel_input x l 7
  exact ⟨by simpa [Exports.destination,Exports.unaryValues,h0] using h.1 0,
    by simpa [Exports.destination,Exports.unaryValues,h5] using h.1 1,
    by simpa [Exports.destination,Exports.binarySources,h7] using h.2 3,
    by simpa [Exports.destination,Exports.binarySources,h1] using h.2 4,
    by simpa [Exports.destination,Exports.binarySources,h3] using h.2 5,
    by simpa [Exports.destination,Exports.binarySources,h5] using h.2 6⟩

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

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
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Step
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

theorem command_eval (r : Fin 16 → Bool) (scopes : List (List ℕ)) (n v z : ℕ)
    (mask out : List Bool) :
    ∃ t rf, t ≤ bound scopes n v z ∧
      Eval command t (Scan.data r scopes n v z mask out)
        (Scan.data rf scopes n v (next scopes v z) mask (output scopes n v z out)) ∧
      (∀ i : Fin 16, 12 ≤ i.val → rf i = r i) := by
  obtain ⟨ts,rs,hts,hs,hrs⟩ := Scan.command_eval r scopes n v z mask out
  rw [Lift.scan_eq_work] at hs
  let bit := decide (Scan.indices scopes v ≠ [])
  let rp := readRegs rs 10 11 (some bit)
  have hp := peek_eval rs scopes n v z mask out
  change Eval peek 2
    (Lift.work rs scopes n v z mask out
      (Encoding.encodeList Rows.unary (Scan.indices scopes v).reverse) [])
    (Lift.work rp scopes n v z mask out
      (Encoding.encodeList Rows.unary (Scan.indices scopes v).reverse) []) at hp
  by_cases hempty : Scan.indices scopes v = []
  · simp only [hempty,List.reverse_nil,Encoding.encodeList] at hs hp
    have hbit : rp 10 = false := by simp [rp,bit,hempty,readRegs]
    obtain ⟨tb,rb,htb,hb,hrb⟩ := neutral_eval rp scopes n v z mask out [false]
    have hbranch := Eval.ite_false (test := 10) (yes := rows) hbit hb
    obtain ⟨tc,rc,htc,hc,hrc⟩ := Lift.clean_eval rb scopes n v (z+1) mask
      (Rows.recordPrefix v n z ++ out) [false]
    have he := hs.seq (hp.seq (hbranch.seq hc))
    refine ⟨ts+(2+((tb+1)+tc)),rc,?_,?_,?_⟩
    · dsimp [bound]; omega
    · simpa [command,branch,next,output,factors,hempty,Encoding.encodeList,
        Rows.prefixes] using he
    · intro i hi
      have h0 : i ≠ 10 := by intro h; subst i; omega
      have h1 : i ≠ 11 := by intro h; subst i; omega
      rw [hrc i (by omega),hrb i (by omega)]
      simpa [rp,readRegs,h0,h1] using hrs i (by omega)
  · have hbit : rp 10 = true := by simp [rp,bit,hempty,readRegs]
    obtain ⟨tb,rb,htb,hb⟩ := Rows.command_eval (Scan.indices scopes v).reverse
      (rp ∘ Lift.registers) v n out []
    simp only [List.append_nil,List.reverse_reverse] at hb
    obtain ⟨rr,hrun,hrr⟩ := Lift.command_eval Rows.command rp scopes n v z mask out
      (Encoding.encodeList Rows.unary (Scan.indices scopes v).reverse) []
      (Rows.prefixes v n (Scan.indices scopes v) ++ out) [] tb rb hb
    have hbranch := Eval.ite_true (test := 10) (no := neutral) hbit hrun
    obtain ⟨tc,rc,htc,hc,hrc⟩ := Lift.clean_eval rr scopes n v z mask
      (Rows.prefixes v n (Scan.indices scopes v) ++ out) []
    have he := hs.seq (hp.seq (hbranch.seq hc))
    refine ⟨ts+(2+((tb+1+1)+tc)),rc,?_,?_,?_⟩
    · dsimp [bound,Lift.cleanBound] at *; omega
    · simpa [command,branch,rows,next,output,factors,hempty] using he
    · intro i hi
      have h0 : i ≠ 10 := by intro h; subst i; omega
      have h1 : i ≠ 11 := by intro h; subst i; omega
      rw [hrc i (by omega),hrr i (by omega)]
      simpa [rp,readRegs,h0,h1] using hrs i (by omega)
end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Step


/-! Runtime high-mask loop for the original-address incidence stream. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Loop
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

theorem body_eval (r : Fin 16 → Bool) (scopes : List (List ℕ)) (n v z : ℕ)
    (high : Bool) (mask out : List Bool) (hr : r 14 = high) :
    ∃ t rf, t ≤ (if high then 2 else Step.bound scopes n v z+1)+2 ∧
      Eval body t (Scan.data r scopes n v z mask out)
        (Scan.data rf scopes n (v+1) (if high then z else Step.next scopes v z) mask
          (recordPrefix (if high then [] else rowPlans scopes n v z) ++ out)) := by
  cases high
  · obtain ⟨t,rr,ht,he,_⟩ := Step.command_eval r scopes n v z mask out
    have hb := Eval.ite_false (test := 14) (yes := .base .skip) hr he
    let a := Scan.data rr scopes n v (Step.next scopes v z) mask (Step.output scopes n v z out)
    have hi := TupleProgram.pushConst_eval (22 : Fin 32) (0 : Fin 16) true a
    let b := TupleProgram.pushedState 22 0 true a
    have hend : b = Scan.data b.regs scopes n (v+1) (Step.next scopes v z) mask
        (recordPrefix (rowPlans scopes n v z) ++ out) := by
      apply congrArg (StructuredProgram.State.mk b.regs)
      funext i; fin_cases i <;>
        simp [a,Scan.data,List.replicate_succ,Step.output,row_prefix]
    change Eval _ _ a b at hi
    rw [hend] at hi
    refine ⟨t+3,b.regs,by simpa using Nat.add_le_add_right ht 3,?_⟩
    simpa [body] using hb.seq hi
  · let a := Scan.data r scopes n v z mask out
    have hb := Eval.ite_true (test := 14) (no := Step.command) hr (Eval.base (.skip a))
    have hi := TupleProgram.pushConst_eval (22 : Fin 32) (0 : Fin 16) true a
    let b := TupleProgram.pushedState 22 0 true a
    have hend : b = Scan.data b.regs scopes n (v+1) z mask out := by
      apply congrArg (StructuredProgram.State.mk b.regs)
      funext i; fin_cases i <;> simp [a,Scan.data,List.replicate_succ]
    change Eval _ _ a b at hi
    rw [hend] at hi
    refine ⟨3,b.regs,by simp,?_⟩
    simpa [body,recordPrefix] using hb.seq hi

end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Loop


/-! Count the physical scope stream before constructing native incidence plans. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

def core : Code := .seq produce (.seq PackingLoaderProgram.command (.seq selection suffix))
def coreProgram := compiled core 32 63

end SubexponentialSAT.SqrtLog.PackingCallerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramState
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingCallerProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open PackingLoaderProgram PackingIncidenceInput
attribute [local simp] Fin.coe_ofNat_eq_mod

noncomputable def middle (a : Wide.Data) (p : Problem)
    (w : Word p.r p.Q) (tail : List (Word p.r p.Q)) : Wide.Local :=
  ⟨fun _=>false,fun i=>if hi : 417 ≤ i.val ∧ i.val < 481
    then (bankOutput a p w tail).stacks ⟨i.val-417,by omega⟩ else a.stacks i⟩

theorem middle_frame (a : Wide.Data) (p : Problem)
    (w : Word p.r p.Q) (tail : List (Word p.r p.Q)) (i : Fin 768)
    (hi : i.val < 417 ∨ 481 ≤ i.val) : (middle a p w tail).stacks i=a.stacks i := by
  simp [middle,show ¬(417 ≤ i.val ∧ i.val < 481) by omega]

end SubexponentialSAT.SqrtLog.PackingCallerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramQueryPackingInput
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The packing problem is determined by the physically measured query.
In particular its incidence count is the same native mask scan exported by
the frontend, including neutral factors for uncovered low variables. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram

theorem packingProblem_incidences (q : LeafQueryFrontend.Query) (k : ℕ)
    (hg : Guard (q.input k)) : (packingProblem q k hg).incidences=(q.input k).incidences := by
  have h := PackingIncidenceInput.Stats.entries_agree q.scopeRows q.forward 0 q.scopeRows.length
    PackingIncidenceInput.Stats.zero
  simpa [packingProblem,PackingCallerProgram.Problem.incidences,
    PackingIncidenceInput.Semantics.nativeEntries,PackingIncidenceInput.Stats.zero,
    LeafQueryFrontend.totals,LeafStatisticsProgram.zeroTotals,
    LeafQueryFrontend.Query.input,LeafQueryFrontend.numericInput] using h

end SubexponentialSAT.SqrtLog.LeafProgram.Query

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramQueryPackingEmpty
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafProgram.Query
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem packing_empty (a : Data) (hz : LeafQueryFrontend.emptyRange a 417 680)
    (hs : PackingSpare a) : PackingCallerProgram.Empty a := by
  refine ⟨?_,hs.1,hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2⟩
  intro i
  change a.stacks (PackingCallerProgram.Wide.ports i)=[]
  apply hz
  · simp only [PackingCallerProgram.Wide.ports_val]
    omega
  · have hi := i.isLt
    simp only [PackingCallerProgram.Wide.ports_val]
    omega

end SubexponentialSAT.SqrtLog.LeafProgram.Query

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafRingSetupProgramReplay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! Syntactic no-read/no-write certificate for the existing native ring
producer.  Hidden collector tapes do not affect its exact execution time. -/
namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Replay
open BitProgram StructuredCalls ProgramTapeReplay

theorem number : AvoidsCmd hidden numberPhase := by
  have hc : ∀i∈workPorts++outputPorts,¬hidden i := by
    intro i hi
    rcases List.mem_append.mp hi with hi|hi
    · obtain ⟨j,_,rfl⟩ := List.mem_map.mp hi
      apply visible
      right
      change 340 ≤ 417+j.val
      omega
    · have hh : ∀i∈outputPorts,¬hidden i := by
        intro j hj
        apply visible
        left
        simp [outputPorts] at hj
        omega
      exact hh i hi
  have hs : AvoidsCmd hidden serializationCall := by
    apply avoids_call_lift_of_range
    intro i
    apply visible
    right
    change 340 ≤ 340+i.val
    omega
  have hu : AvoidsCmd hidden (LeafRingSetupProgram.unaryPlan numericPlan) :=
    unaryPlan _ (by
      intro p hp
      simp only [numericPlan,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl|rfl|rfl|rfl|rfl <;> decide)
  exact ⟨clearPorts _ hc,hs,hu,overwrite 373 511 (by decide) (by decide),resetAll⟩

theorem core : AvoidsCmd hidden coreCommand := by
  have sc : AvoidsCmd hidden scalarCall :=
    avoids_call_lift_of_range _ _ _ _ (fun i => visible _ (scalar_avoids_collector i))
  have se : AvoidsCmd hidden searchCall :=
    avoids_call_lift_of_range _ _ _ _ (fun i => visible _ (search_avoids_collector i))
  have pa : AvoidsCmd hidden paddingCall :=
    avoids_call_lift_of_range _ _ _ _ (fun i => visible _ (search_avoids_collector i))
  have ta : AvoidsCmd hidden tableCall :=
    avoids_call_lift_of_range _ _ _ _ (fun i => visible _ (table_avoids_collector i))
  exact ⟨sc,overwrite 507 253 (by decide) (by decide),resetAll,
    ⟨se,overwrite 202 432 (by decide) (by decide),pa⟩,
    overwrite 498 538 (by decide) (by decide),ta⟩

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Replay

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramJoin
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingCallerProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open PackingLoaderProgram PackingIncidenceInput

def compute : Wide.Code := .seq Wide.stage (Wide.bankCall coreProgram)

end SubexponentialSAT.SqrtLog.PackingCallerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed per-query caller for actual native incidence construction, word
selection, layout metadata construction, and paid master-bank parking. -/
namespace SubexponentialSAT.SqrtLog.PackingCallerProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
attribute [local simp] Fin.coe_ofNat_eq_mod

def command : Wide.Code := .seq compute Wide.finish

noncomputable def result (a : Wide.Data) (p : Problem)
    (w : Word p.r p.Q) (tail : List (Word p.r p.Q)) : Wide.Local :=
  Wide.finished (middle a p w tail)

noncomputable def budget (a : Wide.Data) (p : Problem)
    (w : Word p.r p.Q) (tail : List (Word p.r p.Q)) :=
  computeBudget a p w tail+Wide.finishCost (middle a p w tail)+2

end SubexponentialSAT.SqrtLog.PackingCallerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramOutput
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingCallerProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem middle_parked (a : Wide.Data) (p : Problem) (he : Empty a)
    (w : Word p.r p.Q) (tail : List (Word p.r p.Q)) (i : Fin 14) :
    (middle a p w tail).stacks (LeafProgram.LayoutMasters.high i)=[] := by
  rw [middle_frame]
  · exact he.parked i
  · right; change 481 ≤ 730+i.val; omega

end SubexponentialSAT.SqrtLog.PackingCallerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramCost
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingCallerProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes SubexponentialSAT.SubexpSetupStorage
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem middle_wordBound (a : Wide.Data) (p : Problem)
    (w : Word p.r p.Q) (tail : List (Word p.r p.Q)) (B : ℕ)
    (ha : WordBound B (Wide.project a)) (hb : WordBound B (bankOutput a p w tail)) :
    WordBound B (middle a p w tail) := by
  intro i
  by_cases hi : 417 ≤ i.val ∧ i.val < 481
  · simp only [middle]
    rw [dite_eq_left hi]
    exact hb ⟨i.val-417,by omega⟩
  · simp only [middle]
    rw [dite_eq_right hi]
    simpa only [Wide.project] using ha i

theorem budget_overhead_le (a : Wide.Data) (p : Problem) (he : Empty a)
    (w : Word p.r p.Q) (tail : List (Word p.r p.Q)) (B : ℕ)
    (ha : WordBound B (Wide.project a)) (hb : WordBound B (bankOutput a p w tail)) :
    budget a p w tail ≤ coreBudget (Wide.parameterStore (Wide.project a)) p w tail+1100*(B+1) := by
  have hstage := stageCost_le a B ha
  have hfinish := Wide.finishCost_le (middle a p w tail) B
    (middle_wordBound a p w tail B ha hb)
    (by rw [middle_frame _ _ _ _ _ (by norm_num)]; exact he.words)
    (by rw [middle_frame _ _ _ _ _ (by norm_num)]; exact he.metadata)
    (by rw [middle_frame _ _ _ _ _ (by norm_num)]; exact he.plans)
    (middle_parked a p he w tail)
  unfold budget computeBudget
  omega

end SubexponentialSAT.SqrtLog.PackingCallerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramReplay
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The native packing caller neither reads nor writes the outer carried
tapes. Their contents therefore do not affect its exact running time. -/
namespace SubexponentialSAT.SqrtLog.PackingCallerProgram.Replay
open SubexponentialSAT BitProgram StructuredCalls ProgramTapeReplay
open LeafProgram.OuterCarried
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem command_avoids : AvoidsCmd LeafProgram.OuterCarried.hidden PackingCallerProgram.command := by
  refine ⟨⟨stage_avoids,?_⟩,wideCall_avoids _ ⟨export_avoids,park_avoids⟩⟩
  exact avoids_call_lift_of_range LeafProgram.OuterCarried.hidden coreProgram Wide.registers Wide.ports bank_away

end SubexponentialSAT.SqrtLog.PackingCallerProgram.Replay

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationBetaProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native beta evaluation.  The caller supplies actual coefficient arrays,
not evaluated row values.  Masters205..212 are preserved;220 is the result.
Work230/231/232 holds the framed row scan, choice scan and reverse buffer. -/
namespace SubexponentialSAT.SqrtLog.PerturbationBetaProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexpScanPrimitives

def loop : Code := .while 0 body

end SubexponentialSAT.SqrtLog.PerturbationBetaProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQuerySetup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete preparation and fresh high-counter initialization for the fixed
marked and accepted queries. The witness below is produced by the actual
programs; no implementation or evaluator is supplied as a hypothesis. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup

open OAI BitProgram StructuredCalls SqrtLog LeafParametersProgram
open LeafProgram.Query HashGreedyProgram.NativeRound
open HighMarkedFrontend

abbrev Lower := State 40 768

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramSourceNativeCost
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A uniform cost for the actual source invocation, including its global
staging, four-cache save/restore, and cleanup. The size assumption includes the
live incidence-table accumulator rather than quantifying over unbounded data. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Source
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpSetupStorage
open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
open LayoutSourceRowsProgram

def nativeSourceWorkPolynomial {r Q d : ℕ} (p : SourceBank.Parameters r Q d) (S : ℕ) : ℕ :=
  nativeRowsPolynomial p S+1000000000000*(S+nativeOutputBound p S S+1)

end SubexponentialSAT.SqrtLog.LeafProgram.Source

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQueryCorrect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual whole-query composition after the high iterator. The two joins
below consume the fixed iterator's measured execution, preserve the same
prepared witnesses, and execute the existing complete return and cleanup.
The public marked and accepted theorems instantiate HighQueryCount directly. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect

open BitProgram StructuredCalls HighMarkedFrontend HighQuerySetup
open HashGreedyProgram.NativeRound

abbrev Data := State 40 896

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect
end


