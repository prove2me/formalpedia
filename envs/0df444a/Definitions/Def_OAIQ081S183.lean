-- Prove2me | Definitions.Def_OAIQ081S183
-- name    : OAIQ081S183
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T23:28:15.577245+00:00
-- url     : https://prove2.me/theorems/700c8b46-3974-4af0-b504-2da497821588
-- title:
--   Definitions bundle OAIQ081S183 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 51 declarations of OpenAI's Lean: 40 definitions, 1 inductive type or structure and 10 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query.coreInputBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.coreBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableDenotation.fixedLowJet`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend.acceptedCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend.acceptedLocalCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend.acceptedLocalProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend.acceptedProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend.localProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend.program`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.loopBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.loopSpace`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.ArithmeticData`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.ArithmeticData.arithmeticSteps`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.ArithmeticData.cache`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.ArithmeticData.half`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.ArithmeticData.modulus`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.ArithmeticData.output`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.ArithmeticData.ringState`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PackingData`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedData`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedData.arithmeticData`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedData.arithmeticSteps`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedData.cache`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedData.first`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedData.half`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedData.modulus`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedData.output`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedData.packed`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedData.packingData`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedData.packingSteps`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedData.rest`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedData.ringState`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedData.seedData`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedData.seedRegs`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedData.seedSteps`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.preparedOutput`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect.budget`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect.nodeBudget` and 1 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLogSpace_FactorTableDenotation`, `SubexponentialSAT_SqrtLogSpace_HighMarkedFrontend`, `SubexponentialSAT_SqrtLogSpace_HighQueryCorrect`, `SubexponentialSAT_SqrtLogSpace_HighQuerySetup`, `SubexponentialSAT_SqrtLogSpace_QueryStreamCorrect`, `SubexponentialSAT_SqrtLog_LeafQueryFrontendCore`, `SubexponentialSAT_SqrtLog_LeafQueryFrontendInputBudget`, `SubexponentialSAT_SqrtLog_PackingCallerProgramEnvelope`, `SubexponentialSAT_SqrtLog_PackingCallerProgramFinalSize`, `SubexponentialSAT_SqrtLog_PackingCallerProgramIncidence`, `SubexponentialSAT_SqrtLog_PackingCallerProgramOutput`, `SubexponentialSAT_SqrtLog_PackingCallerProgramQuantitative`, `SubexponentialSAT_SqrtLog_PackingIncidenceInputInstall`, `SubexponentialSAT_SqrtLog_PackingIncidenceInputNative`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S173`, `OAIQ081S174`, `OAIQ081S175`, `OAIQ081S176`, `OAIQ081S177` and `OAIQ081S178` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S186`, `OAIQ081S187` and `OAIQ081S188`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableDenotation.low_payload_realizes`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighFrontendShadow.accepted_denominator_empty`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighFrontendShadow.marked_denominator_empty`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend.accepted_command_front_state`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend.command_front_state`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend.command_kept_frame`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram.Carried.accepted_frontend`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryTimeBounds.runtime_bound`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamBudgets.high_loop_budget_polynomial`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.coreBudget_le_input`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.coreCommand_eval` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.coreCommand_eval_bounded`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.Input.payload_correct`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableDenotation.low_payload_realizes`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighFrontendShadow.accepted_denominator_empty`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighFrontendShadow.marked_denominator_empty`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.accepted`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.marked`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram.Carried.accepted_frontend`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.accepted_replay`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.marked_replay`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryTimeBounds.runtime_bound`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamBudgets.high_loop_budget_polynomial`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.coreBudget_le_input`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.coreCommand_eval` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.coreCommand_eval_bounded`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S173
import Definitions.Def_OAIQ081S174
import Definitions.Def_OAIQ081S175
import Definitions.Def_OAIQ081S176
import Definitions.Def_OAIQ081S177
import Definitions.Def_OAIQ081S178

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorTableDenotation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual normalized incidence payload has the canonical scalarized
source denotation. Source arrays are witnesses produced by the finite source
machine; their full polynomial meanings identify one fixed incidence jet. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableDenotation
open OAI OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing
open MomentsProgram TruncatedRingProgram DensePolynomialProgram
open OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking OAI.Algorithms.SubexponentialSAT.MulticolorTypes LayoutProgram
open scoped BigOperators
noncomputable section
variable {R : Type*} [CommRing R]

/-- The fixed source incidence is independent of the source call's array witness. -/
def fixedLowJet {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (n f j : ℕ) (theta : Coeff (baseWidth 3 p.t) d) (choice : List Bool) :
    Squarefree.Jet (Fin n) (p.model.O p.t) :=
  Moments.incidenceJet (PerturbationAssembly.fixedSourceRow p ps P n f j)
    (p.ops.decode theta)
    (∑ v : Fin n, (PerturbationAssembly.fixedSourceRow p ps P n f j v).eval
      (p.ops.decode theta) * (if choice.getD v.val false then 1 else 0))

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableDenotation
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

noncomputable def coreBudget (q : Query) (k : ℕ) (a : Data) (tau : List Bool) (l : Fin 8 → ℕ) : ℕ :=
  let S := (LeafStatisticsProgram.scopeBits q.scopeRows).length
  let F := q.forward.length
  (copiesCost scopeCopies a+21+HashScopeProgram.Complete.cost 1 0 q.width.length q.modulus
      q.clauses q.codes q.rows q.mark q.index+7*S) +
  (7*q.ambient.length+5+EarlyThreshold.runtimeBound q.ambient+
    (7*S+5+7*q.ambient.length+5+7*tau.length+5)+
    HighIncidenceProgram.Prepare.budget q.scopeRows q.ambient tau+1+17*F+14) +
  (7*S+5+7*F+5+LeafStatisticsProgram.bootBudget q.scopeRows q.forward+
    LeafStatisticsProgram.variableBudget q.scopeRows 0 q.forward+2+
    7*F+5+7*S+5+3+4+RecordPrograms.budget (LeafStatisticsProgram.Arity.cost q.forward)
      (q.scopeRows.map (Encoding.encodeList Encoding.encodeNat))+3*(totals q.scopeRows q.forward).uncovered+10) +
  (7*q.ambient.length+5+7*q.modulus.length+5+2*k.bits.length+1+
    conversionCost (totals q.scopeRows q.forward).free+
    conversionCost (totals q.scopeRows q.forward).occurrence+
    conversionCost (completedArity q.scopeRows q.forward)+
    conversionCost (q.scopeRows.length+(totals q.scopeRows q.forward).uncovered)+
    conversionCost (totals q.scopeRows q.forward).incidences) +
  LeafParametersProgram.Execute.runtimeBound (q.input k) l+1

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendInputBudget
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod

noncomputable def Query.coreInputBudget (q : Query) (k : ℕ) : ℕ :=
  let S := (LeafStatisticsProgram.scopeBits q.scopeRows).length
  let F := q.forward.length
  (q.scopeCopyBudget+21+HashScopeProgram.Complete.cost 1 0 q.width.length q.modulus
      q.clauses q.codes q.rows q.mark q.index+7*S) +
  (7*q.ambient.length+5+EarlyThreshold.runtimeBound q.ambient+
    (7*S+5+7*q.ambient.length+5+7*(Asymptotic.L (BinaryArithmetic.toNat q.ambient)+1)+5)+
    270000*q.highCapacity^3+17*F+14) +
  (7*S+5+7*F+5+LeafStatisticsProgram.bootBudget q.scopeRows q.forward+
    LeafStatisticsProgram.variableBudget q.scopeRows 0 q.forward+2+
    7*F+5+7*S+5+3+4+RecordPrograms.budget (LeafStatisticsProgram.Arity.cost q.forward)
      (q.scopeRows.map (Encoding.encodeList Encoding.encodeNat))+3*(totals q.scopeRows q.forward).uncovered+10) +
  q.numericCost k+LeafParametersProgram.Execute.runtimeBound (q.input k) (q.inputLengths k)+1

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighMarkedFrontend
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The original actual marked-scope/high-mask/parameter frontend is lifted
into the shared leaf ABI. Upper caller words and the marked mass collector
are retained; the lower workspace is reclaimed by an actual cleanup program. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend

open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open LeafParametersProgram

def localProgram (k : ℕ) := compiled (LeafProgram.Query.markedFrontend k) 321 338
def command (k : ℕ) : Code := .call (ProgramLinking.liftProgram (localProgram k) id stackMap)
def program (k : ℕ) := compiled (command k) 321 338

def acceptedLocalCommand (k : ℕ) : LeafProgram.Query.Code :=
  .seq LeafProgram.Query.noMarkInput (LeafQueryFrontend.frontend k)
def acceptedLocalProgram (k : ℕ) := compiled (acceptedLocalCommand k) 700 338
def acceptedCommand (k : ℕ) : Code :=
  .call (ProgramLinking.liftProgram (acceptedLocalProgram k) id stackMap)
def acceptedProgram (k : ℕ) := compiled (acceptedCommand k) 700 338

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend
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

theorem visits (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) :
    ∀ (r : Fin 16 → Bool) (v z : ℕ) (out : List Bool),
    ∃ costs t rf, t ≤ budget scopes n v z mask ∧
      UnaryForPrograms.Visits ports body costs t (Scan.data r scopes n v z mask out)
        (Scan.data rf scopes n (v+mask.length) (finalCounter scopes v z mask) []
          (recordPrefix (plans scopes n v z mask) ++ out)) := by
  induction mask with
  | nil =>
      intro r v z out
      refine ⟨[],2,readRegs r 14 15 none,by simp [budget],?_⟩
      have h := UnaryForPrograms.Visits.done (p := ports) (body := body)
        (Scan.data r scopes n v z [] out) rfl
      rw [pop_data] at h
      simpa [plans,recordPrefix,finalCounter] using h
  | cons high mask ih =>
      intro r v z out
      let rp := readRegs r 14 15 (some high)
      have hbit : rp 14 = high := by simp [rp,readRegs]
      obtain ⟨tb,rb,htb,hb⟩ := body_eval rp scopes n v z high mask out hbit
      obtain ⟨costs,t,rf,ht,he⟩ := ih rb (v+1) (if high then z else Step.next scopes v z)
        (recordPrefix (if high then [] else rowPlans scopes n v z) ++ out)
      have hbp : Eval body tb
          (UnaryForPrograms.popped ports (Scan.data r scopes n v z (high::mask) out))
          (Scan.data rb scopes n (v+1) (if high then z else Step.next scopes v z) mask
            (recordPrefix (if high then [] else rowPlans scopes n v z) ++ out)) := by
        rw [pop_data]; exact hb
      have hx := UnaryForPrograms.Visits.step (p := ports) (body := body)
        (by simp [Scan.data,ports]) hbp (by rw [pop_data]; rfl) he
      refine ⟨tb::costs,tb+t+2,rf,?_,?_⟩
      · simp only [budget]; omega
      · simpa [plans,recordPrefix,List.flatMap_append,List.append_assoc,finalCounter,
          Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hx

theorem command_eval (r : Fin 16 → Bool) (scopes : List (List ℕ)) (n v z : ℕ)
    (mask out : List Bool) :
    ∃ t rf, t ≤ budget scopes n v z mask ∧
      Eval command t (Scan.data r scopes n v z mask out)
        (Scan.data rf scopes n (v+mask.length) (finalCounter scopes v z mask) []
          (recordPrefix (plans scopes n v z mask) ++ out)) := by
  obtain ⟨costs,t,rf,ht,h⟩ := visits scopes n mask r v z out
  exact ⟨t,rf,ht,h.eval⟩

theorem produces (r : Fin 16 → Bool) (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) :
    ∃ t rf, t ≤ budget scopes n 0 scopes.length mask ∧
      Eval command t (Scan.data r scopes n 0 scopes.length mask [false])
        (Scan.data rf scopes n mask.length (finalCounter scopes 0 scopes.length mask) []
          (ProgramEncoding.encodeRecords (PackingIncidenceProgram.planAlphabet
            (plans scopes n 0 scopes.length mask)))) := by
  obtain ⟨t,rf,ht,h⟩ := command_eval r scopes n 0 scopes.length mask [false]
  exact ⟨t,rf,ht,by simpa only [Nat.zero_add,prefix_terminated] using h⟩
end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Loop


/-! Count the physical scope stream before constructing native incidence plans. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Boot
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

theorem full_eval (r : Fin 16 → Bool) (scopes : List (List ℕ)) (n : ℕ)
    (mask : List Bool) :
    ∃ t rf, t+1 ≤ fullBudget scopes n mask ∧
      Eval fullCommand t (Scan.data r scopes n 0 0 mask [])
        (Scan.data rf scopes n mask.length (Loop.finalCounter scopes 0 scopes.length mask) []
          (ProgramEncoding.encodeRecords (PackingIncidenceProgram.planAlphabet
            (Loop.plans scopes n 0 scopes.length mask)))) := by
  obtain ⟨rb,hb⟩ := command_eval r scopes n mask
  obtain ⟨t,rf,ht,he⟩ := Loop.produces rb scopes n mask
  exact ⟨_,rf,by dsimp [fullBudget]; omega,hb.seq he⟩

end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Boot

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceInputInstall
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Raw scope bytes and a mask produce the actual installed incidence-pair table. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Install
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

theorem build_eval (r : Fin 16 → Bool) (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) :
    ∃ t rf, t ≤ Boot.fullBudget scopes n mask ∧
      Eval build t (input r scopes n mask) (produced rf scopes n mask) := by
  obtain ⟨t,rf,ht,he⟩ := Boot.full_eval r scopes n mask
  have h := eval_call_lifted Boot.fullProgram id ports (frame r)
    Function.injective_id ports_injective (compiled_halt_trace he 20 25)
  have hframe (d : Scan.Data) : embedState id ports (frame r) d = state d := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      have h1 := embedState_register id ports (frame r) d Function.injective_id i
      have h2 := state_register d i
      exact h1.trans h2.symm
    · rfl
  exact ⟨t+1,rf,ht,by simpa [build, input, produced, hframe] using h⟩

end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Install

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramIncidence
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Preserve the physically generated owner/factor plans before the incidence
pair installer consumes them. The extra master is local port61. -/
namespace SubexponentialSAT.SqrtLog.PackingCallerProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp
open PackingLoaderProgram PackingIncidenceInput

theorem produce_eval (outside : Store) (regs : Fin 16 → Bool)
    (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool)
    (h52 : outside 52=[]) (h61 : outside 61=[]) :
    ∃ t rf, t ≤ produceBudget scopes n mask ∧ Eval produce t
      (framed outside (Install.input regs scopes n mask))
      (framed (Function.update outside 61 (planBits scopes n mask))
        (Endpoint.result rf scopes n mask)) := by
  obtain ⟨tb,rb,htb,hb⟩ := Install.build_eval regs scopes n mask
  have hbuild := framed_call buildProgram outside (compiled_halt_trace hb 32 20)
  obtain ⟨rs,hs⟩ := saveHigh_eval outside (Install.produced rb scopes n mask) 20 61
    (by decide) (by decide) h52 h61
  have hplans : (Install.produced rb scopes n mask).stacks 20=planBits scopes n mask := by
    rw [Endpoint.produced_stacks]
    simp [Endpoint.builtStacks,planBits]
  rw [hplans,produced_setRegs] at hs
  obtain ⟨tt,rf,htt,ht⟩ := incidenceTail_eval rs scopes n mask
  have htail := framed_call incidenceTailProgram
    (Function.update outside 61 (planBits scopes n mask)) (compiled_halt_trace ht 20 45)
  exact ⟨tb+1+((7*(planBits scopes n mask).length+5)+(tt+1)),rf,
    by dsimp [produceBudget]; omega,hbuild.seq (hs.seq htail)⟩

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

theorem result_frame (a : Wide.Data) (p : Problem)
    (w : Word p.r p.Q) (tail : List (Word p.r p.Q)) (i : Fin 768)
    (hb : i.val < 417 ∨ 481 ≤ i.val) (hl : i.val < 128 ∨ 142 ≤ i.val)
    (hh : i.val < 730 ∨ 744 ≤ i.val) :
    (result a p w tail).stacks i=a.stacks i := by
  rw [result,Wide.finished_frame _ _ hb hl hh,middle_frame _ _ _ _ _ hb]

end SubexponentialSAT.SqrtLog.PackingCallerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramFinalSize
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingCallerProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes SubexponentialSAT.SubexpSetupStorage
attribute [local simp] Fin.coe_ofNat_eq_mod

/-- Exporting and parking never enlarge an individual data word: every
destination is empty, and the private and low banks are subsequently erased. -/
theorem result_wordBound (a : Wide.Data) (p : Problem) (he : Empty a)
    (w : Word p.r p.Q) (tail : List (Word p.r p.Q)) (B : ℕ)
    (ha : WordBound B (Wide.project a)) (hb : WordBound B (bankOutput a p w tail)) :
    WordBound B (result a p w tail) := by
  have hm := middle_wordBound a p w tail B ha hb
  have hx := Wide.exported_wordBound (middle a p w tail) B hm
    (by rw [middle_frame _ _ _ _ _ (by norm_num)]; exact he.words)
    (by rw [middle_frame _ _ _ _ _ (by norm_num)]; exact he.metadata)
    (by rw [middle_frame _ _ _ _ _ (by norm_num)]; exact he.plans)
  apply clearMany_wordBound LeafProgram.LayoutMasters.lowPorts _ B
  apply copyMany_wordBound LeafProgram.LayoutMasters.parkPairs _ B
    LeafProgram.LayoutMasters.park_nodup ?_ LeafProgram.LayoutMasters.park_sep hx
  intro q hq
  simp only [LeafProgram.LayoutMasters.parkPairs,List.mem_map,List.mem_finRange,true_and] at hq
  obtain ⟨i,rfl⟩ := hq
  rw [Wide.exported_high,middle_parked a p he w tail i]

end SubexponentialSAT.SqrtLog.PackingCallerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramEnvelope
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingCallerProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes SubexponentialSAT.SubexpSetupStorage

/-- The global copying, cleanup, and parking add only a linear cost in
the largest input or computed word. This combines independently proved
native-core and output-word polynomial bounds without a runtime oracle. -/
theorem polynomial_envelope (a : Wide.Data) (p : Problem) (he : Empty a)
    (w : Word p.r p.Q) (tail : List (Word p.r p.Q))
    (V cc dc cb db : ℕ) (hV : 1 ≤ V) (hi : inputMass a ≤ V)
    (hc : coreBudget (Wide.parameterStore (Wide.project a)) p w tail ≤ cc*V^dc)
    (hb : WordBound (cb*V^db) (bankOutput a p w tail)) :
    budget a p w tail ≤ combinedConstant cc cb*V^(combinedExponent dc db) ∧
    WordBound (combinedConstant cc cb*V^(combinedExponent dc db)) (result a p w tail) := by
  let D := combinedExponent dc db
  let N := V^D
  have hd1 : 1 ≤ D := le_max_left _ _
  have hdc : dc ≤ D := (le_max_left dc db).trans (le_max_right _ _)
  have hdb : db ≤ D := (le_max_right dc db).trans (le_max_right _ _)
  have hVN : V ≤ N := by simpa [N] using Nat.pow_le_pow_right hV hd1
  have hN : 1 ≤ N := hV.trans hVN
  have hcN : coreBudget (Wide.parameterStore (Wide.project a)) p w tail ≤ cc*N :=
    hc.trans (Nat.mul_le_mul_left cc (Nat.pow_le_pow_right hV hdc))
  have hbN : WordBound (cb*N) (bankOutput a p w tail) := by
    intro i
    exact (hb i).trans (Nat.mul_le_mul_left cb (Nat.pow_le_pow_right hV hdb))
  have ha : WordBound ((cb+1)*N) (Wide.project a) := by
    intro i
    have hx := (inputMass_bound a i).trans (hi.trans hVN)
    change (a.stacks i).length ≤ _
    nlinarith
  have hb' : WordBound ((cb+1)*N) (bankOutput a p w tail) := by
    intro i
    have hx := hbN i
    nlinarith
  have hcost := budget_overhead_le a p he w tail ((cb+1)*N) ha hb'
  have hout := result_wordBound a p he w tail ((cb+1)*N) ha hb'
  have hcap : (cb+1)*N ≤ combinedConstant cc cb*N := by
    unfold combinedConstant
    nlinarith
  constructor
  · change budget a p w tail ≤ combinedConstant cc cb*N
    unfold combinedConstant
    nlinarith
  · intro i
    exact (hout i).trans hcap

end SubexponentialSAT.SqrtLog.PackingCallerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramQuantitative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Polynomial time and output space for the complete native packing
caller, including global staging, cleanup, and master-bank parking. -/
namespace SubexponentialSAT.SqrtLog.PackingCallerProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes SubexponentialSAT.SubexpSetupStorage

theorem budget_polynomial : ∃ C d : ℕ, 1 ≤ d ∧
    ∀ (a : Wide.Data) (p : Problem) (w : Word p.r p.Q) (tail : List (Word p.r p.Q)),
    Sources a p → Empty a →
    (w::tail).map ReadPlan.encodeWord=AssignmentAlphabetSemantics.wordBytes p.r p.Q →
    budget a p w tail ≤ C*(globalSize a p)^d ∧
    WordBound (C*(globalSize a p)^d) (result a p w tail) := by
  obtain ⟨cc,dc,hc⟩ := Bounds.coreBudget_polynomial
  obtain ⟨cb,db,hb⟩ := Bounds.bankOutput_word_polynomial
  refine ⟨combinedConstant cc cb,combinedExponent dc db,le_max_left _ _,?_⟩
  intro a p w tail hs he hrows
  have hsize : Bounds.scalarSize (Wide.parameterStore (Wide.project a)) p+1 ≤ globalSize a p := by
    unfold globalSize; omega
  apply polynomial_envelope a p he w tail (globalSize a p) cc dc cb db
    (by unfold globalSize; omega) (by unfold globalSize; omega)
  · exact (hc _ p w tail hs.parameters hrows).trans
      (Nat.mul_le_mul_left cc (Nat.pow_le_pow_left hsize dc))
  · intro i
    exact (hb a p w tail i).trans (Nat.mul_le_mul_left cb (Nat.pow_le_pow_left hsize db))

end SubexponentialSAT.SqrtLog.PackingCallerProgram

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

noncomputable def preparedOutput (front : Data) (output : Lower) : Data :=
  result front output

structure PackingData (q : LeafQueryFrontend.Query) (k : ℕ) (hg : Guard (q.input k)) where
  first : MulticolorTypes.Word (preparedProblem q k hg).r (preparedProblem q k hg).Q
  rest : List (MulticolorTypes.Word (preparedProblem q k hg).r (preparedProblem q k hg).Q)
  packed : Lower
  packingSteps : ℕ

def ArithmeticData (q : LeafQueryFrontend.Query) (k : ℕ)
    (padding : Fin 8 → ℕ) : Type :=
  ℕ × LeafRingSetupProgram.Data ×
    SubexpPreparedQuartic.Modulus 3 ((preparedModel q k padding).val 33) ×
    RingProgram.ScalarCache 3 ((preparedModel q k padding).val 33) ×
    RingProgram.ScalarCode 3 ((preparedModel q k padding).val 33) × Lower

namespace ArithmeticData

variable {q : LeafQueryFrontend.Query} {k : ℕ} {padding : Fin 8 → ℕ}

abbrev arithmeticSteps (data : ArithmeticData q k padding) := data.1
abbrev ringState (data : ArithmeticData q k padding) := data.2.1
abbrev modulus (data : ArithmeticData q k padding) := data.2.2.1
abbrev cache (data : ArithmeticData q k padding) := data.2.2.2.1
abbrev half (data : ArithmeticData q k padding) := data.2.2.2.2.1
abbrev output (data : ArithmeticData q k padding) := data.2.2.2.2.2

end ArithmeticData

def PreparedData (q : LeafQueryFrontend.Query) (k : ℕ) (hg : Guard (q.input k))
    (padding : Fin 8 → ℕ) : Type :=
  PackingData q k hg × ArithmeticData q k padding × SeedData

namespace PreparedData

variable {q : LeafQueryFrontend.Query} {k : ℕ} {hg : Guard (q.input k)}
  {padding : Fin 8 → ℕ}

abbrev packingData (data : PreparedData q k hg padding) := data.1
abbrev arithmeticData (data : PreparedData q k hg padding) := data.2.1
abbrev seedData (data : PreparedData q k hg padding) := data.2.2

abbrev first (data : PreparedData q k hg padding) := data.packingData.first
abbrev rest (data : PreparedData q k hg padding) := data.packingData.rest
abbrev packed (data : PreparedData q k hg padding) := data.packingData.packed
abbrev packingSteps (data : PreparedData q k hg padding) := data.packingData.packingSteps
abbrev arithmeticSteps (data : PreparedData q k hg padding) :=
  data.arithmeticData.arithmeticSteps
abbrev ringState (data : PreparedData q k hg padding) := data.arithmeticData.ringState
abbrev modulus (data : PreparedData q k hg padding) := data.arithmeticData.modulus
abbrev cache (data : PreparedData q k hg padding) := data.arithmeticData.cache
abbrev half (data : PreparedData q k hg padding) := data.arithmeticData.half
abbrev output (data : PreparedData q k hg padding) := data.arithmeticData.output
abbrev seedSteps (data : PreparedData q k hg padding) := data.seedData.seedSteps
abbrev seedRegs (data : PreparedData q k hg padding) := data.seedData.seedRegs

end PreparedData

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryStreamCorrect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Physical boundaries of the fixed conditioned query. The node invariant
retains the actual prepared words and the exact length of the emitted stream;
it contains no execution or evaluator fields. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect

open OAI BitProgram StructuredCalls SqrtLog SubexpLiftRing SubexpQuarticRing
open SubexpSetupStorage

/-- `work` is the original assembled query resource, instantiated below by
the addressed packing. Its square pays the actual pair and tuple iterator. -/
def nodeBudget (n t d J A work : ℕ) : ℕ :=
  prepareBudget A+StreamedQueryMeasuredCost.pairCoefficient A*work^2+10+
    finishBudget n t d J A

/-- Includes actual high decoding, cursor initialization, every node and the
full canonical reconstruction with its final halt. -/
def budget (n t d Q J A S work : ℕ) : ℕ :=
  18*QueryHeadBudgets.compact A+65*n+67+23*QueryHeadBudgets.compact A+
    Q*(nodeBudget n t d J A work+1)+32+
    QueryReconstruction.budget (QueryHeadBudgets.compact A) S

def space (n t d J A S : ℕ) : ℕ :=
  max (67*QueryHeadBudgets.compact A+37)
    (max (max (919*QueryHeadBudgets.compact A+31) (nodeSpace n t d J A))
      (896*QueryHeadBudgets.compact A+QueryReconstruction.budget (QueryHeadBudgets.compact A) S))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect
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

/-- Prefix storage contains no high-loop runtime or completed-rank count. -/
def space (q : SqrtLog.LeafQueryFrontend.Query) (A frontCost S B cost K D : ℕ) : ℕ :=
  max (A + frontCost) (max (max (prefixBound q S cost B) K) (931 * D + 54))

/-- Every actual high rank pays its stream, refresh, addition and odometer. -/
def loopBudget (n h t d Q J A T work : ℕ) : ℕ :=
  2^h*(QueryStreamCorrect.budget n t d Q J A T work+
    11*QueryHeadBudgets.compact A+16*(n+2)+28*h+27)+3

def loopSpace (n h t d J A T : ℕ) : ℕ :=
  max (max (max (QueryHeadBudgets.compact A) (QueryStreamCorrect.space n t d J A T))
    (20*(n+2))) (40*(h+1))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect
end


