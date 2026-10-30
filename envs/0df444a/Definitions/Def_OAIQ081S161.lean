-- Prove2me | Definitions.Def_OAIQ081S161
-- name    : OAIQ081S161
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T23:04:43.646793+00:00
-- url     : https://prove2.me/theorems/20def1ee-5cdb-40b4-bc4a-0be967eb30a6
-- title:
--   Definitions bundle OAIQ081S161 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 23 declarations of OpenAI's Lean: 3 definitions and 20 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.inputMass`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.setRegs`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.dispatchInput`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: [`SubexponentialSAT_SqrtLogSpace_FactorAssignmentCallback`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/FactorAssignmentCallback.lean), [`SubexponentialSAT_SqrtLog_PackingCallerProgramBasic`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PackingCallerProgramBasic.lean), [`SubexponentialSAT_SqrtLog_PackingCallerProgramCache`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PackingCallerProgramCache.lean), [`SubexponentialSAT_SqrtLog_PackingCallerProgramCleanup`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PackingCallerProgramCleanup.lean), [`SubexponentialSAT_SqrtLog_PackingCallerProgramEnvelope`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PackingCallerProgramEnvelope.lean), [`SubexponentialSAT_SqrtLog_PackingCallerProgramExport`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PackingCallerProgramExport.lean), [`SubexponentialSAT_SqrtLog_PackingCallerProgramExportCost`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PackingCallerProgramExportCost.lean), [`SubexponentialSAT_SqrtLog_PackingCallerProgramExportFacts`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PackingCallerProgramExportFacts.lean), [`SubexponentialSAT_SqrtLog_PackingCallerProgramIncidence`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PackingCallerProgramIncidence.lean), [`SubexponentialSAT_SqrtLog_PackingCallerProgramStage`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PackingCallerProgramStage.lean), [`SubexponentialSAT_SqrtLog_PackingIncidenceInputNative`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PackingIncidenceInputNative.lean).
--
--   **Imports.** It imports the bundles `OAIQ081S115`, `OAIQ081S142`, `OAIQ081S145`, `OAIQ081S147` and `OAIQ081S148` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S171` and `OAIQ081S172`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ081S115
import Definitions.Def_OAIQ081S142
import Definitions.Def_OAIQ081S145
import Definitions.Def_OAIQ081S147
import Definitions.Def_OAIQ081S148

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorAssignmentCallback
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual specialized callback dispatches one stored original factor ID.
The general dispatch theorem fixes its physical payload, flags and exact frame;
hash and marked branch correctness is supplied by their concrete native proofs. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback

open OAI BitProgram StructuredCalls
open SqrtLog SqrtLog.LeafProgram MomentsProgram FactorAssignmentProgram

noncomputable section
attribute [local simp] Fin.coe_ofNat_eq_mod

def dispatchInput (a : FactorAssignmentProgram.Data) : State 40 768 :=
  projectState id lowStack (callbackInitial a)

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback
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

theorem pop_data (r : Fin 16 → Bool) (scopes : List (List ℕ)) (n v z : ℕ)
    (mask out : List Bool) :
    UnaryForPrograms.popped ports (Scan.data r scopes n v z mask out) =
      Scan.data (readRegs r 14 15 mask.head?) scopes n v z mask.tail out := by
  apply congrArg (StructuredProgram.State.mk _)
  funext i; fin_cases i <;> simp [ports,Scan.data]

end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Loop


/-! Count the physical scope stream before constructing native incidence plans. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Framed local storage for the concrete packing caller. Ports53/54 retain
width/alphabet,55..59 parameters,60 scopes,61 plans,62 words,63 metadata. -/
namespace SubexponentialSAT.SqrtLog.PackingCallerProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage
open PackingLoaderProgram

def setRegs (d : Small) (regs : Fin 16 → Bool) : Small := ⟨regs,d.stacks⟩

theorem framed_update_high (outside : Store) (d : Small) (j : Fin 64)
    (hj : 48 ≤ j.val) (bits : List Bool) :
    (framed (Function.update outside j bits) d).stacks =
      Function.update (framed outside d).stacks j bits := by
  funext i
  by_cases hij : i=j
  · subst i
    simp [framed_outside _ _ j (high_not_low j hj)]
  · rw [Function.update_of_ne hij]
    by_cases hi : i.val < 48
    · simp [framed_stack,hi]
    · simp [framed_stack,hi,hij]

/-- A paid low-to-high copy retains the entire low state and all other masters. -/
theorem saveHigh_eval (outside : Store) (d : Small) (src : Fin 48) (dst : Fin 64)
    (hd : 48 ≤ dst.val) (h52 : (52 : Fin 64)≠dst)
    (ht : outside 52=[]) (hz : outside dst=[]) :
    ∃ rf, Eval (saveHigh src dst) (7*(d.stacks src).length+5)
      (framed outside d)
      (framed (Function.update outside dst (d.stacks src)) (setRegs d rf)) := by
  have hsd : lowPorts src≠dst := by
    intro h; exact high_not_low dst hd ⟨src,h⟩
  have hst : lowPorts src≠(52 : Fin 64) := by
    intro h; exact high_not_low 52 (by decide) ⟨src,h⟩
  have htmp : (framed outside d).stacks 52=[] := by
    rw [framed_outside _ _ 52 (high_not_low 52 (by decide)),ht]
  have hdst : (framed outside d).stacks dst=[] := by
    rw [framed_outside _ _ dst (high_not_low dst hd),hz]
  have h := copy_eval (lowPorts src) dst 52 (framed outside d) hsd hst h52 htmp
  let e := copyState (lowPorts src) dst (framed outside d)
  have he : e=framed (Function.update outside dst (d.stacks src)) (setRegs d e.regs) := by
    apply SubexponentialSAT.CounterForPrograms.data_ext
    · simp [setRegs]
    · rw [framed_update_high _ _ _ hd]
      funext i
      simp only [e,copyState_stack,framed_low,hdst,List.append_nil]
      congr 1
  simp only [framed_low] at h
  change Eval (saveHigh src dst) _ _ e at h
  rw [he] at h
  exact ⟨e.regs,h⟩

theorem clearLow_eval (outside : Store) (d : Small) :
    ∃ rf, Eval clearLow (clearManyCost lowClearPorts (framed outside d))
      (framed outside d) (framed outside (⟨rf,fun _=>[]⟩ : Small)) := by
  let e := clearManyState lowClearPorts (framed outside d)
  have he : e=framed outside (⟨e.regs,fun _=>[]⟩ : Small) := by
    apply SubexponentialSAT.CounterForPrograms.data_ext
    · simp
    · funext i
      simp only [e,clearMany_stacks,mem_lowClearPorts,framed_stack]
      split <;> simp_all
  have h := clearMany_eval lowClearPorts (framed outside d)
  change Eval clearLow _ _ e at h
  rw [he] at h
  exact ⟨e.regs,h⟩

end SubexponentialSAT.SqrtLog.PackingCallerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramCache
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingCallerProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open PackingLoaderProgram

theorem cacheInputs_eval (outside : Store) (d : Small)
    (h52 : outside 52=[]) (h53 : outside 53=[]) (h54 : outside 54=[]) :
    ∃ rf, Eval cacheInputs (7*(d.stacks 10).length+5+(7*(d.stacks 39).length+5))
      (framed outside d)
      (framed (cached outside (d.stacks 10) (d.stacks 39)) (setRegs d rf)) := by
  obtain ⟨r1,h1⟩ := saveHigh_eval outside d 10 53 (by decide) (by decide) h52 h53
  obtain ⟨r2,h2⟩ := saveHigh_eval (Function.update outside 53 (d.stacks 10)) (setRegs d r1)
    39 54 (by decide) (by decide) (by simpa using h52) (by simpa using h54)
  exact ⟨r2,h1.seq h2⟩

end SubexponentialSAT.SqrtLog.PackingCallerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramCleanup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingCallerProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage
open PackingLoaderProgram

theorem clear_cost_eq {S : ℕ} (ps : List (Fin S)) (hp : ps.Nodup) (a : State 16 S) :
    clearManyCost ps a=(ps.map (fun i=>2*(a.stacks i).length+3)).sum := by
  induction ps generalizing a with
  | nil => rfl
  | cons p ps ih =>
    rw [clearManyCost,ih hp.tail]
    simp only [List.map_cons,List.sum_cons]
    congr 1
    congr 1
    apply List.map_congr_left
    intro i hi
    have hne : i≠p := by intro h; subst i; exact (List.nodup_cons.mp hp).1 hi
    simp [clearState,hne]

end SubexponentialSAT.SqrtLog.PackingCallerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramExport
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid export of the computed word table, metadata, and original plans,
followed by erasure of the private bank and parking of the source masters. -/
namespace SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem exportLocal_eval (a : Local) (ht : a.stacks 684=[]) :
    Eval exportLocal (exportCost a) a (exported a) :=
  (copyMany_eval 684 exportPairs a (by
    intro p hp
    simp only [exportPairs,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl <;> decide) ht).seq
    (clearMany_eval privatePorts (copyManyState exportPairs a))

theorem exported_frame (a : Local) (i : Fin 768)
    (hb : i.val < 417 ∨ 481 ≤ i.val) (h133 : i≠133) (h135 : i≠135) (h136 : i≠136) :
    (exported a).stacks i=a.stacks i := by
  rw [exported,clearMany_stacks,ite_eq_right (by rw [mem_privatePorts]; omega)]
  apply copyMany_frame
  simp only [exportPairs,List.mem_cons,List.not_mem_nil,or_false]
  rintro p (rfl|rfl|rfl) <;> assumption

theorem parked_frame (a : Local) (i : Fin 768)
    (hl : i.val < 128 ∨ 142 ≤ i.val) (hh : i.val < 730 ∨ 744 ≤ i.val) :
    (LeafProgram.LayoutMasters.parked a).stacks i=a.stacks i := by
  rw [LeafProgram.LayoutMasters.parked,clearMany_stacks,ite_eq_right]
  · apply copyMany_frame
    intro p hp he
    simp only [LeafProgram.LayoutMasters.parkPairs,List.mem_map,List.mem_finRange,true_and] at hp
    obtain ⟨j,rfl⟩ := hp
    have hv := congrArg Fin.val he
    change i.val=730+j.val at hv
    have := j.isLt
    omega
  · simp only [LeafProgram.LayoutMasters.lowPorts,List.mem_map,List.mem_finRange,true_and]
    rintro ⟨j,hj⟩
    have hv := congrArg Fin.val hj
    change 128+j.val=i.val at hv
    have := j.isLt
    omega

theorem finishLocal_eval (a : Local) (ht : a.stacks 684=[]) :
    Eval finishLocal (finishCost a) a (finished a) := by
  apply (exportLocal_eval a ht).seq
  apply LeafProgram.LayoutMasters.park_local_eval
  rw [exported_frame a 684 (by norm_num) (by decide) (by decide) (by decide),ht]

end SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramExportFacts
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem finished_frame (a : Local) (i : Fin 768)
    (hb : i.val < 417 ∨ 481 ≤ i.val) (hl : i.val < 128 ∨ 142 ≤ i.val)
    (hh : i.val < 730 ∨ 744 ≤ i.val) :
    (finished a).stacks i=a.stacks i := by
  rw [finished,parked_frame _ i hl hh]
  apply exported_frame a i hb <;> intro h <;> subst i <;> norm_num at hl

theorem exported_high (a : Local) (i : Fin 14) :
    (exported a).stacks (LeafProgram.LayoutMasters.high i)=a.stacks (LeafProgram.LayoutMasters.high i) := by
  apply exported_frame
  · right; change 481 ≤ 730+i.val; omega
  all_goals intro h; have hv := congrArg Fin.val h; simp [LeafProgram.LayoutMasters.high] at hv; omega

end SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramExportCost
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem export_targets (a : Local) (h133 : a.stacks 133=[]) (h135 : a.stacks 135=[])
    (h136 : a.stacks 136=[]) : ∀ p∈exportPairs,a.stacks p.2=[] := by
  simp only [exportPairs,List.mem_cons,List.not_mem_nil,or_false]
  rintro p (rfl|rfl|rfl) <;> assumption

theorem exported_wordBound (a : Local) (B : ℕ) (h : WordBound B a)
    (h133 : a.stacks 133=[]) (h135 : a.stacks 135=[]) (h136 : a.stacks 136=[]) :
    WordBound B (exported a) :=
  clearMany_wordBound privatePorts _ B (copyMany_wordBound exportPairs a B (by decide)
    (export_targets a h133 h135 h136) export_sep h)

theorem finishCost_le (a : Local) (B : ℕ) (h : WordBound B a)
    (h133 : a.stacks 133=[]) (h135 : a.stacks 135=[]) (h136 : a.stacks 136=[])
    (hz : ∀ i,a.stacks (LeafProgram.LayoutMasters.high i)=[]) :
    finishCost a+1 ≤ 1000*(B+1) := by
  have hc := copyManyCost_le exportPairs a B export_sep (fun p hp=>h p.1)
  have hw := copyMany_wordBound exportPairs a B (by decide)
    (export_targets a h133 h135 h136) export_sep h
  have hd := clearManyCost_le privatePorts _ B hw
  have hp := LeafProgram.LayoutMasters.parkCost_le (exported a) B
    (exported_wordBound a B h h133 h135 h136) (by intro i; rw [exported_high,hz])
  change copyManyCost exportPairs a ≤ 3*(7*B+5) at hc
  change clearManyCost privatePorts (copyManyState exportPairs a) ≤ 64*(2*B+3) at hd
  unfold finishCost exportCost
  omega

end SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide

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

theorem produced_regs (regs : Fin 16 → Bool) (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) :
    (Install.produced regs scopes n mask).regs=regs := by
  funext i
  exact Install.state_register _ i

theorem incidenceTail_eval (regs : Fin 16 → Bool) (scopes : List (List ℕ))
    (n : ℕ) (mask : List Bool) :
    ∃ t rf, t+1 ≤ 4+PackingIncidenceProgram.Install.budget (Install.plans scopes n mask) ∧
      Eval incidenceTail t (Install.produced regs scopes n mask) (Endpoint.result rf scopes n mask) := by
  obtain ⟨ti,hti,e,he,hout,hz,hf⟩ := PackingIncidenceProgram.Install.command_eval
    (Install.plans scopes n mask) (Install.withDepth (Install.produced regs scopes n mask))
    (Install.installed_input regs scopes n mask)
  have hend := Endpoint.exact_output regs scopes n mask e hout hz hf
  have hrun := (Install.depth_eval (Install.produced regs scopes n mask)).seq he
  rw [hend] at hrun
  exact ⟨4+ti,e.regs,by omega,hrun⟩

end SubexponentialSAT.SqrtLog.PackingCallerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramStage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid copies from the actual query frontend's persistent master bank. -/
namespace SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage
open PackingLoaderProgram PackingIncidenceInput
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem stageLocal_eval (a : Local) (ht : a.stacks 684=[]) :
    Eval stageLocal (copyManyCost stagePairs a) a (staged a) :=
  copyMany_eval 684 stagePairs a (by
    intro p hp
    simp only [stagePairs,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide) ht

theorem staged_frame (a : Local) (j : Fin 768)
    (hj : j.val < 417 ∨ 481 ≤ j.val) : (staged a).stacks j=a.stacks j := by
  apply copyMany_frame
  intro p hp h
  simp only [stagePairs,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    have hv := congrArg Fin.val h <;> simp only [ports_val] at hv <;> omega

end SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramEnvelope
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingCallerProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes SubexponentialSAT.SubexpSetupStorage

def inputMass (a : Wide.Data) := ∑ i : Fin 768,(a.stacks i).length

theorem inputMass_bound (a : Wide.Data) (i : Fin 768) : (a.stacks i).length ≤ inputMass a := by
  unfold inputMass
  exact Finset.single_le_sum (s := Finset.univ) (f := fun j : Fin 768 => (a.stacks j).length)
    (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)

end SubexponentialSAT.SqrtLog.PackingCallerProgram

end OAI.Algorithms
end


