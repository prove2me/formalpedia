-- Prove2me | Definitions.Def_OAIQ081S135
-- name    : OAIQ081S135
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:44:44.254086+00:00
-- url     : https://prove2.me/theorems/aa0bfca8-2208-4eec-b5fa-975e0f55badc
-- title:
--   Definitions bundle OAIQ081S135 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 58 declarations of OpenAI's Lean: 38 definitions and 20 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Assembly.WeightReady`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Assembly.inputPairScores`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Assembly.parkReady`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Assembly.unparkReady`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.FactorRows`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.bitRead`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.constructConstants`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.coordinateResult`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.emitTable`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.enterHorner`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.entry`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.finishLiteral`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.loadCoordinate`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.loadRow`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.prepareEntry`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.shiftedValue`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgram.Code`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgram.popRow`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgram.readRow`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationEmitProgram.branch`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationEmitProgram.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationEmitProgram.dropConstant`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationEmitProgram.emitCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationEmitProgram.emitted`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationEmitProgram.loop`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationEmitProgram.loopPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationEmitProgram.readCoefficient`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationEmitProgram.start`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationEmitProgram.step`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationMaskProgram.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationMaskProgram.selectCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationMaskProgram.zeroCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationMaskProgram.zeroLoop`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationMaskProgram.zeroPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram.state`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram.peeked`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter.CanonicalHigh.Code`, `OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentInputProgram.Writes`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLogSpace_HighQueryAdapter`, `SubexponentialSAT_SqrtLog_PackingLoaderProgramCapture`, `SubexponentialSAT_SqrtLog_PackingProgramAssemblyMetadata`, `SubexponentialSAT_SqrtLog_PackingProgramAssemblyWeights`, `SubexponentialSAT_SqrtLog_PackingProgramCombine`, `SubexponentialSAT_SqrtLog_PackingProgramStreams`, `SubexponentialSAT_SqrtLog_PerturbationAssemblyBranch`, `SubexponentialSAT_SqrtLog_PerturbationAssemblyConstants`, `SubexponentialSAT_SqrtLog_PerturbationAssemblyControl`, `SubexponentialSAT_SqrtLog_PerturbationAssemblyCoordinate`, `SubexponentialSAT_SqrtLog_PerturbationAssemblyEntry`, `SubexponentialSAT_SqrtLog_PerturbationAssemblyModel`, `SubexponentialSAT_SqrtLog_PerturbationAssemblyNativeCoordinate`, `SubexponentialSAT_SqrtLog_PerturbationAssemblyNativeFactor`, `SubexponentialSAT_SqrtLog_PerturbationAssemblyPreparation`, `SubexponentialSAT_SqrtLog_PerturbationBetaProgram`, `SubexponentialSAT_SqrtLog_PerturbationEmitProgram`, `SubexponentialSAT_SqrtLog_PerturbationMaskProgram`, `SubexponentialSAT_SqrtLog_SquarefreeKeyMapProgram`, `SubexponentialSAT_SqrtLog_SquarefreeScaleProgram`, `SubexponentialSAT_Subexp_AssignmentInputCall`, `SubexponentialSAT_Subexp_AssignmentInputProgram`, `SubexponentialSAT_Subexp_CandidatePlanPermutation`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S100`, `OAIQ081S102`, `OAIQ081S105`, `OAIQ081S109`, `OAIQ081S110`, `OAIQ081S111`, `OAIQ081S112`, `OAIQ081S113` and `OAIQ081S114` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S150`, `OAIQ081S151` and `OAIQ081S152`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.loadCoordinate_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.shifted_tail_polynomial`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationEmitProgram.command_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationEmitProgram.emit_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram.clip_store` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram.join_store`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.scalePhase_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.loadCoordinate_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.shifted_tail_polynomial`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationEmitProgram.command_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationEmitProgram.emit_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram.clip_store` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram.join_store`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S100
import Definitions.Def_OAIQ081S102
import Definitions.Def_OAIQ081S105
import Definitions.Def_OAIQ081S109
import Definitions.Def_OAIQ081S110
import Definitions.Def_OAIQ081S111
import Definitions.Def_OAIQ081S112
import Definitions.Def_OAIQ081S113
import Definitions.Def_OAIQ081S114

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQueryAdapter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete per-high-assignment setup and compressed head overlays.
The routines read physical counter/mask words and preserve ambient coordinates. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter

open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram

open OAI.Algorithms.SubexponentialSAT.StackRoutines

namespace CanonicalHigh
open DisjointReuse

abbrev Code := Cmd 40 896

open OAI.Algorithms.SubexponentialSAT.StackRoutines

end CanonicalHigh


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingLoaderProgramCapture
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Consume the incidence installer's transient metadata while preserving an
explicit raw-scope master outside the selector's48-stack bank. -/
namespace SubexponentialSAT.SqrtLog.PackingLoaderProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem capture_eval (outside : Store) (regs : Fin 16 → Bool)
    (scopes : List Bool) (n k f : ℕ) (pairs : List Bool) (h60 : outside 60=[]) :
    ∃ rf, Eval capture (captureBudget scopes.length n k f)
      (rawInput outside regs scopes n k f pairs)
      (framed (Function.update outside 60 scopes)
        (SubexponentialSAT.Subexp.AssignmentInputProgram.inputState rf 0 0 0 n f pairs)) := by
  let a := rawInput outside regs scopes n k f pairs
  let b := copyManyState captureCopies a
  let e := clearManyState captureClears b
  have h31 : a.stacks 31=[] := by simp [a,rawInput,framed_stack,rawLocal]
  have h1 := copyMany_eval 31 captureCopies a (by
    intro p hp; simp [captureCopies] at hp; rcases hp with rfl | rfl | rfl <;> decide) h31
  have h2 := clearMany_eval captureClears b
  have he : e=framed (Function.update outside 60 scopes)
      (SubexponentialSAT.Subexp.AssignmentInputProgram.inputState e.regs 0 0 0 n f pairs) := by
    apply SubexponentialSAT.CounterForPrograms.data_ext
    · simp [SubexponentialSAT.Subexp.AssignmentInputProgram.inputState]
    · funext i
      fin_cases i <;> simp [e,b,a,captureClears,captureCopies,clearManyState,clearState,
        copyManyState,copyState,StackRoutines.copyStacks,rawInput,framed_stack,rawLocal,
        SubexponentialSAT.Subexp.AssignmentInputProgram.inputState,h60]
  have hcost : copyManyCost captureCopies a+clearManyCost captureClears b=
      captureBudget scopes.length n k f := by
    simp [captureBudget,captureCopies,captureClears,copyManyCost,clearManyCost,b,a,
      copyManyState,copyState,StackRoutines.copyStacks,clearState,
      rawInput,framed_stack,rawLocal,h60]
    omega
  have h := h1.seq h2
  change Eval capture _ a e at h
  rw [hcost,he] at h
  exact ⟨e.regs,h⟩

end SubexponentialSAT.SqrtLog.PackingLoaderProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_CandidatePlanPermutation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Generated raw-plan order does not change the candidate scores. -/

namespace SubexponentialSAT.Subexp.CandidateScoreRefinement

open SubexponentialSAT.MulticolorTypes SubexponentialSAT.SlotAssignment

theorem score_perm (ctx : PairScoreProgram.Context)
    {left right : List PairScoreProgram.PlanPair} (h : left.Perm right) :
    PairScoreProgram.score ctx left = PairScoreProgram.score ctx right := by
  simp only [PairScoreProgram.score_eq_sum]
  exact (h.map (PairScoreProgram.pairCount ctx)).sum_eq

end SubexponentialSAT.Subexp.CandidateScoreRefinement

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramAssemblyMetadata
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid parking of four runtime integer parameters around the incidence scorer. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

def parkReady (d : Data) : Prop := ∀ j : Fin 48, 12 ≤ j.val → j.val ≤ 16 → d.stacks j=[]
def unparkReady (d : Data) : Prop :=
  d.stacks 16=[] ∧ ∀ j : Fin 48, 20 ≤ j.val → j.val ≤ 23 → d.stacks j=[]

theorem park_ready (d : Data) (h : parkReady d) : MoveReady metadata d := by
  have h12 := h 12 (by decide) (by decide)
  have h13 := h 13 (by decide) (by decide)
  have h14 := h 14 (by decide) (by decide)
  have h15 := h 15 (by decide) (by decide)
  have h16 := h 16 (by decide) (by decide)
  simp [metadata,MoveReady,moved,h12,h13,h14,h15,h16]

theorem unpark_ready (d : Data) (h : unparkReady d) : MoveReady (metadata.map Prod.swap) d := by
  have h20 := h.2 20 (by decide) (by decide)
  have h21 := h.2 21 (by decide) (by decide)
  have h22 := h.2 22 (by decide) (by decide)
  have h23 := h.2 23 (by decide) (by decide)
  simp [metadata,MoveReady,moved,h20,h21,h22,h23,h.1]

theorem unpark_cost (d : Data) : moveCost (metadata.map Prod.swap) d =
    6*((d.stacks 12).length+(d.stacks 13).length+(d.stacks 14).length+(d.stacks 15).length)+24 := by
  simp [moveCost,metadata,moved]
  omega

theorem unpark_eval (d : Data) (h : unparkReady d) :
    Eval unpark (6*((d.stacks 12).length+(d.stacks 13).length+
      (d.stacks 14).length+(d.stacks 15).length)+24) d (unparked d) := by
  simpa only [unpark,unparked,unpark_cost] using
    moveMany_eval (metadata.map Prod.swap) d (unpark_ready d h)

theorem parked_stack (d : Data) (j : Fin 48) :
    (parked d).stacks j =
      if j=12 then d.stacks 20 else if j=13 then d.stacks 21 else
      if j=14 then d.stacks 22 else if j=15 then d.stacks 23 else
      if j=20 ∨ j=21 ∨ j=22 ∨ j=23 then [] else d.stacks j := by
  fin_cases j <;> simp [parked,moveState,metadata,moved]

theorem unparked_stack (d : Data) (j : Fin 48) :
    (unparked d).stacks j =
      if j=20 then d.stacks 12 else if j=21 then d.stacks 13 else
      if j=22 then d.stacks 14 else if j=23 then d.stacks 15 else
      if j=12 ∨ j=13 ∨ j=14 ∨ j=15 then [] else d.stacks j := by
  fin_cases j <;> simp [unparked,moveState,metadata,moved]

/-- Restoring parameters after a framed scorer also restores every scratch
slot used to park them. The scorer may replace output0 only. -/
theorem unpark_after_output (d e : Data) (h : parkReady d)
    (he : ∀ j, j ≠ 0 → e.stacks j=(parked d).stacks j) :
    (unparked e).stacks = Function.update d.stacks 0 (e.stacks 0) := by
  funext j
  have h12 := h 12 (by decide) (by decide)
  have h13 := h 13 (by decide) (by decide)
  have h14 := h 14 (by decide) (by decide)
  have h15 := h 15 (by decide) (by decide)
  rw [unparked_stack]
  fin_cases j <;> simp [he,parked_stack,h12,h13,h14,h15]

end SubexponentialSAT.SqrtLog.PackingProgram.Assembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramCombine
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed two-call score combiner. Inputs are binary weights and canonical
false-unary collision counts. The only modified port is the score accumulator. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

 theorem combineCommand_eval (d : CombineData) (ci ch : ℕ)
    (hi : d.stacks 1 = List.replicate ci false)
    (hh : d.stacks 3 = List.replicate ch false)
    (h5 : d.stacks 5 = []) (h6 : d.stacks 6 = []) (h7 : d.stacks 7 = []) :
    ∃ t ≤ combineBudget d ci ch, ∃ e : CombineData,
      Eval combineCommand t d e ∧
      e.stacks 4 = List.replicate
        (SubexponentialSAT.CounterPrograms.value (d.stacks 0)*ci +
          SubexponentialSAT.CounterPrograms.value (d.stacks 2)*ch) false ++ d.stacks 4 ∧
      (∀ j, j ≠ 4 → e.stacks j = d.stacks j) := by
  obtain ⟨t₁, ht₁, a, ha, ho₁, hf₁⟩ := scale_lifted id incidenceScaleStacks
    Function.injective_id incidenceScaleStacks_injective d ci hi h5 h6 h7
  have hha : a.stacks 3 = List.replicate ch false := (hf₁ 3 (by decide)).trans hh
  have ha5 : a.stacks 5 = [] := (hf₁ 5 (by decide)).trans h5
  have ha6 : a.stacks 6 = [] := (hf₁ 6 (by decide)).trans h6
  have ha7 : a.stacks 7 = [] := (hf₁ 7 (by decide)).trans h7
  obtain ⟨t₂, ht₂, e, he, ho₂, hf₂⟩ := scale_lifted id headScaleStacks
    Function.injective_id headScaleStacks_injective a ch hha ha5 ha6 ha7
  have ha2 : a.stacks 2 = d.stacks 2 := hf₁ 2 (by decide)
  refine ⟨t₁+t₂, ?_, e, ha.seq he, ?_, ?_⟩
  · simp only [incidenceScaleStacks, headScaleStacks, Matrix.cons_val_zero ] at ht₁ ht₂
    change t₁ ≤ scaleBudget (d.stacks 0) ci+1 at ht₁
    change t₂ ≤ scaleBudget (a.stacks 2) ch+1 at ht₂
    rw [ha2] at ht₂
    unfold combineBudget
    omega
  · change a.stacks 4 = List.replicate (SubexponentialSAT.CounterPrograms.value (d.stacks 0)*ci) false ++ d.stacks 4 at ho₁
    change e.stacks 4 = List.replicate (SubexponentialSAT.CounterPrograms.value (a.stacks 2)*ch) false ++ a.stacks 4 at ho₂
    rw [ho₂, ha2, ho₁, ← List.append_assoc, ← List.replicate_add]
    congr 2
    omega
  · intro j hj
    exact (hf₂ j hj).trans (hf₁ j hj)

 theorem combine_lifted {R S : ℕ} (register : Fin 3 → Fin R) (stack : Fin 8 → Fin S)
    (hr : Function.Injective register) (hs : Function.Injective stack)
    (d : State R S) (ci ch : ℕ)
    (hi : d.stacks (stack 1) = List.replicate ci false)
    (hh : d.stacks (stack 3) = List.replicate ch false)
    (h5 : d.stacks (stack 5) = []) (h6 : d.stacks (stack 6) = [])
    (h7 : d.stacks (stack 7) = []) :
    ∃ t ≤ combineBudget (projectState register stack d) ci ch+1, ∃ e : State R S,
      Eval (liftCommand combineCommand 0 4 register stack) t d e ∧
      e.stacks (stack 4) = List.replicate
        (SubexponentialSAT.CounterPrograms.value (d.stacks (stack 0))*ci +
          SubexponentialSAT.CounterPrograms.value (d.stacks (stack 2))*ch) false ++ d.stacks (stack 4) ∧
      (∀ j, j ≠ stack 4 → e.stacks j = d.stacks j) := by
  let a := projectState register stack d
  obtain ⟨t, ht, b, hb, ho, hf⟩ := combineCommand_eval a ci ch hi hh h5 h6 h7
  refine ⟨t+1, Nat.add_le_add_right ht 1, embedState register stack d b,
    eval_liftCommand_from_state _ 0 4 register stack d hr hs hb, ?_, ?_⟩
  · simpa [a, projectState, embedState_stack register stack d b hs 4] using ho
  · intro j hj
    by_cases hm : ∃ i, stack i = j
    · obtain ⟨i, rfl⟩ := hm
      rw [embedState_stack register stack d b hs i]
      exact hf i (fun h => hj (congrArg stack h))
    · exact embedState_stack_frame register stack d b j hm
end SubexponentialSAT.SqrtLog.PackingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramStreams
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingProgram.Streams
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

 theorem eval_congr_output {R S : ℕ} {cmd : Cmd R S} {n : ℕ}
    {a b c : State R S} (h : Eval cmd n a b) (he : b=c) : Eval cmd n a c := by
  cases he
  exact h

end SubexponentialSAT.SqrtLog.PackingProgram.Streams

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramAssemblyWeights
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual native coefficient construction followed by stream weighting. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

def WeightReady (d : Data) : Prop :=
  ∀ j : Fin 13, 4 ≤ j.val → d.stacks (weightPorts j)=[]

theorem weights_eval (d : Data) (h : WeightReady d) :
    ∃ t ≤ 500*(2*dataLength d+4)^2+1, ∃ e : Data,
      Eval weights t d e ∧
      SubexponentialSAT.BinaryArithmetic.toNat (e.stacks 15)=
        (SubexponentialSAT.BinaryArithmetic.toNat (d.stacks 20))^2 *
          (SubexponentialSAT.BinaryArithmetic.toNat (d.stacks 21))^2 ∧
      SubexponentialSAT.BinaryArithmetic.toNat (e.stacks 16)=
        8*(SubexponentialSAT.BinaryArithmetic.toNat (d.stacks 22))^2 *
          (SubexponentialSAT.BinaryArithmetic.toNat (d.stacks 23))^2 ∧
      (e.stacks 15).length ≤ 2*(d.stacks 20).length+2*(d.stacks 21).length+3 ∧
      (e.stacks 16).length ≤ 2*(d.stacks 22).length+2*(d.stacks 23).length+6 ∧
      (∀ j,j≠15→j≠16→e.stacks j=d.stacks j) := by
  obtain ⟨t,ht,e,he,hi,hh,hli,hlh,hf,_⟩ := PackingWeightProgram.command_lifted
    mergeRegisters weightPorts mergeRegisters_injective weightPorts_injective d h
  refine ⟨t,ht,e,he,?_,?_,hli,hlh,hf⟩
  · simpa [PackingWeightProgram.incidence,projectState,weightPorts,mul_pow] using hi
  · simpa [PackingWeightProgram.head,projectState,weightPorts,mul_pow,Nat.mul_assoc] using hh

def inputPairScores (d : Data) (ps : List (ℕ × ℕ)) : Prop :=
  d.stacks 0=ProgramEncoding.encodeRecords (Zip.firstScores ps) ∧
  d.stacks 12=ProgramEncoding.encodeRecords (Zip.secondScores ps) ∧
  (∀ j : Fin 48, j ∈ ({1,2,3,4,5,6,7,13,14,15,16,17} : Finset (Fin 48)) → d.stacks j=[])

end SubexponentialSAT.SqrtLog.PackingProgram.Assembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationEmitProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native emission of the positive part of a shifted coefficient array.
The dimensions and the singleton support mask are runtime data. The constant
cell is consumed without emission; all later cells are framed, including zero
coefficients. No normalization or arithmetic oracle is used. -/
namespace SubexponentialSAT.SqrtLog.PerturbationEmitProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpConvolutionControl

/-- Take one forward fixed-width cell and reverse it for the framed emitter. -/
def readCoefficient : Code := .seq (takeWord 211 226 227 240 228 0 1)
  (.call (StackRoutines.reverseProgram 228 226 227 (0 : Fin 16) 1))

def emitCommand : Code := .call (ProgramLinking.liftProgram
  Squarefree.Program.prependRecordProgram emitRegisters emitMap)

def step : Code := .seq readCoefficient (.seq keyCommand (.seq emitCommand increment))

end SubexponentialSAT.SqrtLog.PerturbationEmitProgram


namespace SubexponentialSAT.SqrtLog.PerturbationEmitProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpConvolutionControl

/-- Exact order of the raw native accumulator: later degrees are prepended.
This deliberately retains zero coefficients; normalization is a separate job. -/
def emitted (mask : List Bool) : ℕ → List (List Bool) → List Bool → List Bool
  | _, [], acc => acc
  | j, c::cs, acc => emitted mask (j+1) cs (record mask j c++acc)

def loopPorts : UnaryForPrograms.Ports 16 256 := ⟨225,0,1⟩
def loop : Code := UnaryForPrograms.forCmd loopPorts step

end SubexponentialSAT.SqrtLog.PerturbationEmitProgram


namespace SubexponentialSAT.SqrtLog.PerturbationEmitProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpConvolutionControl

/-- The first cell is the node value, not a positive-Z coefficient. -/
def dropConstant : Code := .seq (takeWord 211 226 227 240 228 0 1) (clear 228)

def start : Code := .seq (copy 213 225) increment

def branch : Code := .ite 1 (.seq dropConstant loop) (.base .skip)
def command : Code := .seq start (.seq (UnaryForPrograms.popCmd loopPorts)
  (.seq branch (clear 221)))

end SubexponentialSAT.SqrtLog.PerturbationEmitProgram


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationMaskProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed native constructor for original-coordinate singleton masks.
Masters212/218 are retained; output214 and scratch120/221/222/223 are the
only touched stacks. No table of masks or semantic mask oracle is supplied. -/
namespace SubexponentialSAT.SqrtLog.PerturbationMaskProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl SubexpScanPrimitives

def zeroPorts : UnaryForPrograms.Ports 16 256 := ⟨221,0,1⟩
abbrev zeroLoop : Code := UnaryForPrograms.forCmd zeroPorts (pushBit false)
abbrev zeroCommand : Code := .seq (copy 212 221) zeroLoop

/-- Read the zero zeroPrefix, replace the selected bit, and restore the zeroPrefix. -/
abbrev selectCommand : Code :=
  .seq (takeWord 218 221 222 214 223 0 1)
    (.seq (popToken 214) (.seq (pushBit true)
      (.call (StackRoutines.transferProgram 223 214 (0 : Fin 16) 1))))

abbrev command : Code := .seq zeroCommand selectCommand

end SubexponentialSAT.SqrtLog.PerturbationMaskProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyBranch
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native high-variable dispatch from original-coordinate mask/assignment
masters. The runtime index is233, and both source masters are retained. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl SubexpScanPrimitives

def bitRead : Code := .call (ProgramLinking.liftProgram
  Subexp.TypeBitProgram.program flagRegs flagStacks)


end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyControl
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed native staging for the complete per-coordinate perturbation worker.
All dimensions and values are runtime tapes. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl SubexpPolynomialConstructor

/-- Current source row219, full source count210, scalar width211. -/
def loadRow : Code := .seq (move 219 246) (.seq (copy 210 248) (copy 211 250))

/-- Padded stream240 goes to246. The source count is reset from210. The target
zero array192 supplies both seed240 and polynomial-cell width250. -/
def enterHorner : Code := .seq (move 240 246) (.seq (copy 210 248)
  (.seq (clear 250) (.seq (copy 192 250) (copy 192 240))))

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyConstants
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid construction of the polynomial Horner point and seed. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl SubexpPolynomialConstructor
open DensePolynomialProgram (Coeff)
open DensePolynomialProgram.Constructor

/-- Runtime theta209, full-ring one208, full-ring zero207 and jet count243. -/
def constructConstants : Code := .seq (construct 207 207 239)
  (.seq (construct 209 208 247) (copy 207 254))

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyModel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual fixed-length polynomial services instantiate the shifted-row
machine. Its semantic result follows from the executed Horner fold. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open DensePolynomialProgram
open SubexponentialSAT.SubexpSymbolicCost
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

abbrev shiftedValue {B d : ℕ} (ops : RingProgram (Coeff B d))
    (J : ℕ) (theta : Coeff B d) (P : List (Coeff B d)) : Fixed.Array B d J :=
  HornerProgram.fold (HornerProgram.stepValue (Fixed.mul ops) (Fixed.add ops)
    (CRTLocalProgram.Model.linear ops.zeroRun.1 ops.oneRun.1 theta J))
    (P.map (fun c => CRTLocalProgram.Model.constant ops.zeroRun.1 c J)).reverse
    (CRTLocalProgram.Model.zero ops.zeroRun.1 J)

end SubexponentialSAT.SqrtLog.PerturbationAssembly

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

abbrev Code := Cmd 16 256

def popRow : Code := .base (.atom (.pop 230 0 1))

/-- Consume the outer list tag and physically decode one coefficient array. -/
def readRow : Code := .seq popRow
  (.seq (PerturbationBetaFrames.readFrame 230 232 (by decide))
    (PerturbationBetaFrames.transfer 232 246))

end SubexponentialSAT.SqrtLog.PerturbationBetaProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyCoordinate
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Per-coordinate physical composition. Original ambient variable IDs remain
unchanged throughout row loading, singleton support construction and emission. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl SubexpPolynomialConstructor

/-- Read one runtime-framed row, then construct the current support mask. -/
def loadCoordinate : Code := .seq PerturbationBetaProgram.readRow
  (.seq (move 246 219) PerturbationMaskProgram.command)

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyEntry
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Frame an actual completed incidence dictionary under its original variable
ID. The table accumulator is229; all coefficient-emitter work ports are free. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpConvolutionControl
open SubexpPolynomialConstructor

def emitTable : Code :=
  liftCommand PerturbationEmitProgram.emitCommand 0 0 id tableMap

def prepareEntry : Code := .seq (copy 215 222)
  (.seq (.call (StackRoutines.reverseProgram 222 223 224 (0 : Fin 16) 1))
    (.seq (move 217 228)
      (.call (StackRoutines.reverseProgram 228 226 227 (0 : Fin 16) 1))))

def entry : Code := .seq prepareEntry emitTable

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyNativeCoordinate
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open DensePolynomialProgram
open SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def coordinateResult {B d n : ℕ} (ops : RingProgram (Coeff B d)) (J : ℕ)
    (theta : Coeff B d) (v : Fin n) (P : List (Coeff B d)) (acc : List Bool) : List Bool :=
  PerturbationEmitProgram.emitted (Squarefree.encodeMask {v}) 1
    (((shiftedValue ops J theta P).val.map RingProgram.flat).tail) acc

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyPreparation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Executable incidence preparation. The inner worker has no arithmetic,
mask, beta, shifted-polynomial or dictionary oracle. Source generation is
composed as a fixed command in the outer768-stack frame. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl SubexpPolynomialConstructor

def finishLiteral : Code := .seq entry (.seq (clear 215) (clear 205))

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyNativeFactor
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One complete selected-factor incidence slice, from the executed source
provider through all original variables to the interpreter's raw table ABI. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open DensePolynomialProgram SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

variable (t : ℕ) {d : ℕ} (a : RingModel.Data d)
  (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
  (J N : ℕ) (theta : Coeff (baseWidth 3 t) d)

abbrev FactorRows := ℕ → List (Fixed.Array (baseWidth 3 t) d N × Bool)

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeKeyMapProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

def state (regs : Fin 8 → Bool) (s : Store) : Data := ⟨regs,tapes s⟩

end SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram

/-! Public native sparse-key mapper. The instruction table is independent of
the keys, clipping limits, coefficient width, and dictionary length. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeScaleProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Base stage. -/
/-! Fixed physical ABI for scaling all coefficients in a sparse dictionary.
The low 32 stacks are the common coefficient-ring service. The eight high
stacks hold source, reversed output, scalar, key, coefficient staging, frame
staging, final output, and a preserved copy of the unary degree. -/

namespace SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

def peeked (d : Data) : Data := ⟨readRegs d.regs 0 7 (d.stacks 32).head?, d.stacks⟩

end SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram

/-! Moves stage. -/

/-! Emit stage. -/

/-! Native stage. -/

/-! Loop stage. -/

/-! Cost stage. -/

/-! Semantics stage. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_AssignmentInputCall
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One-output physical calls in the assignment-input workspace. -/

namespace SubexponentialSAT.Subexp.AssignmentInputCall

open BitProgram StructuredCalls SubexpSetupStorage

theorem call_eval {r s l : ℕ} (p : Program r s l) (hr : r ≤ 16) (hs : s ≤ 10)
    (inputs : List (Fin 48 × Fin 48)) (q : Fin s) (dst : Fin 48)
    (a : Data) (out : State r s) {ticks : ℕ}
    (hd : dst ∉ work) (htmp : dst ≠ 31)
    (hin : ∀ x ∈ inputs, x.2 ∈ work)
    (hports : ∀ x ∈ inputs, x.1 ≠ x.2 ∧ x.1 ≠ 31 ∧ (31 : Fin 48) ≠ x.2)
    (hc : Clean a)
    (ht : Trace p ticks
      ((project (register hr) (stack hs) (prepareState 31 work inputs a)).withPC
        (some p.entry)) (out.withPC none)) :
    ∃ b, Eval (call p hr hs inputs q dst) (callCost hr hs inputs q dst a out ticks) a b ∧
      b.stacks = Function.update a.stacks dst (out.stacks q) ∧ Clean b := by
  have hframe : ¬ ∃ j, stack hs j = (31 : Fin 48) := by
    rintro ⟨j, h⟩
    have hm := stack_mem hs j
    rw [h, mem_work] at hm
    change 12 ≤ 31 ∧ 31 < 22 at hm
    omega
  have ho : ∀ x ∈ [(stack hs q, dst)], x.1 ≠ x.2 ∧ x.1 ≠ 31 ∧ (31 : Fin 48) ≠ x.2 := by
    intro x hx
    simp only [List.mem_singleton] at hx
    subst x
    refine ⟨?_, ?_, Ne.symm htmp⟩
    · intro he
      change stack hs q = dst at he
      exact hd (he ▸ stack_mem hs q)
    · intro he; exact hframe ⟨q, he⟩
  have h := isolated_eval p (register hr) (stack hs) (register_injective hr)
    (stack_injective hs) 31 work inputs [(stack hs q, dst)] a out hports ho hframe ht
  have hout := finish_one_stacks hr hs inputs a out q dst hd hin hc
  refine ⟨_, h, hout, ?_⟩
  constructor
  · intro j hj
    have hne : j ≠ dst := by intro he; exact hd (he ▸ hj)
    rw [hout, Function.update_of_ne hne]
    exact hc.1 j hj
  · rw [hout, Function.update_of_ne (Ne.symm htmp)]
    exact hc.2

theorem callCost_le {r s : ℕ} (hr : r ≤ 16) (hs : s ≤ 10)
    (inputs : List (Fin 48 × Fin 48)) (q : Fin s) (dst : Fin 48)
    (a : Data) (out : State r s) (ticks B : ℕ)
    (hn : inputs.length ≤ 2) (ha : Within a B) (ho : Within out B) :
    callCost hr hs inputs q dst a out ticks ≤ ticks + 400 * (B + 1) := by
  obtain ⟨hp, hpt⟩ := prepare_bound inputs a B hn ha
  have hm := within_embed hr hs (prepareState 31 work inputs a) out (4 * B) hp
    (within_mono ho (by omega))
  have hf := finish_bound (stack hs q) dst _ (4 * B) hm
  unfold callCost
  omega

end SubexponentialSAT.Subexp.AssignmentInputCall

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_AssignmentInputProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical input construction for sequential type assignment

All parameters are unary stack data. The fixed program constructs the one-hot
word alphabet, reads its actual first word, derives its packed view, and builds
the exact seed range and dimensions expected by `AssignmentInitProgram`.
-/

namespace SubexponentialSAT.Subexp.AssignmentInputProgram

open BitProgram StructuredCalls SubexpSetupStorage AssignmentInputCall

/-- A physical stage changes one public stack and restores the private bank.
The witness is an actual measured execution of its finite instruction table. -/
def Writes (c : Code) (a : Data) (dst : Fin 48) (bits : List Bool) (charge : ℕ) : Prop :=
  ∃ ticks b, Eval c ticks a b ∧ b.stacks = Function.update a.stacks dst bits ∧ Clean b ∧
    ∀ B, Within a B → bits.length ≤ B → 1 ≤ B → ticks ≤ charge + 400 * (B + 1)

theorem repeat_eval (a : Data) (src count dst : Fin 48) (m n : ℕ)
    (hc : Clean a) (hsrc : a.stacks src = unary m) (hcount : a.stacks count = unary n)
    (hd : dst ∉ work) (htmp : dst ≠ 31)
    (hports : ∀ x ∈ [(src, 12), (count, 15)],
      x.1 ≠ x.2 ∧ x.1 ≠ 31 ∧ (31 : Fin 48) ≠ x.2)
    (hcount12 : count ≠ 12) :
    Writes (AssignmentInputCall.call BlockCopyProgram.program (by decide) (by decide)
      [(src, 12), (count, 15)] 1 dst) a dst (unary (n * m))
      (n * (7 * m + 7) + 3) := by
  let pre := project (register (r := 3) (by decide)) (stack (s := 4) (by decide))
    (prepareState 31 work [(src, 12), (count, 15)] a)
  have hp : pre = BlockCopyProgram.initialState n (unary m) [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      have h := prepare_regs [(src, 12), (count, 15)] a (register (by decide) i)
        (by have := i.isLt; simp only [register, Fin.val_castLE]; omega)
      fin_cases i <;> exact h
    · funext i
      have h := prepare_two_local (r := 3) (s := 4) (by decide) (by decide)
        a hc src count 0 3 (by decide) hcount12 i
      change pre.stacks i = _
      change pre.stacks i = _ at h
      rw [h]
      fin_cases i <;> simp [ hsrc, hcount]
  have ht := BlockCopyProgram.program_trace n (unary m) []
  rw [← hp] at ht
  obtain ⟨b, he, hs, hb⟩ := call_eval BlockCopyProgram.program
    (by decide) (by decide) [(src, 12), (count, 15)] 1 dst a
    (BlockCopyProgram.data false false (unary m) (BlockCopyProgram.copies n (unary m) ++ []) [])
    hd htmp (by simp [mem_work]) hports hc ht
  refine ⟨_, b, he, by simpa [BlockCopyProgram.data, copies_unary] using hs, hb, ?_⟩
  intro B ha hresult _
  simp only [List.length_replicate] at hresult
  have hm : m ≤ B := by simpa [hsrc] using ha src
  have ho : Within (BlockCopyProgram.data false false (unary m)
      (BlockCopyProgram.copies n (unary m) ++ []) []) B := by
    intro j; fin_cases j <;> simp [BlockCopyProgram.data, copies_unary, hm, hresult]
  simpa only [List.length_replicate] using callCost_le (r := 3) (s := 4)
    (by decide) (by decide) [(src, 12), (count, 15)] 1 dst a _ _ B (by simp) ha ho

theorem clean_of_update (a b : Data) (dst : Fin 48) (bits : List Bool)
    (hc : Clean a) (hd : dst ∉ work) (htmp : dst ≠ 31)
    (hs : b.stacks = Function.update a.stacks dst bits) : Clean b := by
  constructor
  · intro j hj
    have hn : j ≠ dst := by intro h; exact hd (h ▸ hj)
    simp [hs, hn, hc.1 j hj]
  · simp [hs, Ne.symm htmp, hc.2]

theorem within_of_update (a b : Data) (dst : Fin 48) (bits : List Bool) (B : ℕ)
    (ha : Within a B) (hb : bits.length ≤ B)
    (hs : b.stacks = Function.update a.stacks dst bits) : Within b B := by
  intro j
  by_cases hj : j = dst
  · subst j; simpa only [hs, Function.update_same] using hb
  · simpa [hs, Function.update_apply, hj] using ha j

theorem depth_eval (a : Data) (n : ℕ) (hc : Clean a)
    (h6 : a.stacks 6 = unary n) (h34 : a.stacks 34 = []) :
    Writes depth a 34 (unary (2 * n)) (14 * n + 10) := by
  let b := copyManyState [(6, 34), (6, 34)] a
  have h := copyMany_eval 31 [(6, 34), (6, 34)] a (by simp) hc.2
  have hs : b.stacks = Function.update a.stacks 34 (unary (2 * n)) := by
    funext j
    by_cases hj : j = 34
    · subst j
      simp [b, copyManyState, copyState_stack, h6, h34, unary,
 two_mul]
    · simp [b, copyManyState, copyState_stack, hj]
  refine ⟨_, b, h, hs, clean_of_update a b 34 _ hc (by decide) (by decide) hs, ?_⟩
  intro B _ _ _
  simp [copyManyCost, copyState_stack, h6]
  omega

theorem input_clean (regs : Fin 16 → Bool) (r Q delta D E : ℕ) (pairs : List Bool) :
    Clean (inputState regs r Q delta D E pairs) := by
  constructor
  · intro j hj
    rw [mem_work] at hj
    have h1 : j ≠ 1 := by intro h; subst j; change 12 ≤ 1 ∧ 1 < 22 at hj; omega
    have h2 : j ≠ 2 := by intro h; subst j; change 12 ≤ 2 ∧ 2 < 22 at hj; omega
    have h3 : j ≠ 3 := by intro h; subst j; change 12 ≤ 3 ∧ 3 < 22 at hj; omega
    have h4 : j ≠ 4 := by intro h; subst j; change 12 ≤ 4 ∧ 4 < 22 at hj; omega
    have h5 : j ≠ 5 := by intro h; subst j; change 12 ≤ 5 ∧ 5 < 22 at hj; omega
    have h45 : j ≠ 45 := by intro h; subst j; change 12 ≤ 45 ∧ 45 < 22 at hj; omega
    simp [inputState, h1, h2, h3, h4, h5, h45]
  · rfl

end SubexponentialSAT.Subexp.AssignmentInputProgram

end OAI.Algorithms
end


