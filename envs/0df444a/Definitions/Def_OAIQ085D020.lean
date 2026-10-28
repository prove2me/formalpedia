-- Prove2me | Definitions.Def_OAIQ085D020
-- name    : OAIQ085D020
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T16:17:53.338024+00:00
-- url     : https://prove2.me/theorems/8b6c2972-b16a-4661-92bf-7eb9c30210c6
-- title:
--   Definitions bundle OAIQ085D020 of the split of OpenAI, Constant-factor hardness of directed feedback vertex set (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DirectedFeedback.main`, carved from OpenAI's openai/math development (OpenAI, *Constant-factor hardness of directed feedback vertex set (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 350 declarations of OpenAI's Lean: 92 definitions, 7 inductive types or structures, 1 instance and 250 theorems. The definitions and types are `OAI.DFVSGames.Foundations.Complexity.GraphCounterModel.headerInTime`, `OAI.DFVSGames.Foundations.Complexity.GraphCounterModel.startInTime`, `OAI.DFVSGames.Foundations.Complexity.GraphCounterPrefix.rawOutput`, `OAI.DFVSGames.Foundations.Complexity.GraphCounterPrefix.rowsBits`, `OAI.DFVSGames.Foundations.Complexity.MachineCanonicalOutput.TerminalRun`, `OAI.DFVSGames.Foundations.Complexity.MachineCanonicalOutput.completedMachine`, `OAI.DFVSGames.Foundations.Complexity.MachineCanonicalOutput.completedProgram`, `OAI.DFVSGames.Foundations.Complexity.MachineCanonicalOutput.completedTime`, `OAI.DFVSGames.Foundations.Complexity.MachineCanonicalOutput.embeddedCfg`, `OAI.DFVSGames.Foundations.Complexity.MachineCeilingPower.paddingInTime`, `OAI.DFVSGames.Foundations.Complexity.MachineCloudPadding.padding`, `OAI.DFVSGames.Foundations.Complexity.MachineCloudPadding.program`, `OAI.DFVSGames.Foundations.Complexity.MachineCloudPrefix.amount`, `OAI.DFVSGames.Foundations.Complexity.MachineCloudPrefix.bodyTime`, `OAI.DFVSGames.Foundations.Complexity.MachineCloudPrefix.cycleTime`, `OAI.DFVSGames.Foundations.Complexity.MachineCloudPrefix.loopTime`, `OAI.DFVSGames.Foundations.Complexity.MachineCloudPrefix.program`, `OAI.DFVSGames.Foundations.Complexity.MachineCloudPrefix.sumFrom`, `OAI.DFVSGames.Foundations.Complexity.MachineCloudPrefix.totalTime`, `OAI.DFVSGames.Foundations.Complexity.MachineCloudSelect.cloudSelectSteps`, `OAI.DFVSGames.Foundations.Complexity.MachineCloudSelect.remainder`, `OAI.DFVSGames.Foundations.Complexity.MachineDummyRows.fieldTapes`, `OAI.DFVSGames.Foundations.Complexity.MachineDummyRows.initialTapes`, `OAI.DFVSGames.Foundations.Complexity.MachineDummyRows.program`, `OAI.DFVSGames.Foundations.Complexity.MachineDummyRows.rowBits`, `OAI.DFVSGames.Foundations.Complexity.MachineDummyRows.rowsBits`, `OAI.DFVSGames.Foundations.Complexity.MachineDummyRows.steps`, `OAI.DFVSGames.Foundations.Complexity.MachineDummyRows.trueBits`, `OAI.DFVSGames.Foundations.Complexity.MachineExpanderFamily.LevelLoopRun`, `OAI.DFVSGames.Foundations.Complexity.MachineExpanderFamily.ResizeRun`, `OAI.DFVSGames.Foundations.Complexity.MachineExpanderFamily.affinePhaseInTime`, `OAI.DFVSGames.Foundations.Complexity.MachineExpanderFamily.affineResultTapes`, `OAI.DFVSGames.Foundations.Complexity.MachineExpanderFamily.cleanedCounterTapes`, `OAI.DFVSGames.Foundations.Complexity.MachineExpanderFamily.cleanupCountersInTime`, `OAI.DFVSGames.Foundations.Complexity.MachineExpanderFamily.copyCountInTime`, `OAI.DFVSGames.Foundations.Complexity.MachineExpanderFamily.copyFrame`, `OAI.DFVSGames.Foundations.Complexity.MachineExpanderFamily.installTableInTime`, `OAI.DFVSGames.Foundations.Complexity.MachineExpanderFamily.installedFrame`, `OAI.DFVSGames.Foundations.Complexity.MachineExpanderFamily.installedTapes`, `OAI.DFVSGames.Foundations.Complexity.MachineExpanderFamily.levelLoopCost` and 59 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `DirectedFeedback_Encoding_Bounds`, `DirectedFeedback_Encoding_ExpanderTableWords`, `DirectedFeedback_Encoding_FinalCNFPattern`, `DirectedFeedback_Encoding_PreprocessingRegularTables`, `DirectedFeedback_Encoding_TableIteration`, `DirectedFeedback_Games_ExpanderFamily`, `DirectedFeedback_Games_InitialGraph`, `DirectedFeedback_Games_Preprocessing`, `DirectedFeedback_Machines_FinalCNFHeader`, `DirectedFeedback_Machines_GraphCounterFinish`, `DirectedFeedback_Machines_MachineCloudCount`, `DirectedFeedback_Machines_MachineCloudPadding`, `DirectedFeedback_Machines_MachineCloudSelect`, `DirectedFeedback_Machines_MachineDummyRows`, `DirectedFeedback_Machines_MachineExpanderFamilyLoop`, `DirectedFeedback_Machines_MachineExpanderFamilyTapes`, `DirectedFeedback_Machines_MachineExpanderRow`, `DirectedFeedback_Machines_MachineExpanderRowDivision`, `DirectedFeedback_Machines_MachineExpanderRowLookup`, `DirectedFeedback_Machines_MachineExpanderTableLoop`, `DirectedFeedback_Machines_MachineLazyTableRuntime`, `DirectedFeedback_Machines_MachinePaddedOverlay`, `DirectedFeedback_Machines_MachinePortReindex`, `DirectedFeedback_Machines_MachinePreservingLookupClean`, `DirectedFeedback_Machines_MachineRegularExecutionBounds`, `DirectedFeedback_Machines_MachineTableRows`, `DirectedFeedback_Machines_VertexLabel`.
--
--   **Imports.** It imports the bundles `OAIQ085D012`, `OAIQ085D013` and `OAIQ085D014` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ085D024`, `OAIQ085D025`, `OAIQ085D026` and `OAIQ085D027`.
-- source:
--   OpenAI, Constant-factor hardness of directed feedback vertex set (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Constant-factor-hardness-of-directed-feedback-vertex-set-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ085D012
import Definitions.Def_OAIQ085D013
import Definitions.Def_OAIQ085D014

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_Bounds
attribute [-instance] _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Soundness.ConditionalIncidences.zeroBits _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Complexity.MachineFieldProfile

open Turing

section Transport
variable {K Λ σ τ : Type} [DecidableEq K]

def copyInCompareState (source destination scratch : K)
    (hSD : source ≠ destination) (hST : source ≠ scratch) (hDT : destination ≠ scratch)
    (firstLabel secondLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineCompare.State σ))
    (atFirst : program firstLabel = copyStatement
      (Reduction.MachineTransfer.loopAt source scratch id false firstLabel (some secondLabel)))
    (atSecond : program secondLabel = copyStatement
      (MachineCopy.forkLoop scratch source destination false secondLabel exit))
    (base : K → List Bool) (hScratch : base scratch = []) (ambient : σ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some firstLabel, normalState ambient, base⟩
      (some ⟨exit, normalState ambient,
        Function.update base destination (base source ++ base destination)⟩)
      (2 * ((base source).length + 1)) := by
  let e := copyStateEquiv σ
  let view := MachineControl.program (Equiv.refl Λ) e.symm program
  have hfirst : view firstLabel =
      Reduction.MachineTransfer.loopAt source scratch id false firstLabel (some secondLabel) := by
    dsimp [view, MachineControl.program]
    rw [atFirst]
    exact statement_roundtrip e.symm _
  have hsecond : view secondLabel =
      MachineCopy.forkLoop scratch source destination false secondLabel exit := by
    dsimp [view, MachineControl.program]
    rw [atSecond]
    exact statement_roundtrip e.symm _
  let run := MachineCopy.copyInTime source destination scratch hSD hST hDT false
    firstLabel secondLabel exit view hfirst hsecond base hScratch (ambient, false, none) none
  have hprogram : MachineControl.program (Equiv.refl Λ) e view = program := by
    funext label
    exact statement_roundtrip e (program label)
  have hsim (a b : TM2.Cfg (fun _ : K => Bool) Λ ((σ × Bool × Option Bool) × Option Bool))
      (hab : TM2.step view a = some b) :
      TM2.step program (MachineControl.configuration id e a) =
        some (MachineControl.configuration id e b) := by
    have hh := MachineControl.step_simulation (Equiv.refl Λ) e view a
    rw [hprogram, hab] at hh
    exact hh
  have lifted := MachineComposition.liftExecutionInTime (TM2.step view) (TM2.step program)
    (MachineControl.configuration id e) hsim run
  simpa [MachineControl.configuration, copyStateEquiv, normalState, e] using lifted

end Transport

section PreservedComparison
variable {K Λ σ : Type} [DecidableEq K]

def nonDestructiveCompareInTime (left right workLeft workRight scratch : K)
    (hleft : left ≠ workLeft ∧ left ≠ workRight ∧ left ≠ scratch)
    (hright : right ≠ workLeft ∧ right ≠ workRight ∧ right ≠ scratch)
    (hwork : workLeft ≠ workRight ∧ workLeft ≠ scratch ∧ workRight ≠ scratch)
    (leftFirst leftSecond rightFirst rightSecond compareLabel : Λ)
    (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineCompare.State σ))
    (atLeftFirst : program leftFirst = copyStatement
      (Reduction.MachineTransfer.loopAt left scratch id false leftFirst (some leftSecond)))
    (atLeftSecond : program leftSecond = copyStatement
      (MachineCopy.forkLoop scratch left workLeft false leftSecond (some rightFirst)))
    (atRightFirst : program rightFirst = copyStatement
      (Reduction.MachineTransfer.loopAt right scratch id false rightFirst (some rightSecond)))
    (atRightSecond : program rightSecond = copyStatement
      (MachineCopy.forkLoop scratch right workRight false rightSecond (some compareLabel)))
    (atCompare : program compareLabel =
      MachineCompare.loop workLeft workRight compareLabel equalExit differentExit)
    (base : K → List Bool) (hWL : base workLeft = []) (hWR : base workRight = [])
    (hScratch : base scratch = []) (ambient : σ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some leftFirst, normalState ambient, base⟩
      (some ⟨if base left = base right then equalExit else differentExit,
        normalState ambient, base⟩)
      (2 * ((base left).length + 1) + 2 * ((base right).length + 1) +
        max (base left).length (base right).length + 1) := by
  let t₁ := Function.update base workLeft (base left)
  let t₂ := Function.update t₁ workRight (base right)
  have h₁ := copyInCompareState left workLeft scratch hleft.1 hleft.2.2 hwork.2.1
    leftFirst leftSecond (some rightFirst) program atLeftFirst atLeftSecond base hScratch ambient
  simp only [hWL, List.append_nil] at h₁
  have hSR : t₁ right = base right := by simp [t₁, hright.1]
  have hDR : t₁ workRight = [] := by simp [t₁, Ne.symm hwork.1, hWR]
  have hTR : t₁ scratch = [] := by simp [t₁, Ne.symm hwork.2.1, hScratch]
  have h₂ := copyInCompareState right workRight scratch hright.2.1 hright.2.2 hwork.2.2
    rightFirst rightSecond (some compareLabel) program atRightFirst atRightSecond t₁ hTR ambient
  rw [hSR, hDR] at h₂
  simp only [List.append_nil] at h₂
  have hL : t₂ workLeft = base left := by simp [t₂, t₁, hwork.1]
  have hR : t₂ workRight = base right := by simp [t₂]
  have hrestore : Reduction.MachineTransfer.tapesAt workLeft workRight t₂ [] [] = base := by
    funext p
    by_cases hl : p = workLeft
    · subst p
      simp [Reduction.MachineTransfer.tapesAt, hwork.1, hWL]
    · by_cases hr : p = workRight
      · subst p
        simp [Reduction.MachineTransfer.tapesAt, hWR]
      · simp [Reduction.MachineTransfer.tapesAt, t₂, t₁, hl, hr]
  have h₃ := MachineCompare.compareInTime workLeft workRight hwork.1 compareLabel
    equalExit differentExit program atCompare t₂ ambient none none
  rw [hL, hR, hrestore] at h₃
  let h₁₂ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ h₁ h₂
  let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ h₁₂ h₃
  exact { toEvalsTo := run.toEvalsTo, steps_le_m := by have h := run.steps_le_m; omega }

end PreservedComparison


def stageInTime {q : Nat} (cells : List (Fin q × Fin q)) (r : Nat) (hr : r < cells.length)
    (base : Tape q → List Bool) (hwork : ∀ w : Fin 3, base (.inr w) = []) (profile : Profile q) :
    StateTransition.EvalsToInTime (TM2.step (profileProgram cells))
      ⟨some (labelAt cells r 0), normalState profile, base⟩
      (some ⟨some (labelAt cells (r + 1) 0),
        normalState (setExpected (fun i => base (.inl i)) profile cells[r]), base⟩)
      (pairTime (fun i => base (.inl i)) cells[r]) := by
  let pair := cells[r]
  have copied := nonDestructiveCompareInTime (.inl pair.1) (.inl pair.2)
    (.inr 0 : Tape q) (.inr 1) (.inr 2) (by simp) (by simp) (by simp)
    (labelAt cells r 0) (labelAt cells r 1) (labelAt cells r 2) (labelAt cells r 3)
    (labelAt cells r 4) (some (labelAt cells r 5)) (some (labelAt cells r 6))
    (profileProgram cells)
    (by simp [profileProgram, labelAt, Nat.min_eq_left hr.le, hr, pair])
    (by simp [profileProgram, labelAt, Nat.min_eq_left hr.le, hr, pair])
    (by simp [profileProgram, labelAt, Nat.min_eq_left hr.le, hr, pair])
    (by simp [profileProgram, labelAt, Nat.min_eq_left hr.le, hr, pair])
    (by simp [profileProgram, labelAt, Nat.min_eq_left hr.le, hr])
    base (hwork 0) (hwork 1) (hwork 2) profile
  have stored : StateTransition.EvalsToInTime (TM2.step (profileProgram cells))
      ⟨if base (.inl pair.1) = base (.inl pair.2) then some (labelAt cells r 5)
        else some (labelAt cells r 6), normalState profile, base⟩
      (some ⟨some (labelAt cells (r + 1) 0),
        normalState (setExpected (fun i => base (.inl i)) profile pair), base⟩) 1 := {
    steps := 1
    evals_in_steps := by
      change TM2.step (profileProgram cells)
        ⟨if base (.inl pair.1) = base (.inl pair.2) then some (labelAt cells r 5)
          else some (labelAt cells r 6), normalState profile, base⟩ = _
      by_cases heq : base (.inl pair.1) = base (.inl pair.2)
      · simp [heq, TM2.step, profileProgram, labelAt,
          Nat.min_eq_left hr.le, hr, storePair, TM2.stepAux, normalState,
          setExpected, equalityProfile, pair]
      · simp [heq, TM2.step, profileProgram, labelAt,
          Nat.min_eq_left hr.le, hr, storePair, TM2.stepAux, normalState,
          setExpected, equalityProfile, pair]
    steps_le_m := Nat.le_refl _
  }
  let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ copied stored
  refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
  have h := run.steps_le_m
  dsimp only [pair] at h
  dsimp only [pairTime]
  omega

def prefixInTime {q : Nat} (cells : List (Fin q × Fin q))
    (base : Tape q → List Bool) (hwork : ∀ w : Fin 3, base (.inr w) = []) (initial : Profile q)
    (r : Nat) (hr : r ≤ cells.length) :
    StateTransition.EvalsToInTime (TM2.step (profileProgram cells))
      ⟨some (labelAt cells 0 0), normalState initial, base⟩
      (some ⟨some (labelAt cells r 0),
        normalState (prefixProfile (fun i => base (.inl i)) initial cells r), base⟩)
      (prefixTime (fun i => base (.inl i)) cells r) := by
  induction r with
  | zero =>
    exact { steps := 0, evals_in_steps := rfl, steps_le_m := Nat.le_refl _ }
  | succ r ih =>
    have hrl : r < cells.length := by omega
    let first := ih (by omega)
    let second := stageInTime cells r hrl base hwork
      (prefixProfile (fun i => base (.inl i)) initial cells r)
    let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first second
    rw [prefixProfile_succ _ _ _ _ hrl, prefixTime_succ _ _ _ hrl]
    exact { toEvalsTo := run.toEvalsTo, steps_le_m := by have h := run.steps_le_m; omega }

def profileInTime (q : Nat) (base : Tape q → List Bool)
    (hwork : ∀ w : Fin 3, base (.inr w) = []) (initial : Profile q) :
    StateTransition.EvalsToInTime (profileMachine q).step
      ⟨some (labelAt (allPairs q) 0 0), normalState initial, base⟩
      (some ⟨none, normalState (equalityProfile (fun i => base (.inl i))), base⟩)
      (((allPairs q).map (pairTime (fun i => base (.inl i)))).sum + 1) := by
  let cells := allPairs q
  have first := prefixInTime cells base hwork initial cells.length (Nat.le_refl _)
  have last : StateTransition.EvalsToInTime (TM2.step (profileProgram cells))
      ⟨some (labelAt cells cells.length 0),
        normalState (prefixProfile (fun i => base (.inl i)) initial cells cells.length), base⟩
      (some ⟨none, normalState (equalityProfile (fun i => base (.inl i))), base⟩) 1 := {
    steps := 1
    evals_in_steps := by
      change TM2.step (profileProgram cells)
        ⟨some (labelAt cells cells.length 0),
          normalState (prefixProfile (fun i => base (.inl i)) initial cells cells.length), base⟩ = _
      simp [TM2.step, profileProgram, labelAt, TM2.stepAux,
        prefixProfile, cells, foldProfile_allPairs]
    steps_le_m := Nat.le_refl _
  }
  let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first last
  refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
  have h := run.steps_le_m
  simpa [prefixTime, cells, Nat.add_comm] using h

def profileInTime_bounded (q : Nat) (base : Tape q → List Bool)
    (hwork : ∀ w : Fin 3, base (.inr w) = []) (initial : Profile q)
    (L : Nat) (hL : ∀ i, (base (.inl i)).length ≤ L) :
    StateTransition.EvalsToInTime (profileMachine q).step
      ⟨some (labelAt (allPairs q) 0 0), normalState initial, base⟩
      (some ⟨none, normalState (equalityProfile (fun i => base (.inl i))), base⟩)
      (q * q * (5 * L + 6) + 1) := by
  let run := profileInTime q base hwork initial
  refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
  apply run.steps_le_m.trans
  apply Nat.add_le_add_right
  simpa only [length_allPairs] using totalTime_le (fun i => base (.inl i)) L hL (allPairs q)


end DFVSGames.Foundations.Complexity.MachineFieldProfile


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_ExpanderFamily
attribute [-instance] _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.PCP.PreprocessingLevels

theorem boundedLevel_le_input (k : Nat) : boundedLevel k ≤ k := by
  simpa only [boundedLevel, searchResult, Nat.zero_add] using
    levelLoop_level_le ExpanderFamily.growth k k 0 1

theorem paddedSize_power (k : Nat) :
    paddedSize k = ExpanderFamily.growth ^ boundedLevel k := by
  simpa only [paddedSize, boundedLevel, searchResult, pow_zero] using
    levelLoop_power ExpanderFamily.growth k k 0

theorem le_paddedSize (k : Nat) : k ≤ paddedSize k := by
  exact levelLoop_covers ExpanderFamily.growth k k 0 1
    ExpanderFamily.growth_gt_one (by omega) (by omega)

theorem boundedLevel_eq_level (k : Nat) :
    boundedLevel k = ExpanderFamily.level k := by
  apply Nat.le_antisymm
  · simpa only [boundedLevel, searchResult, pow_zero] using
      levelLoop_le_of_covering_power ExpanderFamily.growth k k 0
        (ExpanderFamily.level k) (Nat.zero_le _) (ExpanderFamily.le_size k)
  · apply (Nat.clog_le_iff_le_pow ExpanderFamily.growth_gt_one).2
    rw [← paddedSize_power]
    exact le_paddedSize k

theorem paddedSize_eq_size (k : Nat) : paddedSize k = ExpanderFamily.size k := by
  rw [paddedSize_power, boundedLevel_eq_level]
  rfl

theorem paddedSize_positive (k : Nat) : 0 < paddedSize k := by
  rw [paddedSize_power]
  exact Nat.pow_pos (by have h := ExpanderFamily.growth_gt_one; omega)

theorem paddedSize_bounds {k : Nat} (hk : 0 < k) :
    k ≤ paddedSize k ∧ paddedSize k ≤ ExpanderFamily.growth * k := by
  rw [paddedSize_eq_size]
  exact ⟨ExpanderFamily.le_size k, ExpanderFamily.size_le_mul hk⟩

def cloudPaddedSize (k : Nat) : Nat := if k = 0 then 0 else paddedSize k

@[simp] theorem cloudPaddedSize_zero : cloudPaddedSize 0 = 0 := rfl

theorem cloudPaddedSize_of_pos {k : Nat} (hk : 0 < k) :
    cloudPaddedSize k = paddedSize k := by
  simp only [cloudPaddedSize, Nat.ne_of_gt hk, ite_false]

theorem cloudPaddedSize_bounds (k : Nat) :
    k ≤ cloudPaddedSize k ∧ cloudPaddedSize k ≤ ExpanderFamily.growth * k := by
  by_cases hk : k = 0
  · subst k
    simp only [cloudPaddedSize_zero, Nat.mul_zero, le_refl, and_self]
  · rw [cloudPaddedSize_of_pos (Nat.pos_of_ne_zero hk)]
    exact paddedSize_bounds (Nat.pos_of_ne_zero hk)

theorem table_vertexCount_eq_paddedSize (k : Nat) :
    ExpanderTables.vertexCount (Expanders.baseDegree * Expanders.baseDegree)
        (boundedLevel k) = paddedSize k := by
  rw [ExpanderTables.vertexCount_eq]
  have hg : (Expanders.baseDegree * Expanders.baseDegree) *
      (Expanders.baseDegree * Expanders.baseDegree) = ExpanderFamily.growth := by
    unfold ExpanderFamily.growth
    ring
  rw [hg]
  exact (paddedSize_power k).symm

end DFVSGames.Foundations.PCP.PreprocessingLevels

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_PreprocessingRegularTables
attribute [-instance] _root_.OAI.DFVSGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.DFVSGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DFVSGames.Quadratic.blockOrientationFintype _root_.OAI.DFVSGames.Quadratic.fieldLineFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.PCP.PreprocessingRegularTables

open scoped BigOperators
open PoweringWalks DegreeReplacement

def padding (t : GraphTables.Table) (v : Fin t.vertices) : Nat :=
  PreprocessingLevels.cloudPaddedSize (PreprocessingCloudIndex.cloudSize t v) -
    PreprocessingCloudIndex.cloudSize t v

theorem cloudSize_add_padding (t : GraphTables.Table) (v : Fin t.vertices) :
    PreprocessingCloudIndex.cloudSize t v + padding t v =
      PreprocessingLevels.cloudPaddedSize (PreprocessingCloudIndex.cloudSize t v) :=
  Nat.add_sub_of_le (PreprocessingLevels.cloudPaddedSize_bounds _).1

theorem vertexCount_eq_sum_cloudPaddedSize (t : GraphTables.Table) :
    vertexCount t (padding t) = ∑ v,
      PreprocessingLevels.cloudPaddedSize (PreprocessingCloudIndex.cloudSize t v) := by
  unfold vertexCount
  rw [← PreprocessingCloudIndex.sum_cloudSize t, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun v _ => cloudSize_add_padding t v)

theorem vertexCount_le (t : GraphTables.Table) :
    vertexCount t (padding t) ≤ ExpanderFamily.growth * t.darts := by
  rw [vertexCount_eq_sum_cloudPaddedSize, ← PreprocessingCloudIndex.sum_cloudSize t,
    Finset.mul_sum]
  exact Finset.sum_le_sum (fun v _ => (PreprocessingLevels.cloudPaddedSize_bounds _).2)

def familyCloudTable (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices) :
    ExpanderTables.Table (PreprocessingCloudIndex.cloudSize t v + padding t v)
      internalDegree :=
  if hk : PreprocessingCloudIndex.cloudSize t v = 0 then
    resizeTable (by rw [cloudSize_add_padding, hk]; rfl) (emptyTable internalDegree)
  else
    resizeTable (by
      rw [cloudSize_add_padding,
        PreprocessingLevels.cloudPaddedSize_of_pos (Nat.pos_of_ne_zero hk)]
      exact PreprocessingLevels.table_vertexCount_eq_paddedSize _)
      (ExpanderTables.family H
        (PreprocessingLevels.boundedLevel (PreprocessingCloudIndex.cloudSize t v)))

def regularize (H : BaseTable) (t : GraphTables.Table) :
    PortTables.Table (vertexCount t (padding t)) (internalDegree + 1) :=
  ofCloudTables t (padding t) (familyCloudTable H t)

end DFVSGames.Foundations.PCP.PreprocessingRegularTables


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineCloudCount
attribute [-instance] _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Foundations.Complexity.MachineCloudCount

open Turing
open MachineComposition

variable {Λ σ : Type}

theorem countTrace (n m v : Nat) (rs : List Row)
    (hwidth : ∀ r ∈ rs, r.2.length = 4097)
    (targetSuffix count : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program (σ := σ))))^[totalSteps n m v rs]
      (some ⟨some .copyFirst, ((ambient, false), register),
        memory (inputWord n m rs) [] (encodeWord v ++ targetSuffix) [] count []⟩) =
      some ⟨none, ((ambient, false), none),
        memory (inputWord n m rs) [] (encodeWord v ++ targetSuffix) []
          (List.replicate (rowsHits v rs) true ++ count) []⟩ := by
  have hcopy := MachineCopy.copyTrace Tape.original Tape.work Tape.spare
    (by decide) (by decide) (by decide) false Label.copyFirst Label.copySecond
    (some Label.headerFirst) program rfl rfl
    (memory (inputWord n m rs) [] (encodeWord v ++ targetSuffix) [] count [])
    rfl (ambient, false) register
  simp only [memory_original, memory_work, List.append_nil, update_memory_work] at hcopy
  have hfirst := MachineLookup.discardTrace Tape.work Label.headerFirst Label.headerSecond
    program rfl
    (memory (inputWord n m rs) (inputWord n m rs) (encodeWord v ++ targetSuffix) [] count [])
    n (encodeWord m ++ encodeWords (rs.flatMap rowWords))
    (by exact inputWord_eq n m rs) (ambient, false) none
  simp only [update_memory_work] at hfirst
  have hsecond := MachineLookup.discardTrace Tape.work Label.headerSecond Label.row
    program rfl
    (memory (inputWord n m rs) (encodeWord m ++ encodeWords (rs.flatMap rowWords))
      (encodeWord v ++ targetSuffix) [] count [])
    m (encodeWords (rs.flatMap rowWords)) rfl (ambient, false) none
  simp only [update_memory_work] at hsecond
  have hrows := rowsTrace rs hwidth v (inputWord n m rs) targetSuffix count [] ambient none
  rw [show totalSteps n m v rs = rowsTime v rs + ((m + 1) + ((n + 1) +
      2 * ((inputWord n m rs).length + 1))) by unfold totalSteps; omega,
    Function.iterate_add_apply _ (rowsTime v rs),
    Function.iterate_add_apply _ (m + 1), Function.iterate_add_apply _ (n + 1),
    hcopy, hfirst, hsecond]
  exact hrows

open DFVSGames.Foundations.PCP

theorem cloudCountTrace (t : GraphTables.Table) (v : Fin t.vertices)
    (targetSuffix countSuffix : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program (σ := σ))))^[totalSteps t.vertices t.darts v.val (tableRows t)]
      (some ⟨some .copyFirst, ((ambient, false), register),
        memory (GraphTables.tableBits t) [] (encodeWord v.val ++ targetSuffix) []
          (encodeWord 0 ++ countSuffix) []⟩) =
      some ⟨none, ((ambient, false), none),
        memory (GraphTables.tableBits t) [] (encodeWord v.val ++ targetSuffix) []
          (encodeWord (PreprocessingCloudIndex.cloudSize t v) ++ countSuffix) []⟩ := by
  have h := countTrace t.vertices t.darts v.val (tableRows t) (tableRows_width t)
    targetSuffix (encodeWord 0 ++ countSuffix) ambient register
  rw [tableRows_input, tableRows_hits, ← List.append_assoc, replicate_encodeWord, Nat.add_zero] at h
  exact h

end DFVSGames.Foundations.Complexity.MachineCloudCount

namespace DFVSGames.Foundations.Complexity.MachineCeilingPower

open Turing
open MachineComposition
open DFVSGames.Foundations.PCP

variable {σ : Type}

theorem compareStep_zero (g p : Nat) (input saved level fuel spare product : List Bool)
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    TM2.step (program g)
      ⟨some .compare, ((ambient, flag), register),
        memory input (encodeWord 0) (encodeWord p) saved level fuel spare product⟩ =
      some ⟨some .restore, ((ambient, flag), none),
        memory input [] (encodeWord p) saved level fuel spare product⟩ := by
  change some (TM2.stepAux compareLoop _ _) = _
  simp [compareLoop, TM2.stepAux, memory, encodeWord]

theorem compareStep_succ_zero (g x : Nat) (input saved level fuel spare product : List Bool)
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    TM2.step (program g)
      ⟨some .compare, ((ambient, flag), register),
        memory input (encodeWord (x + 1)) (encodeWord 0) saved level fuel spare product⟩ =
      some ⟨some .compare, ((ambient, true), none),
        memory input (encodeWord x) (encodeWord 0) saved level fuel spare product⟩ := by
  change some (TM2.stepAux compareLoop _ _) = _
  simp [compareLoop, TM2.stepAux, memory, encodeWord, List.replicate_succ]

theorem compareStep_succ_succ (g x p : Nat) (input saved level fuel spare product : List Bool)
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    TM2.step (program g)
      ⟨some .compare, ((ambient, flag), register),
        memory input (encodeWord (x + 1)) (encodeWord (p + 1)) saved level fuel spare product⟩ =
      some ⟨some .compare, ((ambient, flag), none),
        memory input (encodeWord x) (encodeWord p) (true :: saved) level fuel spare product⟩ := by
  change some (TM2.stepAux compareLoop _ _) = _
  simp [compareLoop, TM2.stepAux, memory, encodeWord, List.replicate_succ]

theorem compareTrace (g x p : Nat) (input saved level fuel spare product : List Bool)
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    (advance (TM2.step (program g)))^[x + 1]
      (some ⟨some .compare, ((ambient, flag), register),
        memory input (encodeWord x) (encodeWord p) saved level fuel spare product⟩) =
      some ⟨some .restore, ((ambient, overflow flag x p), none),
        memory input [] (encodeWord (p - x))
          (List.replicate (min x p) true ++ saved) level fuel spare product⟩ := by
  induction x generalizing p saved flag register with
  | zero =>
      simpa [overflow] using compareStep_zero g p input saved level fuel spare product ambient flag register
  | succ x ih =>
      rw [Function.iterate_succ_apply]
      change (advance (TM2.step (program g)))^[x + 1]
        (TM2.step (program g) ⟨some .compare, ((ambient, flag), register),
          memory input (encodeWord (x + 1)) (encodeWord p) saved level fuel spare product⟩) = _
      cases p with
      | zero =>
          rw [compareStep_succ_zero]
          simpa [overflow] using ih 0 saved true none
      | succ p =>
          rw [compareStep_succ_succ]
          simpa [overflow, Nat.succ_min_succ, List.replicate_succ', List.append_assoc] using
            ih p (true :: saved) flag none

theorem compareRestoredTrace (g k p : Nat) (level fuel : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program g)))^[k + min k p + 2]
      (some ⟨some .compare, ((ambient, false), register),
        memory (encodeWord k) (encodeWord k) (encodeWord p) [] level fuel [] []⟩) =
      some ⟨some .decide, ((ambient, decide (p < k)), none),
        memory (encodeWord k) [] (encodeWord p) [] level fuel [] []⟩ := by
  have hc := compareTrace g k p (encodeWord k) [] level fuel [] [] ambient false register
  simp only [overflow, Bool.false_or, List.append_nil] at hc
  let mid := memory (encodeWord k) [] (encodeWord (p - k))
    (List.replicate (min k p) true) level fuel [] []
  have hr := Reduction.MachineTransfer.transferAt_fromTapes Tape.saved Tape.power (by decide)
    id false Label.restore (some Label.decide) (program g) rfl mid (ambient, decide (p < k)) none
  have hsum : min k p + (p - k) = p := by omega
  simp only [mid, memory, List.length_replicate, List.reverse_replicate, List.map_id,
    Reduction.MachineTransfer.tapesAt, update_saved, update_power] at hr
  rw [replicate_encodeWord, hsum] at hr
  rw [show k + min k p + 2 = (min k p + 1) + (k + 1) by omega,
    Function.iterate_add_apply, hc]
  exact hr

theorem scaleStep_succ (g p b : Nat) (input level fuel : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step (program g)
      ⟨some .scale, ((ambient, false), register),
        memory input [] (encodeWord (p + 1)) [] level fuel [] (List.replicate b true)⟩ =
      some ⟨some .scale, ((ambient, false), some true),
        memory input [] (encodeWord p) [] level fuel [] (List.replicate (g + b) true)⟩ := by
  change some (TM2.stepAux (scaleLoop g) _ _) = _
  simp [scaleLoop, TM2.stepAux, memory, encodeWord, List.replicate_succ,
    Reduction.MachineSubstitution.stepAux_pushWord]

theorem scaleStep_zero (g b : Nat) (input level fuel : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step (program g)
      ⟨some .scale, ((ambient, false), register),
        memory input [] (encodeWord 0) [] level fuel [] (List.replicate b true)⟩ =
      some ⟨some .transfer, ((ambient, false), none),
        memory input [] (encodeWord 0) [] (true :: level) fuel [] (List.replicate b true)⟩ := by
  change some (TM2.stepAux (scaleLoop g) _ _) = _
  simp [scaleLoop, TM2.stepAux, memory, encodeWord]

theorem scaleScanTrace (g p b : Nat) (input level fuel : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program g)))^[p + 1]
      (some ⟨some .scale, ((ambient, false), register),
        memory input [] (encodeWord p) [] level fuel [] (List.replicate b true)⟩) =
      some ⟨some .transfer, ((ambient, false), none),
        memory input [] (encodeWord 0) [] (true :: level) fuel [] (List.replicate (g * p + b) true)⟩ := by
  induction p generalizing b register with
  | zero => simpa using scaleStep_zero g b input level fuel ambient register
  | succ p ih =>
      rw [Function.iterate_succ_apply]
      change (advance (TM2.step (program g)))^[p + 1]
        (TM2.step (program g) ⟨some .scale, ((ambient, false), register),
          memory input [] (encodeWord (p + 1)) [] level fuel [] (List.replicate b true)⟩) = _
      rw [scaleStep_succ, ih]
      have h : g * p + (g + b) = g * (p + 1) + b := by rw [Nat.mul_succ]; omega
      rw [h]

theorem scaleTrace (g k p e : Nat) (fuel : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program g)))^[p + g * p + 2]
      (some ⟨some .scale, ((ambient, false), register),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) fuel [] []⟩) =
      some ⟨some .guard, ((ambient, false), none),
        memory (encodeWord k) [] (encodeWord (p * g)) [] (encodeWord (e + 1)) fuel [] []⟩ := by
  have hs := scaleScanTrace g p 0 (encodeWord k) (encodeWord e) fuel ambient register
  simp only [List.replicate_zero, Nat.add_zero] at hs
  let mid := memory (encodeWord k) [] (encodeWord 0) [] (true :: encodeWord e) fuel []
    (List.replicate (g * p) true)
  have ht := Reduction.MachineTransfer.transferAt_fromTapes Tape.product Tape.power (by decide)
    id false Label.transfer (some Label.guard) (program g) rfl mid (ambient, false) none
  simp only [mid, memory, List.length_replicate, List.reverse_replicate, List.map_id,
    Reduction.MachineTransfer.tapesAt, update_product, update_power,
    replicate_encodeWord, Nat.add_zero] at ht
  have he : true :: encodeWord e = encodeWord (e + 1) := by simp [encodeWord, List.replicate_succ]
  rw [he, Nat.mul_comm g p] at ht
  rw [he, Nat.mul_comm g p] at hs
  have h := appendTrace_inline_MachineCeilingPower (advance (TM2.step (program g))) hs ht
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.mul_comm] using h

theorem cleanupTrace (g k p e f : Nat) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program g)))^[f + 2]
      (some ⟨some .cleanup, ((ambient, false), register),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord f) [] []⟩) =
      some ⟨none, ((ambient, false), none),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) [] [] []⟩ := by
  have h := MachineDrain.drainTrace Tape.fuel Label.cleanup none (program g) rfl
    (memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) [] [] [])
    (encodeWord f) (ambient, false) register
  simpa only [encodeWord_length, update_fuel, Nat.add_assoc] using h

theorem guardStep_succ (g k p e f : Nat) (ambient : σ) (register : Option Bool) :
    TM2.step (program g)
      ⟨some .guard, ((ambient, false), register),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord (f + 1)) [] []⟩ =
      some ⟨some .copyFirst, ((ambient, false), none),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord f) [] []⟩ := by
  have h := MachineUnaryCounter.guardStep_succ Tape.fuel Label.guard Label.copyFirst Label.cleanup
    (program g) rfl (memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) [] [] [])
    f [] (ambient, false) register
  simpa only [MachineUnaryCounter.counterTapes, List.append_nil, update_fuel] using h

theorem guardStep_zero (g k p e : Nat) (ambient : σ) (register : Option Bool) :
    TM2.step (program g)
      ⟨some .guard, ((ambient, false), register),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord 0) [] []⟩ =
      some ⟨some .cleanup, ((ambient, false), none),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord 0) [] []⟩ := by
  have h := MachineUnaryCounter.guardStep_zero Tape.fuel Label.guard Label.copyFirst Label.cleanup
    (program g) rfl (memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) [] [] [])
    [] (ambient, false) register
  simpa only [MachineUnaryCounter.counterTapes, List.append_nil, update_fuel] using h

theorem decideStep (g k p e f : Nat) (ambient : σ) :
    TM2.step (program g)
      ⟨some .decide, ((ambient, decide (p < k)), none),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord f) [] []⟩ =
      some ⟨some (if k ≤ p then Label.cleanup else Label.scale), ((ambient, false), none),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord f) [] []⟩ := by
  by_cases h : k ≤ p
  · have hn : ¬p < k := by omega
    simp [TM2.step, program, TM2.stepAux, h, hn]
  · have hn : p < k := by omega
    simp [TM2.step, program, TM2.stepAux, h, hn]

theorem prefixTrace (g k p e f : Nat) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program g)))^[prefixTime k p]
      (some ⟨some .guard, ((ambient, false), register),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord (f + 1)) [] []⟩) =
      some ⟨some (if k ≤ p then Label.cleanup else Label.scale), ((ambient, false), none),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord f) [] []⟩ := by
  have hg : (advance (TM2.step (program g)))^[1]
      (some ⟨some .guard, ((ambient, false), register),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord (f + 1)) [] []⟩) =
      some ⟨some .copyFirst, ((ambient, false), none),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord f) [] []⟩ :=
    guardStep_succ g k p e f ambient register
  have hc := MachineCopy.copyTrace Tape.input Tape.work Tape.spare
    (by decide) (by decide) (by decide) false Label.copyFirst Label.copySecond
    (some Label.compare) (program g) rfl rfl
    (memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord f) [] [])
    rfl (ambient, false) none
  simp only [memory, encodeWord_length, List.append_nil, update_work] at hc
  have hcmp := compareRestoredTrace g k p (encodeWord e) (encodeWord f) ambient none
  have hd : (advance (TM2.step (program g)))^[1]
      (some ⟨some .decide, ((ambient, decide (p < k)), none),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord f) [] []⟩) =
      some ⟨some (if k ≤ p then Label.cleanup else Label.scale), ((ambient, false), none),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord f) [] []⟩ :=
    decideStep g k p e f ambient
  exact appendTrace_inline_MachineCeilingPower _ (appendTrace_inline_MachineCeilingPower _ (appendTrace_inline_MachineCeilingPower _ hg hc) hcmp) hd

theorem coreTrace (g k f e p : Nat) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program g)))^[coreTime g k f p]
      (some ⟨some .guard, ((ambient, false), register),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord f) [] []⟩) =
      some ⟨none, ((ambient, false), none),
        memory (encodeWord k) []
          (encodeWord (PreprocessingLevels.levelLoop g k f e p).2) []
          (encodeWord (PreprocessingLevels.levelLoop g k f e p).1) [] [] []⟩ := by
  induction f generalizing e p register with
  | zero =>
      have hg : (advance (TM2.step (program g)))^[1]
          (some ⟨some .guard, ((ambient, false), register),
            memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord 0) [] []⟩) =
          some ⟨some .cleanup, ((ambient, false), none),
            memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord 0) [] []⟩ :=
        guardStep_zero g k p e ambient register
      exact appendTrace_inline_MachineCeilingPower _ hg (cleanupTrace g k p e 0 ambient none)
  | succ f ih =>
      have hpref := prefixTrace g k p e f ambient register
      by_cases h : k ≤ p
      · simp only [h, ite_true, if_true] at hpref
        have hrun := appendTrace_inline_MachineCeilingPower _ hpref (cleanupTrace g k p e f ambient none)
        simpa only [coreTime, PreprocessingLevels.levelLoop, h, ite_true, if_true] using hrun
      · simp only [h, ite_false] at hpref
        have hscale := scaleTrace g k p e (encodeWord f) ambient none
        have hrun := appendTrace_inline_MachineCeilingPower _ hpref (appendTrace_inline_MachineCeilingPower _ hscale (ih (e + 1) (p * g) none))
        simpa only [coreTime, PreprocessingLevels.levelLoop, h, ite_false] using hrun

theorem initStep (g k : Nat) (ambient : σ) (register : Option Bool) :
    TM2.step (program g)
      ⟨some .init, ((ambient, false), register), memory (encodeWord k) [] [] [] [] [] [] []⟩ =
      some ⟨some .fuelFirst, ((ambient, false), register),
        memory (encodeWord k) [] (encodeWord 1) [] (encodeWord 0) [] [] []⟩ := by
  change some (TM2.stepAux (program g .init) _ _) = _
  simp [program, TM2.stepAux, memory, encodeWord]

theorem searchTrace (g k : Nat) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program g)))^[totalTime g k]
      (some ⟨some .init, ((ambient, false), register), memory (encodeWord k) [] [] [] [] [] [] []⟩) =
      some ⟨none, ((ambient, false), none),
        memory (encodeWord k) []
          (encodeWord (PreprocessingLevels.levelLoop g k k 0 1).2) []
          (encodeWord (PreprocessingLevels.levelLoop g k k 0 1).1) [] [] []⟩ := by
  have hi : (advance (TM2.step (program g)))^[1]
      (some ⟨some .init, ((ambient, false), register), memory (encodeWord k) [] [] [] [] [] [] []⟩) =
      some ⟨some .fuelFirst, ((ambient, false), register),
        memory (encodeWord k) [] (encodeWord 1) [] (encodeWord 0) [] [] []⟩ :=
    initStep g k ambient register
  have hc := MachineCopy.copyTrace Tape.input Tape.fuel Tape.spare
    (by decide) (by decide) (by decide) false Label.fuelFirst Label.fuelSecond
    (some Label.guard) (program g) rfl rfl
    (memory (encodeWord k) [] (encodeWord 1) [] (encodeWord 0) [] [] [])
    rfl (ambient, false) register
  simp only [memory, encodeWord_length, List.append_nil, update_fuel] at hc
  exact appendTrace_inline_MachineCeilingPower _ (appendTrace_inline_MachineCeilingPower _ hi hc) (coreTrace g k k 0 1 ambient none)

theorem paddingTrace (k : Nat) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program ExpanderFamily.growth)))^[totalTime ExpanderFamily.growth k]
      (some ⟨some .init, ((ambient, false), register), memory (encodeWord k) [] [] [] [] [] [] []⟩) =
      some ⟨none, ((ambient, false), none),
        memory (encodeWord k) [] (encodeWord (PreprocessingLevels.paddedSize k)) []
          (encodeWord (PreprocessingLevels.boundedLevel k)) [] [] []⟩ := by
  exact searchTrace ExpanderFamily.growth k ambient register

def paddingInTime (k : Nat) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step (program ExpanderFamily.growth))
      ⟨some .init, ((ambient, false), register), memory (encodeWord k) [] [] [] [] [] [] []⟩
      (some ⟨none, ((ambient, false), none),
        memory (encodeWord k) [] (encodeWord (PreprocessingLevels.paddedSize k)) []
          (encodeWord (PreprocessingLevels.boundedLevel k)) [] [] []⟩)
      ((timePolynomial ExpanderFamily.growth).eval (encodeWord k).length) where
  steps := totalTime ExpanderFamily.growth k
  evals_in_steps := paddingTrace k ambient register
  steps_le_m := by rw [timePolynomial_encoding]; exact totalTime_le _ _

theorem paddingOutput_bounds (k : Nat) :
    PreprocessingLevels.boundedLevel k ≤ k ∧
      k ≤ PreprocessingLevels.paddedSize k ∧
      PreprocessingLevels.paddedSize k ≤ ExpanderFamily.growth * (k + 1) := by
  refine ⟨PreprocessingLevels.boundedLevel_le_input k, PreprocessingLevels.le_paddedSize k, ?_⟩
  by_cases hk : k = 0
  · subst k
    simpa using ExpanderFamily.growth_gt_one.le
  · exact (PreprocessingLevels.paddedSize_bounds (Nat.pos_of_ne_zero hk)).2.trans
      (Nat.mul_le_mul_left ExpanderFamily.growth (Nat.le_succ k))

end DFVSGames.Foundations.Complexity.MachineCeilingPower

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineCloudPadding
attribute [-instance] _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Foundations.Complexity.MachineCloudPadding

open Turing
open MachineComposition
open DFVSGames.Foundations.PCP

variable {σ : Type}

def program : Label → TM2.Stmt Alphabet Label (State σ)
  | .init => .push .count (fun _ => false) (.goto fun _ => .countCode .copyFirst)
  | .countCode l => Placement.statement countTape Label.countCode (some .branch)
      (MachineCloudCount.program l)
  | .branch => .peek .count (fun state head => (state.1, head))
      (.branch (fun state => state.2.getD false)
        (.load (fun state => (state.1, none)) (.goto fun _ => .powerCode .init))
        (.push .power (fun _ => false) (.push .level (fun _ => false)
          (.load (fun state => (state.1, none)) .halt))))
  | .powerCode l => Placement.statement powerTape Label.powerCode (some .subtract)
      (MachineCeilingPower.program ExpanderFamily.growth l)
  | .subtract => subtractLoop
  | .restore => Reduction.MachineTransfer.loopAt
      .scratch .count id false .restore none

theorem countTrace (t : GraphTables.Table) (v : Fin t.vertices)
    (suffix : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[MachineCloudCount.totalSteps t.vertices t.darts v.val
      (MachineCloudCount.tableRows t)]
      (some ⟨some (.countCode .copyFirst), ((ambient, false), register),
        memory (GraphTables.tableBits t) (encodeWord v.val ++ suffix)
          (encodeWord 0) [] [] [] [] [] [] []⟩) =
      some ⟨some .branch, ((ambient, false), none),
        memory (GraphTables.tableBits t) (encodeWord v.val ++ suffix)
          (encodeWord (PreprocessingCloudIndex.cloudSize t v)) [] [] [] [] [] [] []⟩ := by
  have h := Placement.trace countTape countView countView_left countView_right
    Label.countCode (some Label.branch) (fun _ => [])
    (MachineCloudCount.program (σ := σ)) program (fun _ => rfl) _ _ _
    (MachineCloudCount.cloudCountTrace t v suffix [] ambient register)
  simpa only [Placement.configuration, Placement.label, countTapes, List.append_nil] using h

theorem powerTrace (table query : List Bool) (k : Nat) (ambient : σ)
    (register : Option Bool) :
    (advance (TM2.step program))^[MachineCeilingPower.totalTime ExpanderFamily.growth k]
      (some ⟨some (.powerCode .init), ((ambient, false), register),
        memory table query (encodeWord k) [] [] [] [] [] [] []⟩) =
      some ⟨some .subtract, ((ambient, false), none),
        memory table query (encodeWord k) [] [] []
          (encodeWord (PreprocessingLevels.paddedSize k))
          (encodeWord (PreprocessingLevels.boundedLevel k)) [] []⟩ := by
  have h := Placement.trace powerTape powerView powerView_left powerView_right
    Label.powerCode (some Label.subtract) (memory table query [] [] [] [] [] [] [] [])
    (MachineCeilingPower.program ExpanderFamily.growth (σ := σ)) program (fun _ => rfl)
    _ _ _ (MachineCeilingPower.paddingTrace k ambient register)
  simpa only [Placement.configuration, Placement.label, powerTapes, memory] using h

theorem subtractStep_zero (table query level saved : List Bool) (p : Nat)
    (ambient : σ) (register : Option Bool) :
    TM2.step program
      ⟨some .subtract, ((ambient, false), register),
        memory table query (encodeWord 0) [] saved [] (encodeWord p) level [] []⟩ =
      some ⟨some .restore, ((ambient, false), none),
        memory table query (encodeWord 0) [] saved [] (encodeWord p) level [] []⟩ := by
  change some (TM2.stepAux subtractLoop _ _) = _
  simp [subtractLoop, TM2.stepAux, memory, encodeWord]

theorem subtractStep_succ (table query level saved : List Bool) (k p : Nat)
    (ambient : σ) (register : Option Bool) :
    TM2.step program
      ⟨some .subtract, ((ambient, false), register),
        memory table query (encodeWord (k + 1)) [] saved [] (encodeWord (p + 1)) level [] []⟩ =
      some ⟨some .subtract, ((ambient, false), none),
        memory table query (encodeWord k) [] (true :: saved) [] (encodeWord p) level [] []⟩ := by
  change some (TM2.stepAux subtractLoop _ _) = _
  simp [subtractLoop, TM2.stepAux, memory, encodeWord, List.replicate_succ]

theorem subtractScanTrace (table query level : List Bool) (k p : Nat)
    (saved : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[k + 1]
      (some ⟨some .subtract, ((ambient, false), register),
        memory table query (encodeWord k) [] saved [] (encodeWord (k + p)) level [] []⟩) =
      some ⟨some .restore, ((ambient, false), none),
        memory table query (encodeWord 0) [] (List.replicate k true ++ saved) []
          (encodeWord p) level [] []⟩ := by
  induction k generalizing saved register with
  | zero => simpa only [Nat.zero_add, Function.iterate_one, advance_some,
      List.replicate_zero, List.nil_append] using
      subtractStep_zero table query level saved p ambient register
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    simp only [Nat.succ_add]
    change (advance (TM2.step program))^[k + 1]
      (TM2.step program ⟨some .subtract, ((ambient, false), register),
        memory table query (encodeWord (k + 1)) [] saved []
          (encodeWord ((k + p) + 1)) level [] []⟩) = _
    rw [subtractStep_succ]
    simpa only [List.replicate_succ', List.append_assoc, List.singleton_append] using
      ih (true :: saved) none

theorem subtractTrace (table query level : List Bool) (k p : Nat) (hkp : k ≤ p)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[2 * k + 2]
      (some ⟨some .subtract, ((ambient, false), register),
        memory table query (encodeWord k) [] [] [] (encodeWord p) level [] []⟩) =
      some ⟨none, ((ambient, false), none),
        memory table query (encodeWord k) [] [] [] (encodeWord (p - k)) level [] []⟩ := by
  have hs := subtractScanTrace table query level k (p - k) [] ambient register
  rw [show k + (p - k) = p by omega] at hs
  simp only [List.append_nil] at hs
  let mid := memory table query (encodeWord 0) [] (List.replicate k true) []
    (encodeWord (p - k)) level [] []
  have hr := Reduction.MachineTransfer.transferAt_fromTapes Tape.scratch Tape.count (by decide)
    id false Label.restore none program rfl mid (ambient, false) none
  simp only [mid, memory, List.length_replicate, List.reverse_replicate, List.map_id,
    Reduction.MachineTransfer.tapesAt, update_scratch, update_count] at hr
  rw [MachineCeilingPower.replicate_encodeWord, Nat.add_zero] at hr
  have h := appendTrace_inline_MachineCloudPadding _ hs hr
  simpa only [show (k + 1) + (k + 1) = 2 * k + 2 by omega, Nat.add_zero] using h

theorem branchStep_zero (table query : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.step program
      ⟨some .branch, ((ambient, false), register),
        memory table query (encodeWord 0) [] [] [] [] [] [] []⟩ =
      some ⟨none, ((ambient, false), none),
        memory table query (encodeWord 0) [] [] [] (encodeWord 0) (encodeWord 0) [] []⟩ := by
  simp [TM2.step, program, TM2.stepAux, memory, encodeWord]

theorem branchStep_succ (table query : List Bool) (k : Nat) (ambient : σ)
    (register : Option Bool) :
    TM2.step program
      ⟨some .branch, ((ambient, false), register),
        memory table query (encodeWord (k + 1)) [] [] [] [] [] [] []⟩ =
      some ⟨some (.powerCode .init), ((ambient, false), none),
        memory table query (encodeWord (k + 1)) [] [] [] [] [] [] []⟩ := by
  simp [TM2.step, program, TM2.stepAux, memory, encodeWord, List.replicate_succ]

def padding (k : Nat) : Nat := PreprocessingLevels.cloudPaddedSize k - k

theorem postTrace (table query : List Bool) (k : Nat) (ambient : σ)
    (register : Option Bool) :
    (advance (TM2.step program))^[postTime k]
      (some ⟨some .branch, ((ambient, false), register),
        memory table query (encodeWord k) [] [] [] [] [] [] []⟩) =
      some ⟨none, ((ambient, false), none),
        memory table query (encodeWord k) [] [] [] (encodeWord (padding k))
          (encodeWord (PreprocessingLevels.boundedLevel k)) [] []⟩ := by
  cases k with
  | zero =>
    simpa only [postTime, ite_eq_left rfl, ite_true, if_true, Nat.add_zero, Function.iterate_one, advance_some,
      padding, PreprocessingLevels.cloudPaddedSize_zero, Nat.sub_zero,
      PreprocessingLevels.boundedLevel_zero] using branchStep_zero table query ambient register
  | succ k =>
    have hb : (advance (TM2.step program))^[1]
        (some ⟨some .branch, ((ambient, false), register),
          memory table query (encodeWord (k + 1)) [] [] [] [] [] [] []⟩) =
        some ⟨some (.powerCode .init), ((ambient, false), none),
          memory table query (encodeWord (k + 1)) [] [] [] [] [] [] []⟩ :=
      branchStep_succ table query k ambient register
    have hp := powerTrace table query (k + 1) ambient none
    have hs := subtractTrace table query (encodeWord (PreprocessingLevels.boundedLevel (k + 1)))
      (k + 1) (PreprocessingLevels.paddedSize (k + 1))
      (PreprocessingLevels.le_paddedSize (k + 1)) ambient none
    have h := appendTrace_inline_MachineCloudPadding _ hb (appendTrace_inline_MachineCloudPadding _ hp hs)
    simpa only [postTime, Nat.succ_ne_zero, ite_false, padding,
      PreprocessingLevels.cloudPaddedSize_of_pos (Nat.succ_pos k)] using h

theorem initStep (table query : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.step program
      ⟨some .init, ((ambient, false), register), memory table query [] [] [] [] [] [] [] []⟩ =
      some ⟨some (.countCode .copyFirst), ((ambient, false), register),
        memory table query (encodeWord 0) [] [] [] [] [] [] []⟩ := by
  simp [TM2.step, program, TM2.stepAux, memory, encodeWord]

theorem cloudPaddingTrace (t : GraphTables.Table) (v : Fin t.vertices)
    (suffix : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[totalTime t v]
      (some ⟨some .init, ((ambient, false), register),
        memory (GraphTables.tableBits t) (encodeWord v.val ++ suffix) [] [] [] [] [] [] [] []⟩) =
      some ⟨none, ((ambient, false), none),
        memory (GraphTables.tableBits t) (encodeWord v.val ++ suffix)
          (encodeWord (PreprocessingCloudIndex.cloudSize t v)) [] [] []
          (encodeWord (padding (PreprocessingCloudIndex.cloudSize t v)))
          (encodeWord (PreprocessingLevels.boundedLevel (PreprocessingCloudIndex.cloudSize t v)))
          [] []⟩ := by
  have hi : (advance (TM2.step program))^[1]
      (some ⟨some .init, ((ambient, false), register),
        memory (GraphTables.tableBits t) (encodeWord v.val ++ suffix) [] [] [] [] [] [] [] []⟩) =
      some ⟨some (.countCode .copyFirst), ((ambient, false), register),
        memory (GraphTables.tableBits t) (encodeWord v.val ++ suffix)
          (encodeWord 0) [] [] [] [] [] [] []⟩ :=
    initStep _ _ ambient register
  exact appendTrace_inline_MachineCloudPadding _ (appendTrace_inline_MachineCloudPadding _ hi (countTrace t v suffix ambient register))
    (postTrace _ _ (PreprocessingCloudIndex.cloudSize t v) ambient none)

end DFVSGames.Foundations.Complexity.MachineCloudPadding

namespace DFVSGames.Foundations.Complexity.MachineCloudPrefix

open Turing MachineComposition
open DFVSGames.Foundations.PCP
open scoped BigOperators

variable {σ : Type}

def program : Label → TM2.Stmt Alphabet Label (State σ)
  | .init => .push (.inner .query) (fun _ => false)
      (.push .total (fun _ => false) (.goto fun _ => .copyFirst))
  | .copyFirst => Reduction.MachineTransfer.loopAt
      .bound (.inner .scratch) id false .copyFirst (some .copySecond)
  | .copySecond => MachineCopy.forkLoop
      (.inner .scratch) .bound .remaining false .copySecond (some .guard)
  | .guard => MachineUnaryCounter.guard .remaining (.padding .init) .done
  | .done => .halt
  | .padding l => MachineCloudPadding.Placement.statement Tape.inner Label.padding (some .add) (MachineCloudPadding.program l)
  | .add => MachineUnaryAddAt.loop (.inner .power) .total .add (some .clearCount)
  | .clearCount => MachineLookup.discard (.inner .count) .clearCount .clearLevel
  | .clearLevel => MachineLookup.discard (.inner .level) .clearLevel .increment
  | .increment => .pop (.inner .power) (fun state _ => (state.1, none))
      (.push (.inner .query) (fun _ => true) (.goto fun _ => .guard))

theorem paddingTrace (t : GraphTables.Table) (v : Fin t.vertices)
    (bound remaining total : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[MachineCloudPadding.totalTime t v]
      (some ⟨some (.padding .init), ((ambient, false), register),
        frame (GraphTables.tableBits t) (encodeWord v.val) [] [] [] bound remaining total⟩) =
      some ⟨some .add, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord v.val)
          (encodeWord (PreprocessingCloudIndex.cloudSize t v))
          (encodeWord (MachineCloudPadding.padding (PreprocessingCloudIndex.cloudSize t v)))
          (encodeWord (PreprocessingLevels.boundedLevel (PreprocessingCloudIndex.cloudSize t v)))
          bound remaining total⟩ := by
  have h := MachineCloudPadding.Placement.trace Tape.inner paddingView paddingView_left paddingView_right
    Label.padding (some Label.add) (frame [] [] [] [] [] bound remaining total)
    (MachineCloudPadding.program (σ := σ)) program (fun _ => rfl) _ _ _
    (MachineCloudPadding.cloudPaddingTrace t v [] ambient register)
  simpa only [MachineCloudPadding.Placement.configuration, MachineCloudPadding.Placement.label, placedTapes,
    frame_bound, frame_remaining, frame_total, List.append_nil, frame, memory] using h

theorem incrementStep (table bound remaining total : List Bool) (v : Nat)
    (ambient : σ) (register : Option Bool) :
    TM2.step (program (σ := σ))
      ⟨some .increment, ((ambient, false), register),
        frame table (encodeWord v) [] (encodeWord 0) [] bound remaining total⟩ =
      some ⟨some .guard, ((ambient, false), none),
        frame table (encodeWord (v + 1)) [] [] [] bound remaining total⟩ := by
  simp [TM2.step, program, TM2.stepAux, encodeWord, List.replicate_succ]

def bodyTime (t : GraphTables.Table) (v : Fin t.vertices) : Nat :=
  MachineCloudPadding.totalTime t v + (MachineCloudPadding.padding (PreprocessingCloudIndex.cloudSize t v) + 1) +
    (PreprocessingCloudIndex.cloudSize t v + 1) +
      (PreprocessingLevels.boundedLevel (PreprocessingCloudIndex.cloudSize t v) + 1) + 1

theorem bodyTrace (t : GraphTables.Table) (v : Fin t.vertices)
    (bound remaining : List Bool) (acc : Nat) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[bodyTime t v]
      (some ⟨some (.padding .init), ((ambient, false), register),
        frame (GraphTables.tableBits t) (encodeWord v.val) [] [] []
          bound remaining (encodeWord acc)⟩) =
      some ⟨some .guard, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord (v.val + 1)) [] [] []
          bound remaining (encodeWord (MachineCloudPadding.padding (PreprocessingCloudIndex.cloudSize t v) + acc))⟩ := by
  let k := PreprocessingCloudIndex.cloudSize t v
  let p := MachineCloudPadding.padding k
  let l := PreprocessingLevels.boundedLevel k
  have hp := paddingTrace t v bound remaining (encodeWord acc) ambient register
  have ha := MachineUnaryAddAt.addFromTapes (Tape.inner .power) Tape.total (by decide)
    Label.add (some Label.clearCount) program rfl
    (frame (GraphTables.tableBits t) (encodeWord v.val) (encodeWord k)
      (encodeWord p) (encodeWord l) bound remaining (encodeWord acc))
    p acc [] [] (by simp) (by simp) (ambient, false) none
  simp only [MachineUnaryAddAt.unaryTapes, Reduction.MachineTransfer.tapesAt,
    List.append_nil, update_frame_power, update_frame_total] at ha
  have hc := MachineLookup.discardTrace (Tape.inner .count) Label.clearCount Label.clearLevel
    program rfl
    (frame (GraphTables.tableBits t) (encodeWord v.val) (encodeWord k)
      (encodeWord 0) (encodeWord l) bound remaining (encodeWord (p + acc)))
    k [] (by simp) (ambient, false) none
  simp only [update_frame_count] at hc
  have hl := MachineLookup.discardTrace (Tape.inner .level) Label.clearLevel Label.increment
    program rfl
    (frame (GraphTables.tableBits t) (encodeWord v.val) []
      (encodeWord 0) (encodeWord l) bound remaining (encodeWord (p + acc)))
    l [] (by simp) (ambient, false) none
  simp only [update_frame_level] at hl
  have hi : (advance (TM2.step program))^[1]
      (some ⟨some .increment, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord v.val) [] (encodeWord 0) []
          bound remaining (encodeWord (p + acc))⟩) =
      some ⟨some .guard, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord (v.val + 1)) [] [] []
          bound remaining (encodeWord (p + acc))⟩ :=
    incrementStep _ _ _ _ _ ambient none
  exact appendTrace_inline_MachineCloudPrefix _ (appendTrace_inline_MachineCloudPrefix _ (appendTrace_inline_MachineCloudPrefix _ (appendTrace_inline_MachineCloudPrefix _ hp ha) hc) hl) hi

theorem guardStep_succ (table bound suffix total : List Bool) (v n : Nat)
    (ambient : σ) (register : Option Bool) :
    TM2.step (program (σ := σ))
      ⟨some .guard, ((ambient, false), register),
        frame table (encodeWord v) [] [] [] bound (encodeWord (n + 1) ++ suffix) total⟩ =
      some ⟨some (.padding .init), ((ambient, false), none),
        frame table (encodeWord v) [] [] [] bound (encodeWord n ++ suffix) total⟩ := by
  simp [TM2.step, program, MachineUnaryCounter.guard, TM2.stepAux, encodeWord,
    List.replicate_succ]

theorem guardStep_zero (table bound suffix total : List Bool) (v : Nat)
    (ambient : σ) (register : Option Bool) :
    TM2.step (program (σ := σ))
      ⟨some .guard, ((ambient, false), register),
        frame table (encodeWord v) [] [] [] bound (encodeWord 0 ++ suffix) total⟩ =
      some ⟨some .done, ((ambient, false), none),
        frame table (encodeWord v) [] [] [] bound (encodeWord 0 ++ suffix) total⟩ := rfl

theorem zeroTrace (table bound suffix total : List Bool) (v : Nat)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program (σ := σ))))^[2]
      (some ⟨some .guard, ((ambient, false), register),
        frame table (encodeWord v) [] [] [] bound (encodeWord 0 ++ suffix) total⟩) =
      some ⟨none, ((ambient, false), none),
        frame table (encodeWord v) [] [] [] bound (encodeWord 0 ++ suffix) total⟩ := by
  rw [Function.iterate_succ_apply]
  change advance (TM2.step (program (σ := σ)))
    (TM2.step program ⟨some .guard, ((ambient, false), register),
      frame table (encodeWord v) [] [] [] bound (encodeWord 0 ++ suffix) total⟩) = _
  rw [guardStep_zero]
  rfl

def amount (t : GraphTables.Table) (v : Nat) : Nat :=
  if h : v < t.vertices then MachineCloudPadding.padding (PreprocessingCloudIndex.cloudSize t ⟨v, h⟩) else 0

def cycleTime (t : GraphTables.Table) (v : Nat) : Nat :=
  if h : v < t.vertices then 1 + bodyTime t ⟨v, h⟩ else 0

def sumFrom (t : GraphTables.Table) (v : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => amount t v + sumFrom t (v + 1) n

def loopTime (t : GraphTables.Table) (v : Nat) : Nat → Nat
  | 0 => 2
  | n + 1 => cycleTime t v + loopTime t (v + 1) n

theorem loopTrace (t : GraphTables.Table) (n v : Nat) (hvn : v + n ≤ t.vertices)
    (bound suffix : List Bool) (acc : Nat) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[loopTime t v n]
      (some ⟨some .guard, ((ambient, false), register),
        frame (GraphTables.tableBits t) (encodeWord v) [] [] []
          bound (encodeWord n ++ suffix) (encodeWord acc)⟩) =
      some ⟨none, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord (v + n)) [] [] []
          bound (encodeWord 0 ++ suffix) (encodeWord (sumFrom t v n + acc))⟩ := by
  induction n generalizing v acc register with
  | zero =>
      simpa only [loopTime, sumFrom, Nat.add_zero, Nat.zero_add] using
        zeroTrace _ bound suffix (encodeWord acc) v ambient register
  | succ n ih =>
      have hv : v < t.vertices := by omega
      have hnext : v + 1 + n ≤ t.vertices := by omega
      have hg : (advance (TM2.step program))^[1]
          (some ⟨some .guard, ((ambient, false), register),
            frame (GraphTables.tableBits t) (encodeWord v) [] [] []
              bound (encodeWord (n + 1) ++ suffix) (encodeWord acc)⟩) =
          some ⟨some (.padding .init), ((ambient, false), none),
            frame (GraphTables.tableBits t) (encodeWord v) [] [] []
              bound (encodeWord n ++ suffix) (encodeWord acc)⟩ :=
        guardStep_succ _ bound suffix (encodeWord acc) v n ambient register
      have hb := bodyTrace t ⟨v, hv⟩ bound (encodeWord n ++ suffix) acc ambient none
      have ht := ih (v + 1) hnext
        (MachineCloudPadding.padding (PreprocessingCloudIndex.cloudSize t ⟨v, hv⟩) + acc) none
      have hall := appendTrace_inline_MachineCloudPrefix _ (appendTrace_inline_MachineCloudPrefix _ hg hb) ht
      simpa only [loopTime, cycleTime, dite_eq_left hv, sumFrom, amount,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

theorem sumFrom_list (t : GraphTables.Table) (xs : List (Fin t.vertices)) (v : Nat)
    (hseq : ∀ i (hi : i < xs.length), (xs[i]).val = v + i) :
    sumFrom t v xs.length = (xs.map (PreprocessingRegularTables.padding t)).sum := by
  induction xs generalizing v with
  | nil => simp [sumFrom]
  | cons x xs ih =>
      have hx : x.val = v := by
        have hhead := hseq 0 (by simp)
        simp only [List.getElem_cons_zero, Nat.add_zero] at hhead
        exact hhead
      have hv : v < t.vertices := by simpa only [hx] using x.isLt
      have he : (⟨v, hv⟩ : Fin t.vertices) = x := Fin.ext hx.symm
      have hnext : ∀ i (hi : i < xs.length), (xs[i]).val = v + 1 + i := by
        intro i hi
        have h := hseq (i + 1) (by simpa using Nat.succ_lt_succ hi)
        simpa only [List.getElem_cons_succ, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using h
      simp only [List.length_cons, sumFrom, amount, dite_eq_left hv, he,
        List.map_cons, List.sum_cons]
      rw [ih (v + 1) hnext]
      rfl

theorem sumFrom_eq_offset (t : GraphTables.Table) (b : Nat) (hb : b ≤ t.vertices) :
    sumFrom t 0 b =
      PreprocessingPaddingOffsets.offset (PreprocessingRegularTables.padding t) b := by
  have h := sumFrom_list t ((List.finRange t.vertices).take b) 0
    (by intro i hi; simp only [List.getElem_take, List.getElem_finRange, Fin.val_cast,
      Nat.zero_add])
  simpa only [List.length_take, List.length_finRange, Nat.min_eq_left hb,
    PreprocessingPaddingOffsets.offset] using h

theorem initStep (table bound : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.step (program (σ := σ))
      ⟨some .init, ((ambient, false), register), frame table [] [] [] [] bound [] []⟩ =
      some ⟨some .copyFirst, ((ambient, false), register),
        frame table (encodeWord 0) [] [] [] bound [] (encodeWord 0)⟩ := by
  simp [TM2.step, program, TM2.stepAux, encodeWord]

def totalTime (t : GraphTables.Table) (b : Nat) (suffix : List Bool) : Nat :=
  (1 + 2 * ((encodeWord b ++ suffix).length + 1)) + loopTime t 0 b

theorem prefixTrace (t : GraphTables.Table) (b : Nat) (hb : b ≤ t.vertices)
    (suffix : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[totalTime t b suffix]
      (some ⟨some .init, ((ambient, false), register),
        frame (GraphTables.tableBits t) [] [] [] [] (encodeWord b ++ suffix) [] []⟩) =
      some ⟨none, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord b) [] [] []
          (encodeWord b ++ suffix) (encodeWord 0 ++ suffix)
          (encodeWord (PreprocessingPaddingOffsets.offset
            (PreprocessingRegularTables.padding t) b))⟩ := by
  have hi : (advance (TM2.step program))^[1]
      (some ⟨some .init, ((ambient, false), register),
        frame (GraphTables.tableBits t) [] [] [] [] (encodeWord b ++ suffix) [] []⟩) =
      some ⟨some .copyFirst, ((ambient, false), register),
        frame (GraphTables.tableBits t) (encodeWord 0) [] [] []
          (encodeWord b ++ suffix) [] (encodeWord 0)⟩ :=
    initStep _ _ ambient register
  have hc := MachineCopy.copyTrace Tape.bound Tape.remaining (Tape.inner .scratch)
    (by decide) (by decide) (by decide) false Label.copyFirst Label.copySecond
    (some Label.guard) program rfl rfl
    (frame (GraphTables.tableBits t) (encodeWord 0) [] [] []
      (encodeWord b ++ suffix) [] (encodeWord 0)) rfl (ambient, false) register
  simp only [frame_bound, frame_remaining, List.append_nil, update_frame_remaining] at hc
  have hl := loopTrace t b 0 (by simpa only [Nat.zero_add] using hb)
    (encodeWord b ++ suffix) suffix 0 ambient none
  simp only [Nat.zero_add, Nat.add_zero, sumFrom_eq_offset t b hb] at hl
  exact appendTrace_inline_MachineCloudPrefix _ (appendTrace_inline_MachineCloudPrefix _ hi hc) hl

theorem bodyTime_le (t : GraphTables.Table) (v : Fin t.vertices) (L : Nat)
    (hL : (GraphTables.tableBits t).length ≤ L) :
    1 + bodyTime t v ≤ cycleBudget L := by
  have hn := GraphTables.vertices_le_tableBits_length t
  have hv := v.isLt
  have hinput : MachineCloudPadding.inputLength t v [] ≤ 2 * L := by
    simp only [MachineCloudPadding.inputLength, List.append_nil, encodeWord_length]
    omega
  have hp := (MachineCloudPadding.totalTime_le t v []).trans
    (natPolynomial_eval_mono MachineCloudPadding.timePolynomial hinput)
  simp only [MachineCloudPadding.timePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat] at hp
  have hk : PreprocessingCloudIndex.cloudSize t v ≤ L :=
    (PreprocessingCloudIndex.cloudSize_le_darts t v).trans
      ((GraphTables.darts_le_tableBits_length t).trans hL)
  have hl := (PreprocessingLevels.boundedLevel_le_input
    (PreprocessingCloudIndex.cloudSize t v)).trans hk
  have hpad : MachineCloudPadding.padding (PreprocessingCloudIndex.cloudSize t v) ≤
      ExpanderFamily.growth * L := by
    have hsize := (PreprocessingLevels.cloudPaddedSize_bounds
      (PreprocessingCloudIndex.cloudSize t v)).2
    have hmul := Nat.mul_le_mul_left ExpanderFamily.growth hk
    unfold MachineCloudPadding.padding
    omega
  unfold bodyTime cycleBudget
  simp only [Nat.add_mul] at hp ⊢
  omega

theorem loopTime_le (t : GraphTables.Table) (n v : Nat) (hvn : v + n ≤ t.vertices)
    (L : Nat) (hL : (GraphTables.tableBits t).length ≤ L) :
    loopTime t v n ≤ n * cycleBudget L + 2 := by
  induction n generalizing v with
  | zero => simp only [loopTime, Nat.zero_mul, Nat.zero_add, le_refl]
  | succ n ih =>
      have hv : v < t.vertices := by omega
      have hnext : v + 1 + n ≤ t.vertices := by omega
      have hbody := bodyTime_le t ⟨v, hv⟩ L hL
      have htail := ih (v + 1) hnext
      simp only [loopTime, cycleTime, dite_eq_left hv, Nat.succ_mul]
      omega

theorem totalTime_le (t : GraphTables.Table) (b : Nat) (hb : b ≤ t.vertices)
    (suffix : List Bool) :
    totalTime t b suffix ≤ timePolynomial.eval (inputLength t b suffix) := by
  let L := inputLength t b suffix
  have htable : (GraphTables.tableBits t).length ≤ L := by
    unfold L inputLength
    omega
  have hbound : (encodeWord b ++ suffix).length ≤ L := by
    unfold L inputLength
    omega
  have hbL : b ≤ L := hb.trans ((GraphTables.vertices_le_tableBits_length t).trans htable)
  have hloop := loopTime_le t b 0 (by simpa only [Nat.zero_add] using hb) L htable
  have hmul := Nat.mul_le_mul_right (cycleBudget L) hbL
  have htotal : totalTime t b suffix ≤ L * cycleBudget L + 2 * (L + 1) + 3 := by
    unfold totalTime
    omega
  simpa only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat,
    Polynomial.eval_one, cycleBudget, L] using htotal

end DFVSGames.Foundations.Complexity.MachineCloudPrefix

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_Preprocessing
attribute [-instance] _root_.OAI.DFVSGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.DFVSGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DFVSGames.Quadratic.blockOrientationFintype _root_.OAI.DFVSGames.Quadratic.fieldLineFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Foundations.PCP.PreprocessingTables

open PreprocessingRegularTables

def regularVertices (t : GraphTables.Table) : Nat := vertexCount t (padding t)
def vertices (t : GraphTables.Table) : Nat := PreprocessingLevels.paddedSize (regularVertices t)

def padded (H : BaseTable) (t : GraphTables.Table) :
    PortTables.Table (vertices t) (internalDegree + 1) :=
  PreprocessingPaddingTables.pad (regularize H t)
    (PreprocessingLevels.le_paddedSize (regularVertices t))

def overlayFamily (H : BaseTable) (t : GraphTables.Table) :
    ExpanderTables.Table (vertices t) internalDegree :=
  resizeTable (PreprocessingLevels.table_vertexCount_eq_paddedSize (regularVertices t))
    (ExpanderTables.family H (PreprocessingLevels.boundedLevel (regularVertices t)))

def preprocess (H : BaseTable) (t : GraphTables.Table) :
    PortTables.Table (vertices t) degree :=
  PreprocessingOverlayTables.lazy
    (PreprocessingOverlayTables.overlay (padded H t) (overlayFamily H t))

theorem regularVertices_ge_darts (t : GraphTables.Table) : t.darts ≤ regularVertices t := by
  change t.darts ≤ t.darts + _
  omega

theorem regularVertices_le (t : GraphTables.Table) :
    regularVertices t ≤ ExpanderFamily.growth * t.darts := vertexCount_le t

theorem vertices_positive (t : GraphTables.Table) : 0 < vertices t :=
  PreprocessingLevels.paddedSize_positive _

theorem vertices_le_of_positive (t : GraphTables.Table) (ht : 0 < t.darts) :
    vertices t ≤ ExpanderFamily.growth ^ 2 * t.darts := by
  have hr : 0 < regularVertices t := ht.trans_le (regularVertices_ge_darts t)
  calc
    _ ≤ ExpanderFamily.growth * regularVertices t :=
      (PreprocessingLevels.paddedSize_bounds hr).2
    _ ≤ ExpanderFamily.growth * (ExpanderFamily.growth * t.darts) :=
      Nat.mul_le_mul_left _ (regularVertices_le t)
    _ = _ := by ring

end DFVSGames.Foundations.PCP.PreprocessingTables

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_InitialGraph
attribute [-instance] _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Foundations.PCP.RoundTables

def powered (H : BaseTable) (table : GraphTables.Table) : GenericGraphTables.Table alphabet :=
  PoweringTables.table (PreprocessingTables.preprocess H table) walkParameter

def build (H : BaseTable) (table : GraphTables.Table) : GraphTables.Table :=
  AlphabetTable.Table.build (powered H table)

theorem powered_vertices (H : BaseTable) (table : GraphTables.Table) :
    (powered H table).vertices = PreprocessingTables.vertices table := rfl

theorem powered_darts (H : BaseTable) (table : GraphTables.Table) :
    (powered H table).darts = 2 * PreprocessingTables.vertices table *
      PreprocessingTables.degree ^ (walkParameter + 1) := rfl

theorem build_darts_positive (H : BaseTable) (table : GraphTables.Table) :
    0 < (build H table).darts := by
  change 0 < (AlphabetTable.Table.build (powered H table)).darts
  rw [AlphabetTableBounds.build_darts, powered_darts]
  exact Nat.mul_pos (Nat.mul_pos
    (Nat.mul_pos (by decide) (PreprocessingTables.vertices_positive table))
    (Nat.pow_pos degree_positive)) (dartFactor_positive alphabet)

theorem build_size_le (H : BaseTable) (table : GraphTables.Table)
    (ht : 0 < table.darts) :
    (build H table).vertices + (build H table).darts ≤
      sizeFactor * (table.vertices + table.darts) := by
  have hv := PreprocessingTables.vertices_le_of_positive table ht
  have he : (powered H table).vertices + (powered H table).darts =
      PreprocessingTables.vertices table *
        (1 + 2 * PreprocessingTables.degree ^ (walkParameter + 1)) := by
    rw [powered_vertices, powered_darts]
    ring
  have hp := Nat.mul_le_mul_right
    (1 + 2 * PreprocessingTables.degree ^ (walkParameter + 1)) hv
  calc
    _ ≤ AlphabetGraphBounds.sizeFactor alphabet *
        ((powered H table).vertices + (powered H table).darts) :=
      AlphabetTableBounds.build_total_le (powered H table)
    _ = AlphabetGraphBounds.sizeFactor alphabet *
        (PreprocessingTables.vertices table *
          (1 + 2 * PreprocessingTables.degree ^ (walkParameter + 1))) := by rw [he]
    _ ≤ AlphabetGraphBounds.sizeFactor alphabet *
        ((ExpanderFamily.growth ^ 2 * table.darts) *
          (1 + 2 * PreprocessingTables.degree ^ (walkParameter + 1))) :=
      Nat.mul_le_mul_left _ hp
    _ = sizeFactor * table.darts := by unfold sizeFactor; ring
    _ ≤ sizeFactor * (table.vertices + table.darts) :=
      Nat.mul_le_mul_left _ (Nat.le_add_left _ _)

end DFVSGames.Foundations.PCP.RoundTables

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_FinalCNFPattern
attribute [-instance] _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Foundations.PCP.GraphTableComplexity

open DFVSGames.Foundations.Complexity
open Polynomial

theorem encodingPolynomial_eval (q n : Nat) :
    (encodingPolynomial q).eval n = n ^ 2 + (2 * (q * q) + 1) * n + 2 := by
  simp [encodingPolynomial]

theorem encodingPolynomial_mono (q : Nat) {n m : Nat} (hnm : n ≤ m) :
    (encodingPolynomial q).eval n ≤ (encodingPolynomial q).eval m := by
  rw [encodingPolynomial_eval, encodingPolynomial_eval]
  exact Nat.add_le_add_right
    (Nat.add_le_add (Nat.pow_le_pow_left hnm 2) (Nat.mul_le_mul_left _ hnm)) 2

theorem rowBound_le_polynomial (q vertices darts : Nat) :
    vertices + darts + 2 + darts * (vertices + darts + 2 * (q * q)) ≤
      (encodingPolynomial q).eval (vertices + darts) := by
  have hd : darts ≤ vertices + darts := Nat.le_add_left darts vertices
  calc
    _ ≤ vertices + darts + 2 +
        (vertices + darts) * (vertices + darts + 2 * (q * q)) :=
      Nat.add_le_add_left (Nat.mul_le_mul_right _ hd) _
    _ = _ := by rw [encodingPolynomial_eval]; ring

theorem bits_le_polynomial (table : GraphTables.Table) :
    (GraphTables.tableBits table).length ≤
      (encodingPolynomial 64).eval (table.vertices + table.darts) :=
  (GraphTables.tableBits_length_le table).trans
    (rowBound_le_polynomial 64 table.vertices table.darts)

theorem bits_le_of_size_le {N : Nat} (table : GraphTables.Table)
    (hsize : table.vertices + table.darts ≤ N) :
    (GraphTables.tableBits table).length ≤ (encodingPolynomial 64).eval N :=
  (bits_le_polynomial table).trans (encodingPolynomial_mono 64 hsize)

end DFVSGames.Foundations.PCP.GraphTableComplexity

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_TableIteration
attribute [-instance] _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Foundations.PCP.TableIteration

open RoundTables
open Target Complexity

def runTables (H : BaseTable) : Nat → GraphTables.Table → GraphTables.Table :=
  AmplificationIteration.run (build H)

end DFVSGames.Foundations.PCP.TableIteration

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachinePreservingLookupClean
attribute [-instance] _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeBEq _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Complexity.MachineCloudRank

open Turing MachineComposition MachineCloudCount

variable {σ : Type}

theorem rankTrace (n m v k : Nat) (rs : List Row) (hk : k ≤ rs.length)
    (hwidth : ∀ r ∈ rs, r.2.length = 4097) (querySuffix count : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (rankProgram (σ := σ))))^[rankSteps n m v k rs querySuffix]
      (some ⟨some .queryFirst, ((ambient, false), register),
        memory (inputWord n m rs) [] (queryWord v k querySuffix) [] count []⟩) =
      some ⟨none, ((ambient, false), none),
        memory (inputWord n m rs) (encodeWords ((rs.drop k).flatMap rowWords))
          (queryWord v k querySuffix) []
          (List.replicate (rowsHits v (rs.take k)) true ++ count)
          (encodeWord 0 ++ querySuffix)⟩ := by
  have hquery := MachineCopy.copyTrace Tape.target Tape.spare Tape.scratch
    (by decide) (by decide) (by decide) false RankLabel.queryFirst RankLabel.querySecond
    (some RankLabel.querySkip) rankProgram rfl rfl
    (memory (inputWord n m rs) [] (queryWord v k querySuffix) [] count [])
    rfl (ambient, false) register
  simp only [memory_target, memory_spare, List.append_nil, update_memory_spare] at hquery
  have hquerySkip := MachineLookup.discardTrace Tape.spare RankLabel.querySkip RankLabel.tableFirst
    rankProgram rfl
    (memory (inputWord n m rs) [] (queryWord v k querySuffix) [] count (queryWord v k querySuffix))
    v (encodeWord k ++ querySuffix) rfl (ambient, false) none
  simp only [update_memory_spare] at hquerySkip
  have hcopy := MachineCopy.copyTrace Tape.original Tape.work Tape.scratch
    (by decide) (by decide) (by decide) false RankLabel.tableFirst RankLabel.tableSecond
    (some RankLabel.headerFirst) rankProgram rfl rfl
    (memory (inputWord n m rs) [] (queryWord v k querySuffix) [] count
      (encodeWord k ++ querySuffix)) rfl (ambient, false) none
  simp only [memory_original, memory_work, List.append_nil, update_memory_work] at hcopy
  have hfirst := MachineLookup.discardTrace Tape.work RankLabel.headerFirst RankLabel.headerSecond
    rankProgram rfl
    (memory (inputWord n m rs) (inputWord n m rs) (queryWord v k querySuffix) [] count
      (encodeWord k ++ querySuffix))
    n (encodeWord m ++ encodeWords (rs.flatMap rowWords))
    (inputWord_eq n m rs) (ambient, false) none
  simp only [update_memory_work] at hfirst
  have hsecond := MachineLookup.discardTrace Tape.work RankLabel.headerSecond RankLabel.row
    rankProgram rfl
    (memory (inputWord n m rs) (encodeWord m ++ encodeWords (rs.flatMap rowWords))
      (queryWord v k querySuffix) [] count (encodeWord k ++ querySuffix))
    m (encodeWords (rs.flatMap rowWords)) rfl (ambient, false) none
  simp only [update_memory_work] at hsecond
  have hprefix := prefixTrace (rs.take k)
    (by intro r hr; exact hwidth r (List.mem_of_mem_take hr)) v
    (inputWord n m rs) (encodeWords ((rs.drop k).flatMap rowWords))
    (encodeWord k ++ querySuffix) querySuffix count ambient none
  have htake : (rs.take k).length = k := by
    simp only [List.length_take, Nat.min_eq_left hk]
  rw [htake, ← encoded_rows_split rs k] at hprefix
  rw [show rankSteps n m v k rs querySuffix = prefixTime v (rs.take k) +
      ((m + 1) + ((n + 1) + (2 * ((inputWord n m rs).length + 1) +
        ((v + 1) + 2 * ((queryWord v k querySuffix).length + 1))))) by
      unfold rankSteps; omega,
    Function.iterate_add_apply _ (prefixTime v (rs.take k)),
    Function.iterate_add_apply _ (m + 1), Function.iterate_add_apply _ (n + 1),
    Function.iterate_add_apply _ (2 * ((inputWord n m rs).length + 1)),
    Function.iterate_add_apply _ (v + 1), hquery, hquerySkip, hcopy, hfirst, hsecond]
  exact hprefix

open DFVSGames.Foundations.PCP

theorem tableRows_length (t : GraphTables.Table) : (tableRows t).length = t.darts := by
  simp only [tableRows, List.length_map, GraphTables.rowList_length]

theorem cloudRank_eq_prefix_count (t : GraphTables.Table) (v : Fin t.vertices)
    (e : DegreeReplacement.Cloud (GraphTables.semantics t) v) :
    (PreprocessingCloudIndex.cloudRank t v e).val =
      rowsHits v.val ((tableRows t).take e.val.val) := by
  have hindex := idxOf_filter_prefix (fun x : Fin t.darts => decide (t.rows[x].tail = v))
    e.val (by simpa using e.property) (List.finRange t.darts) (List.mem_finRange e.val)
  simp only [List.idxOf_finRange] at hindex
  change (PreprocessingCloudIndex.cloudDarts t v).idxOf e.val = _
  unfold PreprocessingCloudIndex.cloudDarts
  rw [hindex, rowsHits_eq_filter]
  simp only [tableRows, rowList_eq_finRange_map, ← List.map_take, List.filter_map,
    List.length_map, Function.comp_def, Fin.val_inj]

theorem cloudRankTrace (t : GraphTables.Table) (v : Fin t.vertices)
    (e : DegreeReplacement.Cloud (GraphTables.semantics t) v)
    (querySuffix countSuffix : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (rankProgram (σ := σ))))^[
        rankSteps t.vertices t.darts v.val e.val.val (tableRows t) querySuffix]
      (some ⟨some .queryFirst, ((ambient, false), register),
        memory (GraphTables.tableBits t) [] (queryWord v.val e.val.val querySuffix) []
          (encodeWord 0 ++ countSuffix) []⟩) =
      some ⟨none, ((ambient, false), none),
        memory (GraphTables.tableBits t)
          (encodeWords (((tableRows t).drop e.val.val).flatMap rowWords))
          (queryWord v.val e.val.val querySuffix) []
          (encodeWord (PreprocessingCloudIndex.cloudRank t v e).val ++ countSuffix)
          (encodeWord 0 ++ querySuffix)⟩ := by
  have hk : e.val.val ≤ (tableRows t).length := by
    rw [tableRows_length]
    exact e.val.isLt.le
  have h := rankTrace t.vertices t.darts v.val e.val.val (tableRows t) hk
    (tableRows_width t) querySuffix (encodeWord 0 ++ countSuffix) ambient register
  rw [tableRows_input, ← cloudRank_eq_prefix_count t v e, ← List.append_assoc,
    replicate_encodeWord, Nat.add_zero] at h
  exact h

end DFVSGames.Foundations.Complexity.MachineCloudRank

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineTableRows
attribute [-instance] _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.Complexity.MachineTableRows

open Turing
open PCP.GraphTables

variable {K Λ σ : Type} [DecidableEq K]

theorem prefixTrace (fields : Fin 3 → K) (row output scratch : K)
    (hfields : ∀ i, fields i ≠ row ∧ fields i ≠ scratch)
    (hrowScratch : row ≠ scratch) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (hprogram : ∀ label, program (labels label) = routine fields row output scratch labels exit label)
    (base : K → List Bool) (hscratch : base scratch = [])
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[2 * (fieldSize fields base + 3)]
      (some ⟨some (labels .relationRead), (ambient, register), base⟩) =
      some ⟨some (labels .appendOld), (ambient, none), prefixTapes fields row base⟩ := by
  let afterRelation := Function.update base row (base (fields 2) ++ base row)
  let afterReverse := Function.update afterRelation row
    (base (fields 1) ++ afterRelation row)
  have hfirst := MachineCopy.copyTrace (fields 2) row scratch
    (hfields 2).1 (hfields 2).2 hrowScratch false
    (labels .relationRead) (labels .relationRestore) (some (labels .reverseRead))
    program (hprogram .relationRead) (hprogram .relationRestore) base hscratch ambient register
  change (MachineComposition.advance (TM2.step program))^[2 * ((base (fields 2)).length + 1)]
    (some ⟨some (labels .relationRead), (ambient, register), base⟩) =
    some ⟨some (labels .reverseRead), (ambient, none), afterRelation⟩ at hfirst
  have hsecond := MachineCopy.copyTrace (fields 1) row scratch
    (hfields 1).1 (hfields 1).2 hrowScratch false
    (labels .reverseRead) (labels .reverseRestore) (some (labels .tailRead))
    program (hprogram .reverseRead) (hprogram .reverseRestore) afterRelation
    (by simp [afterRelation, Ne.symm hrowScratch, hscratch]) ambient none
  have hrev : afterRelation (fields 1) = base (fields 1) := by
    simp [afterRelation, (hfields 1).1]
  rw [hrev] at hsecond
  change (MachineComposition.advance (TM2.step program))^[2 * ((base (fields 1)).length + 1)]
    (some ⟨some (labels .reverseRead), (ambient, none), afterRelation⟩) =
    some ⟨some (labels .tailRead), (ambient, none), afterReverse⟩ at hsecond
  have hthird := MachineCopy.copyTrace (fields 0) row scratch
    (hfields 0).1 (hfields 0).2 hrowScratch false
    (labels .tailRead) (labels .tailRestore) (some (labels .appendOld))
    program (hprogram .tailRead) (hprogram .tailRestore) afterReverse
    (by simp [afterReverse, afterRelation, Ne.symm hrowScratch, hscratch]) ambient none
  have htail : afterReverse (fields 0) = base (fields 0) := by
    simp [afterReverse, afterRelation, (hfields 0).1]
  rw [htail] at hthird
  have hfinal : Function.update afterReverse row
      (base (fields 0) ++ afterReverse row) = prefixTapes fields row base := by
    simp [afterReverse, afterRelation, prefixTapes, fieldBits, List.append_assoc]
  rw [hfinal] at hthird
  rw [show 2 * (fieldSize fields base + 3) =
    2 * ((base (fields 0)).length + 1) +
      (2 * ((base (fields 1)).length + 1) + 2 * ((base (fields 2)).length + 1)) by
        simp only [fieldSize]; omega,
    Function.iterate_add_apply,
    Function.iterate_add_apply (m := 2 * ((base (fields 1)).length + 1))
      (n := 2 * ((base (fields 2)).length + 1)), hfirst, hsecond]
  exact hthird

theorem appendTrace (fields : Fin 3 → K) (row output scratch : K)
    (hfields : ∀ i, fields i ≠ row ∧ fields i ≠ scratch)
    (hrowOutput : row ≠ output) (hrowScratch : row ≠ scratch)
    (houtputScratch : output ≠ scratch) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (hprogram : ∀ label, program (labels label) = routine fields row output scratch labels exit label)
    (base : K → List Bool) (hrow : base row = []) (hscratch : base scratch = [])
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[
        4 * fieldSize fields base + 2 * (base output).length + 9]
      (some ⟨some (labels .relationRead), (ambient, register), base⟩) =
      some ⟨exit, (ambient, none),
        Function.update base output (base output ++ fieldBits fields base)⟩ := by
  have hprefix := prefixTrace fields row output scratch hfields hrowScratch
    labels exit program hprogram base hscratch ambient register
  have happend := MachineAppendAt.appendTrace row output scratch hrowOutput hrowScratch
    houtputScratch false (labels .appendOld) (labels .appendRow) (labels .appendBack)
    exit program (hprogram .appendOld) (hprogram .appendRow) (hprogram .appendBack)
    (prefixTapes fields row base)
    (by simp [prefixTapes, Ne.symm hrowScratch, hscratch]) ambient none
  have hrowbits : prefixTapes fields row base row = fieldBits fields base := by
    simp [prefixTapes, hrow]
  have hout : prefixTapes fields row base output = base output := by
    simp [prefixTapes, Ne.symm hrowOutput]
  rw [hrowbits, hout, fieldBits_length] at happend
  have hfinal : MachineAppendAt.appendTapes row output (prefixTapes fields row base) =
      Function.update base output (base output ++ fieldBits fields base) := by
    funext k
    by_cases ho : k = output
    · subst k
      simp [MachineAppendAt.appendTapes, hrowbits, hout]
    · by_cases hr : k = row
      · subst k
        simp [MachineAppendAt.appendTapes, Reduction.MachineTransfer.tapesAt,
          prefixTapes, hrowOutput, hrow]
      · simp [MachineAppendAt.appendTapes, Reduction.MachineTransfer.tapesAt,
          prefixTapes, ho, hr]
  rw [hfinal] at happend
  rw [show 4 * fieldSize fields base + 2 * (base output).length + 9 =
      (2 * (fieldSize fields base + (base output).length) + 3) +
        2 * (fieldSize fields base + 3) by omega,
    Function.iterate_add_apply, hprefix]
  exact happend

theorem rowBits_eq {n m : Nat} (r : DartRow n m) :
    encodeWords (rowWords r) = encodeWord r.tail.val ++
      encodeWord r.reverseIndex.val ++ encodeWords (relationWords r.relation) := by
  simp [rowWords, encodeWords]

end DFVSGames.Foundations.Complexity.MachineTableRows

end

section

namespace DFVSGames.Foundations.Complexity.MachineRegularOriginalRow

open Turing MachineComposition
open PCP PCP.GraphTables PCP.PreprocessingRegularTables

abbrev Buffer := MachineFixedBlockMap.Buffer 4096
abbrev State (σ : Type) := (σ × Buffer) × Option Bool

def zeroBuffer : Buffer := MachineFixedBlockMap.emptyBuffer 4096

def copyStateEquiv (σ : Type) : ((σ × Option Bool) × Buffer) ≃ State σ where
  toFun s := ((s.1.1, s.2), s.1.2)
  invFun s := ((s.1.1, s.2), s.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

end DFVSGames.Foundations.Complexity.MachineRegularOriginalRow
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_ExpanderTableWords
attribute [-instance] _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.PCP.ExpanderTableWords

open ExpanderTables
open DFVSGames.Foundations.Complexity (encodeWords decodeWords)

variable {v d : ℕ}

theorem rotationWords_getElem? (table : Table v d) (i : Fin (v * d)) :
    (rotationWords table)[i.val]? = some (reverseIndex table i).val := by
  apply List.getElem?_eq_some_iff.mpr
  exact ⟨by simpa only [rotationWords_length] using i.isLt,
    rotationWords_getElem table i.val i.isLt⟩

end DFVSGames.Foundations.PCP.ExpanderTableWords
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineCloudSelect
attribute [-instance] _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Complexity.MachineCloudSelect

open Turing MachineComposition
open MachineCloudCount (Row rowWords rowTime rowsHits tableRows)

variable {σ : Type}

theorem cleanupTrace (original work target rank position : List Bool) (ambient : σ) :
    (advance (TM2.step program))^[work.length + rank.length + 4]
      (some (cfg (some (.inl .clearWork)) .finishing
        original work target [] rank position ambient none)) =
      some (cfg none .checking original [] target [] [] position ambient none) := by
  have hwork := MachineDrain.drainTrace MachineCloudCount.Tape.work BaseLabel.clearWork (some BaseLabel.clearRank)
    baseProgram rfl (MachineCloudCount.memory original work target [] [] rank) work
    (ambient, false) none
  simp only [MachineCloudCount.update_memory_work] at hwork
  have hrank := MachineDrain.drainTrace MachineCloudCount.Tape.spare BaseLabel.clearRank (some BaseLabel.done)
    baseProgram rfl (MachineCloudCount.memory original [] target [] [] rank) rank
    (ambient, false) none
  simp only [MachineCloudRank.update_memory_spare] at hrank
  have raw : (advance (TM2.step baseProgram))^[work.length + rank.length + 3]
      (some ⟨some .clearWork, ((ambient, false), none),
        MachineCloudCount.memory original work target [] [] rank⟩) =
      some ⟨none, ((ambient, false), none),
        MachineCloudCount.memory original [] target [] [] []⟩ := by
    rw [show work.length + rank.length + 3 =
        1 + ((rank.length + 1) + (work.length + 1)) by omega,
      Function.iterate_add_apply _ 1, Function.iterate_add_apply _ (rank.length + 1),
      hwork, hrank, Function.iterate_one, advance_some]
    rfl
  have lifted := liftTrace Phase.finishing position _ _ _ raw
  have h : (advance (TM2.step program))^[work.length + rank.length + 3]
      (some (cfg (some (.inl .clearWork)) .finishing
        original work target [] rank position ambient none)) =
      some (cfg (some (.inr .dispatch)) .finishing
        original [] target [] [] position ambient none) := by
    convert lifted using 1 <;> rfl
  rw [show work.length + rank.length + 4 = (work.length + rank.length + 3) + 1 by omega,
    Function.iterate_succ_apply', h, advance_some]
  exact finishStep original target position ambient

theorem selectedTrace (v : Nat) (original work targetSuffix rankSuffix position : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[2 * v + work.length + rankSuffix.length + 8]
      (some (cfg (some (.inl .field)) .checking original (encodeWord v ++ work)
        (encodeWord v ++ targetSuffix) [] (encodeWord 0 ++ rankSuffix) position ambient register)) =
      some (cfg none .checking original [] (encodeWord v ++ targetSuffix) [] [] position ambient none) := by
  have hcompare := compareTrace original work targetSuffix (encodeWord 0 ++ rankSuffix)
    position v v ambient register
  simp only [ite_true, if_true, List.replicate_succ, List.replicate_zero] at hcompare
  rw [show 2 * v + work.length + rankSuffix.length + 8 =
      (work.length + rankSuffix.length + 4) + (1 + (v + min v v + 3)) by
        simp only [Nat.min_self]; omega,
    Function.iterate_add_apply _ (work.length + rankSuffix.length + 4),
    Function.iterate_add_apply _ 1, hcompare, Function.iterate_one, advance_some,
    dispatch_hit_zero]
  exact cleanupTrace original work (encodeWord v ++ targetSuffix) rankSuffix position ambient

theorem prepareTrace (n m v rank : Nat) (rs : List Row)
    (querySuffix position : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[prepareSteps n m v rank rs querySuffix]
      (some (cfg (some (.inl .queryFirst)) .checking (MachineCloudCount.inputWord n m rs)
        [] (queryWord v rank querySuffix) [] [] position ambient register)) =
      some (cfg (some (.inl .field)) .checking (MachineCloudCount.inputWord n m rs)
        (encodeWords (rs.flatMap rowWords)) (queryWord v rank querySuffix) []
        (encodeWord rank ++ querySuffix) position ambient none) := by
  have hquery := MachineCopy.copyTrace MachineCloudCount.Tape.target MachineCloudCount.Tape.spare MachineCloudCount.Tape.scratch
    (by decide) (by decide) (by decide) false BaseLabel.queryFirst BaseLabel.querySecond
    (some BaseLabel.querySkip) baseProgram rfl rfl
    (MachineCloudCount.memory (MachineCloudCount.inputWord n m rs) []
      (queryWord v rank querySuffix) [] [] []) rfl (ambient, false) register
  simp only [MachineCloudCount.memory_target, MachineCloudCount.memory_spare,
    List.append_nil, MachineCloudRank.update_memory_spare] at hquery
  have hquerySkip := MachineLookup.discardTrace MachineCloudCount.Tape.spare BaseLabel.querySkip BaseLabel.tableFirst
    baseProgram rfl (MachineCloudCount.memory (MachineCloudCount.inputWord n m rs) []
      (queryWord v rank querySuffix) [] [] (queryWord v rank querySuffix))
    v (encodeWord rank ++ querySuffix) rfl (ambient, false) none
  simp only [MachineCloudRank.update_memory_spare] at hquerySkip
  have hcopy := MachineCopy.copyTrace MachineCloudCount.Tape.original MachineCloudCount.Tape.work MachineCloudCount.Tape.scratch
    (by decide) (by decide) (by decide) false BaseLabel.tableFirst BaseLabel.tableSecond
    (some BaseLabel.headerFirst) baseProgram rfl rfl
    (MachineCloudCount.memory (MachineCloudCount.inputWord n m rs) []
      (queryWord v rank querySuffix) [] [] (encodeWord rank ++ querySuffix))
    rfl (ambient, false) none
  simp only [MachineCloudCount.memory_original, MachineCloudCount.memory_work,
    List.append_nil, MachineCloudCount.update_memory_work] at hcopy
  have hfirst := MachineLookup.discardTrace MachineCloudCount.Tape.work BaseLabel.headerFirst BaseLabel.headerSecond
    baseProgram rfl (MachineCloudCount.memory (MachineCloudCount.inputWord n m rs)
      (MachineCloudCount.inputWord n m rs) (queryWord v rank querySuffix) [] []
      (encodeWord rank ++ querySuffix))
    n (encodeWord m ++ encodeWords (rs.flatMap rowWords))
    (MachineCloudCount.inputWord_eq n m rs) (ambient, false) none
  simp only [MachineCloudCount.update_memory_work] at hfirst
  have hsecond := MachineLookup.discardTrace MachineCloudCount.Tape.work BaseLabel.headerSecond BaseLabel.field
    baseProgram rfl (MachineCloudCount.memory (MachineCloudCount.inputWord n m rs)
      (encodeWord m ++ encodeWords (rs.flatMap rowWords)) (queryWord v rank querySuffix)
      [] [] (encodeWord rank ++ querySuffix))
    m (encodeWords (rs.flatMap rowWords)) rfl (ambient, false) none
  simp only [MachineCloudCount.update_memory_work] at hsecond
  have raw : (advance (TM2.step baseProgram))^[prepareSteps n m v rank rs querySuffix]
      (some ⟨some .queryFirst, ((ambient, false), register),
        MachineCloudCount.memory (MachineCloudCount.inputWord n m rs) []
          (queryWord v rank querySuffix) [] [] []⟩) =
      some ⟨some .field, ((ambient, false), none),
        MachineCloudCount.memory (MachineCloudCount.inputWord n m rs)
          (encodeWords (rs.flatMap rowWords)) (queryWord v rank querySuffix) [] []
          (encodeWord rank ++ querySuffix)⟩ := by
    rw [show prepareSteps n m v rank rs querySuffix =
        (m + 1) + ((n + 1) + (2 * ((MachineCloudCount.inputWord n m rs).length + 1) +
          ((v + 1) + 2 * ((queryWord v rank querySuffix).length + 1)))) by
          unfold prepareSteps; omega,
      Function.iterate_add_apply _ (m + 1), Function.iterate_add_apply _ (n + 1),
      Function.iterate_add_apply _ (2 * ((MachineCloudCount.inputWord n m rs).length + 1)),
      Function.iterate_add_apply _ (v + 1), hquery, hquerySkip, hcopy, hfirst]
    exact hsecond
  convert liftTrace Phase.checking position _ _ _ raw using 1 <;> rfl

theorem prefixSelectedTrace (preceding : List Row)
    (hwidth : ∀ r ∈ preceding, r.2.length = 4097) (v position : Nat)
    (original work targetSuffix rankSuffix outputSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[prefixTime v preceding + 2 * v + work.length + rankSuffix.length + 8]
      (some (cfg (some (.inl .field)) .checking original
        (encodeWords (preceding.flatMap rowWords) ++ (encodeWord v ++ work))
        (encodeWord v ++ targetSuffix) [] (encodeWord (rowsHits v preceding) ++ rankSuffix)
        (encodeWord position ++ outputSuffix) ambient register)) =
      some (cfg none .checking original [] (encodeWord v ++ targetSuffix) [] []
        (encodeWord (position + preceding.length) ++ outputSuffix) ambient none) := by
  have hp := prefixTrace preceding hwidth v 0 position original (encodeWord v ++ work)
    targetSuffix rankSuffix outputSuffix ambient register
  simp only [Nat.add_zero] at hp
  have hs := selectedTrace v original work targetSuffix rankSuffix
    (encodeWord (position + preceding.length) ++ outputSuffix) ambient
    (if preceding = [] then register else none)
  rw [show prefixTime v preceding + 2 * v + work.length + rankSuffix.length + 8 =
      (2 * v + work.length + rankSuffix.length + 8) + prefixTime v preceding by omega,
    Function.iterate_add_apply, hp]
  exact hs

theorem fullTrace (n m v rank : Nat) (rs preceding : List Row) (work : List Bool)
    (hwidth : ∀ r ∈ preceding, r.2.length = 4097)
    (hword : encodeWords (rs.flatMap rowWords) =
      encodeWords (preceding.flatMap rowWords) ++ (encodeWord v ++ work))
    (hrank : rank = rowsHits v preceding) (querySuffix outputSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[totalSteps n m v rank rs preceding work querySuffix]
      (some (cfg (some (.inr .initialize_)) .checking (MachineCloudCount.inputWord n m rs)
        [] (queryWord v rank querySuffix) [] [] outputSuffix ambient register)) =
      some (cfg none .checking (MachineCloudCount.inputWord n m rs) []
        (queryWord v rank querySuffix) [] [] (encodeWord preceding.length ++ outputSuffix) ambient none) := by
  have hp := prepareTrace n m v rank rs querySuffix (encodeWord 0 ++ outputSuffix) ambient none
  have hs := prefixSelectedTrace preceding hwidth v 0 (MachineCloudCount.inputWord n m rs) work
    (encodeWord rank ++ querySuffix) querySuffix outputSuffix ambient none
  simp only [Nat.zero_add] at hs
  rw [← hrank, ← hword] at hs
  rw [show totalSteps n m v rank rs preceding work querySuffix =
      (prefixTime v preceding + 2 * v + work.length + querySuffix.length + 8) +
        (prepareSteps n m v rank rs querySuffix + 1) by unfold totalSteps; omega,
    Function.iterate_add_apply _ (prefixTime v preceding + 2 * v + work.length + querySuffix.length + 8),
    Function.iterate_succ_apply _ (prepareSteps n m v rank rs querySuffix),
    advance_some, initializeStep, hp]
  exact hs

open DFVSGames.Foundations.PCP

def remainder (t : GraphTables.Table) (e : Fin t.darts) : List Bool :=
  encodeWords (t.rows[e].reverseIndex.val :: GraphTables.relationWords t.rows[e].relation) ++
    encodeWords (((tableRows t).drop (e.val + 1)).flatMap rowWords)

theorem tableRows_getElem (t : GraphTables.Table) (e : Fin t.darts) :
    (tableRows t)[e.val]'(by rw [MachineCloudRank.tableRows_length]; exact e.isLt) =
      (t.rows[e].tail.val, t.rows[e].reverseIndex.val :: GraphTables.relationWords t.rows[e].relation) := by
  simp only [MachineCloudCount.tableRows, MachineCloudCount.rowList_eq_finRange_map,
    List.getElem_map, List.getElem_finRange]
  apply congrArg (fun j : Fin t.darts =>
    (t.rows[j].tail.val, t.rows[j].reverseIndex.val :: GraphTables.relationWords t.rows[j].relation))
  apply Fin.ext
  rfl

theorem tableWord_split (t : GraphTables.Table) (v : Fin t.vertices) (e : Fin t.darts)
    (owner : t.rows[e].tail = v) :
    encodeWords ((tableRows t).flatMap rowWords) =
      encodeWords (((tableRows t).take e.val).flatMap rowWords) ++
        (encodeWord v.val ++ remainder t e) := by
  have he : e.val < (tableRows t).length := by
    rw [MachineCloudRank.tableRows_length]
    exact e.isLt
  rw [MachineCloudRank.encoded_rows_split (tableRows t) e.val, List.drop_eq_getElem_cons he]
  simp only [List.flatMap_cons, encodeWords_append]
  rw [tableRows_getElem]
  simp only [rowWords, encodeWords, owner, remainder, List.append_assoc]

def cloudSelectSteps (t : GraphTables.Table) (v : Fin t.vertices)
    (i : Fin (PreprocessingCloudIndex.cloudSize t v)) (querySuffix : List Bool) : Nat :=
  let e := (PreprocessingCloudIndex.cloudSelect t v i).val
  totalSteps t.vertices t.darts v.val i.val (tableRows t) ((tableRows t).take e.val)
    (remainder t e) querySuffix

theorem cloudSelectTrace (t : GraphTables.Table) (v : Fin t.vertices)
    (i : Fin (PreprocessingCloudIndex.cloudSize t v)) (querySuffix outputSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[cloudSelectSteps t v i querySuffix]
      (some (cfg (some (.inr .initialize_)) .checking (GraphTables.tableBits t)
        [] (queryWord v.val i.val querySuffix) [] [] outputSuffix ambient register)) =
      some (cfg none .checking (GraphTables.tableBits t) [] (queryWord v.val i.val querySuffix)
        [] [] (encodeWord (PreprocessingCloudIndex.cloudSelect t v i).val.val ++ outputSuffix)
        ambient none) := by
  let e := PreprocessingCloudIndex.cloudSelect t v i
  have hword := tableWord_split t v e.val e.property
  have hrank : i.val = rowsHits v.val ((tableRows t).take e.val.val) := by
    simpa only [PreprocessingCloudIndex.cloudRank_cloudSelect] using
      MachineCloudRank.cloudRank_eq_prefix_count t v (PreprocessingCloudIndex.cloudSelect t v i)
  have h := fullTrace t.vertices t.darts v.val i.val (tableRows t)
    ((tableRows t).take e.val.val) (remainder t e.val)
    (by intro r hr; exact MachineCloudCount.tableRows_width t r (List.mem_of_mem_take hr))
    hword hrank querySuffix outputSuffix ambient register
  have htake : ((tableRows t).take e.val.val).length = e.val.val := by
    rw [List.length_take, MachineCloudRank.tableRows_length,
      Nat.min_eq_left e.val.isLt.le]
  rw [MachineCloudCount.tableRows_input, htake] at h
  exact h

theorem cloudSelectSteps_le (t : GraphTables.Table) (v : Fin t.vertices)
    (i : Fin (PreprocessingCloudIndex.cloudSize t v)) (querySuffix : List Bool) :
    cloudSelectSteps t v i querySuffix ≤
      10 * ((GraphTables.tableBits t).length + (queryWord v.val i.val querySuffix).length) + 20 := by
  let e := PreprocessingCloudIndex.cloudSelect t v i
  have h := totalSteps_le t.vertices t.darts v.val i.val (tableRows t)
    ((tableRows t).take e.val.val) (remainder t e.val) querySuffix
    (tableWord_split t v e.val e.property)
  simpa only [cloudSelectSteps, e, MachineCloudCount.tableRows_input] using h

end DFVSGames.Foundations.Complexity.MachineCloudSelect


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineExpanderRowDivision
attribute [-instance] _root_.OAI.DFVSGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.DFVSGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DFVSGames.Quadratic.blockOrientationFintype _root_.OAI.DFVSGames.Quadratic.fieldLineFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.Complexity.MachineExpanderRow

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl

variable {K Λ ρ : Type} [DecidableEq K] [Fintype ρ]

theorem firstDivisionTrace {d : Nat} (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (portsInjective : Function.Injective ports)
    (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (atProgram : ∀ label, target (labels label) = statement positive H ports labels exit label)
    (base : K → List Bool) (n : Nat)
    (sourceSuffix quotientSuffix remainderSuffix : List Bool)
    (sourceInput : base (ports .lookupOutput) = encodeWord n ++ sourceSuffix)
    (quotientInput : base (ports .quotientFirst) = encodeWord 0 ++ quotientSuffix)
    (remainderInput : base (ports .remainderFirst) = encodeWord 0 ++ remainderSuffix)
    (ambient : ρ) (control : Control d) (register : Option Bool) :
    (MachineComposition.advance (TM2.step target))^[n + 2]
      (some ⟨some (labels .firstScan), divisionState positive ambient control register, base⟩) =
      some ⟨some (labels .clearQuery), divisionState positive ambient
        (receiveFirst control (MachineFixedDivMod.residue (degree d)
          (Nat.mul_pos positive positive) n)) none,
        divisionOutput d ports .quotientFirst .remainderFirst base n
          sourceSuffix quotientSuffix remainderSuffix⟩ := by
  have hsq : ports .lookupOutput ≠ ports .quotientFirst :=
    fun h => Tape.noConfusion (portsInjective h)
  have hsr : ports .lookupOutput ≠ ports .remainderFirst :=
    fun h => Tape.noConfusion (portsInjective h)
  have hqr : ports .quotientFirst ≠ ports .remainderFirst :=
    fun h => Tape.noConfusion (portsInjective h)
  have hs : target (labels .firstScan) = MachineControl.statement id (divisionStates ρ d)
      (MachineFixedDivMod.scanLoop (degree d) (Nat.mul_pos positive positive)
        (ports .lookupOutput) (ports .quotientFirst) (labels .firstScan)
        (fun r => labels (.firstResidue r))) := atProgram .firstScan
  have he : ∀ r, target (labels (.firstResidue r)) =
      MachineControl.statement id (divisionStates ρ d)
        (MachineFixedDivMod.emitterWithFinish (degree d) (Nat.mul_pos positive positive)
          (ports .remainderFirst) (some (labels .clearQuery)) firstFinish r) :=
    fun r => atProgram (.firstResidue r)
  have h := transportedDivision_inline_MachineExpanderRowDivision (degree d) (Nat.mul_pos positive positive)
    (ports .lookupOutput) (ports .quotientFirst) (ports .remainderFirst) hsq hsr hqr
    (divisionStates ρ d) (labels .firstScan) (fun r => labels (.firstResidue r))
    (some (labels .clearQuery)) firstFinish target hs he base n sourceSuffix quotientSuffix
    remainderSuffix sourceInput quotientInput remainderInput ((ambient, control), ()) register
  simpa only [MachineControl.configuration, divisionStates_apply, firstFinish, divisionState,
    divisionOutput, Option.map_some, id_eq] using h

theorem secondDivisionTrace {d : Nat} (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (portsInjective : Function.Injective ports)
    (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (atProgram : ∀ label, target (labels label) = statement positive H ports labels exit label)
    (base : K → List Bool) (n : Nat)
    (sourceSuffix quotientSuffix remainderSuffix : List Bool)
    (sourceInput : base (ports .lookupOutput) = encodeWord n ++ sourceSuffix)
    (quotientInput : base (ports .quotientSecond) = encodeWord 0 ++ quotientSuffix)
    (remainderInput : base (ports .remainderSecond) = encodeWord 0 ++ remainderSuffix)
    (ambient : ρ) (control : Control d) (register : Option Bool) :
    (MachineComposition.advance (TM2.step target))^[n + 2]
      (some ⟨some (labels .secondScan), divisionState positive ambient control register, base⟩) =
      some ⟨some (labels (.outputEmit (PCP.AlphabetTable.Emitter.labelAt 3 _ 0 .entry))),
        divisionState positive ambient
          (receiveSecond H control (MachineFixedDivMod.residue (degree d)
            (Nat.mul_pos positive positive) n)) none,
        divisionOutput d ports .quotientSecond .remainderSecond base n
          sourceSuffix quotientSuffix remainderSuffix⟩ := by
  have hsq : ports .lookupOutput ≠ ports .quotientSecond :=
    fun h => Tape.noConfusion (portsInjective h)
  have hsr : ports .lookupOutput ≠ ports .remainderSecond :=
    fun h => Tape.noConfusion (portsInjective h)
  have hqr : ports .quotientSecond ≠ ports .remainderSecond :=
    fun h => Tape.noConfusion (portsInjective h)
  have hs : target (labels .secondScan) = MachineControl.statement id (divisionStates ρ d)
      (MachineFixedDivMod.scanLoop (degree d) (Nat.mul_pos positive positive)
        (ports .lookupOutput) (ports .quotientSecond) (labels .secondScan)
        (fun r => labels (.secondResidue r))) := atProgram .secondScan
  have he : ∀ r, target (labels (.secondResidue r)) =
      MachineControl.statement id (divisionStates ρ d)
        (MachineFixedDivMod.emitterWithFinish (degree d) (Nat.mul_pos positive positive)
          (ports .remainderSecond)
          (some (labels (.outputEmit (PCP.AlphabetTable.Emitter.labelAt 3 _ 0 .entry))))
          (secondFinish H) r) := fun r => atProgram (.secondResidue r)
  have h := transportedDivision_inline_MachineExpanderRowDivision (degree d) (Nat.mul_pos positive positive)
    (ports .lookupOutput) (ports .quotientSecond) (ports .remainderSecond) hsq hsr hqr
    (divisionStates ρ d) (labels .secondScan) (fun r => labels (.secondResidue r))
    (some (labels (.outputEmit (PCP.AlphabetTable.Emitter.labelAt 3 _ 0 .entry))))
    (secondFinish H) target hs he base n sourceSuffix quotientSuffix remainderSuffix
    sourceInput quotientInput remainderInput ((ambient, control), ()) register
  simpa only [MachineControl.configuration, divisionStates_apply, secondFinish, divisionState,
    divisionOutput, Option.map_some, id_eq] using h

end DFVSGames.Foundations.Complexity.MachineExpanderRow

end

section

namespace DFVSGames.Foundations.Complexity.MachineExpanderTable

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl

variable {ρ : Type} [Fintype ρ]

def rowTapes (vertex : Nat) (oldTable output : List Bool) : MachineExpanderRow.Tape → List Bool
  | .inputVertex => encodeWord vertex
  | .table => oldTable
  | .output => output
  | _ => []

def extraTapes (remaining : Nat) (countSuffix result : List Bool) : ExtraTape → List Bool
  | .vertexCount => encodeWord remaining ++ countSuffix
  | .result => result

def boundaryTapes (vertex remaining : Nat) (oldTable output countSuffix result : List Bool) :
    (tape : Tape) → List (Alphabet tape) :=
  MachineEmbedding.tapes (rowTapes vertex oldTable output) (extraTapes remaining countSuffix result)

def initialTapes (vertices : Nat) (oldTable countSuffix : List Bool) :
    (tape : Tape) → List (Alphabet tape) :=
  MachineEmbedding.tapes
    (fun tape => match tape with | .table => oldTable | _ => [])
    (extraTapes vertices countSuffix [])

def finalTapes (vertices : Nat) (oldTable output countSuffix : List Bool) :
    (tape : Tape) → List (Alphabet tape) :=
  boundaryTapes vertices 0 oldTable [] countSuffix output

end DFVSGames.Foundations.Complexity.MachineExpanderTable
end

section

namespace DFVSGames.Foundations.Complexity.MachineAlphabetTransport

open Turing.TM2

variable {K Λ σ : Type} {Γ Δ : K → Type}

variable [DecidableEq K]

theorem step_simulation (h : Γ = Δ) (source : Λ → Stmt Γ Λ σ) (start : Cfg Γ Λ σ) :
    step (program h source) (configuration h start) =
      (step source start).map (configuration h) := by
  cases h
  simp only [program_rfl, configuration_rfl, map_configuration_rfl]

theorem trace_transport (h : Γ = Δ) (source : Λ → Stmt Γ Λ σ)
    (n : Nat) (start : Option (Cfg Γ Λ σ)) :
    (MachineComposition.advance (step (program h source)))^[n]
      (start.map (configuration h)) =
      ((MachineComposition.advance (step source))^[n] start).map (configuration h) := by
  cases h
  simp only [program_rfl, map_configuration_rfl]

theorem successfulTrace (h : Γ = Δ) (source : Λ → Stmt Γ Λ σ)
    (n : Nat) (start finish : Cfg Γ Λ σ)
    (trace : (MachineComposition.advance (step source))^[n] (some start) = some finish) :
    (MachineComposition.advance (step (program h source)))^[n]
      (some (configuration h start)) = some (configuration h finish) := by
  have transported := trace_transport h source n (some start)
  simpa only [Option.map_some, trace] using transported

end DFVSGames.Foundations.Complexity.MachineAlphabetTransport

end

section

namespace DFVSGames.Foundations.Complexity.MachineExpanderFamily

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords

instance alphabetFintype (tape : Tape) : Fintype (Alphabet tape) := by
  rw [alphabet_eq]
  exact inferInstanceAs (Fintype Bool)

end DFVSGames.Foundations.Complexity.MachineExpanderFamily
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineExpanderFamilyTapes
attribute [-instance] _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.Complexity.MachineExpanderFamily

open Turing

theorem transport_tapes_apply_inline_MachineExpanderFamilyTapes {K : Type} {Γ Δ : K → Type}
    (h : Γ = Δ) (base : (k : K) → List (Γ k)) (k : K) :
    MachineAlphabetTransport.tapes h base k =
      Eq.mp (congrArg (fun alphabet => List (alphabet k)) h) (base k) := by
  cases h
  rfl

theorem toBoolTapes_eq_transport (base : (tape : Tape) → List (Alphabet tape)) :
    toBoolTapes base = MachineAlphabetTransport.tapes alphabet_eq base := by
  funext tape
  rw [transport_tapes_apply_inline_MachineExpanderFamilyTapes]
  rcases tape with tape | tape
  · cases tape <;> rfl
  · rfl

theorem fromBoolTapes_eq_transport (base : Tape → List Bool) :
    fromBoolTapes base = MachineAlphabetTransport.tapes alphabet_eq.symm base := by
  funext tape
  rw [transport_tapes_apply_inline_MachineExpanderFamilyTapes]
  rcases tape with tape | tape
  · cases tape <;> rfl
  · rfl

theorem configuration_fromBool {ρ : Type} {d : Nat} (label : Option (Label d))
    (state : State ρ d) (base : Tape → List Bool) :
    MachineAlphabetTransport.configuration alphabet_eq.symm ⟨label, state, base⟩ =
      ⟨label, state, fromBoolTapes base⟩ := by
  rw [MachineAlphabetTransport.configuration_mk, fromBoolTapes_eq_transport]

theorem configuration_toBool {ρ : Type} {d : Nat} (label : Option (Label d))
    (state : State ρ d) (base : (tape : Tape) → List (Alphabet tape)) :
    MachineAlphabetTransport.configuration alphabet_eq ⟨label, state, base⟩ =
      ⟨label, state, toBoolTapes base⟩ := by
  rw [MachineAlphabetTransport.configuration_mk, toBoolTapes_eq_transport]

end DFVSGames.Foundations.Complexity.MachineExpanderFamily
end

section

namespace DFVSGames.Foundations.Complexity.MachineExpanderFamily

open Turing MachineComposition
open PCP.ExpanderTables PCP.ExpanderRowControl

theorem controlDrainTrace {K Λ σ τ : Type} [DecidableEq K]
    (states : (σ × Option Bool) ≃ τ) (source : K) (again : Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ τ)
    (code : target again = MachineControl.statement id states
      (MachineDrain.drain source again exit))
    (base : K → List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step target))^[(base source).length + 1]
      (some ⟨some again, states (ambient, register), base⟩) =
      some ⟨exit, states (ambient, none), Function.update base source []⟩ := by
  let raw := MachineControl.program (Equiv.refl Λ) states.symm target
  have atRaw : raw again = MachineDrain.drain source again exit := by
    change MachineControl.statement id states.symm (target again) = _
    rw [code]
    exact controlStatementInverse states _
  have run := MachineDrain.drainTrace source again exit raw atRaw base (base source) ambient register
  simp only [Function.update_eq_self] at run
  simpa only [MachineControl.configuration, Option.map_some, id_eq, Option.map_id] using
    controlTrace states target ((base source).length + 1) _ _ run

variable {ρ : Type} {d : Nat}

variable [Fintype ρ]

theorem boolTraceActual (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (n : Nat)
    (start finish : TM2.Cfg BoolAlphabet (Label d) (State ρ d))
    (run : (advance (TM2.step (boolView positive H growth)))^[n] (some start) = some finish) :
    (advance (TM2.step (program positive H growth)))^[n]
      (some (MachineAlphabetTransport.configuration alphabet_eq.symm start)) =
      some (MachineAlphabetTransport.configuration alphabet_eq.symm finish) := by
  have h := MachineAlphabetTransport.successfulTrace alphabet_eq.symm
    (boolView positive H growth) n start finish run
  simpa only [boolView, MachineAlphabetTransport.program_symm_roundtrip] using h

theorem drainBoolTrace (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (source : Tape) (again next : OuterLabel)
    (code : boolOuterStatement (ρ := ρ) positive H again = drainStatement source again next)
    (base : Tape → List Bool) (state : State ρ d) :
    (advance (TM2.step (boolView positive H growth)))^[(base source).length + 1]
      (some ⟨some (.inr again), state, base⟩) =
      some ⟨some (.inr next), clearRegister state, Function.update base source []⟩ := by
  have atLoop : boolView (ρ := ρ) positive H growth (.inr again) =
      MachineControl.statement id (registerStates ρ d)
        (MachineDrain.drain source (.inr again) (some (.inr next))) := by
    rw [boolView_outer, code]
    rfl
  have h := controlDrainTrace (registerStates ρ d) source (.inr again) (some (.inr next))
    (boolView positive H growth) atLoop base
    ((registerStates ρ d).symm state).1 ((registerStates ρ d).symm state).2
  simpa only [Prod.mk.eta, Equiv.apply_symm_apply, registerStates_reset] using h

theorem transferBoolTrace (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (source destination : Tape) (distinct : source ≠ destination)
    (again next : OuterLabel)
    (code : boolOuterStatement (ρ := ρ) positive H again =
      MachineControl.statement id (registerStates ρ d)
        (Reduction.MachineTransfer.loopAt (Γ := BoolAlphabet) source destination id false
          (.inr again) (some (.inr next))))
    (base : Tape → List Bool) (state : State ρ d) :
    (advance (TM2.step (boolView positive H growth)))^[(base source).length + 1]
      (some ⟨some (.inr again), state, base⟩) =
      some ⟨some (.inr next), clearRegister state,
        Reduction.MachineTransfer.tapesAt source destination base []
          ((base source).reverse ++ base destination)⟩ := by
  have atLoop : boolView (ρ := ρ) positive H growth (.inr again) =
      MachineControl.statement id (registerStates ρ d)
        (Reduction.MachineTransfer.loopAt source destination id false
          (.inr again) (some (.inr next))) := by
    rw [boolView_outer, code]
  have h := controlTransferTrace (registerStates ρ d) source destination distinct
    (.inr again) (some (.inr next)) (boolView positive H growth) atLoop base
    ((registerStates ρ d).symm state).1 ((registerStates ρ d).symm state).2
  simpa only [Prod.mk.eta, Equiv.apply_symm_apply, registerStates_reset] using h

def installedTapes (base : Tape → List Bool) (newWord : List Bool) : Tape → List Bool :=
  Function.update
    (Function.update
      (Function.update (Function.update base tableTape newWord) resultTape [])
      (.inr .tableReverse) [])
    (.inr .currentSize) []

def cleanedCounterTapes (base : Tape → List Bool) : Tape → List Bool :=
  Function.update (Function.update base inputVertexTape []) vertexCountTape []

theorem installTableBoolTrace (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : Tape → List Bool) (newWord : List Bool)
    (resultWord : base resultTape = newWord) (reverseEmpty : base (.inr .tableReverse) = [])
    (state : State ρ d) :
    (advance (TM2.step (boolView positive H growth)))^[
        (base tableTape).length + 2 * newWord.length + (base (.inr .currentSize)).length + 4]
      (some ⟨some (.inr .clearOldTable), state, base⟩) =
      some ⟨some (.inr (.affine .multiplySize .seed)), clearRegister state,
        installedTapes base newWord⟩ := by
  let b0 := Function.update base tableTape []
  let b1 := Function.update (Function.update b0 resultTape []) (.inr .tableReverse) newWord.reverse
  let b2 := Function.update (Function.update b1 (.inr .tableReverse) []) tableTape newWord
  let b3 := Function.update b2 (.inr .currentSize) []
  have h0 := drainBoolTrace positive H growth tableTape .clearOldTable .reverseResult rfl base state
  have b0Result : b0 resultTape = newWord := by
    simpa [b0, tableTape, resultTape] using resultWord
  have b0Reverse : b0 (.inr .tableReverse) = [] := by
    simpa [b0, tableTape] using reverseEmpty
  have h1 : (advance (TM2.step (boolView positive H growth)))^[newWord.length + 1]
      (some ⟨some (.inr .reverseResult), clearRegister state, b0⟩) =
      some ⟨some (.inr .reverseTable), clearRegister state, b1⟩ := by
    simpa only [b0Result, b0Reverse, List.append_nil, Reduction.MachineTransfer.tapesAt,
      clearRegister_idempotent] using
      transferBoolTrace positive H growth resultTape (.inr .tableReverse) (by decide)
        .reverseResult .reverseTable rfl b0 (clearRegister state)
  have b1Reverse : b1 (.inr .tableReverse) = newWord.reverse := by simp [b1]
  have b1Table : b1 tableTape = [] := by simp [b1, b0, tableTape, resultTape]
  have h2 : (advance (TM2.step (boolView positive H growth)))^[newWord.length + 1]
      (some ⟨some (.inr .reverseTable), clearRegister state, b1⟩) =
      some ⟨some (.inr .clearCurrentSize), clearRegister state, b2⟩ := by
    simpa only [b1Reverse, b1Table, List.reverse_reverse, List.length_reverse,
      List.append_nil, Reduction.MachineTransfer.tapesAt, clearRegister_idempotent] using
      transferBoolTrace positive H growth (.inr .tableReverse) tableTape (by decide)
        .reverseTable .clearCurrentSize rfl b1 (clearRegister state)
  have b2Current : b2 (.inr .currentSize) = base (.inr .currentSize) := by
    simp [b2, b1, b0, tableTape, resultTape]
  have h3 : (advance (TM2.step (boolView positive H growth)))^[
      (base (.inr .currentSize)).length + 1]
      (some ⟨some (.inr .clearCurrentSize), clearRegister state, b2⟩) =
      some ⟨some (.inr (.affine .multiplySize .seed)), clearRegister state, b3⟩ := by
    simpa only [b2Current, clearRegister_idempotent] using
      drainBoolTrace positive H growth (.inr .currentSize) .clearCurrentSize
        (.affine .multiplySize .seed) rfl b2 (clearRegister state)
  have final : b3 = installedTapes base newWord := by
    funext tape
    rcases tape with table | extra
    · rcases table with row | tableExtra
      · cases row <;> simp [b3, b2, b1, b0, installedTapes, tableTape, resultTape]
      · cases tableExtra <;> simp [b3, b2, b1, b0, installedTapes, tableTape, resultTape]
    · cases extra <;> simp [b3, b2, b1, b0, installedTapes, tableTape, resultTape]
  rw [show (base tableTape).length + 2 * newWord.length +
        (base (.inr .currentSize)).length + 4 =
      ((base (.inr .currentSize)).length + 1) +
        ((newWord.length + 1) + ((newWord.length + 1) + ((base tableTape).length + 1))) by omega,
    Function.iterate_add_apply _ ((base (.inr .currentSize)).length + 1),
    Function.iterate_add_apply _ (newWord.length + 1) ((newWord.length + 1) + ((base tableTape).length + 1)),
    Function.iterate_add_apply _ (newWord.length + 1) ((base tableTape).length + 1),
    h0, h1, h2, h3, final]

theorem cleanupCountersBoolTrace (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : Tape → List Bool) (state : State ρ d) :
    (advance (TM2.step (boolView positive H growth)))^[
        (base inputVertexTape).length + (base vertexCountTape).length + 2]
      (some ⟨some (.inr .drainInputVertex), state, base⟩) =
      some ⟨some (.inr .levelGuard), clearRegister state, cleanedCounterTapes base⟩ := by
  have h0 := drainBoolTrace positive H growth inputVertexTape .drainInputVertex .drainVertexCount
    rfl base state
  have count : (Function.update base inputVertexTape []) vertexCountTape = base vertexCountTape := by
    simp [inputVertexTape, vertexCountTape]
  have h1 := drainBoolTrace positive H growth vertexCountTape .drainVertexCount .levelGuard
    rfl (Function.update base inputVertexTape []) (clearRegister state)
  simp only [count, clearRegister_idempotent] at h1
  rw [show (base inputVertexTape).length + (base vertexCountTape).length + 2 =
      ((base vertexCountTape).length + 1) + ((base inputVertexTape).length + 1) by omega,
    Function.iterate_add_apply, h0]
  exact h1

theorem installTableTrace (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : (tape : Tape) → List (Alphabet tape))
    (newWord : List Bool) (resultWord : toBoolTapes base resultTape = newWord)
    (reverseEmpty : toBoolTapes base (.inr .tableReverse) = []) (state : State ρ d) :
    (advance (TM2.step (program positive H growth)))^[
        (toBoolTapes base tableTape).length + 2 * newWord.length +
          (toBoolTapes base (.inr .currentSize)).length + 4]
      (some ⟨some (.inr .clearOldTable), state, base⟩) =
      some ⟨some (.inr (.affine .multiplySize .seed)), clearRegister state,
        fromBoolTapes (installedTapes (toBoolTapes base) newWord)⟩ := by
  have h := installTableBoolTrace positive H growth (toBoolTapes base) newWord resultWord reverseEmpty state
  simpa only [configuration_fromBool, fromBool_toBool] using boolTraceActual positive H growth _ _ _ h

theorem cleanupCountersTrace (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : (tape : Tape) → List (Alphabet tape))
    (state : State ρ d) :
    (advance (TM2.step (program positive H growth)))^[
        (toBoolTapes base inputVertexTape).length + (toBoolTapes base vertexCountTape).length + 2]
      (some ⟨some (.inr .drainInputVertex), state, base⟩) =
      some ⟨some (.inr .levelGuard), clearRegister state,
        fromBoolTapes (cleanedCounterTapes (toBoolTapes base))⟩ := by
  have h := cleanupCountersBoolTrace positive H growth (toBoolTapes base) state
  simpa only [configuration_fromBool, fromBool_toBool] using boolTraceActual positive H growth _ _ _ h

def installTableInTime (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : (tape : Tape) → List (Alphabet tape))
    (newWord : List Bool) (resultWord : toBoolTapes base resultTape = newWord)
    (reverseEmpty : toBoolTapes base (.inr .tableReverse) = []) (state : State ρ d) :
    StateTransition.EvalsToInTime (TM2.step (program positive H growth))
      ⟨some (.inr .clearOldTable), state, base⟩
      (some ⟨some (.inr (.affine .multiplySize .seed)), clearRegister state,
        fromBoolTapes (installedTapes (toBoolTapes base) newWord)⟩)
      ((toBoolTapes base tableTape).length + 2 * newWord.length +
        (toBoolTapes base (.inr .currentSize)).length + 4) where
  steps := (toBoolTapes base tableTape).length + 2 * newWord.length +
    (toBoolTapes base (.inr .currentSize)).length + 4
  evals_in_steps := installTableTrace positive H growth base newWord resultWord reverseEmpty state
  steps_le_m := Nat.le_refl _

def cleanupCountersInTime (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : (tape : Tape) → List (Alphabet tape))
    (state : State ρ d) :
    StateTransition.EvalsToInTime (TM2.step (program positive H growth))
      ⟨some (.inr .drainInputVertex), state, base⟩
      (some ⟨some (.inr .levelGuard), clearRegister state,
        fromBoolTapes (cleanedCounterTapes (toBoolTapes base))⟩)
      ((toBoolTapes base inputVertexTape).length + (toBoolTapes base vertexCountTape).length + 2) where
  steps := (toBoolTapes base inputVertexTape).length + (toBoolTapes base vertexCountTape).length + 2
  evals_in_steps := cleanupCountersTrace positive H growth base state
  steps_le_m := Nat.le_refl _

end DFVSGames.Foundations.Complexity.MachineExpanderFamily
end

section

namespace DFVSGames.Foundations.Complexity.MachineExpanderFamily

open Turing MachineComposition
open PCP.ExpanderTables PCP.ExpanderRowControl

theorem affine_source_ne_scratch (phase : AffinePhase) :
    affineSource phase ≠ .inr .unaryScratch := by cases phase <;> decide

theorem affine_source_ne_destination (phase : AffinePhase) :
    affineSource phase ≠ affineDestination phase := by cases phase <;> decide

theorem affine_scratch_ne_destination (phase : AffinePhase) :
    (.inr .unaryScratch : Tape) ≠ affineDestination phase := by cases phase <;> decide

def affineResultTapes (d : Nat) (phase : AffinePhase)
    (base : (tape : Tape) → List (Alphabet tape)) (n : Nat) :
    (tape : Tape) → List (Alphabet tape) :=
  Function.update base (affineDestination phase)
    (boolWord (affineDestination phase)
      (encodeWord (affineCoefficient d phase * n) ++ toBoolTapes base (affineDestination phase)))

variable {ρ : Type} [Fintype ρ] {d : Nat}

theorem affinePhaseBoolTrace (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (phase : AffinePhase) (base : Tape → List Bool)
    (n : Nat) (suffix : List Bool)
    (sourceWord : base (affineSource phase) = encodeWord n ++ suffix)
    (scratchEmpty : base (.inr .unaryScratch) = []) (state : State ρ d) :
    (advance (TM2.step (boolView positive H growth)))^[2 * (n + 1) + 1]
      (some ⟨some (.inr (.affine phase .seed)), state, base⟩) =
      some ⟨some (affineExit d phase), clearRegister state,
        Function.update base (affineDestination phase)
          (encodeWord (affineCoefficient d phase * n) ++ base (affineDestination phase))⟩ := by
  let states := registerStates ρ d
  let target := boolView (ρ := ρ) positive H growth
  let sourceProgram := MachineControl.program (Equiv.refl (Label d)) states.symm target
  have atSeed : sourceProgram (.inr (.affine phase .seed)) =
      MachineUnaryAffineAt.seed (affineDestination phase) 0 (.inr (.affine phase .scan)) := by
    change MachineControl.statement id states.symm
      (boolView positive H growth (.inr (.affine phase .seed))) = _
    rw [boolView_outer]
    exact controlStatementInverse states _
  have atScan : sourceProgram (.inr (.affine phase .scan)) =
      MachineUnaryAffineAt.scan (affineSource phase) (.inr .unaryScratch)
        (affineDestination phase) (affineCoefficient d phase)
        (.inr (.affine phase .scan)) (.inr (.affine phase .restore)) := by
    change MachineControl.statement id states.symm
      (boolView positive H growth (.inr (.affine phase .scan))) = _
    rw [boolView_outer]
    exact controlStatementInverse states _
  have atRestore : sourceProgram (.inr (.affine phase .restore)) =
      Reduction.MachineTransfer.loopAt (.inr .unaryScratch) (affineSource phase) id false
        (.inr (.affine phase .restore)) (some (affineExit d phase)) := by
    change MachineControl.statement id states.symm
      (boolView positive H growth (.inr (.affine phase .restore))) = _
    rw [boolView_outer]
    exact controlStatementInverse states _
  have raw := MachineUnaryAffineAt.seededAffineTrace
    (affineSource phase) (.inr .unaryScratch) (affineDestination phase)
    (affine_source_ne_scratch phase) (affine_source_ne_destination phase)
    (affine_scratch_ne_destination phase) (affineCoefficient d phase) 0
    (.inr (.affine phase .seed)) (.inr (.affine phase .scan)) (.inr (.affine phase .restore))
    (some (affineExit d phase)) sourceProgram atSeed atScan atRestore base n suffix
    sourceWord scratchEmpty (states.symm state).1 (states.symm state).2
  have run := controlTrace states target (2 * (n + 1) + 1) _ _ raw
  simpa only [states, target, MachineControl.configuration, Option.map_some, id_eq, Prod.mk.eta,
    Equiv.apply_symm_apply, Nat.add_zero, registerStates_reset] using run

theorem affinePhaseTrace (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (phase : AffinePhase)
    (base : (tape : Tape) → List (Alphabet tape)) (n : Nat) (suffix : List Bool)
    (sourceWord : toBoolTapes base (affineSource phase) = encodeWord n ++ suffix)
    (scratchEmpty : base (.inr .unaryScratch) = []) (state : State ρ d) :
    (advance (TM2.step (program positive H growth)))^[2 * (n + 1) + 1]
      (some ⟨some (.inr (.affine phase .seed)), state, base⟩) =
      some ⟨some (affineExit d phase), clearRegister state,
        affineResultTapes d phase base n⟩ := by
  have raw := affinePhaseBoolTrace positive H growth phase (toBoolTapes base) n suffix
    sourceWord scratchEmpty state
  have transported := boolTraceActual positive H growth (2 * (n + 1) + 1) _ _ raw
  simpa only [configuration_fromBool, fromBoolTapes_update, fromBool_toBool,
    affineResultTapes] using transported

def affinePhaseInTime (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (phase : AffinePhase)
    (base : (tape : Tape) → List (Alphabet tape)) (n : Nat) (suffix : List Bool)
    (sourceWord : toBoolTapes base (affineSource phase) = encodeWord n ++ suffix)
    (scratchEmpty : base (.inr .unaryScratch) = []) (state : State ρ d) :
    StateTransition.EvalsToInTime (TM2.step (program positive H growth))
      ⟨some (.inr (.affine phase .seed)), state, base⟩
      (some ⟨some (affineExit d phase), clearRegister state,
        affineResultTapes d phase base n⟩) (2 * (n + 1) + 1) where
  steps := 2 * (n + 1) + 1
  evals_in_steps := affinePhaseTrace positive H growth phase base n suffix sourceWord scratchEmpty state
  steps_le_m := Nat.le_refl _

def copyCountInTime (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : (tape : Tape) → List (Alphabet tape))
    (n : Nat) (sourceWord : base (.inr .currentSize) = encodeWord n)
    (scratchEmpty : base (.inr .unaryScratch) = [])
    (destinationEmpty : base vertexCountTape = []) (state : State ρ d) :
    StateTransition.EvalsToInTime (TM2.step (program positive H growth))
      ⟨some (.inr (.affine .copyCount .seed)), state, base⟩
      (some ⟨some (.inl (.inr .initialize_)), clearRegister state,
        Function.update base vertexCountTape (encodeWord n)⟩) (2 * (n + 1) + 1) := by
  have run := affinePhaseInTime positive H growth .copyCount base n []
    (by simpa only [affineSource, toBoolTapes, toBoolWord, List.append_nil] using sourceWord)
    scratchEmpty state
  change base (.inl (.inr .vertexCount)) = [] at destinationEmpty
  simpa only [affineExit, affineResultTapes, affineDestination, affineCoefficient,
    Nat.one_mul, vertexCountTape, boolWord, toBoolTapes, toBoolWord,
    destinationEmpty, List.append_nil] using run

def multiplySizeInTime (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : (tape : Tape) → List (Alphabet tape))
    (n : Nat) (sourceWord : base inputVertexTape = encodeWord n)
    (scratchEmpty : base (.inr .unaryScratch) = [])
    (destinationEmpty : base (.inr .currentSize) = []) (state : State ρ d) :
    StateTransition.EvalsToInTime (TM2.step (program positive H growth))
      ⟨some (.inr (.affine .multiplySize .seed)), state, base⟩
      (some ⟨some (.inr .drainInputVertex), clearRegister state,
        Function.update base (.inr .currentSize) (encodeWord (cloudSize d * n))⟩)
      (2 * (n + 1) + 1) := by
  have run := affinePhaseInTime positive H growth .multiplySize base n []
    (by simpa only [affineSource, inputVertexTape, toBoolTapes, toBoolWord,
      List.append_nil] using sourceWord)
    scratchEmpty state
  simpa only [affineExit, affineResultTapes, affineDestination, affineCoefficient,
    boolWord, toBoolTapes, toBoolWord, destinationEmpty, List.append_nil] using run

end DFVSGames.Foundations.Complexity.MachineExpanderFamily
end

section

namespace DFVSGames.Foundations.Complexity.MachineExpanderRow

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.AlphabetTable

theorem affinePlan_bits {σ : Type} {bound : Nat} (coefficient : Nat)
    (offset : σ → Fin bound) (n : Nat) (ambient : σ) :
    Emitter.prefixBits (affinePlan coefficient offset) (fun _ : Fin 1 => n) ambient 3 =
      encodeWord (coefficient * n + (offset ambient).val) := by
  change Emitter.prefixBits
    (Emitter.listCommands (Emitter.affineCommands [((0 : Fin 1), coefficient)] offset))
    (fun _ : Fin 1 => n) ambient
    (Emitter.affineCommands [((0 : Fin 1), coefficient)] offset).length = _
  rw [Emitter.bits_listCommands, Emitter.affineCommands_bits]
  simp [Emitter.affineValue]

theorem affinePlan_steps {σ : Type} {bound : Nat} (coefficient : Nat)
    (offset : σ → Fin bound) (n : Nat) :
    Emitter.prefixSteps (affinePlan coefficient offset) (fun _ : Fin 1 => n) 3 + 1 =
      emitSteps n := by
  simp [affinePlan, Emitter.prefixSteps, Emitter.commandAt, Emitter.listCommands,
    Emitter.affineCommands, Emitter.commandSteps, emitSteps]

end DFVSGames.Foundations.Complexity.MachineExpanderRow

end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineExpanderRowLookup
attribute [-instance] _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.Complexity.MachineExpanderRow

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords
open MachineComposition

def lookupPhaseLabel {d : Nat} (second : Bool)
    (l : MachinePreservingLookupClean.Label) : Label d :=
  if second then .secondLookup l else .firstLookup l

def scanPhaseLabel {d : Nat} (second : Bool) : Label d :=
  if second then .secondScan else .firstScan

def reversePhaseLabel {d : Nat} (second : Bool) : Label d :=
  if second then .secondReverse else .firstReverse

theorem lookupTape_injective : Function.Injective lookupTape := by decide

variable {K Λ ρ : Type} [DecidableEq K] [Fintype ρ]

section Reverse

variable {d : Nat} (second : Bool) (positive : 0 < d)
    (H : Table (cloudSize d) d) (ports : Tape → K)
    (distinct : Function.Injective ports) (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (code : ∀ l, target (labels l) = statement positive H ports labels exit l)
    (base : K → List Bool)
    (ambient : (Ambient ρ d × Fin (degree d)) × Unit) (register : Option Bool)

include positive H distinct exit code

theorem reversePhaseTrace :
    (advance (TM2.step target))^[(base (ports .queryReverse)).length + 1]
      (some ⟨some (labels (reversePhaseLabel second)), (ambient, register), base⟩) =
      some ⟨some (labels (lookupPhaseLabel second (.run .copyFirst))), (ambient, none),
        Reduction.MachineTransfer.tapesAt (ports .queryReverse) (ports .queryIndex) base []
          ((base (ports .queryReverse)).reverse ++ base (ports .queryIndex))⟩ := by
  have h := Reduction.MachineTransfer.transferAt_fromTapes
    (ports .queryReverse) (ports .queryIndex)
    (fun h => (by decide : Tape.queryReverse ≠ .queryIndex) (distinct h))
    id false (labels (reversePhaseLabel second))
    (some (labels (lookupPhaseLabel second (.run .copyFirst)))) target
    (by cases second <;> exact code _) base ambient register
  unfold Reduction.MachineTransfer.nextAt at h
  unfold advance
  simpa only [List.map_id] using h

theorem reversePhaseTrace_unary (index : Nat) (suffix : List Bool)
    (queryWord : base (ports .queryReverse) = (encodeWord index).reverse)
    (indexWord : base (ports .queryIndex) = suffix) :
    (advance (TM2.step target))^[index + 2]
      (some ⟨some (labels (reversePhaseLabel second)), (ambient, register), base⟩) =
      some ⟨some (labels (lookupPhaseLabel second (.run .copyFirst))), (ambient, none),
        Reduction.MachineTransfer.tapesAt (ports .queryReverse) (ports .queryIndex) base []
          (encodeWord index ++ suffix)⟩ := by
  have h := reversePhaseTrace second positive H ports distinct labels exit target code
    base ambient register
  simpa only [queryWord, indexWord, List.length_reverse, encodeWord_length,
    List.reverse_reverse, Nat.add_assoc] using h

end Reverse

end DFVSGames.Foundations.Complexity.MachineExpanderRow
end

section

namespace DFVSGames.Foundations.Complexity.MachineExpanderRow

open Turing MachineComposition
open PCP.ExpanderTables PCP.ExpanderRowControl

variable {K Λ ρ : Type} [DecidableEq K]

def cleanupSteps (ports : Tape → K) (base : K → List Bool) : Nat :=
  ((base (ports .queryIndex)).length + 1) +
  ((base (ports .lookupOutput)).length + 1) +
  ((base (ports .quotientFirst)).length + 1) +
  ((base (ports .quotientSecond)).length + 1) +
  ((base (ports .remainderFirst)).length + 1) +
  ((base (ports .remainderSecond)).length + 1)

variable [Fintype ρ] {d : Nat}

theorem cleanupOneTraceAt (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (code : ∀ label, target (labels label) = statement positive H ports labels exit label)
    (i : Fin 6) (base : K → List Bool) (state : State ρ d) :
    (advance (TM2.step target))^[((base (ports (dirtyTape i))).length + 1)]
      (some ⟨some (labels (.cleanup i)), state, base⟩) =
      some ⟨some (if hi : i.val + 1 < 6 then labels (.cleanup ⟨i.val + 1, hi⟩)
          else labels .done),
        (state.1, none), Function.update base (ports (dirtyTape i)) []⟩ := by
  have run := MachineDrain.drainTrace (ports (dirtyTape i)) (labels (.cleanup i))
    (some (if hi : i.val + 1 < 6 then labels (.cleanup ⟨i.val + 1, hi⟩)
      else labels .done)) target
    (by simpa only [statement] using code (.cleanup i))
    base (base (ports (dirtyTape i))) state.1 state.2
  simpa only [Function.update_eq_self] using run

theorem cleanupTraceAt (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (distinct : Function.Injective ports)
    (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (code : ∀ label, target (labels label) = statement positive H ports labels exit label)
    (base : K → List Bool) (state : State ρ d) :
    (advance (TM2.step target))^[cleanupSteps ports base]
      (some ⟨some (labels (.cleanup 0)), state, base⟩) =
      some ⟨some (labels .done), (state.1, none), cleanupTapes ports base⟩ := by
  let t1 := Function.update base (ports .queryIndex) []
  let t2 := Function.update t1 (ports .lookupOutput) []
  let t3 := Function.update t2 (ports .quotientFirst) []
  let t4 := Function.update t3 (ports .quotientSecond) []
  let t5 := Function.update t4 (ports .remainderFirst) []
  have h0 := cleanupOneTraceAt positive H ports labels exit target code 0 base state
  have h1 := cleanupOneTraceAt positive H ports labels exit target code 1 t1 (state.1, none)
  have h2 := cleanupOneTraceAt positive H ports labels exit target code 2 t2 (state.1, none)
  have h3 := cleanupOneTraceAt positive H ports labels exit target code 3 t3 (state.1, none)
  have h4 := cleanupOneTraceAt positive H ports labels exit target code 4 t4 (state.1, none)
  have h5 := cleanupOneTraceAt positive H ports labels exit target code 5 t5 (state.1, none)
  simp [t1, t2, t3, t4, t5, distinct.eq_iff,
    -Function.iterate_succ] at h0 h1 h2 h3 h4 h5
  have finished := join_trace_inline_MachineExpanderRowCleanup (join_trace_inline_MachineExpanderRowCleanup (join_trace_inline_MachineExpanderRowCleanup (join_trace_inline_MachineExpanderRowCleanup (join_trace_inline_MachineExpanderRowCleanup h0 h1) h2) h3) h4) h5
  simpa only [cleanupSteps, cleanupTapes] using finished

theorem doneStepAt (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (code : ∀ label, target (labels label) = statement positive H ports labels exit label)
    (base : K → List Bool) (state : State ρ d) :
    TM2.step target ⟨some (labels .done), state, base⟩ = some ⟨exit, state, base⟩ := by
  change some (TM2.stepAux (target (labels .done)) state base) = _
  rw [code]
  cases exit <;> rfl

theorem cleanupExitTraceAt (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (distinct : Function.Injective ports)
    (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (code : ∀ label, target (labels label) = statement positive H ports labels exit label)
    (base : K → List Bool) (state : State ρ d) :
    (advance (TM2.step target))^[cleanupSteps ports base + 1]
      (some ⟨some (labels (.cleanup 0)), state, base⟩) =
      some ⟨exit, (state.1, none), cleanupTapes ports base⟩ := by
  have cleaned := cleanupTraceAt positive H ports distinct labels exit target code base state
  have done : (advance (TM2.step target))^[1]
      (some ⟨some (labels .done), (state.1, none), cleanupTapes ports base⟩) =
      some ⟨exit, (state.1, none), cleanupTapes ports base⟩ := by
    simpa only [Function.iterate_one, advance_some] using
      doneStepAt positive H ports labels exit target code (cleanupTapes ports base) (state.1, none)
  exact join_trace_inline_MachineExpanderRowCleanup cleaned done

theorem initializeStepAt (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (distinct : Function.Injective ports)
    (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (code : ∀ label, target (labels label) = statement positive H ports labels exit label)
    (base : K → List Bool) (state : State ρ d) :
    TM2.step target ⟨some (labels .initialize_), state, base⟩ =
      some ⟨some (labels (.firstEmit (PCP.AlphabetTable.Emitter.labelAt 3 _ 0 .entry))),
        (state.1, none), initializedTapes ports base⟩ := by
  change some (TM2.stepAux (target (labels .initialize_)) state base) = _
  rw [code]
  simp [statement, TM2.stepAux, initializedTapes, distinct.eq_iff]

theorem clearQueryStepAt (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (distinct : Function.Injective ports)
    (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (code : ∀ label, target (labels label) = statement positive H ports labels exit label)
    (base : K → List Bool) (state : State ρ d) :
    TM2.step target ⟨some (labels .clearQuery), state, base⟩ =
      some ⟨some (labels (.secondEmit (PCP.AlphabetTable.Emitter.labelAt 3 _ 0 .entry))),
        state, clearedQueryTapes ports base⟩ := by
  change some (TM2.stepAux (target (labels .clearQuery)) state base) = _
  rw [code]
  simp [statement, TM2.stepAux, clearedQueryTapes, distinct.eq_iff]

end DFVSGames.Foundations.Complexity.MachineExpanderRow
end

section

namespace DFVSGames.Foundations.Complexity.MachineExpanderRow

open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords

namespace RowData

variable {v d : Nat} (r : RowData v d)

def tableLength : Nat := (encodeWords (rotationWords r.oldTable)).length

theorem query1_eq_firstRow : r.query1 = r.firstRow.val :=
  firstAddress_eq_rowIndex r.inputVertex r.control0

theorem query2_eq_secondRow : r.query2 = r.secondRow.val :=
  secondAddress_eq_rowIndex r.firstVertex r.control1

theorem firstReturn_eq_residue (positive : 0 < d) :
    r.firstReturn = MachineFixedDivMod.residue (degree d) (Nat.mul_pos positive positive)
      r.firstValue := Fin.ext rfl

theorem secondReturn_eq_residue (positive : 0 < d) :
    r.secondReturn = MachineFixedDivMod.residue (degree d) (Nat.mul_pos positive positive)
      r.secondValue := Fin.ext rfl

theorem rows_le_tableLength : v * degree d ≤ r.tableLength := by
  simp only [tableLength, encodeWords_length, rotationWords_length]
  omega

theorem query1_le_tableLength : r.query1 ≤ r.tableLength := by
  rw [query1_eq_firstRow]
  exact r.firstRow.isLt.le.trans r.rows_le_tableLength

theorem query2_le_tableLength : r.query2 ≤ r.tableLength := by
  rw [query2_eq_secondRow]
  exact r.secondRow.isLt.le.trans r.rows_le_tableLength

theorem firstValue_le_tableLength : r.firstValue ≤ r.tableLength :=
  (reverseIndex r.oldTable r.firstRow).isLt.le.trans r.rows_le_tableLength

theorem secondValue_le_tableLength : r.secondValue ≤ r.tableLength :=
  (reverseIndex r.oldTable r.secondRow).isLt.le.trans r.rows_le_tableLength

theorem inputVertex_le_tableLength : r.inputVertex.val ≤ r.tableLength := by
  have hq : 1 ≤ degree d := Nat.zero_lt_of_lt r.inputPort.isLt
  have hv : v ≤ v * degree d := by simpa using Nat.mul_le_mul_left v hq
  exact r.inputVertex.isLt.le.trans (hv.trans r.rows_le_tableLength)

theorem firstVertex_le_tableLength : r.firstVertex.val ≤ r.tableLength := by
  rw [← firstValue_div_degree]
  exact (Nat.div_le_self r.firstValue (degree d)).trans r.firstValue_le_tableLength

theorem secondVertex_le_tableLength : r.secondVertex.val ≤ r.tableLength := by
  rw [← secondValue_div_degree]
  exact (Nat.div_le_self r.secondValue (degree d)).trans r.secondValue_le_tableLength

theorem firstReturn_le_tableLength : r.firstReturn.val ≤ r.tableLength := by
  rw [← firstValue_mod_degree]
  exact (Nat.mod_le r.firstValue (degree d)).trans r.firstValue_le_tableLength

theorem secondReturn_le_tableLength : r.secondReturn.val ≤ r.tableLength := by
  rw [← secondValue_mod_degree]
  exact (Nat.mod_le r.secondValue (degree d)).trans r.secondValue_le_tableLength

end RowData

variable {v d : Nat}

theorem final_frame_eq (r : RowData v d) (output : List Bool) :
    frame12 r output = emittedWord .output (frame0 r output) r.finalValue := by
  funext tape
  cases tape <;> simp [frame0, emittedWord, frameContents]

theorem cleanupSteps_le_tableLength (r : RowData v d) (output : List Bool) :
    cleanupSteps id (frame11 r output) ≤ 6 * (r.tableLength + 1) + 6 := by
  have h1 := r.firstVertex_le_tableLength
  have h2 := r.secondVertex_le_tableLength
  have h3 := r.firstReturn_le_tableLength
  have h4 := r.secondReturn_le_tableLength
  simp only [cleanupSteps, frame11_eq, id_eq, frameContents, encodeWord_length]
  omega

end DFVSGames.Foundations.Complexity.MachineExpanderRow
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineExpanderRow
attribute [-instance] _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.Complexity.MachineExpanderRow

open Turing MachineComposition
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords PCP.AlphabetTable

def rowSteps {v d : Nat} (r : RowData v d) (output : List Bool) : Nat :=
  1 + emitSteps r.inputVertex.val + (r.query1 + 2) +
    MachinePreservingLookupClean.steps (rotationWords r.oldTable) r.firstRow.val +
    (r.firstValue + 2) + 1 + emitSteps r.firstVertex.val + (r.query2 + 2) +
    MachinePreservingLookupClean.steps (rotationWords r.oldTable) r.secondRow.val +
    (r.secondValue + 2) + emitSteps r.secondVertex.val +
    (cleanupSteps id (frame11 r output) + 1)

theorem rowSteps_le {v d : Nat} (r : RowData v d) (output : List Bool) :
    rowSteps r output ≤ 80 * (r.tableLength + 1) := by
  have lookup1 := MachinePreservingLookupClean.steps_le (rotationWords r.oldTable)
    r.firstRow.val r.firstValue (rotationWords_getElem? r.oldTable r.firstRow)
  have lookup2 := MachinePreservingLookupClean.steps_le (rotationWords r.oldTable)
    r.secondRow.val r.secondValue (rotationWords_getElem? r.oldTable r.secondRow)
  have h0 := r.inputVertex_le_tableLength
  have h1 := r.query1_le_tableLength
  have h2 := r.firstValue_le_tableLength
  have h3 := r.firstVertex_le_tableLength
  have h4 := r.query2_le_tableLength
  have h5 := r.secondValue_le_tableLength
  have h6 := r.secondVertex_le_tableLength
  have clean := cleanupSteps_le_tableLength r output
  change _ ≤ 6 * r.tableLength + 4 at lookup1 lookup2
  simp only [rowSteps, emitSteps]
  omega

end DFVSGames.Foundations.Complexity.MachineExpanderRow
end

section

namespace DFVSGames.Foundations.Complexity.MachineExpanderTable

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl

variable {ρ : Type} {d : Nat}

theorem nextPosition_val_of_lt (positive : 0 < d) (position : Position d)
    (more : position.val + 1 < rowFactor d) :
    (nextPosition positive position).val = position.val + 1 := Nat.mod_eq_of_lt more

theorem boundaryTapes_update_count (vertex remaining next : Nat)
    (oldTable output countSuffix result : List Bool) :
    Function.update (boundaryTapes vertex remaining oldTable output countSuffix result)
      (.inr .vertexCount) (encodeWord next ++ countSuffix) =
      boundaryTapes vertex next oldTable output countSuffix result := by
  funext tape
  rcases tape with row | extra
  · cases row <;> simp [boundaryTapes, rowTapes, MachineEmbedding.tapes, Function.update]
  · cases extra <;> simp [boundaryTapes, extraTapes, MachineEmbedding.tapes, Function.update]

theorem boundaryTapes_increment_vertex (vertex remaining : Nat)
    (oldTable output countSuffix result : List Bool) :
    Function.update (boundaryTapes vertex remaining oldTable output countSuffix result)
      (.inl .inputVertex) (true :: encodeWord vertex) =
      boundaryTapes (vertex + 1) remaining oldTable output countSuffix result := by
  funext tape
  rcases tape with row | extra
  · cases row <;>
      simp [boundaryTapes, rowTapes, MachineEmbedding.tapes, Function.update,
        encodeWord, List.replicate_succ]
  · cases extra <;>
      simp [boundaryTapes, extraTapes, MachineEmbedding.tapes, Function.update]

theorem initialTapes_initialize (vertices : Nat) (oldTable countSuffix : List Bool) :
    Function.update (initialTapes vertices oldTable countSuffix) (.inl .inputVertex) [false] =
      boundaryTapes 0 vertices oldTable [] countSuffix [] := by
  funext tape
  rcases tape with row | extra
  · cases row <;>
      simp [initialTapes, boundaryTapes, rowTapes, MachineEmbedding.tapes,
        Function.update, encodeWord]
  · cases extra <;>
      simp [initialTapes, boundaryTapes, extraTapes, MachineEmbedding.tapes,
        Function.update]

variable [Fintype ρ]

theorem initializeStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (base : ∀ tape, List (Alphabet tape)) (state : State ρ d) :
    TM2.step (program positive H) ⟨some (.inr .initialize_), state, base⟩ =
      some ⟨some (.inr .vertexGuard), resetState positive H state,
        Function.update base (.inl .inputVertex) (false :: base (.inl .inputVertex))⟩ := by
  change some (TM2.stepAux (program positive H (.inr .initialize_)) state base) = _
  rw [program_outer]
  rfl

theorem initialize_boundaryStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (vertices : Nat) (oldTable countSuffix : List Bool) (state : State ρ d) :
    TM2.step (program positive H)
      ⟨some (.inr .initialize_), state, initialTapes vertices oldTable countSuffix⟩ =
      some ⟨some (.inr .vertexGuard), initialState positive H (caller state),
        boundaryTapes 0 vertices oldTable [] countSuffix []⟩ := by
  have h := initializeStep positive H (initialTapes vertices oldTable countSuffix) state
  have input : initialTapes vertices oldTable countSuffix (.inl .inputVertex) = [] := rfl
  simp only [input, resetState] at h
  exact h.trans (congrArg
    (fun tapes : ∀ tape, List (Alphabet tape) =>
      (some ⟨some (.inr .vertexGuard), initialState positive H (caller state), tapes⟩ :
        Option (TM2.Cfg Alphabet (Label d) (State ρ d))))
    (initialTapes_initialize vertices oldTable countSuffix))

theorem vertexGuard_succStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (base : ∀ tape, List (Alphabet tape)) (state : State ρ d)
    (remaining : Nat) (suffix : List Bool)
    (counter : base (.inr .vertexCount) = encodeWord (remaining + 1) ++ suffix) :
    TM2.step (program positive H) ⟨some (.inr .vertexGuard), state, base⟩ =
      some ⟨some (.inr .prepareRow), clearRegister state,
        Function.update base (.inr .vertexCount) (encodeWord remaining ++ suffix)⟩ := by
  change some (TM2.stepAux (program positive H (.inr .vertexGuard)) state base) = _
  rw [program_outer]
  simp [outerStatement, MachineControl.statement, vertexGuardCore, TM2.stepAux,
    guardStates, clearRegister, counter, encodeWord, List.replicate_succ]

theorem vertexGuard_zeroStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (base : ∀ tape, List (Alphabet tape)) (state : State ρ d)
    (suffix : List Bool)
    (counter : base (.inr .vertexCount) = encodeWord 0 ++ suffix) :
    TM2.step (program positive H) ⟨some (.inr .vertexGuard), state, base⟩ =
      some ⟨some (.inr .reverseOutput), clearRegister state, base⟩ := by
  change some (TM2.stepAux (program positive H (.inr .vertexGuard)) state base) = _
  rw [program_outer]
  simp [outerStatement, MachineControl.statement, vertexGuardCore, TM2.stepAux,
    guardStates, clearRegister, counter, encodeWord]

theorem vertexGuard_boundary_succStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (vertex remaining : Nat) (oldTable output countSuffix result : List Bool)
    (state : State ρ d) :
    TM2.step (program positive H)
      ⟨some (.inr .vertexGuard), state,
        boundaryTapes vertex (remaining + 1) oldTable output countSuffix result⟩ =
      some ⟨some (.inr .prepareRow), clearRegister state,
        boundaryTapes vertex remaining oldTable output countSuffix result⟩ := by
  simpa only [boundaryTapes_update_count] using
    vertexGuard_succStep positive H
      (boundaryTapes vertex (remaining + 1) oldTable output countSuffix result)
      state remaining countSuffix rfl

theorem vertexGuard_boundary_zeroStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (vertex : Nat) (oldTable output countSuffix result : List Bool) (state : State ρ d) :
    TM2.step (program positive H)
      ⟨some (.inr .vertexGuard), state,
        boundaryTapes vertex 0 oldTable output countSuffix result⟩ =
      some ⟨some (.inr .reverseOutput), clearRegister state,
        boundaryTapes vertex 0 oldTable output countSuffix result⟩ :=
  vertexGuard_zeroStep positive H
    (boundaryTapes vertex 0 oldTable output countSuffix result) state countSuffix rfl

theorem prepareRowStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (base : ∀ tape, List (Alphabet tape)) (state : State ρ d) :
    TM2.step (program positive H) ⟨some (.inr .prepareRow), state, base⟩ =
      some ⟨some (.inl .initialize_), prepareState positive H state, base⟩ := by
  change some (TM2.stepAux (program positive H (.inr .prepareRow)) state base) = _
  rw [program_outer]
  rfl

theorem afterRow_moreStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (base : ∀ tape, List (Alphabet tape)) (state : State ρ d)
    (more : state.2.val + 1 < rowFactor d) :
    TM2.step (program positive H) ⟨some (.inr .afterRow), state, base⟩ =
      some ⟨some (.inr .prepareRow), advancePositionState positive state, base⟩ := by
  change some (TM2.stepAux (program positive H (.inr .afterRow)) state base) = _
  rw [program_outer]
  simp [outerStatement, TM2.stepAux, more]

theorem afterRow_lastStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (base : ∀ tape, List (Alphabet tape)) (state : State ρ d)
    (last : ¬ state.2.val + 1 < rowFactor d) :
    TM2.step (program positive H) ⟨some (.inr .afterRow), state, base⟩ =
      some ⟨some (.inr .vertexGuard), resetPositionState positive state,
        Function.update base (.inl .inputVertex) (true :: base (.inl .inputVertex))⟩ := by
  change some (TM2.stepAux (program positive H (.inr .afterRow)) state base) = _
  rw [program_outer]
  simp [outerStatement, TM2.stepAux, last]

theorem afterRow_last_boundaryStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (vertex remaining : Nat) (oldTable output countSuffix result : List Bool)
    (state : State ρ d) (last : ¬ state.2.val + 1 < rowFactor d) :
    TM2.step (program positive H)
      ⟨some (.inr .afterRow), state,
        boundaryTapes vertex remaining oldTable output countSuffix result⟩ =
      some ⟨some (.inr .vertexGuard), resetPositionState positive state,
        boundaryTapes (vertex + 1) remaining oldTable output countSuffix result⟩ := by
  have input : boundaryTapes vertex remaining oldTable output countSuffix result
      (.inl .inputVertex) = encodeWord vertex := rfl
  have h := afterRow_lastStep positive H
    (boundaryTapes vertex remaining oldTable output countSuffix result) state last
  simp only [input] at h
  exact h.trans (congrArg
    (fun tapes : ∀ tape, List (Alphabet tape) =>
      (some ⟨some (.inr .vertexGuard), resetPositionState positive state, tapes⟩ :
        Option (TM2.Cfg Alphabet (Label d) (State ρ d))))
    (boundaryTapes_increment_vertex vertex remaining oldTable output countSuffix result))

theorem reverseOutput_consStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (base : ∀ tape, List (Alphabet tape)) (state : State ρ d)
    (symbol : Bool) (word : List Bool) (source : base (.inl .output) = symbol :: word) :
    TM2.step (program positive H) ⟨some (.inr .reverseOutput), state, base⟩ =
      some ⟨some (.inr .reverseOutput), ((state.1.1, some symbol), state.2),
        Function.update (Function.update base (.inl .output) word)
          (.inr .result) (symbol :: base (.inr .result))⟩ := by
  change some (TM2.stepAux (program positive H (.inr .reverseOutput)) state base) = _
  rw [program_outer]
  simp [outerStatement, MachineControl.statement, Reduction.MachineTransfer.loopAt,
    Reduction.MachineTransfer.exitAt, TM2.stepAux, guardStates, source]

theorem reverseOutput_nilStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (base : ∀ tape, List (Alphabet tape)) (state : State ρ d)
    (source : base (.inl .output) = []) :
    TM2.step (program positive H) ⟨some (.inr .reverseOutput), state, base⟩ =
      some ⟨some (.inr .done), clearRegister state, base⟩ := by
  have same : Function.update base (.inl .output) [] = base := by
    simpa only [source] using Function.update_eq_self (.inl .output) base
  change some (TM2.stepAux (program positive H (.inr .reverseOutput)) state base) = _
  rw [program_outer]
  simp [outerStatement, MachineControl.statement, Reduction.MachineTransfer.loopAt,
    Reduction.MachineTransfer.exitAt, TM2.stepAux, guardStates, clearRegister, source, same]

theorem doneStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (base : ∀ tape, List (Alphabet tape)) (state : State ρ d) :
    TM2.step (program positive H) ⟨some (.inr .done), state, base⟩ =
      some ⟨none, state, base⟩ := by
  change some (TM2.stepAux (program positive H (.inr .done)) state base) = _
  rw [program_outer]
  rfl

end DFVSGames.Foundations.Complexity.MachineExpanderTable
end

section

namespace DFVSGames.Foundations.PCP.ExpanderTableEnumeration

open ExpanderTables ExpanderRowControl ExpanderTableWords
open DFVSGames.Foundations.Complexity

variable {v d : Nat}

theorem vertexWords_drop_succ (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (vertex : Fin v) (position : Fin (rowFactor d)) :
    (vertexWords G H vertex).drop position.val =
      rowValue G H vertex position :: (vertexWords G H vertex).drop (position.val + 1) := by
  rw [List.drop_eq_getElem_cons (by simp)]
  simp [vertexWords]

theorem vertexWords_drop_last (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (vertex : Fin v) (position : Fin (rowFactor d))
    (last : position.val + 1 = rowFactor d) :
    (vertexWords G H vertex).drop position.val = [rowValue G H vertex position] := by
  rw [vertexWords_drop_succ, last, vertexWords_drop_full]

theorem priorVertices_succ (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (k : Nat) (hk : k < v) :
    priorVertices G H (k + 1) = priorVertices G H k ++ vertexWords G H ⟨k, hk⟩ := by
  unfold priorVertices
  rw [List.take_succ_eq_append_getElem (by simpa using hk), List.flatten_append]
  simp

theorem accumulate_eq (values : List Nat) (initial : List Bool) :
    accumulate values initial = (encodeWords values).reverse ++ initial := by
  induction values generalizing initial with
  | nil => simp [accumulate, encodeWords]
  | cons value values ih =>
      simpa only [accumulate, List.foldl_cons, encodeWords, List.reverse_append,
        List.append_assoc] using ih ((encodeWord value).reverse ++ initial)

theorem accumulate_append (first second : List Nat) (initial : List Bool) :
    accumulate (first ++ second) initial = accumulate second (accumulate first initial) := by
  simp only [accumulate, List.foldl_append]

theorem accumulate_generatedWords (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (initial : List Bool) :
    accumulate (generatedWords G H) initial =
      (encodeWords (rotationWords (step G H))).reverse ++ initial := by
  rw [accumulate_eq, generatedWords_eq_rotationWords]

theorem encode_generatedWords_length_le (G : Table v (degree d)) (H : Table (cloudSize d) d) :
    (encodeWords (generatedWords G H)).length ≤
      (v * rowFactor d) * (v * rowFactor d + 1) := by
  rw [generatedWords_eq_rotationWords, rowCount_eq]
  exact encode_rotationWords_length_le (step G H)

end DFVSGames.Foundations.PCP.ExpanderTableEnumeration

end

section

namespace DFVSGames.Foundations.Complexity.MachineExpanderTable

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords
open PCP.ExpanderTableEnumeration

theorem tableRowData_finalValue {v d : Nat} (G : Table v (degree d))
    (H : Table (cloudSize d) d) (vertex : Fin v) (position : Position d) :
    (tableRowData G H vertex position).finalValue = rowValue G H vertex position := rfl

theorem tableRowData_frame0 {v d : Nat} (G : Table v (degree d))
    (H : Table (cloudSize d) d) (vertex : Fin v) (position : Position d) (output : List Bool) :
    MachineExpanderRow.frame0 (tableRowData G H vertex position) output =
      rowTapes vertex.val (encodeWords (rotationWords G)) output := by
  funext tape
  cases tape <;> rfl

theorem tableRowData_finalFrame {v d : Nat} (G : Table v (degree d))
    (H : Table (cloudSize d) d) (vertex : Fin v) (position : Position d) (output : List Bool) :
    MachineExpanderRow.emittedWord .output
      (MachineExpanderRow.frame0 (tableRowData G H vertex position) output)
      (tableRowData G H vertex position).finalValue =
      rowTapes vertex.val (encodeWords (rotationWords G))
        ((encodeWord (rowValue G H vertex position)).reverse ++ output) := by
  rw [tableRowData_frame0, tableRowData_finalValue]
  funext tape
  cases tape <;> simp [MachineExpanderRow.emittedWord, rowTapes]

variable {ρ : Type} [Fintype ρ] {v d : Nat}

structure VertexSuffixRun (positive : 0 < d) (G : Table v (degree d))
    (H : Table (cloudSize d) d) (vertex : Fin v) (state : State ρ d)
    (remaining : Nat) (output countSuffix result : List Bool) where
  finalState : State ρ d
  caller_preserved : caller finalState = caller state
  position_zero : finalState.2 = zeroPosition positive
  execution : StateTransition.EvalsToInTime (TM2.step (program positive H))
    ⟨some (.inr .prepareRow), state,
      boundaryTapes vertex.val remaining (encodeWords (rotationWords G)) output countSuffix result⟩
    (some ⟨some (.inr .vertexGuard), finalState,
      boundaryTapes (vertex.val + 1) remaining (encodeWords (rotationWords G))
        (accumulate ((vertexWords G H vertex).drop state.2.val) output) countSuffix result⟩)
    ((rowFactor d - state.2.val) * (80 * ((encodeWords (rotationWords G)).length + 1) + 2))

structure VertexRun (positive : 0 < d) (G : Table v (degree d))
    (H : Table (cloudSize d) d) (vertex : Fin v) (state : State ρ d)
    (remaining : Nat) (output countSuffix result : List Bool) where
  finalState : State ρ d
  caller_preserved : caller finalState = caller state
  position_zero : finalState.2 = zeroPosition positive
  execution : StateTransition.EvalsToInTime (TM2.step (program positive H))
    ⟨some (.inr .prepareRow), state,
      boundaryTapes vertex.val remaining (encodeWords (rotationWords G)) output countSuffix result⟩
    (some ⟨some (.inr .vertexGuard), finalState,
      boundaryTapes (vertex.val + 1) remaining (encodeWords (rotationWords G))
        (accumulate (vertexWords G H vertex) output) countSuffix result⟩)
    (rowFactor d * (80 * ((encodeWords (rotationWords G)).length + 1) + 2))

end DFVSGames.Foundations.Complexity.MachineExpanderTable
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineExpanderTableLoop
attribute [-instance] _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.Complexity.MachineExpanderTable

open Turing MachineComposition
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords
open PCP.ExpanderTableEnumeration

theorem accumulatedVertices_succ {v d : Nat} (G : Table v (degree d))
    (H : Table (cloudSize d) d) (current : Nat) (valid : current < v) :
    accumulatedVertices G H (current + 1) =
      accumulate (vertexWords G H ⟨current, valid⟩) (accumulatedVertices G H current) := by
  simp only [accumulatedVertices, priorVertices_succ G H current valid, accumulate_append]

theorem accumulatedVertices_full {v d : Nat} (G : Table v (degree d))
    (H : Table (cloudSize d) d) : accumulatedVertices G H v =
      (encodeWords (rotationWords (step G H))).reverse := by
  simp [accumulatedVertices, accumulate_generatedWords]

def vertexBodyBudget {v d : Nat} (G : Table v (degree d)) : Nat :=
  rowFactor d * (80 * ((oldTableWord G).length + 1) + 2)

def vertexLoopBudget {v d : Nat} (G : Table v (degree d)) (remaining : Nat) : Nat :=
  remaining * (vertexBodyBudget G + 1) + 1

def vertexLoopTapes {v d : Nat} (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (current remaining : Nat) (suffix : List Bool) : ∀ tape, List (Alphabet tape) :=
  boundaryTapes current remaining (oldTableWord G) (accumulatedVertices G H current) suffix []

structure VertexLoopRun {v d : Nat} {ρ : Type} [Fintype ρ]
    (positive : 0 < d) (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (current remaining : Nat) (state : State ρ d) (suffix : List Bool) where
  finalState : State ρ d
  caller_preserved : caller finalState = caller state
  position_zero : finalState.2 = zeroPosition positive
  execution : StateTransition.EvalsToInTime (TM2.step (program positive H))
    ⟨some (.inr .vertexGuard), state, vertexLoopTapes G H current remaining suffix⟩
    (some ⟨some (.inr .reverseOutput), finalState, vertexLoopTapes G H v 0 suffix⟩)
    (vertexLoopBudget G remaining)

end DFVSGames.Foundations.Complexity.MachineExpanderTable
end

section

namespace DFVSGames.Foundations.Complexity.MachineExpanderTable

open Turing
open MachineComposition
open PCP.ExpanderTables PCP.ExpanderRowControl

variable {ρ : Type} {d : Nat}

theorem boundaryTapes_reverse_update (vertex remaining : Nat)
    (oldTable output countSuffix result nextOutput nextResult : List Bool) :
    Function.update
      (Function.update (boundaryTapes vertex remaining oldTable output countSuffix result)
        (.inl .output) nextOutput)
      (.inr .result) nextResult =
      boundaryTapes vertex remaining oldTable nextOutput countSuffix nextResult := by
  funext tape
  rcases tape with row | extra
  · cases row <;>
      simp [boundaryTapes, rowTapes, MachineEmbedding.tapes, Function.update]
  · cases extra <;>
      simp [boundaryTapes, extraTapes, MachineEmbedding.tapes, Function.update]

variable [Fintype ρ]

theorem reverseOutputTrace (positive : 0 < d) (H : Table (cloudSize d) d)
    (vertex remaining : Nat) (oldTable output countSuffix result : List Bool)
    (state : State ρ d) :
    (advance (TM2.step (program positive H)))^[output.length + 1]
      (some ⟨some (.inr .reverseOutput), state,
        boundaryTapes vertex remaining oldTable output countSuffix result⟩) =
      some ⟨some (.inr .done), clearRegister state,
        boundaryTapes vertex remaining oldTable [] countSuffix (output.reverse ++ result)⟩ := by
  induction output generalizing result state with
  | nil =>
      simpa only [List.length_nil, Nat.zero_add, Function.iterate_one, advance_some,
        List.reverse_nil, List.nil_append] using
        reverseOutput_nilStep positive H
          (boundaryTapes vertex remaining oldTable [] countSuffix result) state rfl
  | cons symbol output ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [advance_some]
      rw [reverseOutput_consStep positive H
        (boundaryTapes vertex remaining oldTable (symbol :: output) countSuffix result)
        state symbol output rfl]
      change (advance (TM2.step (program positive H)))^[output.length + 1]
        (some ⟨some (.inr .reverseOutput), ((state.1.1, some symbol), state.2),
          Function.update
            (Function.update
              (boundaryTapes vertex remaining oldTable (symbol :: output) countSuffix result)
              (.inl .output) output)
            (.inr .result) (symbol :: result)⟩) = _
      rw [boundaryTapes_reverse_update]
      simpa only [clearRegister, List.reverse_cons, List.append_assoc,
        List.singleton_append] using
        ih (symbol :: result) ((state.1.1, some symbol), state.2)

theorem reverseOutputHaltTrace (positive : 0 < d) (H : Table (cloudSize d) d)
    (vertex remaining : Nat) (oldTable output countSuffix result : List Bool)
    (state : State ρ d) :
    (advance (TM2.step (program positive H)))^[output.length + 2]
      (some ⟨some (.inr .reverseOutput), state,
        boundaryTapes vertex remaining oldTable output countSuffix result⟩) =
      some ⟨none, clearRegister state,
        boundaryTapes vertex remaining oldTable [] countSuffix (output.reverse ++ result)⟩ := by
  rw [show output.length + 2 = (output.length + 1) + 1 by omega,
    Function.iterate_succ_apply',
    reverseOutputTrace positive H vertex remaining oldTable output countSuffix result state]
  exact doneStep positive H
    (boundaryTapes vertex remaining oldTable [] countSuffix (output.reverse ++ result))
    (clearRegister state)

def reverseOutputHaltInTime (positive : 0 < d) (H : Table (cloudSize d) d)
    (vertex remaining : Nat) (oldTable output countSuffix result : List Bool)
    (state : State ρ d) :
    StateTransition.EvalsToInTime (TM2.step (program positive H))
      ⟨some (.inr .reverseOutput), state,
        boundaryTapes vertex remaining oldTable output countSuffix result⟩
      (some ⟨none, clearRegister state,
        boundaryTapes vertex remaining oldTable [] countSuffix (output.reverse ++ result)⟩)
      (output.length + 2) where
  steps := output.length + 2
  evals_in_steps := reverseOutputHaltTrace positive H vertex remaining oldTable output countSuffix result state
  steps_le_m := Nat.le_refl _

end DFVSGames.Foundations.Complexity.MachineExpanderTable
end

section

namespace DFVSGames.Foundations.Complexity.MachineExpanderTable

open Turing MachineComposition
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords
open PCP.ExpanderTableEnumeration

def completeBudget {v d : Nat} (G : Table v (degree d)) (H : Table (cloudSize d) d) : Nat :=
  1 + vertexLoopBudget G v + ((encodeWords (rotationWords (step G H))).length + 2)

theorem vertices_le_word_length {v d : Nat} (positive : 0 < d)
    (G : Table v (degree d)) : v ≤ (oldTableWord G).length := by
  have hq : 1 ≤ degree d := Nat.mul_pos positive positive
  have hv : v ≤ v * degree d := by simpa using Nat.mul_le_mul_left v hq
  have hr : v * degree d ≤ (oldTableWord G).length := by
    simp only [oldTableWord, encodeWords_length, rotationWords_length]
    omega
  exact hv.trans hr

theorem completeBudget_le {v d : Nat} (positive : 0 < d)
    (G : Table v (degree d)) (H : Table (cloudSize d) d) :
    completeBudget G H ≤ (timePolynomial d).eval (oldTableWord G).length := by
  let L := (oldTableWord G).length
  let M := rowFactor d
  have vBound : v ≤ L + 1 := (vertices_le_word_length positive G).trans (Nat.le_succ L)
  have emitBound : 80 * (L + 1) + 2 ≤ 82 * (L + 1) := by omega
  have bodyBound : vertexBodyBudget G + 1 ≤ (82 * M + 1) * (L + 1) := by
    have mulBound := Nat.mul_le_mul_left M emitBound
    change M * (80 * (L + 1) + 2) + 1 ≤ _
    nlinarith
  have iterations := Nat.mul_le_mul vBound bodyBound
  have loopBound : v * (vertexBodyBudget G + 1) ≤ (82 * M + 1) * (L + 1)^2 := by
    calc
      _ ≤ (L + 1) * ((82 * M + 1) * (L + 1)) := iterations
      _ = _ := by ring
  have rowBound : v * M ≤ M * (L + 1) := by
    simpa only [Nat.mul_comm v M] using Nat.mul_le_mul_left M vBound
  have rowSuccBound : v * M + 1 ≤ (M + 1) * (L + 1) := by nlinarith
  have productBound := Nat.mul_le_mul rowBound rowSuccBound
  have lengthBound : (encodeWords (rotationWords (step G H))).length ≤
      M * (M + 1) * (L + 1)^2 := by
    calc
      _ ≤ (v * M) * (v * M + 1) := by
        simpa only [generatedWords_eq_rotationWords] using encode_generatedWords_length_le G H
      _ ≤ (M * (L + 1)) * ((M + 1) * (L + 1)) := productBound
      _ = _ := by ring
  have oneBound : 1 ≤ (L + 1)^2 := by nlinarith
  have combined := Nat.add_le_add loopBound lengthBound
  simp only [timePolynomial, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
  change completeBudget G H ≤ (M * (M + 1) + 82 * M + 5) * (L + 1)^2
  unfold completeBudget vertexLoopBudget
  nlinarith

structure TableRun {v d : Nat} {ρ : Type} [Fintype ρ]
    (positive : 0 < d) (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (state : State ρ d) (suffix : List Bool) where
  finalState : State ρ d
  caller_preserved : caller finalState = caller state
  position_zero : finalState.2 = zeroPosition positive
  execution : StateTransition.EvalsToInTime (TM2.step (program positive H))
    ⟨some (.inr .initialize_), state, initialTapes v (oldTableWord G) suffix⟩
    (some ⟨none, finalState,
      finalTapes v (oldTableWord G) (encodeWords (rotationWords (step G H))) suffix⟩)
    ((timePolynomial d).eval (oldTableWord G).length)

def initializeInTime_inline_MachineExpanderTable {v d : Nat} {ρ : Type} [Fintype ρ]
    (positive : 0 < d) (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (state : State ρ d) (suffix : List Bool) :
    StateTransition.EvalsToInTime (TM2.step (program positive H))
      ⟨some (.inr .initialize_), state, initialTapes v (oldTableWord G) suffix⟩
      (some ⟨some (.inr .vertexGuard), initialState positive H (caller state),
        vertexLoopTapes G H 0 v suffix⟩) 1 where
  steps := 1
  evals_in_steps := by
    change TM2.step (program (ρ := ρ) positive H)
      ⟨some (.inr .initialize_), state, initialTapes v (oldTableWord G) suffix⟩ =
      some ⟨some (.inr .vertexGuard), initialState positive H (caller state),
        vertexLoopTapes G H 0 v suffix⟩
    simpa only [vertexLoopTapes, accumulatedVertices_zero] using
      initialize_boundaryStep positive H v (oldTableWord G) suffix state
  steps_le_m := Nat.le_refl _

end DFVSGames.Foundations.Complexity.MachineExpanderTable
end

section

namespace DFVSGames.Foundations.Complexity.MachineExpanderFamily

open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords

theorem boundaryTapes_eq_cycleTapes (remaining current : Nat) (word suffix : List Bool) :
    boundaryTapes remaining current word suffix =
      cycleTapes remaining word (encodeWord current) [] [] [] suffix := by
  funext tape
  rcases tape with tape | tape
  · rcases tape with row | extra
    · cases row <;> rfl
    · cases extra <;> rfl
  · cases tape <;> rfl

def copyFrame (remaining current : Nat) (word suffix : List Bool) :
    (tape : Tape) → List (Alphabet tape) :=
  MachineEmbedding.tapes (MachineExpanderTable.initialTapes current word [])
    (extraFrame remaining current suffix)

def returnFrame (remaining current : Nat) (oldWord newWord suffix : List Bool) :
    (tape : Tape) → List (Alphabet tape) :=
  MachineEmbedding.tapes (MachineExpanderTable.finalTapes current oldWord newWord [])
    (extraFrame remaining current suffix)

def installedFrame (remaining current : Nat) (newWord suffix : List Bool) :
    (tape : Tape) → List (Alphabet tape) :=
  cycleTapes remaining newWord [] (encodeWord current) (encodeWord 0) [] suffix

def multipliedFrame (d remaining current : Nat) (newWord suffix : List Bool) :
    (tape : Tape) → List (Alphabet tape) :=
  cycleTapes remaining newWord (encodeWord (cloudSize d * current))
    (encodeWord current) (encodeWord 0) [] suffix

theorem copyFrame_eq_cycleTapes (remaining current : Nat) (word suffix : List Bool) :
    copyFrame remaining current word suffix =
      cycleTapes remaining word (encodeWord current) [] (encodeWord current) [] suffix := by
  funext tape
  rcases tape with tape | tape
  · rcases tape with row | extra
    · cases row <;> rfl
    · cases extra <;> simp [copyFrame, MachineEmbedding.tapes,
        MachineExpanderTable.initialTapes, MachineExpanderTable.extraTapes,
        cycleTapes, fromBoolTapes, boolWord, cycleWords]
  · cases tape <;> rfl

theorem returnFrame_eq_cycleTapes (remaining current : Nat)
    (oldWord newWord suffix : List Bool) :
    returnFrame remaining current oldWord newWord suffix =
      cycleTapes remaining oldWord (encodeWord current) (encodeWord current)
        (encodeWord 0) newWord suffix := by
  funext tape
  rcases tape with tape | tape
  · rcases tape with row | extra
    · cases row <;> rfl
    · cases extra <;> simp [returnFrame, MachineEmbedding.tapes,
        MachineExpanderTable.finalTapes, MachineExpanderTable.boundaryTapes,
        MachineExpanderTable.extraTapes, cycleTapes, fromBoolTapes, boolWord, cycleWords]
  · cases tape <;> rfl

theorem copyFrame_eq_update (remaining current : Nat) (word suffix : List Bool) :
    Function.update (boundaryTapes remaining current word suffix)
      vertexCountTape (encodeWord current) = copyFrame remaining current word suffix := by
  rw [boundaryTapes_eq_cycleTapes, copyFrame_eq_cycleTapes]
  funext tape
  rcases tape with tape | tape
  · rcases tape with row | extra
    · cases row <;> rfl
    · cases extra <;> rfl
  · cases tape <;> rfl

theorem multipliedFrame_eq_update (d remaining current : Nat) (word suffix : List Bool) :
    Function.update (installedFrame remaining current word suffix)
      (.inr .currentSize) (encodeWord (cloudSize d * current)) =
      multipliedFrame d remaining current word suffix := by
  funext tape
  rcases tape with tape | tape
  · rcases tape with row | extra
    · cases row <;> rfl
    · cases extra <;> rfl
  · cases tape <;> rfl

end DFVSGames.Foundations.Complexity.MachineExpanderFamily
end

section

namespace DFVSGames.Foundations.Complexity.MachineExpanderFamilyBounds

open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords

def resizeCoefficient (d : Nat) : Nat :=
  MachineExpanderTable.timeCoefficient d * (degree d + 1) ^ 4 +
    3 * (degree d + 1) ^ 2 + 21

theorem wordLength_add_one_le {v q N : Nat} (G : Table v q) (hv : v ≤ N) :
    (encodeWords (rotationWords G)).length + 1 ≤ (q + 1)^2 * (N + 1)^2 := by
  have hlength := encode_rotationWords_length_le G
  have hrow : v * q + 1 ≤ (q + 1) * (N + 1) := by
    have h := Nat.mul_le_mul_right q hv
    nlinarith
  calc
    _ ≤ (v * q + 1)^2 := by nlinarith
    _ ≤ ((q + 1) * (N + 1))^2 := Nat.pow_le_pow_left hrow 2
    _ = _ := by ring

theorem resizeCost_le {v d : Nat} (G : Table v (degree d))
    (H : Table (cloudSize d) d) (N : Nat) (hv : v ≤ N)
    (hnext : v * cloudSize d ≤ N) :
    resizeCost G H ≤ resizeCoefficient d * (N + 1)^4 := by
  let oldL := (MachineExpanderTable.oldTableWord G).length
  let newL := (encodeWords (rotationWords (step G H))).length
  have oldBound : oldL + 1 ≤ (degree d + 1)^2 * (N + 1)^2 :=
    wordLength_add_one_le G hv
  have newBound : newL + 1 ≤ (degree d + 1)^2 * (N + 1)^2 :=
    wordLength_add_one_le (step G H) hnext
  have timeBound : (MachineExpanderTable.timePolynomial d).eval oldL ≤
      MachineExpanderTable.timeCoefficient d * (degree d + 1)^4 * (N + 1)^4 := by
    simp only [MachineExpanderTable.timePolynomial, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_one]
    calc
      _ ≤ MachineExpanderTable.timeCoefficient d *
          ((degree d + 1)^2 * (N + 1)^2)^2 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left oldBound 2)
      _ = _ := by ring
  have pow24 : (N + 1)^2 ≤ (N + 1)^4 :=
    Nat.pow_le_pow_right (Nat.succ_pos N) (by decide)
  have overheadBound : oldL + 2 * newL ≤
      3 * (degree d + 1)^2 * (N + 1)^4 := by
    have h := Nat.mul_le_mul_left ((degree d + 1)^2) pow24
    calc
      _ ≤ 3 * ((degree d + 1)^2 * (N + 1)^2) := by omega
      _ ≤ 3 * ((degree d + 1)^2 * (N + 1)^4) := Nat.mul_le_mul_left 3 h
      _ = _ := by ring
  have npow : N + 1 ≤ (N + 1)^4 := by
    simpa only [pow_one] using
      Nat.pow_le_pow_right (Nat.succ_pos N) (show 1 ≤ 4 by decide)
  have linearBound : 6 * v + 15 ≤ 21 * (N + 1)^4 := by omega
  change (MachineExpanderTable.timePolynomial d).eval oldL + 6 * v + oldL +
    2 * newL + 15 ≤ _
  unfold resizeCoefficient
  nlinarith only [timeBound, overheadBound, linearBound]

theorem resizeSum_succ {d : Nat} (H : Table (cloudSize d) d) (level : Nat) :
    resizeSum H (level + 1) = resizeSum H level + resizeCost (family H level) H := by
  simp only [resizeSum, Finset.sum_range_succ]

theorem resizeSum_le {d : Nat} (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (level : Nat) :
    resizeSum H level ≤ resizeCoefficient d * (vertexCount (degree d) level + 1)^5 := by
  let N := vertexCount (degree d) level
  have positive : 0 < degree d := by
    have h : 1 < degree d * degree d := growth
    nlinarith
  have hmono := vertexCount_monotone positive
  have hlevel : level ≤ N := level_le_vertexCount growth level
  have eachBound : ∀ i ∈ Finset.range level,
      resizeCost (family H i) H ≤ resizeCoefficient d * (N + 1)^4 := by
    intro i hi
    have hi' : i < level := Finset.mem_range.mp hi
    apply resizeCost_le (family H i) H N
    · exact hmono (by omega)
    · exact hmono (show i + 1 ≤ level by omega)
  have sumBound : resizeSum H level ≤ level * (resizeCoefficient d * (N + 1)^4) := by
    calc
      _ ≤ ∑ _i ∈ Finset.range level, resizeCoefficient d * (N + 1)^4 :=
        Finset.sum_le_sum eachBound
      _ = _ := by simp
  calc
    _ ≤ level * (resizeCoefficient d * (N + 1)^4) := sumBound
    _ ≤ (N + 1) * (resizeCoefficient d * (N + 1)^4) :=
      Nat.mul_le_mul_right _ (hlevel.trans (Nat.le_succ N))
    _ = _ := by ring

theorem familyBudget_le {d : Nat} (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (level : Nat) :
    familyBudget H level ≤
      (resizeCoefficient d + 4) * (vertexCount (degree d) level + 1)^5 := by
  have hsum := resizeSum_le H growth level
  have hlevel := level_le_vertexCount growth level
  have hpow : vertexCount (degree d) level + 1 ≤
      (vertexCount (degree d) level + 1)^5 := by
    simpa only [pow_one] using Nat.pow_le_pow_right
      (Nat.succ_pos (vertexCount (degree d) level)) (show 1 ≤ 5 by decide)
  have overhead : level + 3 ≤ 4 * (vertexCount (degree d) level + 1)^5 := by omega
  unfold familyBudget
  nlinarith only [hsum, overhead]

theorem paddedSize_le_succ_input (k : Nat) :
    PCP.PreprocessingLevels.paddedSize k ≤ PCP.ExpanderFamily.growth * (k + 1) := by
  by_cases hk : k = 0
  · subst k
    have h := PCP.ExpanderFamily.growth_gt_one
    simp only [PCP.PreprocessingLevels.paddedSize_zero, Nat.zero_add, Nat.mul_one]
    omega
  · exact (PCP.PreprocessingLevels.paddedSize_bounds (Nat.pos_of_ne_zero hk)).2.trans
      (Nat.mul_le_mul_left _ (Nat.le_succ k))

def inputCoefficient : Nat :=
  (resizeCoefficient PCP.Expanders.baseDegree + 4) * (PCP.ExpanderFamily.growth + 1)^5

theorem familyBudget_at_boundedLevel_le
    (H : Table (cloudSize PCP.Expanders.baseDegree) PCP.Expanders.baseDegree) (k : Nat) :
    familyBudget H (PCP.PreprocessingLevels.boundedLevel k) ≤ inputCoefficient * (k + 1)^5 := by
  have hg : cloudSize PCP.Expanders.baseDegree = PCP.ExpanderFamily.growth := by
    unfold cloudSize degree PCP.ExpanderFamily.growth
    ring
  have growth : 1 < cloudSize PCP.Expanders.baseDegree := by
    rw [hg]
    exact PCP.ExpanderFamily.growth_gt_one
  have bound := familyBudget_le H growth (PCP.PreprocessingLevels.boundedLevel k)
  rw [PCP.PreprocessingLevels.table_vertexCount_eq_paddedSize] at bound
  have sizeBound : PCP.PreprocessingLevels.paddedSize k + 1 ≤
      (PCP.ExpanderFamily.growth + 1) * (k + 1) := by
    have h := paddedSize_le_succ_input k
    nlinarith
  calc
    _ ≤ (resizeCoefficient PCP.Expanders.baseDegree + 4) *
        (PCP.PreprocessingLevels.paddedSize k + 1)^5 := bound
    _ ≤ (resizeCoefficient PCP.Expanders.baseDegree + 4) *
        ((PCP.ExpanderFamily.growth + 1) * (k + 1))^5 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left sizeBound 5)
    _ = _ := by unfold inputCoefficient; ring

end DFVSGames.Foundations.Complexity.MachineExpanderFamilyBounds

end

section

namespace DFVSGames.Foundations.Complexity.MachineExpanderFamily

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords
open MachineExpanderFamilyBounds

theorem installed_returnFrame (remaining current : Nat) (oldWord newWord suffix : List Bool) :
    fromBoolTapes (installedTapes (toBoolTapes (returnFrame remaining current oldWord newWord suffix))
      newWord) = installedFrame remaining current newWord suffix := by
  rw [returnFrame_eq_cycleTapes, toBool_cycleTapes]
  funext tape
  rcases tape with tape | tape
  · rcases tape with row | extra
    · cases row <;> rfl
    · cases extra <;> rfl
  · cases tape <;> rfl

theorem cleaned_multipliedFrame (d remaining current : Nat) (newWord suffix : List Bool) :
    fromBoolTapes (cleanedCounterTapes
      (toBoolTapes (multipliedFrame d remaining current newWord suffix))) =
      boundaryTapes remaining (current * cloudSize d) newWord suffix := by
  rw [boundaryTapes_eq_cycleTapes]
  unfold multipliedFrame
  rw [toBool_cycleTapes]
  have multiply : cloudSize d * current = current * cloudSize d := Nat.mul_comm _ _
  rw [multiply]
  funext tape
  rcases tape with tape | tape
  · rcases tape with row | extra
    · cases row <;> rfl
    · cases extra <;> rfl
  · cases tape <;> rfl

structure ResizeRun {v d : Nat} {ρ : Type} [Fintype ρ]
    (positive : 0 < d) (H : Table (cloudSize d) d) (growth : 1 < cloudSize d)
    (G : Table v (degree d)) (remaining : Nat) (state : State ρ d) (suffix : List Bool) where
  finalState : State ρ d
  caller_preserved : caller finalState = caller state
  execution : StateTransition.EvalsToInTime (TM2.step (program positive H growth))
    ⟨some (.inr (.affine .copyCount .seed)), state,
      boundaryTapes remaining v (MachineExpanderTable.oldTableWord G) suffix⟩
    (some ⟨some (.inr .levelGuard), finalState,
      boundaryTapes remaining (v * cloudSize d)
        (encodeWords (rotationWords (step G H))) suffix⟩)
    (resizeCost G H)

end DFVSGames.Foundations.Complexity.MachineExpanderFamily
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineExpanderFamilyLoop
attribute [-instance] _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.Complexity.MachineExpanderFamily

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl

variable {ρ : Type} {d : Nat}

theorem boundaryTapes_update_level (remaining current next : Nat)
    (word suffix : List Bool) :
    Function.update (boundaryTapes remaining current word suffix)
      (.inr .remainingLevel) (encodeWord next ++ suffix) =
      boundaryTapes next current word suffix := by
  funext tape
  rcases tape with tape | extra
  · rcases tape with row | extra
    · cases row <;> simp [boundaryTapes, tableFrame, MachineEmbedding.tapes, Function.update]
    · cases extra <;> simp [boundaryTapes, tableFrame, MachineEmbedding.tapes, Function.update]
  · cases extra <;> simp [boundaryTapes, extraFrame, MachineEmbedding.tapes, Function.update]

theorem initialTapes_initialize (level : Nat) (suffix : List Bool) :
    Function.update
      (Function.update (initialTapes level suffix) tableTape (initialEncoding d))
      (.inr .currentSize) (encodeWord 1) =
      boundaryTapes level 1 (initialEncoding d) suffix := by
  funext tape
  rcases tape with tape | extra
  · rcases tape with row | extra
    · cases row <;> simp [initialTapes, boundaryTapes, tableFrame,
        MachineEmbedding.tapes, Function.update, tableTape]
    · cases extra <;> simp [initialTapes, boundaryTapes, tableFrame,
        MachineEmbedding.tapes, Function.update, tableTape]
  · cases extra <;> simp [initialTapes, boundaryTapes, extraFrame,
      MachineEmbedding.tapes, Function.update, tableTape]

variable [Fintype ρ]

theorem actualStep_of_boolStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d)
    (start finish : TM2.Cfg BoolAlphabet (Label d) (State ρ d))
    (run : TM2.step (boolView positive H growth) start = some finish) :
    TM2.step (program positive H growth)
      (MachineAlphabetTransport.configuration alphabet_eq.symm start) =
      some (MachineAlphabetTransport.configuration alphabet_eq.symm finish) := by
  have h := MachineAlphabetTransport.step_simulation alphabet_eq.symm
    (boolView positive H growth) start
  rw [run] at h
  simpa only [boolView, MachineAlphabetTransport.program_symm_roundtrip,
    Option.map_some] using h

theorem bool_initializeStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : Tape → List Bool) (state : State ρ d) :
    TM2.step (boolView positive H growth) ⟨some (.inr .initialize_), state, base⟩ =
      some ⟨some (.inr .levelGuard), normalizeState positive H state,
        Function.update
          (Function.update base tableTape (initialEncoding d ++ base (.inl (.inl .table))))
          (.inr .currentSize) (encodeWord 1 ++ base (.inr .currentSize))⟩ := by
  change some (TM2.stepAux (boolView positive H growth (.inr .initialize_)) state base) = _
  rw [boolView_outer]
  simp only [boolOuterStatement, Reduction.MachineSubstitution.stepAux_pushWord,
    List.reverse_reverse, TM2.stepAux]
  rfl

theorem bool_levelGuard_succStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : Tape → List Bool) (state : State ρ d)
    (remaining : Nat) (suffix : List Bool)
    (counter : base (.inr .remainingLevel) = encodeWord (remaining + 1) ++ suffix) :
    TM2.step (boolView positive H growth) ⟨some (.inr .levelGuard), state, base⟩ =
      some ⟨some (.inr (.affine .copyCount .seed)), clearRegister state,
        Function.update base (.inr .remainingLevel) (encodeWord remaining ++ suffix)⟩ := by
  change some (TM2.stepAux (boolView positive H growth (.inr .levelGuard)) state base) = _
  rw [boolView_outer]
  simp [boolOuterStatement, MachineControl.statement, MachineUnaryCounter.guard,
    TM2.stepAux, registerStates, clearRegister, MachineExpanderTable.clearRegister,
    counter, encodeWord, List.replicate_succ]

theorem bool_levelGuard_zeroStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : Tape → List Bool) (state : State ρ d)
    (suffix : List Bool)
    (counter : base (.inr .remainingLevel) = encodeWord 0 ++ suffix) :
    TM2.step (boolView positive H growth) ⟨some (.inr .levelGuard), state, base⟩ =
      some ⟨some (.inr .done), clearRegister state, base⟩ := by
  change some (TM2.stepAux (boolView positive H growth (.inr .levelGuard)) state base) = _
  rw [boolView_outer]
  simp [boolOuterStatement, MachineControl.statement, MachineUnaryCounter.guard,
    TM2.stepAux, registerStates, clearRegister, MachineExpanderTable.clearRegister,
    counter, encodeWord]

theorem bool_doneStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : Tape → List Bool) (state : State ρ d) :
    TM2.step (boolView positive H growth) ⟨some (.inr .done), state, base⟩ =
      some ⟨none, normalizeState positive H state, base⟩ := by
  change some (TM2.stepAux (boolView positive H growth (.inr .done)) state base) = _
  rw [boolView_outer]
  rfl

theorem initializeStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : ∀ tape, List (Alphabet tape)) (state : State ρ d) :
    TM2.step (program positive H growth) ⟨some (.inr .initialize_), state, base⟩ =
      some ⟨some (.inr .levelGuard), normalizeState positive H state,
        Function.update
          (Function.update base tableTape (initialEncoding d ++ base (.inl (.inl .table))))
          (.inr .currentSize) (encodeWord 1 ++ base (.inr .currentSize))⟩ := by
  have h := actualStep_of_boolStep positive H growth _ _
    (bool_initializeStep positive H growth (toBoolTapes base) state)
  simp only [configuration_fromBool, fromBoolTapes_update, fromBool_toBool] at h
  exact h

theorem levelGuard_succStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : ∀ tape, List (Alphabet tape)) (state : State ρ d)
    (remaining : Nat) (suffix : List Bool)
    (counter : base (.inr .remainingLevel) = encodeWord (remaining + 1) ++ suffix) :
    TM2.step (program positive H growth) ⟨some (.inr .levelGuard), state, base⟩ =
      some ⟨some (.inr (.affine .copyCount .seed)), clearRegister state,
        Function.update base (.inr .remainingLevel) (encodeWord remaining ++ suffix)⟩ := by
  have h := actualStep_of_boolStep positive H growth _ _
    (bool_levelGuard_succStep positive H growth (toBoolTapes base) state
      remaining suffix counter)
  simpa only [configuration_fromBool, fromBoolTapes_update, fromBool_toBool,
    boolWord] using h

theorem levelGuard_zeroStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : ∀ tape, List (Alphabet tape)) (state : State ρ d)
    (suffix : List Bool)
    (counter : base (.inr .remainingLevel) = encodeWord 0 ++ suffix) :
    TM2.step (program positive H growth) ⟨some (.inr .levelGuard), state, base⟩ =
      some ⟨some (.inr .done), clearRegister state, base⟩ := by
  have h := actualStep_of_boolStep positive H growth _ _
    (bool_levelGuard_zeroStep positive H growth (toBoolTapes base) state suffix counter)
  simpa only [configuration_fromBool, fromBool_toBool] using h

theorem doneStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : ∀ tape, List (Alphabet tape)) (state : State ρ d) :
    TM2.step (program positive H growth) ⟨some (.inr .done), state, base⟩ =
      some ⟨none, normalizeState positive H state, base⟩ := by
  have h := actualStep_of_boolStep positive H growth _ _
    (bool_doneStep positive H growth (toBoolTapes base) state)
  simpa only [configuration_fromBool, fromBool_toBool] using h

theorem initialize_boundaryStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (level : Nat) (suffix : List Bool) (state : State ρ d) :
    TM2.step (program positive H growth)
      ⟨some (.inr .initialize_), state, initialTapes level suffix⟩ =
      some ⟨some (.inr .levelGuard), initialState positive H (caller state),
        boundaryTapes level 1 (initialEncoding d) suffix⟩ := by
  have h := initializeStep positive H growth (initialTapes level suffix) state
  have ht : initialTapes level suffix (.inl (.inl .table)) = [] := rfl
  have hc : initialTapes level suffix (.inr .currentSize) = [] := rfl
  simp only [ht, hc, List.append_nil, normalizeState] at h
  exact h.trans (congrArg
    (fun tapes : ∀ tape, List (Alphabet tape) =>
      (some ⟨some (.inr .levelGuard), initialState positive H (caller state), tapes⟩ :
        Option (TM2.Cfg Alphabet (Label d) (State ρ d))))
    (initialTapes_initialize level suffix))

theorem levelGuard_boundary_succStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (remaining current : Nat)
    (word suffix : List Bool) (state : State ρ d) :
    TM2.step (program positive H growth)
      ⟨some (.inr .levelGuard), state, boundaryTapes (remaining + 1) current word suffix⟩ =
      some ⟨some (.inr (.affine .copyCount .seed)), clearRegister state,
        boundaryTapes remaining current word suffix⟩ := by
  simpa only [boundaryTapes_update_level] using
    levelGuard_succStep positive H growth
      (boundaryTapes (remaining + 1) current word suffix) state remaining suffix rfl

theorem levelGuard_boundary_zeroStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (current : Nat)
    (word suffix : List Bool) (state : State ρ d) :
    TM2.step (program positive H growth)
      ⟨some (.inr .levelGuard), state, boundaryTapes 0 current word suffix⟩ =
      some ⟨some (.inr .done), clearRegister state,
        boundaryTapes 0 current word suffix⟩ :=
  levelGuard_zeroStep positive H growth
    (boundaryTapes 0 current word suffix) state suffix rfl

end DFVSGames.Foundations.Complexity.MachineExpanderFamily
end

section

namespace DFVSGames.Foundations.Complexity.MachineExpanderFamily

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords
open MachineExpanderFamilyBounds

noncomputable def levelLoopCost {d : Nat} (H : Table (cloudSize d) d) : Nat → Nat → Nat
  | _, 0 => 1
  | start, remaining + 1 => 1 + resizeCost (family H start) H +
      levelLoopCost H (start + 1) remaining

theorem levelLoopCost_prefix {d : Nat} (H : Table (cloudSize d) d) (start remaining : Nat) :
    levelLoopCost H start remaining + resizeSum H start =
      resizeSum H (start + remaining) + remaining + 1 := by
  induction remaining generalizing start with
  | zero => simp [levelLoopCost, Nat.add_comm]
  | succ remaining ih =>
      have h := ih (start + 1)
      rw [resizeSum_succ] at h
      have index : start + 1 + remaining = start + (remaining + 1) := by omega
      rw [index] at h
      simp only [levelLoopCost]
      omega

theorem levelLoopCost_zero_start {d : Nat} (H : Table (cloudSize d) d) (remaining : Nat) :
    levelLoopCost H 0 remaining = resizeSum H remaining + remaining + 1 := by
  simpa only [resizeSum_zero, Nat.add_zero, Nat.zero_add] using
    levelLoopCost_prefix H 0 remaining

def levelLoopTapes {d : Nat} (H : Table (cloudSize d) d)
    (completed remaining : Nat) (suffix : List Bool) : ∀ tape, List (Alphabet tape) :=
  boundaryTapes remaining (vertexCount (degree d) completed)
    (encodeWords (rotationWords (family H completed))) suffix

structure LevelLoopRun {d : Nat} {ρ : Type} [Fintype ρ]
    (positive : 0 < d) (H : Table (cloudSize d) d) (growth : 1 < cloudSize d)
    (completed remaining : Nat) (state : State ρ d) (suffix : List Bool) where
  finalState : State ρ d
  caller_preserved : caller finalState = caller state
  execution : StateTransition.EvalsToInTime (TM2.step (program positive H growth))
    ⟨some (.inr .levelGuard), state, levelLoopTapes H completed remaining suffix⟩
    (some ⟨some (.inr .done), finalState, familyTapes H (completed + remaining) suffix⟩)
    (levelLoopCost H completed remaining)

end DFVSGames.Foundations.Complexity.MachineExpanderFamily
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineDummyRows
attribute [-instance] _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.Complexity.MachineDummyRows

open Turing
open PCP.GraphTables
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)

def trueBits : List Bool := encodeWords (relationWords trueRelation)

theorem trueBits_length : trueBits.length = 8192 := by
  simp only [trueBits, encodeWords_length, relationWords, trueRelation,
    Vector.toList_replicate, List.map_replicate, List.sum_replicate_nat,
    List.length_replicate] ; rfl

def rowBits (v e : Nat) : List Bool := encodeWord v ++ encodeWord e ++ trueBits

theorem rowBits_length (v e : Nat) : (rowBits v e).length = v + e + 8194 := by
  simp [rowBits, trueBits_length, encodeWord_length]
  omega

theorem rowBits_eq_graph_row {n m : Nat} (v : Fin n) (e : Fin m) :
    rowBits v.val e.val = encodeWords (rowWords (⟨v, e, trueRelation⟩ : DartRow n m)) := by
  rw [MachineTableRows.rowBits_eq]
  rfl

def rowsBits (v e : Nat) : Nat → List Bool
  | 0 => []
  | count + 1 => rowBits v e ++ rowsBits v (e + 1) count

variable {σ : Type}

def program (d : Nat) : Label d → TM2.Stmt Alphabet (Label d) (σ × Option Bool)
  | .inl () => pushWord 2 trueBits.reverse
      (.load (fun state => (state.1, none)) (continueAt (entry d)))
  | .inr (p, .inl stage) => MachineTableRows.routine fields 3 4 5
      (rowLabel p) (some (bumpLabel p)) stage
  | .inr (p, .inr ()) => .push 1 (fun _ => true) (continueAt (afterPort p))

def fieldTapes (v e : Nat) (output : List Bool) : Fin 6 → List Bool :=
  ![encodeWord v, encodeWord e, trueBits, [], output, []]

def initialTapes (v e : Nat) (output : List Bool) : Fin 6 → List Bool :=
  Function.update (fieldTapes v e output) 2 []

theorem initializeStep (d v e : Nat) (output : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step (program d) ⟨some (start d), (ambient, register), initialTapes v e output⟩ =
      some ⟨entry d, (ambient, none), fieldTapes v e output⟩ := by
  change some (TM2.stepAux (program d (start d)) (ambient, register)
    (initialTapes v e output)) = _
  simp only [start, program, stepAux_pushWord, List.reverse_reverse, TM2.stepAux,
    initialTapes, Function.update_self, List.append_nil, Function.update_idem]
  have ht : Function.update (fieldTapes v e output) 2 trueBits = fieldTapes v e output := by
    funext i
    fin_cases i <;> simp [fieldTapes]
  rw [ht, stepAux_continueAt]

theorem rowTrace {d : Nat} (p : Fin d) (v e : Nat) (output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step (program d)))^[
        4 * (v + e + 8194) + 2 * output.length + 9]
      (some ⟨some (rowLabel p .relationRead), (ambient, register), fieldTapes v e output⟩) =
      some ⟨some (bumpLabel p), (ambient, none), fieldTapes v e (output ++ rowBits v e)⟩ := by
  have hfields (i : Fin 3) : fields i ≠ (3 : Fin 6) ∧ fields i ≠ (5 : Fin 6) := by
    fin_cases i <;> decide
  have h := MachineTableRows.appendTrace fields (3 : Fin 6) 4 5 hfields
    (by decide) (by decide) (by decide) (rowLabel p) (some (bumpLabel p))
    (program d) (fun _ => rfl) (fieldTapes v e output) rfl rfl ambient register
  have hbits : MachineTableRows.fieldBits fields (fieldTapes v e output) = rowBits v e := by
    rfl
  have hsize : MachineTableRows.fieldSize fields (fieldTapes v e output) = v + e + 8194 := by
    rw [← MachineTableRows.fieldBits_length, hbits, rowBits_length]
  have ht : Function.update (fieldTapes v e output) 4 (output ++ rowBits v e) =
      fieldTapes v e (output ++ rowBits v e) := by
    funext i
    fin_cases i <;> simp [fieldTapes]
  simpa only [hsize, hbits, show fieldTapes v e output 4 = output from rfl, ht] using h

theorem bumpStep {d : Nat} (p : Fin d) (v e : Nat) (output : List Bool) (ambient : σ) :
    TM2.step (program d) ⟨some (bumpLabel p), (ambient, none), fieldTapes v e output⟩ =
      some ⟨afterPort p, (ambient, none), fieldTapes v (e + 1) output⟩ := by
  change some (TM2.stepAux (program d (bumpLabel p)) (ambient, none)
    (fieldTapes v e output)) = _
  simp only [bumpLabel, program, TM2.stepAux]
  rw [stepAux_continueAt]
  congr 2
  funext i
  fin_cases i <;> simp [fieldTapes, encodeWord, List.replicate_succ]

theorem rowAndBumpTrace {d : Nat} (p : Fin d) (v e : Nat) (output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step (program d)))^[
        4 * (v + e + 8194) + 2 * output.length + 10]
      (some ⟨some (rowLabel p .relationRead), (ambient, register), fieldTapes v e output⟩) =
      some ⟨afterPort p, (ambient, none), fieldTapes v (e + 1) (output ++ rowBits v e)⟩ := by
  rw [show 4 * (v + e + 8194) + 2 * output.length + 10 =
      (4 * (v + e + 8194) + 2 * output.length + 9) + 1 by omega,
    Function.iterate_succ_apply', rowTrace, MachineComposition.advance_some]
  exact bumpStep p v e (output ++ rowBits v e) ambient

def steps (v e : Nat) (output : List Bool) : Nat → Nat
  | 0 => 0
  | count + 1 => (4 * (v + e + 8194) + 2 * output.length + 10) +
      steps v (e + 1) (output ++ rowBits v e) count

theorem suffixTrace {d : Nat} (count : Nat) (p : Fin d) (hp : p.val + count = d)
    (v e : Nat) (output : List Bool) (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step (program d)))^[steps v e output count]
      (some ⟨some (rowLabel p .relationRead), (ambient, register), fieldTapes v e output⟩) =
      some ⟨none, (ambient, none), fieldTapes v (e + count) (output ++ rowsBits v e count)⟩ := by
  induction count generalizing p v e output register with
  | zero =>
    have hlt := p.isLt
    omega
  | succ count ih =>
    rw [steps, Nat.add_comm (4 * (v + e + 8194) + 2 * output.length + 10),
      Function.iterate_add_apply, rowAndBumpTrace]
    by_cases hc : count = 0
    · subst count
      have hlast : ¬ p.val + 1 < d := by omega
      simp [afterPort, hlast, steps, rowsBits]
    · have hnext : p.val + 1 < d := by omega
      rw [afterPort, dite_eq_left hnext]
      have hh := ih ⟨p.val + 1, hnext⟩ (by change (p.val + 1) + count = d; omega)
        v (e + 1) (output ++ rowBits v e) none
      have he : (e + 1) + count = e + (count + 1) := by omega
      simpa only [rowsBits, List.append_assoc, he] using hh

theorem allTrace (d v e : Nat) (output : List Bool) (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step (program d)))^[steps v e output d + 1]
      (some ⟨some (start d), (ambient, register), initialTapes v e output⟩) =
      some ⟨none, (ambient, none), fieldTapes v (e + d) (output ++ rowsBits v e d)⟩ := by
  rw [Function.iterate_succ_apply]
  change (MachineComposition.advance (TM2.step (program d)))^[steps v e output d]
    (TM2.step (program d) ⟨some (start d), (ambient, register), initialTapes v e output⟩) = _
  rw [initializeStep]
  by_cases hd : 0 < d
  · rw [entry, dite_eq_left hd]
    exact suffixTrace d ⟨0, hd⟩ (by simp) v e output ambient none
  · have hz : d = 0 := by omega
    subst d
    simp [entry, steps, rowsBits]

theorem steps_le_bound (v e : Nat) (output : List Bool) (count : Nat) :
    steps v e output count ≤ count *
      (4 * (v + e + count + 8194) +
        2 * (output.length + count * (v + e + count + 8194)) + 10) := by
  induction count generalizing e output with
  | zero => simp [steps]
  | succ count ih =>
    let B := v + e + (count + 1) + 8194
    let C := 4 * B + 2 * (output.length + (count + 1) * B) + 10
    have hb : v + (e + 1) + count + 8194 = B := by dsimp [B]; omega
    have hi := ih (e + 1) (output ++ rowBits v e)
    rw [List.length_append, rowBits_length, hb] at hi
    have hrow : v + e + 8194 ≤ B := by dsimp [B]; omega
    have hout : output.length + (v + e + 8194) + count * B ≤
        output.length + (count + 1) * B := by
      calc
        _ ≤ output.length + B + count * B :=
          Nat.add_le_add_right (Nat.add_le_add_left hrow output.length) _
        _ = _ := by simp only [Nat.add_mul, Nat.one_mul]; omega
    have hconstant : 4 * B + 2 * (output.length + (v + e + 8194) + count * B) + 10 ≤ C := by
      exact Nat.add_le_add_right
        (Nat.add_le_add_left (Nat.mul_le_mul_left 2 hout) (4 * B)) 10
    have hremaining := hi.trans (Nat.mul_le_mul_left count hconstant)
    have hbody : 4 * (v + e + 8194) + 2 * output.length + 10 ≤ C := by
      exact Nat.add_le_add_right (Nat.add_le_add (Nat.mul_le_mul_left 4 hrow)
        (Nat.mul_le_mul_left 2 (Nat.le_add_right output.length ((count + 1) * B)))) 10
    change (4 * (v + e + 8194) + 2 * output.length + 10) +
      steps v (e + 1) (output ++ rowBits v e) count ≤ (count + 1) * C
    calc
      _ ≤ C + count * C := Nat.add_le_add hbody hremaining
      _ = (count + 1) * C := by rw [Nat.add_mul, Nat.one_mul]; omega

end DFVSGames.Foundations.Complexity.MachineDummyRows

end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineRegularExecutionBounds
attribute [-instance] _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.Complexity.MachineCanonicalOutput

open Turing MachineComposition

section Machine

variable {K Λ σ : Type} [DecidableEq K] [Fintype K] [Fintype Λ] [Fintype σ]

def completedProgram (P : Program K Λ σ) (chosen : List K) :
    Label Λ chosen → TM2.Stmt (fun _ : K => Bool) (Label Λ chosen) (σ × Option Bool)
  | .inl label => extendedStmt Sum.inl (cleanupEntry chosen) (P.code label)
  | .inr (.inl label) => MachineDrainMany.instruction chosen (cleanupLabel chosen)
      (some (resetLabel chosen)) label
  | .inr (.inr _) => .load (fun _ => (P.initial, none)) .halt

def completedMachine (P : Program K Λ σ) (chosen : List K) : FinTM2 where
  K := K
  k₀ := P.input
  k₁ := P.output
  Γ _ := Bool
  Λ := Label Λ chosen
  main := .inl P.main
  σ := σ × Option Bool
  initialState := (P.initial, none)
  m := completedProgram P chosen

theorem finiteAlphabet (P : Program K Λ σ) (chosen : List K) :
    MachineFiniteAlphabet.FiniteAlphabet (completedMachine P chosen) := by
  intro k
  exact inferInstanceAs (Finite Bool)

def embeddedCfg (P : Program K Λ σ) (chosen : List K)
    (cfg : (sourceMachine P).Cfg) : (completedMachine P chosen).Cfg :=
  extendedCfg Sum.inl (cleanupEntry chosen) none cfg

theorem step_simulation (P : Program K Λ σ) (chosen : List K)
    (a b : (sourceMachine P).Cfg) (step : (sourceMachine P).step a = some b) :
    (completedMachine P chosen).step (embeddedCfg P chosen a) =
      some (embeddedCfg P chosen b) := by
  cases a with
  | mk label state tapes =>
    cases label with
    | none => simp [FinTM2.step, TM2.step] at step
    | some label =>
      have hb : TM2.stepAux (P.code label) state tapes = b := Option.some.inj step
      rw [← hb]
      change some (TM2.stepAux
        (extendedStmt Sum.inl (cleanupEntry chosen) (P.code label)) (state, none) tapes) = _
      exact congrArg some
        (stepAux_extended Sum.inl (cleanupEntry chosen) (P.code label) state none tapes)

@[simp] theorem embedded_init (P : Program K Λ σ) (chosen : List K) (input : List Bool) :
    embeddedCfg P chosen (initList (sourceMachine P) input) =
      initList (completedMachine P chosen) input := rfl

omit [Fintype K] [Fintype Λ] [Fintype σ] in
theorem finalTapes_eq (P : Program K Λ σ) (chosen : List K)
    (complete : ∀ k, k ∈ chosen ↔ k ≠ P.output) (base : K → List Bool) :
    MachineDrainMany.finalTapes chosen base =
      MachineDrainMany.haltTapes P.output (base P.output) := by
  funext k
  rw [MachineDrainMany.finalTapes_apply]
  by_cases h : k = P.output
  · subst k
    simp [MachineDrainMany.haltTapes, complete]
  · simp [MachineDrainMany.haltTapes, complete, h]

theorem haltList_eq (P : Program K Λ σ) (chosen : List K) (output : List Bool) :
    haltList (completedMachine P chosen) output =
      ⟨none, (P.initial, none), MachineDrainMany.haltTapes P.output output⟩ := by
  congr 1

noncomputable def completedTime (P : Program K Λ σ) (chosen : List K)
    (rawTime : Polynomial Nat) : Polynomial Nat :=
  rawTime + Polynomial.C chosen.length *
    (Polynomial.X + rawTime * Polynomial.C (Runtime.programPushBound (sourceMachine P)) + 1) + 1

theorem completedTime_eval (P : Program K Λ σ) (chosen : List K)
    (rawTime : Polynomial Nat) (n : Nat) :
    (completedTime P chosen rawTime).eval n =
      rawTime.eval n + chosen.length *
        (n + rawTime.eval n * Runtime.programPushBound (sourceMachine P) + 1) + 1 := by
  simp [completedTime]

structure TerminalRun (P : Program K Λ σ) (input output : List Bool) (budget : Nat) where
  state : σ
  tapes : K → List Bool
  execution : StateTransition.EvalsToInTime (sourceMachine P).step
    (initList (sourceMachine P) input) (some ⟨none, state, tapes⟩) budget
  output_eq : tapes P.output = output

end Machine

end DFVSGames.Foundations.Complexity.MachineCanonicalOutput
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachinePortReindex
attribute [-instance] _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.Complexity.MachinePortReindex

open Turing MachineComposition
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)

variable {K Λ A : Type} [DecidableEq K]

theorem reindexTrace (d : Nat) (positive : 0 < d) (c b : Nat)
    (tape : Fin 5 → K) (distinct : Function.Injective tape)
    (labels : Label d → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A d))
    (atLabels : ∀ l, program (labels l) = instruction d positive c b tape labels exit l)
    (base : K → List Bool) (j : Nat) (suffix : List Bool)
    (sourceWord : base (tape 0) = encodeWord j ++ suffix)
    (scratchEmpty : base (tape 1) = []) (workEmpty : base (tape 2) = [])
    (quotientEmpty : base (tape 3) = []) (ambient : A) :
    (advance (TM2.step program))^[steps d j]
      (some ⟨some (labels .copySeed), clean d positive ambient, base⟩) =
      some ⟨exit, clean d positive ambient,
        Function.update base (tape 4) (encodeWord (value d c b j) ++ base (tape 4))⟩ := by
  have hd (i k : Fin 5) (h : i ≠ k) : tape i ≠ tape k := fun e => h (distinct e)
  let q := j / d
  let r := MachineFixedDivMod.residue d positive j
  let copied := Function.update base (tape 2) (encodeWord j)
  let initialized := frame_inline_MachinePortReindex tape base (encodeWord j) (encodeWord 0)
    (encodeWord 0 ++ base (tape 4))
  let divided := frame_inline_MachinePortReindex tape base (encodeWord 0) (encodeWord q)
    (encodeWord 0 ++ base (tape 4))
  let emitted := frame_inline_MachinePortReindex tape base (encodeWord 0) (encodeWord q)
    (encodeWord (r.val + b) ++ base (tape 4))
  let computed := frame_inline_MachinePortReindex tape base (encodeWord 0) (encodeWord q)
    (encodeWord (c * q + (r.val + b)) ++ base (tape 4))
  let drained := frame_inline_MachinePortReindex tape base (encodeWord 0) []
    (encodeWord (c * q + (r.val + b)) ++ base (tape 4))
  have copyRun : (advance (TM2.step program))^[2 * (j + 1) + 1]
      (some ⟨some (labels .copySeed), clean d positive ambient, base⟩) =
      some ⟨some (labels .initialize_), clean d positive ambient, copied⟩ := by
    simpa only [clean, copied, Nat.one_mul, Nat.add_zero, workEmpty, List.append_nil] using
      MachineUnaryAffineAt.seededAffineTrace (tape 0) (tape 1) (tape 2)
        (hd 0 1 (by decide)) (hd 0 2 (by decide)) (hd 1 2 (by decide)) 1 0
        (labels .copySeed) (labels .copyScan) (labels .copyRestore)
        (some (labels .initialize_)) program (atLabels .copySeed) (atLabels .copyScan)
        (atLabels .copyRestore) base j suffix sourceWord scratchEmpty
        (ambient, MachineFixedDivMod.residue d positive 0) none
  have initRun : (advance (TM2.step program))^[1]
      (some ⟨some (labels .initialize_), clean d positive ambient, copied⟩) =
      some ⟨some (labels .divide), clean d positive ambient, initialized⟩ := by
    change some (TM2.stepAux (program (labels .initialize_)) _ _) = _
    rw [atLabels]
    simp [instruction, TM2.stepAux, copied, initialized, frame_inline_MachinePortReindex, MachineCopy.forkTapes,
      hd 3 2 (by decide), hd 4 2 (by decide), hd 4 3 (by decide), quotientEmpty, encodeWord]
  have divisionInput : MachineFixedDivMod.unaryTapes (tape 2) (tape 3) (tape 4)
      base j 0 0 [] [] (base (tape 4)) = initialized := by
    simp only [MachineFixedDivMod.unaryTapes, MachineFixedDivMod.tapes,
      List.append_nil, initialized, frame_inline_MachinePortReindex]
  have divisionOutput : MachineFixedDivMod.unaryTapes (tape 2) (tape 3) (tape 4)
      base 0 q 0 [] [] (base (tape 4)) = divided := by
    simp only [MachineFixedDivMod.unaryTapes, MachineFixedDivMod.tapes,
      List.append_nil, divided, frame_inline_MachinePortReindex]
  have divideRun : (advance (TM2.step program))^[j + 1]
      (some ⟨some (labels .divide), clean d positive ambient, initialized⟩) =
      some ⟨some (labels (.emit r)), ((ambient, r), some false), divided⟩ := by
    have h := MachineFixedDivMod.scanTrace_fromCount d positive (tape 2) (tape 3) (tape 4)
      (hd 2 3 (by decide)) (hd 2 4 (by decide)) (hd 3 4 (by decide))
      (labels .divide) (fun a => labels (.emit a)) program (atLabels .divide)
      base j 0 [] [] (base (tape 4)) ambient none
    simpa only [Nat.zero_div, Nat.zero_add, divisionInput, divisionOutput, clean, r, q] using h
  have emitRun : (advance (TM2.step program))^[1]
      (some ⟨some (labels (.emit r)), ((ambient, r), some false), divided⟩) =
      some ⟨some (labels .affineScan), clean d positive ambient, emitted⟩ := by
    change some (TM2.stepAux (program (labels (.emit r))) _ _) = _
    rw [atLabels]
    simp [instruction, emit, stepAux_pushWord, TM2.stepAux, divided, emitted, frame_inline_MachinePortReindex,
      MachineCopy.forkTapes, List.reverse_replicate, encodeWord, List.append_assoc]
  have affineInput : MachineUnaryAffineAt.tapes (tape 3) (tape 1) (tape 4)
      emitted (encodeWord q ++ []) [] (encodeWord (r.val + b) ++ base (tape 4)) = emitted := by
    have heq : emitted (tape 3) = encodeWord q := by
      simp [emitted, frame_inline_MachinePortReindex, MachineCopy.forkTapes, hd 3 4 (by decide)]
    have hempty : emitted (tape 1) = [] := by
      simp [emitted, frame_inline_MachinePortReindex, MachineCopy.forkTapes, hd 1 2 (by decide),
        hd 1 3 (by decide), hd 1 4 (by decide), scratchEmpty]
    have hout : emitted (tape 4) = encodeWord (r.val + b) ++ base (tape 4) := by
      simp [emitted, frame_inline_MachinePortReindex, MachineCopy.forkTapes]
    rw [List.append_nil, ← heq, ← hempty, ← hout]
    exact MachineCopy.forkTapes_self _ _ _ _
  have affineOutput : MachineUnaryAffineAt.tapes (tape 3) (tape 1) (tape 4)
      emitted (encodeWord q ++ []) [] (encodeWord (c * q + (r.val + b)) ++ base (tape 4)) =
      computed := by
    funext k
    by_cases h1 : k = tape 1
    · subst k
      simp [MachineUnaryAffineAt.tapes, emitted, computed, frame_inline_MachinePortReindex, MachineCopy.forkTapes,
        hd 1 2 (by decide), hd 1 3 (by decide), hd 1 4 (by decide), scratchEmpty]
    · by_cases h3 : k = tape 3
      · subst k
        simp [MachineUnaryAffineAt.tapes, emitted, computed, frame_inline_MachinePortReindex, MachineCopy.forkTapes,
          hd 3 1 (by decide), hd 3 4 (by decide)]
      · by_cases h4 : k = tape 4
        · subst k; simp [MachineUnaryAffineAt.tapes, computed, frame_inline_MachinePortReindex, MachineCopy.forkTapes]
        · simp [MachineUnaryAffineAt.tapes, emitted, computed, frame_inline_MachinePortReindex, MachineCopy.forkTapes,
            h1, h3, h4]
  have affineRun : (advance (TM2.step program))^[2 * (q + 1)]
      (some ⟨some (labels .affineScan), clean d positive ambient, emitted⟩) =
      some ⟨some (labels .drainQuotient), clean d positive ambient, computed⟩ := by
    have h := MachineUnaryAffineAt.affineTrace (tape 3) (tape 1) (tape 4)
      (hd 3 1 (by decide)) (hd 3 4 (by decide)) (hd 1 4 (by decide)) c
      (labels .affineScan) (labels .affineRestore) (some (labels .drainQuotient))
      program (atLabels .affineScan) (atLabels .affineRestore) emitted q (r.val + b)
      [] (base (tape 4)) (ambient, MachineFixedDivMod.residue d positive 0) none
    simpa only [affineInput, affineOutput, clean] using h
  have quotientWord : computed (tape 3) = encodeWord q := by
    simp [computed, frame_inline_MachinePortReindex, MachineCopy.forkTapes, hd 3 4 (by decide)]
  have drainOutput : Function.update computed (tape 3) [] = drained := by
    funext k
    by_cases h3 : k = tape 3
    · subst k
      simp [drained, frame_inline_MachinePortReindex, MachineCopy.forkTapes, hd 3 4 (by decide)]
    · by_cases h4 : k = tape 4
      · subst k
        simp [computed, drained, frame_inline_MachinePortReindex, MachineCopy.forkTapes, hd 4 3 (by decide)]
      · simp [computed, drained, frame_inline_MachinePortReindex, MachineCopy.forkTapes, h3, h4]
  have drainRun : (advance (TM2.step program))^[q + 2]
      (some ⟨some (labels .drainQuotient), clean d positive ambient, computed⟩) =
      some ⟨some (labels .finish), clean d positive ambient, drained⟩ := by
    have h := MachineDrain.drainTrace (tape 3) (labels .drainQuotient)
      (some (labels .finish)) program (atLabels .drainQuotient)
      computed (computed (tape 3)) (ambient, MachineFixedDivMod.residue d positive 0) none
    rw [Function.update_eq_self, drainOutput, quotientWord, encodeWord_length] at h
    exact h
  have finishOutput : Function.update drained (tape 2) [] =
      Function.update base (tape 4) (encodeWord (value d c b j) ++ base (tape 4)) := by
    have hv : c * q + (r.val + b) = value d c b j := by
      simp [value, q, r, MachineFixedDivMod.residue, Nat.add_assoc]
    funext k
    by_cases h2 : k = tape 2
    · subst k
      simp [hd 2 4 (by decide), workEmpty]
    · by_cases h3 : k = tape 3
      · subst k
        simp [drained, frame_inline_MachinePortReindex, MachineCopy.forkTapes, hd 3 2 (by decide),
          hd 3 4 (by decide), quotientEmpty]
      · by_cases h4 : k = tape 4
        · subst k
          simp [drained, frame_inline_MachinePortReindex, MachineCopy.forkTapes, hd 4 2 (by decide), hv]
        · simp [drained, frame_inline_MachinePortReindex, MachineCopy.forkTapes, h2, h3, h4]
  have finishRun : (advance (TM2.step program))^[1]
      (some ⟨some (labels .finish), clean d positive ambient, drained⟩) =
      some ⟨exit, clean d positive ambient,
        Function.update base (tape 4) (encodeWord (value d c b j) ++ base (tape 4))⟩ := by
    have hw : drained (tape 2) = encodeWord 0 := by
      simp [drained, frame_inline_MachinePortReindex, MachineCopy.forkTapes, hd 2 3 (by decide), hd 2 4 (by decide)]
    change some (TM2.stepAux (program (labels .finish)) _ _) = _
    rw [atLabels]
    cases exit <;> simp [instruction, TM2.stepAux, exitAt, hw, encodeWord, finishOutput, clean]
  have total := joinTrace_inline_MachinePortReindex (joinTrace_inline_MachinePortReindex (joinTrace_inline_MachinePortReindex (joinTrace_inline_MachinePortReindex (joinTrace_inline_MachinePortReindex
    (joinTrace_inline_MachinePortReindex copyRun initRun) divideRun) emitRun) affineRun) drainRun) finishRun
  have hsteps : steps d j =
      (((((2 * (j + 1) + 1) + 1) + (j + 1)) + 1) + 2 * (q + 1)) + (q + 2) + 1 := by
    dsimp [steps, q]
    omega
  rw [hsteps]
  exact total

end DFVSGames.Foundations.Complexity.MachinePortReindex

end

section

namespace DFVSGames.Foundations.PCP.PreprocessingLazyWords

open PortTables GraphTables PreprocessingOverlayTables
open DFVSGames.Foundations.Complexity

variable {n d : Nat}

def row (table : PortTables.Table n d) (v : Fin n) (p : Fin d) :
    DartRow n (n * d) :=
  ⟨v, table.reverseIndex[rowIndex n d (v, p)], table.relations[rowIndex n d (v, p)]⟩

def stayRow (d : Nat) (v : Fin n) (p : Fin d) : DartRow n (n * (2 * d)) :=
  ⟨v, rowIndex n (2 * d) (v, lazyPorts d (false, p)), trueRelation⟩

def moveRow (table : PortTables.Table n d) (v : Fin n) (p : Fin d) :
    DartRow n (n * (2 * d)) :=
  ⟨v, rowIndex n (2 * d) ((rotation table (v, p)).1,
    lazyPorts d (true, (rotation table (v, p)).2)),
    table.relations[rowIndex n d (v, p)]⟩

theorem stayRow_reverse_val (v : Fin n) (p : Fin d) :
    (stayRow d v p).reverseIndex.val = 2 * d * v.val + p.val := by
  simp only [stayRow, rowIndex_val, lazyPorts_false_val]
  omega

theorem moveRow_reverse_val (table : PortTables.Table n d) (v : Fin n) (p : Fin d) :
    (moveRow table v p).reverseIndex.val =
      reverseMap d (row table v p).reverseIndex.val := by
  simp only [moveRow, rowIndex_val, lazyPorts_true_val, reverseMap, row]
  change (table.reverseIndex[rowIndex n d (v, p)]).val % d + d +
      (2 * d) * ((table.reverseIndex[rowIndex n d (v, p)]).val / d) = _
  omega

theorem moveRow_words (table : PortTables.Table n d) (v : Fin n) (p : Fin d) :
    rowWords (moveRow table v p) =
      [v.val, reverseMap d (row table v p).reverseIndex.val] ++
        relationWords (row table v p).relation := by
  rw [rowWords, moveRow_reverse_val]
  rfl

end DFVSGames.Foundations.PCP.PreprocessingLazyWords
end

section

namespace DFVSGames.Foundations.Complexity.MachineLazyRows

open Turing MachineComposition PCP.GraphTables
open PCP.PreprocessingLazyWords (reverseMap moveRow moveRow_words)

variable {K Λ A : Type} [DecidableEq K]

theorem reindexRowTrace (d : Nat) (positive : 0 < d) (c b : Nat) (tape : Fin 9 → K)
    (distinct : Function.Injective tape) (labels : Label d → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State A d))
    (atLabels : ∀ l, program (labels l) = reindexInstruction d positive c b tape labels exit l)
    (base : K → List Bool) (v j : Nat) (relation : RelationTable)
    (tailWord : base (tape 0) = encodeWord v)
    (reverseWord : base (tape 1) = encodeWord j)
    (relationWord : base (tape 2) = encodeWords (relationWords relation))
    (scratchEmpty : base (tape 3) = []) (workEmpty : base (tape 4) = [])
    (quotientEmpty : base (tape 5) = []) (newReverseEmpty : base (tape 6) = [])
    (rowEmpty : base (tape 8) = []) (ambient : A) :
    (advance (TM2.step program))^[reindexSteps d c b v j relation (base (tape 7))]
      (some ⟨some (labels (.inl .copySeed)), MachinePortReindex.clean d positive ambient, base⟩) =
      some ⟨exit, MachinePortReindex.clean d positive ambient,
        reindexResultTapes d c b v j relation tape base⟩ := by
  have hd (i k : Fin 9) (h : i ≠ k) : tape i ≠ tape k := fun e => h (distinct e)
  have ha0 : addressIndex 0 = 1 := rfl
  have ha4 : addressIndex 4 = 6 := rfl
  have mapRun := MachinePortReindex.reindexTrace d positive c b
    (tape ∘ addressIndex) (distinct.comp addressIndex_injective)
    (fun stage => labels (.inl stage)) (some (labels (.inr .relationRead)))
    program (fun stage => atLabels (.inl stage)) base j []
    (by simpa only [Function.comp_apply, ha0, List.append_nil] using reverseWord)
    scratchEmpty workEmpty quotientEmpty ambient
  simp only [Function.comp_apply, ha4, newReverseEmpty,
    List.append_nil] at mapRun
  change (advance (TM2.step program))^[MachinePortReindex.steps d j]
    (some ⟨some (labels (.inl .copySeed)), MachinePortReindex.clean d positive ambient, base⟩) =
    some ⟨some (labels (.inr .relationRead)), MachinePortReindex.clean d positive ambient,
      reindexMappedTapes d c b j tape base⟩ at mapRun
  have hfields (i : Fin 3) : fields tape i ≠ tape 8 ∧ fields tape i ≠ tape 3 := by
    fin_cases i
    · exact ⟨hd 0 8 (by decide), hd 0 3 (by decide)⟩
    · exact ⟨hd 6 8 (by decide), hd 6 3 (by decide)⟩
    · exact ⟨hd 2 8 (by decide), hd 2 3 (by decide)⟩
  have hbits : MachineTableRows.fieldBits (fields tape) (reindexMappedTapes d c b j tape base) =
      reindexRowBits d c b v j relation := by
    simp [MachineTableRows.fieldBits, fields, reindexMappedTapes, hd 0 6 (by decide),
      hd 2 6 (by decide), tailWord, relationWord, reindexRowBits]
  have hsize : MachineTableRows.fieldSize (fields tape) (reindexMappedTapes d c b j tape base) =
      (reindexRowBits d c b v j relation).length := by
    rw [← MachineTableRows.fieldBits_length, hbits]
  have hout : reindexMappedTapes d c b j tape base (tape 7) = base (tape 7) := by
    simp [reindexMappedTapes, hd 7 6 (by decide)]
  have appendRun := MachineTableRows.appendTrace (fields tape) (tape 8) (tape 7) (tape 3)
    hfields (hd 8 7 (by decide)) (hd 8 3 (by decide)) (hd 7 3 (by decide))
    (fun stage => labels (.inr stage)) exit program
    (fun stage => atLabels (.inr stage)) (reindexMappedTapes d c b j tape base)
    (by simp [reindexMappedTapes, hd 8 6 (by decide), rowEmpty])
    (by simp [reindexMappedTapes, hd 3 6 (by decide), scratchEmpty])
    (ambient, MachineFixedDivMod.residue d positive 0) none
  rw [hsize, hout, hbits] at appendRun
  change (advance (TM2.step program))^[4 * (reindexRowBits d c b v j relation).length +
      2 * (base (tape 7)).length + 9]
    (some ⟨some (labels (.inr .relationRead)), MachinePortReindex.clean d positive ambient,
      reindexMappedTapes d c b j tape base⟩) =
    some ⟨exit, MachinePortReindex.clean d positive ambient,
      reindexResultTapes d c b v j relation tape base⟩ at appendRun
  rw [show reindexSteps d c b v j relation (base (tape 7)) =
      (4 * (reindexRowBits d c b v j relation).length + 2 * (base (tape 7)).length + 9) +
        MachinePortReindex.steps d j by unfold reindexSteps; omega,
    Function.iterate_add_apply, mapRun, appendRun]

theorem rowBits_eq_moveRow {n d : Nat} (table : PCP.PortTables.Table n d)
    (v : Fin n) (p : Fin d) :
    rowBits d v.val (PCP.PreprocessingLazyWords.row table v p).reverseIndex.val
        (PCP.PreprocessingLazyWords.row table v p).relation =
      encodeWords (rowWords (moveRow table v p)) := by
  rw [moveRow_words]
  simp [rowBits, encodeWords]

abbrev Buffer := MachineRegularOriginalRow.Buffer
abbrev StreamState (A : Type) (d : Nat) := State (A × Buffer) d

def streamClean (d : Nat) (positive : 0 < d) (ambient : A) : StreamState A d :=
  MachinePortReindex.clean d positive (ambient, MachineRegularOriginalRow.zeroBuffer)

def relationStateEquiv (A : Type) (d : Nat) :
    MachineRegularOriginalRow.State (A × Fin d) ≃ StreamState A d where
  toFun s := (((s.1.1.1, s.1.2), s.1.1.2), s.2)
  invFun s := (((s.1.1.1, s.1.2), s.1.1.2), s.2)
  left_inv _ := rfl
  right_inv _ := rfl

end DFVSGames.Foundations.Complexity.MachineLazyRows
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_VertexLabel
attribute [-instance] _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace DFVSGames.Foundations.Complexity.MachineLazyRows
open Turing MachineComposition PCP.GraphTables
open PCP.PreprocessingLazyWords (reverseMap moveRow moveRow_words)
variable {K Λ A : Type} [DecidableEq K]

def recordsInput {n m : Nat} (rows : List (DartRow n m)) : List Bool :=
  rows.flatMap (fun r => inputRowBits r.tail.val r.reverseIndex.val r.relation)

def recordsOutput {n m : Nat} (d c b : Nat) (rows : List (DartRow n m)) : List Bool :=
  rows.flatMap (fun r => reindexRowBits d c b r.tail.val r.reverseIndex.val r.relation)

def streamFrame {n m : Nat} (tape : Fin 10 → K) (base : K → List Bool)
    (rows : List (DartRow n m)) (output : List Bool) : K → List Bool :=
  Function.update (Function.update base (tape 9) (recordsInput rows ++ base (tape 9)))
    (tape 7) output

theorem recordsInput_eq_codec {n m : Nat} (rows : List (DartRow n m)) :
    recordsInput rows = encodeWords (rows.flatMap rowWords) := by
  induction rows with
  | nil => rfl
  | cons r rows ih =>
      simp only [recordsInput, List.flatMap_cons, encodeWords_append,
        MachineTableRows.rowBits_eq, inputRowBits] at ih ⊢
      rw [ih]

theorem recordsOutput_lazy {n d : Nat} (table : PCP.PortTables.Table n d) (v : Fin n) :
    recordsOutput d (2 * d) d (List.ofFn (PCP.PreprocessingLazyWords.row table v)) =
      encodeWords ((List.ofFn (moveRow table v)).flatMap rowWords) := by
  rw [encodeWords_flatMap_inline_MachineLazyRows]
  simp only [recordsOutput, List.flatMap_def, List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext p
  change reindexRowBits d (2 * d) d v.val
      (PCP.PreprocessingLazyWords.row table v p).reverseIndex.val
      (PCP.PreprocessingLazyWords.row table v p).relation =
    encodeWords (rowWords (moveRow table v p))
  have h := rowBits_eq_moveRow table v p
  simpa only [rowBits, reindexRowBits, MachinePortReindex.lazy_value, reverseMap] using h

theorem reindexValue_le {n m : Nat} (d c b : Nat) (r : DartRow n m) :
    MachinePortReindex.value d c b r.reverseIndex.val ≤ valueBound c b m := by
  have hj := r.reverseIndex.isLt.le
  have hdiv := (Nat.div_le_self r.reverseIndex.val d).trans hj
  have hmod := (Nat.mod_le r.reverseIndex.val d).trans hj
  have hmul := Nat.mul_le_mul_left c hdiv
  unfold MachinePortReindex.value valueBound
  omega

theorem reindexRowBits_length_le {n m : Nat} (d c b : Nat) (r : DartRow n m) :
    (reindexRowBits d c b r.tail.val r.reverseIndex.val r.relation).length ≤
      rowSizeBound c b n m := by
  have htail := r.tail.isLt.le
  have hvalue := reindexValue_le d c b r
  have hrelation := relationBits_length_le r.relation
  simp only [reindexRowBits, List.length_append, encodeWord_length]
  unfold rowSizeBound
  omega

end DFVSGames.Foundations.Complexity.MachineLazyRows
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachinePaddedOverlay
attribute [-instance] _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.Complexity.MachineLazyCodec
open PCP.GraphTables PCP.PreprocessingLazyWords

theorem rowsBits_ofFn (v e count : Nat) :
    MachineDummyRows.rowsBits v e count =
      (List.ofFn fun p : Fin count => MachineDummyRows.rowBits v (e + p.val)).flatten := by
  induction count generalizing e with
  | zero => rfl
  | succ count ih =>
    rw [MachineDummyRows.rowsBits, List.ofFn_succ, List.flatten_cons]
    simp only [Fin.val_zero, Nat.add_zero]
    apply congrArg (MachineDummyRows.rowBits v e ++ ·)
    rw [ih]
    apply congrArg List.flatten
    congr 1
    funext p
    simp only [Fin.val_succ]
    congr 1
    omega

theorem encodeWords_flatMap_inline_MachineLazyCodec {α : Type*} (items : List α) (words : α → List Nat) :
    encodeWords (items.flatMap words) = items.flatMap (fun x => encodeWords (words x)) := by
  induction items with
  | nil => rfl
  | cons item items ih => simp only [List.flatMap_cons, encodeWords_append, ih]

theorem rowBits_stay {n d : Nat} (v : Fin n) (p : Fin d) :
    MachineDummyRows.rowBits v.val (2 * d * v.val + p.val) =
      encodeWords (rowWords (stayRow d v p)) := by
  have h := MachineDummyRows.rowBits_eq_graph_row v (stayRow d v p).reverseIndex
  rw [stayRow_reverse_val] at h
  exact h

theorem rowsBits_stay {n d : Nat} (v : Fin n) :
    MachineDummyRows.rowsBits v.val (2 * d * v.val) d =
      encodeWords ((List.ofFn (stayRow d v)).flatMap rowWords) := by
  rw [rowsBits_ofFn, encodeWords_flatMap_inline_MachineLazyCodec]
  simp only [List.flatMap_def, List.map_ofFn]
  apply congrArg List.flatten
  congr 1
  funext p
  exact rowBits_stay v p

end DFVSGames.Foundations.Complexity.MachineLazyCodec
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineLazyTableRuntime
attribute [-instance] _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.Complexity.MachineLogCounter

open Turing

theorem stripTrace (n : Nat) (scratch output : List Bool) (state : State) :
    next^[n + 1] (some (configuration (some 1) state (encodeWord n) scratch output)) =
      some (configuration (some 4) initialState [] (List.replicate n true ++ scratch) output) := by
  induction n generalizing scratch state with
  | zero =>
    simpa only [encodeWord, List.replicate_zero, List.nil_append, Nat.zero_add,
      Function.iterate_one, next, MachineComposition.advance_some] using
      stripStep_false scratch output state
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    change next^[n + 1]
      (machine.step (configuration (some 1) state (true :: encodeWord n) scratch output)) = _
    rw [stripStep_true, ih]
    congr 2
    simp only [List.replicate_add, List.replicate_one, List.append_assoc, List.singleton_append]

end DFVSGames.Foundations.Complexity.MachineLogCounter

end

section

namespace DFVSGames.Foundations.Complexity.GraphCounterModel

open Turing

theorem headerStep_zero (again next : Label)
    (atHeader : program again = readHeader again next)
    (suffix archive : List Bool) (sum : Nat)
    (state : MachineLogCounter.State) (register : Option Bool) :
    TM2.step program
      ⟨some again, (state, register), startMemory (encodeWord 0 ++ suffix) archive (encodeWord sum)⟩ =
      some ⟨some next, (state, none), startMemory suffix archive (encodeWord sum)⟩ := by
  change some (TM2.stepAux (program again) _ _) = _
  rw [atHeader]
  simp only [readHeader, TM2.stepAux, startMemory, startExtra, encodeWord,
    List.replicate_zero, List.nil_append, List.singleton_append, List.head?_cons,
    List.tail_cons, Option.getD_some, Bool.cond_false]
  rw [startMemory_input_update]

theorem headerStep_succ (again next : Label)
    (atHeader : program again = readHeader again next)
    (n sum : Nat) (suffix archive : List Bool)
    (state : MachineLogCounter.State) (register : Option Bool) :
    TM2.step program
      ⟨some again, (state, register),
        startMemory (encodeWord (n + 1) ++ suffix) archive (encodeWord sum)⟩ =
      some ⟨some again, (state, some true),
        startMemory (encodeWord n ++ suffix) archive (encodeWord (sum + 1))⟩ := by
  change some (TM2.stepAux (program again) _ _) = _
  rw [atHeader]
  simp only [readHeader, TM2.stepAux, startMemory, startExtra, encodeWord,
    List.replicate_succ, List.cons_append, List.head?_cons, List.tail_cons,
    Option.getD_some, Bool.cond_true]
  rw [startMemory_input_update, startMemory_sum_update]
  rfl

theorem headerTrace (again next : Label)
    (atHeader : program again = readHeader again next)
    (n sum : Nat) (suffix archive : List Bool)
    (state : MachineLogCounter.State) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[n + 1]
      (some ⟨some again, (state, register),
        startMemory (encodeWord n ++ suffix) archive (encodeWord sum)⟩) =
      some ⟨some next, (state, none), startMemory suffix archive (encodeWord (n + sum))⟩ := by
  induction n generalizing sum register with
  | zero =>
      simpa only [Nat.zero_add, Function.iterate_one, MachineComposition.advance_some] using
        headerStep_zero again next atHeader suffix archive sum state register
  | succ n ih =>
      rw [Function.iterate_succ_apply, MachineComposition.advance_some]
      rw [headerStep_succ again next atHeader n sum suffix archive state register]
      simpa only [Nat.add_assoc, Nat.add_comm 1 sum] using ih (sum + 1) (some true)

def headerInTime (again next : Label)
    (atHeader : program again = readHeader again next)
    (n sum : Nat) (suffix archive : List Bool)
    (state : MachineLogCounter.State) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some again, (state, register), startMemory (encodeWord n ++ suffix) archive (encodeWord sum)⟩
      (some ⟨some next, (state, none), startMemory suffix archive (encodeWord (n + sum))⟩)
      (n + 1) where
  steps := n + 1
  evals_in_steps := headerTrace again next atHeader n sum suffix archive state register
  steps_le_m := le_rfl

theorem clockInitialMemory (word rest : List Bool) (sum : Nat) :
    clockConfiguration (startExtra rest word) none
      (initList MachineLogCounter.machine (encodeWord sum)) =
      ⟨some (.inl 0), initialState, startMemory rest word (encodeWord sum)⟩ := by
  have ht : clockTapes (initList MachineLogCounter.machine (encodeWord sum)).stk
      (startExtra rest word) = startMemory rest word (encodeWord sum) := by
    funext tape
    cases tape with
    | inl k => fin_cases k <;> rfl
    | inr k => rfl
  exact congrArg (TM2.Cfg.mk _ _) ht

def startInTime (n m : Nat) (rest : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (initList machine (encodeWords [n, m] ++ rest))
      (some (clockConfiguration (startExtra rest (encodeWords [n, m] ++ rest)) none
        (initList MachineLogCounter.machine (encodeWord (n + m)))))
      (2 * ((encodeWords [n, m] ++ rest).length + 1) + 1 + (n + 1) + (m + 1)) := by
  let word := encodeWords [n, m] ++ rest
  let b₀ := startMemory word [] []
  let b₁ := startMemory word word []
  let b₂ := startMemory word word (encodeWord 0)
  have hc : Function.update b₀ (.inr .archive) (b₀ (.inr .input) ++ b₀ (.inr .archive)) = b₁ := by
    funext tape
    cases tape with
    | inl k => simp [b₀, b₁, startMemory]
    | inr k => cases k <;> simp [b₀, b₁, startMemory, startExtra]
  let copy := MachineCopy.copyInTime (.inr ExtraTape.input) (.inr ExtraTape.archive)
    (.inr ExtraTape.scratch) (by decide) (by decide) (by decide) false
    (.inr ExtraLabel.copyFirst) (.inr ExtraLabel.copySecond) (some (.inr ExtraLabel.seed))
    program rfl rfl b₀ rfl MachineLogCounter.initialState none
  have copy' : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.inr .copyFirst), initialState, b₀⟩
      (some ⟨some (.inr .seed), initialState, b₁⟩) (2 * (word.length + 1)) := by
    have h := copy
    rw [hc] at h
    simpa only [initialState, show b₀ (.inr .input) = word from rfl] using h
  have seed : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.inr .seed), initialState, b₁⟩
      (some ⟨some (.inr .headerFirst), initialState, b₂⟩) 1 := by
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    change some (TM2.stepAux (program (.inr .seed)) initialState b₁) = _
    simp only [program, TM2.stepAux, b₁, startMemory]
    rw [startMemory_sum_update]
    rfl
  have first := headerInTime (.inr .headerFirst) (.inr .headerSecond) rfl
    n 0 (encodeWord m ++ rest) word MachineLogCounter.initialState none
  have first' : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.inr .headerFirst), initialState, b₂⟩
      (some ⟨some (.inr .headerSecond), initialState,
        startMemory (encodeWord m ++ rest) word (encodeWord n)⟩) (n + 1) := by
    simpa only [b₂, initialState, word, encodeWords, List.append_nil, List.append_assoc,
      Nat.add_zero] using first
  have second := headerInTime (.inr .headerSecond) (.inl 0) rfl
    m n rest word MachineLogCounter.initialState none
  have second' : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.inr .headerSecond), initialState,
        startMemory (encodeWord m ++ rest) word (encodeWord n)⟩
      (some ⟨some (.inl 0), initialState, startMemory rest word (encodeWord (n + m))⟩)
      (m + 1) := by simpa only [initialState, Nat.add_comm m n] using second
  let p₀ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ copy' seed
  let p₁ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀ first'
  let p := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₁ second'
  rw [initialMemory, clockInitialMemory]
  exact {
    toEvalsTo := p.toEvalsTo
    steps_le_m := by
      have h := p.steps_le_m
      change p.steps ≤ 2 * (word.length + 1) + 1 + (n + 1) + (m + 1)
      omega
  }

end DFVSGames.Foundations.Complexity.GraphCounterModel
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_GraphCounterFinish
attribute [-instance] _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Foundations.Complexity.GraphCounterFinish

open Turing GraphCounterModel

theorem drainTrace (rest original counter : List Bool) :
    (MachineComposition.advance (TM2.step program))^[rest.length + 1]
      (some ⟨some (.inr .clearInput), initialState, frame rest original counter [] []⟩) =
      some ⟨some (.inr .clockCopy), initialState, frame [] original counter [] []⟩ := by
  have h := (MachineDrain.drainInTime (Sum.inr ExtraTape.input) (Sum.inr ExtraLabel.clearInput)
    (some (.inr .clockCopy)) program rfl (frame rest original counter [] [])
    MachineLogCounter.initialState none).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[rest.length + 1]
    (some ⟨some (.inr .clearInput), initialState, frame rest original counter [] []⟩) = _ at h
  have update : Function.update (frame rest original counter [] []) (.inr .input) [] =
      frame [] original counter [] [] := by
    funext tape
    cases tape with
    | inl i => simp [frame]
    | inr k => cases k <;> simp [frame]
  simpa only [update, initialState] using h

end DFVSGames.Foundations.Complexity.GraphCounterFinish

namespace DFVSGames.Foundations.Complexity.GraphCounterPrefix

open Turing PCP GraphCounterModel GraphCounterFinish

def rawOutput (n m : Nat) (rest : List Bool) : List Bool :=
  encodeWord ((n + m).log2 + 1) ++ (encodeWords [n, m] ++ rest)

def rowsBits (table : GraphTables.Table) : List Bool :=
  encodeWords ((GraphTables.rowList table).flatMap GraphTables.rowWords)

theorem tableBits_decomposition (table : GraphTables.Table) :
    GraphTables.tableBits table = encodeWords [table.vertices, table.darts] ++ rowsBits table :=
  encodeWords_append _ _

end DFVSGames.Foundations.Complexity.GraphCounterPrefix

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_FinalCNFHeader
attribute [-instance] _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.Complexity.FinalCNFMachine.Program

open Turing PCP PCP.AlphabetTable FinalCNFTableAdapter

theorem prepared_input (base : Tape → List Bool) (table : GraphTables.Table)
    (e : Fin table.darts) (rest : List Bool) :
    preparedTapes base table e rest .input = rowRest table e rest := by
  simp [preparedTapes, Lookup.headLookupTapes, MachineLookup.tapes, endpointTapes,
    Hastad.SourceMachine.fieldTapes]

theorem prepared_head (base : Tape → List Bool) (table : GraphTables.Table)
    (e : Fin table.darts) (rest : List Bool) :
    preparedTapes base table e rest .head =
      encodeWord table.rows[table.rows[e].reverseIndex].tail.val := by
  simp [preparedTapes, Lookup.headLookupTapes, MachineLookup.tapes,
    genericTable_headValue, GraphTables.semantics, ConstraintGraph.head,
    GraphTables.reverseAt]

theorem prepared_tail (base : Tape → List Bool) (table : GraphTables.Table)
    (e : Fin table.darts) (rest : List Bool) :
    preparedTapes base table e rest .tail = encodeWord table.rows[e].tail.val ++ base .tail := by
  simp [preparedTapes, Lookup.headLookupTapes, MachineLookup.tapes, endpointTapes,
    Hastad.SourceMachine.fieldTapes]

theorem prepared_reverse (base : Tape → List Bool) (table : GraphTables.Table)
    (e : Fin table.darts) (rest : List Bool) :
    preparedTapes base table e rest .reverseIndex =
      encodeWord table.rows[e].reverseIndex.val ++ base .reverseIndex := by
  simp [preparedTapes, Lookup.headLookupTapes, MachineLookup.tapes, endpointTapes,
    Hastad.SourceMachine.fieldTapes]

theorem prepared_frame (base : Tape → List Bool) (table : GraphTables.Table)
    (e : Fin table.darts) (rest : List Bool) (tape : Tape)
    (hi : tape ≠ .input) (ht : tape ≠ .tail) (hr : tape ≠ .reverseIndex)
    (hh : tape ≠ .head) (hs : tape ≠ .scanWork) (hx : tape ≠ .indexWork) :
    preparedTapes base table e rest tape = base tape := by
  simp [preparedTapes, Lookup.headLookupTapes, MachineLookup.tapes, endpointTapes,
    Hastad.SourceMachine.fieldTapes, hi, ht, hr, hh, hs, hx]

theorem rowResult_frame (plan : Plan) (base : Tape → List Bool)
    (table : GraphTables.Table) (e : Fin table.darts) (rest : List Bool) (tape : Tape)
    (hi : tape ≠ .input) (ht : tape ≠ .tail) (hr : tape ≠ .reverseIndex)
    (hh : tape ≠ .head) (hs : tape ≠ .scanWork) (hx : tape ≠ .indexWork)
    (ha : tape ≠ .accumulator) (hc : tape ≠ .rowIndex) :
    rowResultTapes plan base table e rest tape = base tape := by
  simp only [rowResultTapes, finishTapes, emittedTapes, Function.update_of_ne hi,
    Function.update_of_ne ht, Function.update_of_ne hr, Function.update_of_ne hh,
    Function.update_of_ne ha, Function.update_of_ne hc]
  exact prepared_frame base table e rest tape hi ht hr hh hs hx

theorem prepared_operands (base : Tape → List Bool) (table : GraphTables.Table)
    (e : Fin table.darts) (rest : List Bool)
    (hn : base .vertices = encodeWord table.vertices)
    (hm : base .darts = encodeWord table.darts)
    (hr : base .rowIndex = encodeWord e.val)
    (ht : base .tail = []) :
    ∀ i, (Function.update (preparedTapes base table e rest) Tape.input rest) (source i) =
      encodeWord (rowOperands table e i) := by
  intro i
  fin_cases i
  · simpa [source, rowOperands, values] using
      prepared_frame base table e rest .vertices (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) |>.trans hn
  · change (Function.update (preparedTapes base table e rest) Tape.input rest) Tape.darts = _
    simp only [Function.update_of_ne (show Tape.darts ≠ Tape.input by decide)]
    exact (prepared_frame base table e rest .darts (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans hm
  · change (Function.update (preparedTapes base table e rest) Tape.input rest) Tape.tail = _
    simp only [Function.update_of_ne (show Tape.tail ≠ Tape.input by decide), prepared_tail,
      ht, List.append_nil]
    rfl
  · change (Function.update (preparedTapes base table e rest) Tape.input rest) Tape.head = _
    simp only [Function.update_of_ne (show Tape.head ≠ Tape.input by decide), prepared_head]
    rfl
  · change (Function.update (preparedTapes base table e rest) Tape.input rest) Tape.rowIndex = _
    simp only [Function.update_of_ne (show Tape.rowIndex ≠ Tape.input by decide)]
    exact (prepared_frame base table e rest .rowIndex (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans hr

theorem rowOperands_bounded (table : GraphTables.Table) (e : Fin table.darts) :
    ∀ i, rowOperands table e i ≤ (GraphTables.tableBits table).length := by
  intro i
  fin_cases i
  · exact GraphTables.vertices_le_tableBits_length table
  · exact GraphTables.darts_le_tableBits_length table
  · exact table.rows[e].tail.isLt.le.trans (GraphTables.vertices_le_tableBits_length table)
  · exact table.rows[table.rows[e].reverseIndex].tail.isLt.le.trans
      (GraphTables.vertices_le_tableBits_length table)
  · exact e.isLt.le.trans (GraphTables.darts_le_tableBits_length table)

end DFVSGames.Foundations.Complexity.FinalCNFMachine.Program
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end


