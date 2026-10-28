-- Prove2me | Definitions.Def_OAIQ087A024
-- name    : OAIQ087A024
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T17:35:48.431985+00:00
-- url     : https://prove2.me/theorems/6631cf61-798b-4954-a233-690405647f85
-- title:
--   Definitions bundle OAIQ087A024 of the split of OpenAI, A Direct Proof of Optimal Max-Cut Hardness (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.OptimalMaxCut.main`, carved from OpenAI's openai/math development (OpenAI, *A Direct Proof of Optimal Max-Cut Hardness (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 303 declarations of OpenAI's Lean: 134 definitions, 4 inductive types or structures, 2 instances and 163 theorems. The definitions and types are `OAI.MaxCutGames.Foundations.Complexity.MachineExpanderFamilyBounds.inputCoefficient`, `OAI.MaxCutGames.Foundations.Complexity.MachineExpanderFamilyBounds.resizeCoefficient`, `OAI.MaxCutGames.Foundations.Complexity.MachineExpanderRow.cleanupSteps`, `OAI.MaxCutGames.Foundations.Complexity.MachineExpanderRow.lookupPhaseLabel`, `OAI.MaxCutGames.Foundations.Complexity.MachineExpanderRow.reversePhaseLabel`, `OAI.MaxCutGames.Foundations.Complexity.MachineExpanderRow.rowSteps`, `OAI.MaxCutGames.Foundations.Complexity.MachineExpanderRow.scanPhaseLabel`, `OAI.MaxCutGames.Foundations.Complexity.MachineFieldProfile.copyInCompareState`, `OAI.MaxCutGames.Foundations.Complexity.MachineFieldProfile.nonDestructiveCompareInTime`, `OAI.MaxCutGames.Foundations.Complexity.MachineFieldProfile.prefixInTime`, `OAI.MaxCutGames.Foundations.Complexity.MachineFieldProfile.profileInTime`, `OAI.MaxCutGames.Foundations.Complexity.MachineFieldProfile.profileInTime_bounded`, `OAI.MaxCutGames.Foundations.Complexity.MachineFieldProfile.stageInTime`, `OAI.MaxCutGames.Foundations.Complexity.MachineLazyRows.State`, `OAI.MaxCutGames.Foundations.Complexity.MachineLazyRows.StreamState`, `OAI.MaxCutGames.Foundations.Complexity.MachineLazyRows.inputRowBits`, `OAI.MaxCutGames.Foundations.Complexity.MachineLazyRows.recordsInput`, `OAI.MaxCutGames.Foundations.Complexity.MachineLazyRows.recordsOutput`, `OAI.MaxCutGames.Foundations.Complexity.MachineLazyRows.reindexInstruction`, `OAI.MaxCutGames.Foundations.Complexity.MachineLazyRows.reindexMappedTapes`, `OAI.MaxCutGames.Foundations.Complexity.MachineLazyRows.reindexResultTapes`, `OAI.MaxCutGames.Foundations.Complexity.MachineLazyRows.reindexRowBits`, `OAI.MaxCutGames.Foundations.Complexity.MachineLazyRows.reindexSteps`, `OAI.MaxCutGames.Foundations.Complexity.MachineLazyRows.relationStateEquiv`, `OAI.MaxCutGames.Foundations.Complexity.MachineLazyRows.rowBits`, `OAI.MaxCutGames.Foundations.Complexity.MachineLazyRows.streamClean`, `OAI.MaxCutGames.Foundations.Complexity.MachineLazyRows.streamFrame`, `OAI.MaxCutGames.Foundations.Complexity.MachineLazyRows.streamInstruction`, `OAI.MaxCutGames.Foundations.Complexity.MachineLazyRows.streamRelationCopy`, `OAI.MaxCutGames.Foundations.Complexity.MachineLazyRows.streamResultTapes`, `OAI.MaxCutGames.Foundations.Complexity.MachineLazyRows.streamRowSteps`, `OAI.MaxCutGames.Foundations.Complexity.MachineLazyRows.vertexInstruction`, `OAI.MaxCutGames.Foundations.Complexity.MachineLazyRows.vertexSteps`, `OAI.MaxCutGames.Foundations.Complexity.MachineLazyTable.State`, `OAI.MaxCutGames.Foundations.Complexity.MachineLazyTable.clean`, `OAI.MaxCutGames.Foundations.Complexity.MachineOverlayRows.State`, `OAI.MaxCutGames.Foundations.Complexity.MachineOverlayRows.instruction`, `OAI.MaxCutGames.Foundations.Complexity.MachineOverlayRows.resultTapes`, `OAI.MaxCutGames.Foundations.Complexity.MachineOverlayRows.rowBits`, `OAI.MaxCutGames.Foundations.Complexity.MachineOverlayRows.rowCostBound` and 98 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `MaxCut_Machines_Alphabet`, `MaxCut_Machines_MachineExpanderFamilyAffine`, `MaxCut_Machines_MachineExpanderFamilyCycle`, `MaxCut_Machines_MachineExpanderRowFrames`, `MaxCut_Machines_MachineExpanderTableProgram`, `MaxCut_Machines_MachineExpanderTableRows`, `MaxCut_Machines_MachineFieldProfile`, `MaxCut_Machines_MachineFixedDivMod`, `MaxCut_Machines_MachineLazyRows`, `MaxCut_Machines_MachineLazyTable`, `MaxCut_Machines_MachineOverlayRows`, `MaxCut_Machines_MachineOverlayTable`, `MaxCut_Machines_MachinePaddedExpanderFamilyBounds`, `MaxCut_Machines_MachinePaddedOverlay`, `MaxCut_Machines_MachinePortReindex`, `MaxCut_Machines_MachineRegularLift`, `MaxCut_Machines_MachineRegularTableRuntime`, `MaxCut_Machines_MachineRegularTableTrace`, `MaxCut_Machines_Runtime2`, `MaxCut_Machines_SelectorMachine`, `MaxCut_PCP_ExpanderRowControl`, `MaxCut_PCP_ExpanderTableEnumeration`, `MaxCut_PCP_GraphGap`, `MaxCut_PCP_PreprocessingLazyWords`, `MaxCut_PCP_PreprocessingOverlayWords`, `MaxCut_PCP_PreprocessingPaddingWords`, `MaxCut_PCP_PreprocessingStageMaps`.
--
--   **Imports.** It imports the bundles `OAIQ087A014`, `OAIQ087A016` and `OAIQ087A017` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ087A029`, `OAIQ087A030`, `OAIQ087A031` and `OAIQ087A032`.
-- source:
--   OpenAI, A Direct Proof of Optimal Max-Cut Hardness (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-Direct-Proof-of-Optimal-Max-Cut-Hardness-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ087A014
import Definitions.Def_OAIQ087A016
import Definitions.Def_OAIQ087A017

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineFieldProfile
attribute [-instance] _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Preserved comparisons of actual field stacks and their finite equality profile.
All whole-word equalities below are specifications of finite-head comparison.
-/

namespace MaxCutGames.Foundations.Complexity.MachineFieldProfile

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

/-- One fully constructed copy/copy/compare/store stage, restoring every stack. -/
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

/-- Compose the actual stages up to any fixed position in the pair list. -/
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

/-- Compute every matrix entry while preserving all original field stacks. -/
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

/-- A linear bound in the maximum original field length, for fixed `q`.
The actual machine and execution witness are retained. -/
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

end MaxCutGames.Foundations.Complexity.MachineFieldProfile

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_GraphGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.PCP.PreprocessingOverlayTables

open PoweringWalks

theorem overlay_rotation_old {n d e : Nat} (G : PortTables.Table n d)
    (H : ExpanderTables.Table n e) (v : Fin n) (i : Fin d) :
    PortTables.rotation (overlay G H) (v, overlayPorts d e (Sum.inl i)) =
      ((PortTables.rotation G (v, i)).1,
        overlayPorts d e (Sum.inl (PortTables.rotation G (v, i)).2)) := by
  exact rotation_materialize_image _ _ v (Sum.inl i)

theorem overlay_rotation_expander {n d e : Nat} (G : PortTables.Table n d)
    (H : ExpanderTables.Table n e) (v : Fin n) (i : Fin e) :
    PortTables.rotation (overlay G H) (v, overlayPorts d e (Sum.inr i)) =
      ((ExpanderTables.lookup H (v, i)).1,
        overlayPorts d e (Sum.inr (ExpanderTables.lookup H (v, i)).2)) := by
  exact rotation_materialize_image _ _ v (Sum.inr i)

theorem lazy_rotation_false {n d : Nat} (G : PortTables.Table n d)
    (v : Fin n) (i : Fin d) :
    PortTables.rotation (lazy G) (v, lazyPorts d (false, i)) =
      (v, lazyPorts d (false, i)) := by
  exact rotation_materialize_image _ _ v (false, i)

theorem lazy_rotation_true {n d : Nat} (G : PortTables.Table n d)
    (v : Fin n) (i : Fin d) :
    PortTables.rotation (lazy G) (v, lazyPorts d (true, i)) =
      ((PortTables.rotation G (v, i)).1,
        lazyPorts d (true, (PortTables.rotation G (v, i)).2)) := by
  exact rotation_materialize_image _ _ v (true, i)

end MaxCutGames.Foundations.PCP.PreprocessingOverlayTables

/-!
Actual finite counting for rounding copied dart labels. Minority color classes
are small enough for the cloud's directed-cut expansion. Their boundary darts
inject into all label disagreements. A separate endpoint charge counts at
most two affected original darts per changed copied label.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_Runtime2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every work tape of the actual alphabet-table machine stores Bool symbols.
This checks the work alphabets separately from the finite-machine structure's
input-alphabet condition, without changing the runtime certificate. -/

/-!
# Exact register-equivalence transport for finite-stack programs

The instruction translation reuses `MachineControl.statement` with unchanged
labels. An explicit register equivalence changes neither tapes nor labels.
The transition function, every iterated trace, and runtime witnesses are
transported in exactly the same number of transitions, including failed or
halted traces. No simulation premise is assumed.
-/

/-!
# Finite tape program for a powered relation row

The radius, address count, and powered alphabet size are fixed machine
parameters. The machine consumes live base predicate bits and endpoint-match
bits. Its finite register selects the first matching address, looks up the two
fixed powered labels, and conjoins the bounded list of base predicates.

Both input and output bits use the graph-table unary natural-word codec.
The theorems below describe actual TM2 transitions, not assumed execution
costs. Producing this input block from live graph rotor lookups is a separate
frontend composition obligation; no graph table occurs in the machine's
finite transition function.
-/

namespace MaxCutGames.Foundations.Complexity.PoweringMachineRow

open Turing
open MachineFixedBlockMap
open MaxCutGames.Foundations.PCP

/-! ## Fixed finite relation calculation -/

/-! ## Actual unary Boolean field instructions -/

theorem encodeBits_graphWords (bits : List Bool) :
    encodeBits bits = encodeWords (bits.map GraphTables.bitWord) := by
  induction bits with
  | nil => rfl
  | cons b bits ih => cases b <;> simp [encodeBits, encodeBit, encodeWords,
      GraphTables.bitWord, encodeWord, ih]

/-! ## Concrete row machine and its actual one-step execution -/

end MaxCutGames.Foundations.Complexity.PoweringMachineRow

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineRegularLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Machine execution for an inherited regularization row

The machine reads the original reverse index from the physically stored input
table. The unread working copy then starts at the 4096 original predicate
fields; a fixed finite Boolean block copy retains exactly those fields. Unary
arithmetic computes the new reverse index, and the checked row emitter appends
the three physical fields. No input table or unbounded arithmetic function is
stored in the machine's finite state or instructions.
-/

namespace MaxCutGames.Foundations.Complexity.MachineRegularOriginalRow

open Turing MachineComposition
open PCP PCP.GraphTables PCP.PreprocessingRegularTables

theorem vectorBits_eq_encodedBlock {n : Nat} (relation : Vector Bool n) :
    PoweringMachineRow.encodeBits (List.ofFn (fun i : Fin n => relation[i])) =
      encodeWords (relation.toList.map GraphTables.bitWord) := by
  rw [PoweringMachineRow.encodeBits_graphWords]
  congr 1
  congr 1
  have hvec : Vector.ofFn (fun i : Fin n => relation[i]) = relation := by
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_ofFn, Fin.getElem_fin]
  exact Vector.toList_ofFn.symm.trans (congrArg Vector.toList hvec)

theorem relationBits_eq_encodedBlock (relation : RelationTable) :
    PoweringMachineRow.encodeBits (List.ofFn (fun i : Fin 4096 => relation[i])) =
      encodeWords (relationWords relation) := vectorBits_eq_encodedBlock relation

/-- Reusable identity copy of exactly the physically read 4096 unary Boolean
fields. The fixed register is reset; every other state component is retained. -/
theorem relationCopy_step {K Λ σ : Type} [DecidableEq K]
    (src dst : K) (hne : src ≠ dst) (label : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State σ))
    (code : program label = relationCopyAt src dst exit)
    (relation : RelationTable) (suffix : List Bool) (base : K → List Bool)
    (input : base src = encodeWords (relationWords relation) ++ suffix)
    (ambient : σ) (buffer : Buffer) (register : Option Bool) :
    TM2.step program ⟨some label, ((ambient, buffer), register), base⟩ =
      some ⟨exit, ((ambient, zeroBuffer), register),
        Function.update (Function.update base src suffix) dst
          (encodeWords (relationWords relation) ++ base dst)⟩ := by
  change some (TM2.stepAux (program label) _ base) = _
  rw [code]
  unfold relationCopyAt
  rw [MachineStateEquiv.stepAux_transport_symm]
  change some (MachineStateEquiv.configuration (copyStateEquiv σ)
    (TM2.stepAux (PoweringMachineRow.encodedBlockAt src dst (id : Buffer → Buffer) exit)
      ((ambient, register), buffer) base)) = _
  have hinput : base src = PoweringMachineRow.encodeBits
      (List.ofFn (fun i : Fin 4096 => relation[i])) ++ suffix := by
    rw [relationBits_eq_encodedBlock]
    exact input
  rw [PoweringMachineRow.stepAux_encodedBlockAt src dst (id : Buffer → Buffer)
    exit hne (fun i : Fin 4096 => relation[i]) suffix
    ((ambient, register), buffer) base hinput]
  simp only [id_eq, relationBits_eq_encodedBlock, MachineStateEquiv.configuration,
    copyStateEquiv, zeroBuffer]
  rfl

end MaxCutGames.Foundations.Complexity.MachineRegularOriginalRow

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_ExpanderRowControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.PCP.ExpanderRowControl

open ExpanderTables

theorem firstAddress_eq_rowIndex {v d : Nat} (vertex : Fin v) (s : Control d) :
    firstAddress vertex.val s =
      (rowIndex v (degree d) (vertex,firstOffset s)).val := by
  rw [rowIndex_val]
  exact Nat.add_comm _ _

theorem secondAddress_eq_rowIndex {v d : Nat} (vertex : Fin v) (s : Control d) :
    secondAddress vertex.val s =
      (rowIndex v (degree d) (vertex,secondOffset s)).val := by
  rw [rowIndex_val]
  exact Nat.add_comm _ _

end MaxCutGames.Foundations.PCP.ExpanderRowControl

/-!
# Raw natural-word serialization of actual expander rotation tables

The list keeps the stored row order `port + degree * vertex`; no header is
inserted. Lookup equalities and complete unary output lengths are data facts,
not machine execution certificates. Kernel-checked with Lean 4.33.1.
-/

namespace MaxCutGames.Foundations.PCP.ExpanderTableWords

open ExpanderTables
open MaxCutGames.Foundations.Complexity (encodeWords decodeWords)

variable {v d : ℕ}

/-- The exact zero-based lookup hypothesis consumed by the machine lookup API. -/
theorem rotationWords_getElem? (table : Table v d) (i : Fin (v * d)) :
    (rotationWords table)[i.val]? = some (reverseIndex table i).val := by
  apply List.getElem?_eq_some_iff.mpr
  exact ⟨by simpa only [rotationWords_length] using i.isLt,
    rotationWords_getElem table i.val i.isLt⟩

/-- The serialized reverse index decodes to the actual table lookup. -/
theorem rotationWords_lookup (table : Table v d) (x : Fin v × Fin d) :
    (rotationWords table)[(rowIndex v d x).val]? =
      some (rowIndex v d (lookup table x)).val := by
  simpa only [lookup, Equiv.apply_symm_apply] using
    rotationWords_getElem? table (rowIndex v d x)

/-- Both the input and output use port-first mixed-radix row coordinates. -/
theorem rotationWords_row_order (table : Table v d) (x : Fin v × Fin d) :
    (rotationWords table)[x.2.val + d * x.1.val]? =
      some ((lookup table x).2.val + d * (lookup table x).1.val) := by
  simpa only [rowIndex_val] using rotationWords_lookup table x

end MaxCutGames.Foundations.PCP.ExpanderTableWords

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineFixedDivMod
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Complexity.MachineFixedDivMod

open Turing
open Reduction.MachineSubstitution (pushWord stepAux_pushWord )

variable {K Λ σ : Type} [DecidableEq K]

/-- A scan transition updates the actual quotient and finite residue of the
already-processed count. The count itself is a proof index, not machine state. -/
theorem scanStep_succ (d : Nat) (positive : 0 < d) (source quotient remainder : K)
    (sourceQuotient : source ≠ quotient) (sourceRemainder : source ≠ remainder)
    (quotientRemainder : quotient ≠ remainder) (scanLabel : Λ) (emitterLabel : Fin d → Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ d))
    (atScan : program scanLabel = scanLoop d positive source quotient scanLabel emitterLabel)
    (base : K → List Bool) (n k : Nat)
    (sourceSuffix quotientSuffix remainderSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step program ⟨some scanLabel, ((ambient, residue d positive k), register),
      unaryTapes source quotient remainder base (n + 1) (k / d) 0
        sourceSuffix quotientSuffix remainderSuffix⟩ =
      some ⟨some scanLabel, ((ambient, residue d positive (k + 1)), some true),
        unaryTapes source quotient remainder base n ((k + 1) / d) 0
          sourceSuffix quotientSuffix remainderSuffix⟩ := by
  change some (TM2.stepAux (program scanLabel) ((ambient, residue d positive k), register)
    (unaryTapes source quotient remainder base (n + 1) (k / d) 0
      sourceSuffix quotientSuffix remainderSuffix)) = _
  rw [atScan]
  simp only [unaryTapes, encodeWord, List.replicate_succ, List.cons_append]
  rw [scanAux_true d positive source quotient remainder sourceQuotient sourceRemainder
    quotientRemainder, nextResidue_residue]
  by_cases hmod : (k + 1) % d = 0
  · rw [Nat.succ_div_of_mod_eq_zero hmod]
    simp [residue, hmod, List.replicate_succ]
  · rw [Nat.succ_div_of_mod_ne_zero hmod]
    simp [residue, hmod]

theorem scanStep_zero (d : Nat) (positive : 0 < d) (source quotient remainder : K)
    (sourceQuotient : source ≠ quotient) (sourceRemainder : source ≠ remainder)
    (quotientRemainder : quotient ≠ remainder) (scanLabel : Λ) (emitterLabel : Fin d → Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ d))
    (atScan : program scanLabel = scanLoop d positive source quotient scanLabel emitterLabel)
    (base : K → List Bool) (q : Nat)
    (sourceSuffix quotientSuffix remainderSuffix : List Bool)
    (ambient : σ) (r : Fin d) (register : Option Bool) :
    TM2.step program ⟨some scanLabel, ((ambient, r), register),
      unaryTapes source quotient remainder base 0 q 0
        sourceSuffix quotientSuffix remainderSuffix⟩ =
      some ⟨some (emitterLabel r), ((ambient, r), some false),
        unaryTapes source quotient remainder base 0 q 0
          sourceSuffix quotientSuffix remainderSuffix⟩ := by
  change some (TM2.stepAux (program scanLabel) ((ambient, r), register)
    (unaryTapes source quotient remainder base 0 q 0
      sourceSuffix quotientSuffix remainderSuffix)) = _
  rw [atScan]
  simp only [unaryTapes, encodeWord, List.replicate_zero, List.nil_append,
    List.singleton_append]
  rw [scanAux_false d positive source quotient remainder sourceQuotient sourceRemainder
    quotientRemainder]

theorem emitterStep (d : Nat) (positive : 0 < d) (source quotient remainder : K)
    (emitterLabel : Fin d → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ d))
    (atEmitter : ∀ r, program (emitterLabel r) = emitter d positive remainder exit r)
    (base : K → List Bool) (n q : Nat)
    (sourceSuffix quotientSuffix remainderSuffix : List Bool)
    (ambient : σ) (r : Fin d) (register : Option Bool) :
    TM2.step program ⟨some (emitterLabel r), ((ambient, r), register),
      unaryTapes source quotient remainder base n q 0
        sourceSuffix quotientSuffix remainderSuffix⟩ =
      some ⟨exit, ((ambient, residue d positive 0), none),
        unaryTapes source quotient remainder base n q r.val
          sourceSuffix quotientSuffix remainderSuffix⟩ := by
  change some (TM2.stepAux (program (emitterLabel r)) ((ambient, r), register)
    (unaryTapes source quotient remainder base n q 0
      sourceSuffix quotientSuffix remainderSuffix)) = _
  rw [atEmitter]
  unfold emitter
  rw [stepAux_pushWord]
  simp only [unaryTapes, MachineCopy.forkTapes_right, List.reverse_replicate]
  rw [update_remainder_inline_MachineFixedDivMod]
  cases exit <;>
    simp [TM2.stepAux, Reduction.MachineTransfer.exitAt, encodeWord, List.append_assoc]

/-- The general invariant starts at the finite residue and unary quotient of
`k`, then scans `n` additional input bits. It is an actual execution theorem. -/
theorem trace_fromCount (d : Nat) (positive : 0 < d) (source quotient remainder : K)
    (sourceQuotient : source ≠ quotient) (sourceRemainder : source ≠ remainder)
    (quotientRemainder : quotient ≠ remainder) (scanLabel : Λ) (emitterLabel : Fin d → Λ)
    (exit : Option Λ) (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ d))
    (atScan : program scanLabel = scanLoop d positive source quotient scanLabel emitterLabel)
    (atEmitter : ∀ r, program (emitterLabel r) = emitter d positive remainder exit r)
    (base : K → List Bool) (n k : Nat)
    (sourceSuffix quotientSuffix remainderSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[n + 2]
      (some ⟨some scanLabel, ((ambient, residue d positive k), register),
        unaryTapes source quotient remainder base n (k / d) 0
          sourceSuffix quotientSuffix remainderSuffix⟩) =
      some ⟨exit, ((ambient, residue d positive 0), none),
        unaryTapes source quotient remainder base 0 ((k + n) / d) ((k + n) % d)
          sourceSuffix quotientSuffix remainderSuffix⟩ := by
  induction n generalizing k register with
  | zero =>
    change (TM2.step program ⟨some scanLabel, ((ambient, residue d positive k), register),
      unaryTapes source quotient remainder base 0 (k / d) 0
        sourceSuffix quotientSuffix remainderSuffix⟩).bind (TM2.step program) = _
    rw [scanStep_zero d positive source quotient remainder sourceQuotient sourceRemainder
      quotientRemainder scanLabel emitterLabel program atScan, Option.bind_some]
    simpa only [residue, Nat.add_zero] using
      emitterStep d positive source quotient remainder emitterLabel exit program atEmitter
        base 0 (k / d) sourceSuffix quotientSuffix remainderSuffix ambient
        (residue d positive k) (some false)
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    change (MachineComposition.advance (TM2.step program))^[n + 2]
      (TM2.step program ⟨some scanLabel, ((ambient, residue d positive k), register),
        unaryTapes source quotient remainder base (n + 1) (k / d) 0
          sourceSuffix quotientSuffix remainderSuffix⟩) = _
    rw [scanStep_succ d positive source quotient remainder sourceQuotient sourceRemainder
      quotientRemainder scanLabel emitterLabel program atScan]
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (k + 1) (some true)

/-- Exact unary quotient and remainder, with both output counters initially zero. -/
theorem divModTrace (d : Nat) (positive : 0 < d) (source quotient remainder : K)
    (sourceQuotient : source ≠ quotient) (sourceRemainder : source ≠ remainder)
    (quotientRemainder : quotient ≠ remainder) (scanLabel : Λ) (emitterLabel : Fin d → Λ)
    (exit : Option Λ) (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ d))
    (atScan : program scanLabel = scanLoop d positive source quotient scanLabel emitterLabel)
    (atEmitter : ∀ r, program (emitterLabel r) = emitter d positive remainder exit r)
    (base : K → List Bool) (n : Nat)
    (sourceSuffix quotientSuffix remainderSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[n + 2]
      (some ⟨some scanLabel, ((ambient, residue d positive 0), register),
        unaryTapes source quotient remainder base n 0 0
          sourceSuffix quotientSuffix remainderSuffix⟩) =
      some ⟨exit, ((ambient, residue d positive 0), none),
        unaryTapes source quotient remainder base 0 (n / d) (n % d)
          sourceSuffix quotientSuffix remainderSuffix⟩ := by
  simpa only [Nat.zero_add, Nat.zero_div] using
    trace_fromCount d positive source quotient remainder sourceQuotient sourceRemainder
      quotientRemainder scanLabel emitterLabel exit program atScan atEmitter base n 0
      sourceSuffix quotientSuffix remainderSuffix ambient register

/-- Stop just before emission, retaining the final finite residue as actual control. -/
theorem scanTrace_fromCount (d : Nat) (positive : 0 < d) (source quotient remainder : K)
    (sourceQuotient : source ≠ quotient) (sourceRemainder : source ≠ remainder)
    (quotientRemainder : quotient ≠ remainder) (scanLabel : Λ) (emitterLabel : Fin d → Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ d))
    (atScan : program scanLabel = scanLoop d positive source quotient scanLabel emitterLabel)
    (base : K → List Bool) (n k : Nat)
    (sourceSuffix quotientSuffix remainderSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[n + 1]
      (some ⟨some scanLabel, ((ambient, residue d positive k), register),
        unaryTapes source quotient remainder base n (k / d) 0
          sourceSuffix quotientSuffix remainderSuffix⟩) =
      some ⟨some (emitterLabel (residue d positive (k + n))),
        ((ambient, residue d positive (k + n)), some false),
        unaryTapes source quotient remainder base 0 ((k + n) / d) 0
          sourceSuffix quotientSuffix remainderSuffix⟩ := by
  induction n generalizing k register with
  | zero =>
    simpa only [Nat.zero_add, Nat.add_zero, Function.iterate_one,
      MachineComposition.advance_some] using
      scanStep_zero d positive source quotient remainder sourceQuotient sourceRemainder
        quotientRemainder scanLabel emitterLabel program atScan base (k / d)
        sourceSuffix quotientSuffix remainderSuffix ambient (residue d positive k) register
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    change (MachineComposition.advance (TM2.step program))^[n + 1]
      (TM2.step program ⟨some scanLabel, ((ambient, residue d positive k), register),
        unaryTapes source quotient remainder base (n + 1) (k / d) 0
          sourceSuffix quotientSuffix remainderSuffix⟩) = _
    rw [scanStep_succ d positive source quotient remainder sourceQuotient sourceRemainder
      quotientRemainder scanLabel emitterLabel program atScan]
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (k + 1) (some true)

theorem emitterWithFinishStep [Fintype σ] (d : Nat) (positive : 0 < d)
    (source quotient remainder : K) (emitterLabel : Fin d → Λ) (exit : Option Λ)
    (finish : σ → Fin d → σ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ d))
    (atEmitter : ∀ r, program (emitterLabel r) =
      emitterWithFinish d positive remainder exit finish r)
    (base : K → List Bool) (n q : Nat)
    (sourceSuffix quotientSuffix remainderSuffix : List Bool)
    (ambient : σ) (r : Fin d) (register : Option Bool) :
    TM2.step program ⟨some (emitterLabel r), ((ambient, r), register),
      unaryTapes source quotient remainder base n q 0
        sourceSuffix quotientSuffix remainderSuffix⟩ =
      some ⟨exit, ((finish ambient r, residue d positive 0), none),
        unaryTapes source quotient remainder base n q r.val
          sourceSuffix quotientSuffix remainderSuffix⟩ := by
  change some (TM2.stepAux (program (emitterLabel r)) ((ambient, r), register)
    (unaryTapes source quotient remainder base n q 0
      sourceSuffix quotientSuffix remainderSuffix)) = _
  rw [atEmitter]
  unfold emitterWithFinish
  rw [stepAux_pushWord]
  simp only [unaryTapes, MachineCopy.forkTapes_right, List.reverse_replicate]
  rw [update_remainder_inline_MachineFixedDivMod]
  cases exit <;>
    simp [TM2.stepAux, Reduction.MachineTransfer.exitAt, encodeWord, List.append_assoc]

/-- The callback is a fixed finite-control table, applied in the existing emitter transition. -/
theorem divModTraceWithFinish [Fintype σ] (d : Nat) (positive : 0 < d)
    (source quotient remainder : K)
    (sourceQuotient : source ≠ quotient) (sourceRemainder : source ≠ remainder)
    (quotientRemainder : quotient ≠ remainder) (scanLabel : Λ) (emitterLabel : Fin d → Λ)
    (exit : Option Λ) (finish : σ → Fin d → σ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ d))
    (atScan : program scanLabel = scanLoop d positive source quotient scanLabel emitterLabel)
    (atEmitter : ∀ r, program (emitterLabel r) =
      emitterWithFinish d positive remainder exit finish r)
    (base : K → List Bool) (n : Nat)
    (sourceSuffix quotientSuffix remainderSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[n + 2]
      (some ⟨some scanLabel, ((ambient, residue d positive 0), register),
        unaryTapes source quotient remainder base n 0 0
          sourceSuffix quotientSuffix remainderSuffix⟩) =
      some ⟨exit, ((finish ambient (residue d positive n), residue d positive 0), none),
        unaryTapes source quotient remainder base 0 (n / d) (n % d)
          sourceSuffix quotientSuffix remainderSuffix⟩ := by
  have hscan := scanTrace_fromCount d positive source quotient remainder
    sourceQuotient sourceRemainder quotientRemainder scanLabel emitterLabel program atScan
    base n 0 sourceSuffix quotientSuffix remainderSuffix ambient register
  simp only [Nat.zero_add, Nat.zero_div] at hscan
  rw [Function.iterate_succ_apply', hscan, MachineComposition.advance_some]
  exact emitterWithFinishStep d positive source quotient remainder emitterLabel exit finish
    program atEmitter base 0 (n / d) sourceSuffix quotientSuffix remainderSuffix ambient
    (residue d positive n) (some false)

theorem divModFromTapesWithFinish [Fintype σ] (d : Nat) (positive : 0 < d)
    (source quotient remainder : K)
    (sourceQuotient : source ≠ quotient) (sourceRemainder : source ≠ remainder)
    (quotientRemainder : quotient ≠ remainder) (scanLabel : Λ) (emitterLabel : Fin d → Λ)
    (exit : Option Λ) (finish : σ → Fin d → σ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ d))
    (atScan : program scanLabel = scanLoop d positive source quotient scanLabel emitterLabel)
    (atEmitter : ∀ r, program (emitterLabel r) =
      emitterWithFinish d positive remainder exit finish r)
    (base : K → List Bool) (n : Nat)
    (sourceSuffix quotientSuffix remainderSuffix : List Bool)
    (sourceInput : base source = encodeWord n ++ sourceSuffix)
    (quotientInput : base quotient = encodeWord 0 ++ quotientSuffix)
    (remainderInput : base remainder = encodeWord 0 ++ remainderSuffix)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[n + 2]
      (some ⟨some scanLabel, ((ambient, residue d positive 0), register), base⟩) =
      some ⟨exit, ((finish ambient (residue d positive n), residue d positive 0), none),
        unaryTapes source quotient remainder base 0 (n / d) (n % d)
          sourceSuffix quotientSuffix remainderSuffix⟩ := by
  have hbase : unaryTapes source quotient remainder base n 0 0 sourceSuffix quotientSuffix
      remainderSuffix = base := by
    simp only [unaryTapes, ← sourceInput, ← quotientInput, ← remainderInput,
      MachineCopy.forkTapes_self]
  have h := divModTraceWithFinish d positive source quotient remainder sourceQuotient
    sourceRemainder quotientRemainder scanLabel emitterLabel exit finish program atScan
    atEmitter base n sourceSuffix quotientSuffix remainderSuffix ambient register
  rw [hbase] at h
  exact h

end MaxCutGames.Foundations.Complexity.MachineFixedDivMod

/-!
The two actual division phases of the expander-row program. Static state
conjugation connects the fixed-divisor machine to the common emitter state.
Only the concrete statement placement equations are premises; no phase trace
or whole-row execution is assumed. Each phase has exactly `n + 2` transitions.
-/

namespace MaxCutGames.Foundations.Complexity.MachineExpanderRow

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl

/-- Pull the actual target program into division-state coordinates, derive its
trace from its concrete statements, then transport every actual transition back. -/
theorem transportedDivision_inline_MachineExpanderRowDivision {K Λ σ τ : Type} [DecidableEq K] [Fintype σ]
    (q : Nat) (positive : 0 < q) (source quotient remainder : K)
    (sourceQuotient : source ≠ quotient) (sourceRemainder : source ≠ remainder)
    (quotientRemainder : quotient ≠ remainder)
    (states : MachineFixedDivMod.State σ q ≃ τ)
    (scanLabel : Λ) (emitterLabel : Fin q → Λ) (exit : Option Λ)
    (finish : σ → Fin q → σ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ τ)
    (atScan : target scanLabel = MachineControl.statement id states
      (MachineFixedDivMod.scanLoop q positive source quotient scanLabel emitterLabel))
    (atEmitter : ∀ r, target (emitterLabel r) = MachineControl.statement id states
      (MachineFixedDivMod.emitterWithFinish q positive remainder exit finish r))
    (base : K → List Bool) (n : Nat)
    (sourceSuffix quotientSuffix remainderSuffix : List Bool)
    (sourceInput : base source = encodeWord n ++ sourceSuffix)
    (quotientInput : base quotient = encodeWord 0 ++ quotientSuffix)
    (remainderInput : base remainder = encodeWord 0 ++ remainderSuffix)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step target))^[n + 2]
      (some (MachineControl.configuration id states
        ⟨some scanLabel, ((ambient, MachineFixedDivMod.residue q positive 0), register), base⟩)) =
      some (MachineControl.configuration id states
        ⟨exit, ((finish ambient (MachineFixedDivMod.residue q positive n),
          MachineFixedDivMod.residue q positive 0), none),
          MachineFixedDivMod.unaryTapes source quotient remainder base 0 (n / q) (n % q)
            sourceSuffix quotientSuffix remainderSuffix⟩) := by
  let sourceProgram := MachineControl.program (Equiv.refl Λ) states.symm target
  have sourceScan : sourceProgram scanLabel =
      MachineFixedDivMod.scanLoop q positive source quotient scanLabel emitterLabel := by
    change MachineControl.statement id states.symm (target scanLabel) = _
    rw [atScan]
    exact controlStatement_inverse_inline_MachineExpanderRowDivision states _
  have sourceEmit : ∀ r, sourceProgram (emitterLabel r) =
      MachineFixedDivMod.emitterWithFinish q positive remainder exit finish r := by
    intro r
    change MachineControl.statement id states.symm (target (emitterLabel r)) = _
    rw [atEmitter]
    exact controlStatement_inverse_inline_MachineExpanderRowDivision states _
  have htrace := MachineFixedDivMod.divModFromTapesWithFinish q positive source quotient
    remainder sourceQuotient sourceRemainder quotientRemainder scanLabel emitterLabel exit
    finish sourceProgram sourceScan sourceEmit base n sourceSuffix quotientSuffix remainderSuffix
    sourceInput quotientInput remainderInput ambient register
  have roundtrip : MachineControl.program (Equiv.refl Λ) states sourceProgram = target := by
    funext label
    change MachineControl.statement id states
      (MachineControl.statement id states.symm (target label)) = target label
    exact controlStatement_inverse_inline_MachineExpanderRowDivision states.symm _
  have simulation : ∀ a b, TM2.step sourceProgram a = some b →
      TM2.step target (MachineControl.configuration id states a) =
        some (MachineControl.configuration id states b) := by
    intro a b hab
    have h := MachineControl.step_simulation (Equiv.refl Λ) states sourceProgram a
    rw [roundtrip, hab] at h
    exact h
  exact MachineComposition.liftSuccessfulTrace (TM2.step sourceProgram) (TM2.step target)
    (MachineControl.configuration id states) simulation (n + 2) _ _ htrace

variable {K Λ ρ : Type} [DecidableEq K] [Fintype ρ]

/-- Exact first lookup-result division, including the receiveFirst control update. -/
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

/-- Exact second division, including receiveSecond and the actual output-emitter entry label. -/
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

end MaxCutGames.Foundations.Complexity.MachineExpanderRow

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineExpanderTableProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Complexity.MachineExpanderTable

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl

instance alphabetFintype (tape : Tape) : Fintype (Alphabet tape) := by
  cases tape <;> exact inferInstanceAs (Fintype Bool)

end MaxCutGames.Foundations.Complexity.MachineExpanderTable

/-! Static, pointwise Boolean presentation of the actual family tape alphabet.
Every conversion below is an identity on symbols and has no machine runtime. -/

/-!
# Actual family-table installation and counter cleanup

Checked physical drain and transfer loops are placed in the family program
through its finite register equivalence. Alphabet equality transports their
actual traces back to the dependent alphabet of the full family machine.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineExpanderFamilyAffine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Complexity.MachineExpanderRow

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

end MaxCutGames.Foundations.Complexity.MachineExpanderRow

/-!
# Actual lookup and reversal phases of the expander row program

The Boolean phase selector chooses the first or second occurrence of the same
preserving lookup. The selected word is proved to be the actual stored reverse
index of the supplied graph row. All execution facts follow from the concrete
program statements; no phase execution is assumed.
-/

namespace MaxCutGames.Foundations.Complexity.MachineExpanderRow

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

variable {d : Nat} (second : Bool) (positive : 0 < d)
    (H : Table (cloudSize d) d) (ports : Tape → K)
    (distinct : Function.Injective ports) (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (code : ∀ l, target (labels l) = statement positive H ports labels exit l)
    (base : K → List Bool)
    (ambient : (Ambient ρ d × Fin (degree d)) × Unit) (register : Option Bool)

include positive H distinct exit code

/-- The reversal consumes the reverse query word and prepends its forward
encoding to the index tape, retaining every other tape and finite state. -/
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

/-- Reversing an actual emitted unary field takes exactly `index + 2` steps.
This includes consuming the field's delimiter and leaving the reversal loop. -/
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

end MaxCutGames.Foundations.Complexity.MachineExpanderRow

namespace MaxCutGames.Foundations.Complexity.MachineExpanderRow

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

/-- One cleanup phase follows the actual drain instruction at its placed label. -/
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

/-- All six phases execute in the common program, with exactly the sum of
the six initial word lengths plus one empty-branch transition per tape. -/
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

/-- The done label transfers control without inspecting or modifying any tape. -/
theorem doneStepAt (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (code : ∀ label, target (labels label) = statement positive H ports labels exit label)
    (base : K → List Bool) (state : State ρ d) :
    TM2.step target ⟨some (labels .done), state, base⟩ = some ⟨exit, state, base⟩ := by
  change some (TM2.stepAux (target (labels .done)) state base) = _
  rw [code]
  cases exit <;> rfl

/-- Cleanup followed by the actual done-to-caller transition. -/
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

/-- Initialization physically pushes four delimiters and resets the bit register. -/
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

/-- The query-clear phase removes one symbol from each of its two tapes and
preserves the complete finite state and every other tape. -/
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

end MaxCutGames.Foundations.Complexity.MachineExpanderRow

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineExpanderRowFrames
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Concrete data and tape frames for an actual expander-row computation

Only the five actual row inputs are stored. Every address, table return and
finite control value below is computed from those inputs. The thirteen tape
frames use the existing phase-output functions. These are data identities and
size bounds, not assumed machine executions.
-/

namespace MaxCutGames.Foundations.Complexity.MachineExpanderRow

open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords

namespace RowData

variable {v d : Nat} (r : RowData v d)

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

end RowData

variable {v d : Nat}

theorem final_frame_eq (r : RowData v d) (output : List Bool) :
    frame12 r output = emittedWord .output (frame0 r output) r.finalValue := by
  funext tape
  cases tape <;> simp [frame0, emittedWord, frameContents]

/-! Direct input facts for the individual checked phase traces. -/

end MaxCutGames.Foundations.Complexity.MachineExpanderRow

/-!
# Complete execution of one expander-table row

The actual finite program performs both stored-table lookups, splits their
results by its fixed degree, emits the resulting square/zigzag reverse index,
and clears its work tapes. Its transition bound is linear in the unary input
table length. The output accumulator and finite caller state are arbitrary.
-/

namespace MaxCutGames.Foundations.Complexity.MachineExpanderRow

open Turing MachineComposition
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords PCP.AlphabetTable

/-- The actual number of transitions, retaining both concrete lookup costs. -/
def rowSteps {v d : Nat} (r : RowData v d) (output : List Bool) : Nat :=
  1 + emitSteps r.inputVertex.val + (r.query1 + 2) +
    MachinePreservingLookupClean.steps (rotationWords r.oldTable) r.firstRow.val +
    (r.firstValue + 2) + 1 + emitSteps r.firstVertex.val + (r.query2 + 2) +
    MachinePreservingLookupClean.steps (rotationWords r.oldTable) r.secondRow.val +
    (r.secondValue + 2) + emitSteps r.secondVertex.val +
    (cleanupSteps id (frame11 r output) + 1)

end MaxCutGames.Foundations.Complexity.MachineExpanderRow

/-!
# Concrete boundary steps of the expander-table machine

Every execution theorem below reduces the actual common program statement.
States and dependent tape frames are arbitrary; only the relevant unary word
or finite-position branch is specified. No phase execution is a premise.
-/

namespace MaxCutGames.Foundations.Complexity.MachineExpanderTable

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl

variable {ρ : Type} {d : Nat}

variable [Fintype ρ]

theorem initializeStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (base : ∀ tape, List (Alphabet tape)) (state : State ρ d) :
    TM2.step (program positive H) ⟨some (.inr .initialize_), state, base⟩ =
      some ⟨some (.inr .vertexGuard), resetState positive H state,
        Function.update base (.inl .inputVertex) (false :: base (.inl .inputVertex))⟩ := by
  change some (TM2.stepAux (program positive H (.inr .initialize_)) state base) = _
  rw [program_outer]
  rfl

/-- Preparing a row modifies finite control only, preserving every tape. -/
theorem prepareRowStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (base : ∀ tape, List (Alphabet tape)) (state : State ρ d) :
    TM2.step (program positive H) ⟨some (.inr .prepareRow), state, base⟩ =
      some ⟨some (.inl .initialize_), prepareState positive H state, base⟩ := by
  change some (TM2.stepAux (program positive H (.inr .prepareRow)) state base) = _
  rw [program_outer]
  rfl

end MaxCutGames.Foundations.Complexity.MachineExpanderTable

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_ExpanderTableEnumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact row enumeration and accumulator contents for an expander-table step

The outer loop enumerates original vertices, and the inner loop enumerates
cloud/port positions in increasing mixed-radix order. The resulting list is
the actual next table's stored rotation-word list. Prefix and reverse-encoding
identities describe data accumulated by a row loop; they assert no runtime.
-/

namespace MaxCutGames.Foundations.PCP.ExpanderTableEnumeration

open ExpanderTables ExpanderRowControl ExpanderTableWords
open MaxCutGames.Foundations.Complexity

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

end MaxCutGames.Foundations.PCP.ExpanderTableEnumeration

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineExpanderTableRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual execution of all expander-table positions for one vertex

The inner loop calls the complete row machine once per fixed cloud/port position.
The returned state and the successful machine execution are constructed together.
Neither a row execution nor an inner-loop execution is a caller premise.
-/

namespace MaxCutGames.Foundations.Complexity.MachineExpanderTable

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords
open PCP.ExpanderTableEnumeration

theorem tableRowData_finalValue {v d : Nat} (G : Table v (degree d))
    (H : Table (cloudSize d) d) (vertex : Fin v) (position : Position d) :
    (tableRowData G H vertex position).finalValue = rowValue G H vertex position := rfl

end MaxCutGames.Foundations.Complexity.MachineExpanderTable

/-!
# Actual outer vertex iteration for expander tables

The invariant is the reversed unary encoding of all completed vertices. Each
positive unary guard invokes the proved complete fixed-position row loop;
the zero guard enters the actual output-reversal phase. No execution premise
is supplied by the caller.
-/

/-!
# Complete finite machine execution for the next expander table

The initialized old table and unary vertex count are consumed by one actual
finite program. The machine writes precisely the complete square/zigzag
rotation table, preserving its old table and all promised framing. The bound
is quadratic in the unary old-table length for each fixed small graph.
-/

/-!
# Bounds for materializing the actual expander family

The costs use the encoded old and new rotation tables, and the already checked
table-machine polynomial. The finite sum follows the actual recursive table
family. These arithmetic lemmas introduce no execution assumptions and make no
claim that the output is polynomial in an isolated binary level parameter.
-/

namespace MaxCutGames.Foundations.Complexity.MachineExpanderFamilyBounds

open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords

def resizeCoefficient (d : Nat) : Nat :=
  MachineExpanderTable.timeCoefficient d * (degree d + 1) ^ 4 +
    3 * (degree d + 1) ^ 2 + 21

def inputCoefficient : Nat :=
  (resizeCoefficient PCP.Expanders.baseDegree + 4) * (PCP.ExpanderFamily.growth + 1)^5

end MaxCutGames.Foundations.Complexity.MachineExpanderFamilyBounds

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineExpanderFamilyCycle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual counted repetition of complete table-expansion cycles. The input
counter is physically decremented, and the invariant carries the exact table
at the completed family level. -/

namespace MaxCutGames.Foundations.Complexity.MachinePaddedExpanderFamily

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl

theorem familyView_right (j : Tape) (tape : MachineExpanderFamily.Tape)
    (h : familyView j = some tape) : familyTape tape = j := by
  cases j with
  | inl j =>
    have hj : j = tape := Option.some.inj h
    subst tape
    rfl
  | inr j => simp [familyView] at h

theorem ceilingView_right (j : Tape) (tape : MachineCeilingPower.Tape)
    (h : ceilingView j = some tape) : ceilingTape tape = j := by
  cases j with
  | inl j =>
    cases j with
    | inl j => simp [ceilingView] at h
    | inr j => cases j <;> simp_all [ceilingView, ceilingTape] ; cases h ; rfl
  | inr j => cases j <;> simp_all [ceilingView, ceilingTape] <;> cases h <;> rfl

end MaxCutGames.Foundations.Complexity.MachinePaddedExpanderFamily

namespace MaxCutGames.Foundations.Complexity.MachinePaddedExpanderFamily

open Turing
open MachineCloudPadding
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords

def ceilingInput (requested : Nat) : MachineCeilingPower.Tape → List Bool :=
  MachineCeilingPower.memory (encodeWord requested) [] [] [] [] [] [] []

def ceilingOutput (requested : Nat) : MachineCeilingPower.Tape → List Bool :=
  MachineCeilingPower.memory (encodeWord requested) []
    (encodeWord (PCP.PreprocessingLevels.paddedSize requested)) []
    (encodeWord (PCP.PreprocessingLevels.boundedLevel requested)) [] [] []

def retainedFrame (requested : Nat) : Tape → List Bool
  | .inl _ => []
  | .inr tape => retainedCeilingTapes requested tape

theorem ceiling_initial_tapes (requested : Nat) :
    Placement.tapes ceilingView (ceilingInput requested) (fun _ => []) =
      initialTapes requested := by
  funext tape
  rcases tape with tape | tape
  · rcases tape with tape | tape
    · rfl
    · cases tape <;> rfl
  · cases tape <;> rfl

/-- The produced unary level is already on the exact family input tape. -/
theorem ceiling_handoff_tapes (requested : Nat) :
    Placement.tapes ceilingView (ceilingOutput requested) (fun _ => []) =
      handoffTapes requested := by
  funext tape
  rcases tape with tape | tape
  · rcases tape with tape | tape
    · rcases tape with tape | tape
      · cases tape <;> rfl
      · cases tape <;> rfl
    · cases tape <;>
        simp [Placement.tapes, ceilingView, ceilingOutput, handoffTapes,
          MachineExpanderFamily.toBoolTapes, MachineExpanderFamily.toBoolWord,
          MachineExpanderFamily.initialTapes, MachineEmbedding.tapes,
          MachineCeilingPower.memory]
  · cases tape <;> rfl

theorem family_initial_tapes (requested : Nat) :
    Placement.tapes familyView
      (MachineExpanderFamily.toBoolTapes
        (MachineExpanderFamily.initialTapes (PCP.PreprocessingLevels.boundedLevel requested) []))
      (retainedFrame requested) = handoffTapes requested := by
  funext tape
  cases tape <;> rfl

theorem family_final_tapes (H : SmallTable) (requested : Nat) :
    Placement.tapes familyView
      (MachineExpanderFamily.toBoolTapes
        (MachineExpanderFamily.familyTapes H (PCP.PreprocessingLevels.boundedLevel requested) []))
      (retainedFrame requested) = finalTapes H requested := by
  funext tape
  cases tape <;> rfl

/-- Ceiling halt enters the family initializer with no intervening transition. -/
theorem ceiling_handoff_configuration {ρ : Type} (requested : Nat)
    (state : MachineExpanderFamily.State ρ fixedDegree) :
    Placement.configuration ceilingView ceilingLabel (some familyEntry) (fun _ => [])
      (MachineStateEquiv.configuration (ceilingStates ρ)
        ⟨none, ((state, false), none), ceilingOutput requested⟩) =
      ⟨some familyEntry, (state, (false, none)), handoffTapes requested⟩ := by
  simp only [Placement.configuration, Placement.label, MachineStateEquiv.configuration,
    ceilingStates_apply, ceiling_handoff_tapes]

theorem finalTapes_table (H : SmallTable) (requested : Nat) :
    finalTapes H requested (familyTape MachineExpanderFamily.tableTape) =
      encodeWords (rotationWords (family H (PCP.PreprocessingLevels.boundedLevel requested))) := rfl

end MaxCutGames.Foundations.Complexity.MachinePaddedExpanderFamily

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachinePaddedExpanderFamilyBounds
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Complexity.MachinePaddedExpanderFamilyBounds

open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords

def timeCoefficient : Nat :=
  MachineExpanderFamilyBounds.inputCoefficient + PCP.ExpanderFamily.growth + 29

noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.C timeCoefficient * Polynomial.X^5

theorem timePolynomial_encoding (k : Nat) :
    timePolynomial.eval (encodeWord k).length = timeCoefficient * (k + 1)^5 := by
  simp only [timePolynomial, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, encodeWord_length]

theorem ceilingCost_le (g k : Nat) :
    (MachineCeilingPower.timePolynomial g).eval (encodeWord k).length ≤
      (g + 29) * (k + 1)^5 := by
  rw [MachineCeilingPower.timePolynomial_encoding]
  have squareBound : (k + 1)^2 ≤ (k + 1)^5 :=
    Nat.pow_le_pow_right (Nat.succ_pos k) (by decide)
  have linearBound : k + 1 ≤ (k + 1)^5 := by
    simpa only [pow_one] using Nat.pow_le_pow_right
      (Nat.succ_pos k) (show 1 ≤ 5 by decide)
  have constantBound : 1 ≤ (k + 1)^5 := by omega
  have squareCost := Nat.mul_le_mul_left (g + 8) squareBound
  have linearCost := Nat.mul_le_mul_left 18 linearBound
  have constantCost := Nat.mul_le_mul_left 3 constantBound
  unfold MachineCeilingPower.timeBound
  nlinarith only [squareCost, linearCost, constantCost]

theorem combinedCost_le (k : Nat) :
    (MachineCeilingPower.timePolynomial PCP.ExpanderFamily.growth).eval
        (encodeWord k).length +
      MachineExpanderFamilyBounds.inputCoefficient * (k + 1)^5 ≤
        timePolynomial.eval (encodeWord k).length := by
  rw [timePolynomial_encoding]
  have h := ceilingCost_le PCP.ExpanderFamily.growth k
  unfold timeCoefficient
  nlinarith only [h]

end MaxCutGames.Foundations.Complexity.MachinePaddedExpanderFamilyBounds

/-!
# Actual requested-size to expander-table computation

One finite program physically computes the padding level and then constructs
the complete corresponding rotation table. The level output of the first
phase is the input tape of the second phase. The actual execution preserves
the request, retains the padded size, and has a fixed polynomial time bound
in the unary request length.
-/

/-!
# Materializing a cloud rotor inside the regularization machine

Core tape 4 contains the unary cloud size and core tape 7 receives the complete
forward rotor table. The actual family computation runs on private tapes;
three retained unary words are then physically drained. All other core tapes
are preserved and all private tapes are empty on return.
-/

namespace MaxCutGames.Foundations.Complexity.MachineRegularFamily

open Turing MachineComposition
open MachineCloudPadding

abbrev Alphabet (_ : Tape) := Bool

/-- Unused private shadows of the two public roles remain empty. -/
def familyTape (t : NativeTape) : Tape :=
  if t = inputNative then .inl 4 else if t = outputNative then .inl 7 else .inr t

theorem familyView_left (t : NativeTape) : familyView (familyTape t) = some t := by
  by_cases hi : t = inputNative
  · subst t; simp [familyTape, familyView]
  · by_cases ho : t = outputNative
    · subst t; simp [familyTape, familyView, hi]
    · simp [familyTape, familyView, hi, ho]

theorem familyView_right (j : Tape) (t : NativeTape)
    (h : familyView j = some t) : familyTape t = j := by
  cases j with
  | inl i =>
    by_cases hi : i = 4
    · subst i
      have ht : inputNative = t := by simpa [familyView] using h
      subst t; simp [familyTape]
    · by_cases ho : i = 7
      · subst i
        have ht : outputNative = t := by simpa [familyView] using h
        subst t; simp [familyTape, inputNative, outputNative]
      · simp [familyView, hi, ho] at h
  | inr j =>
    by_cases hi : j = inputNative
    · simp [familyView, hi] at h
    · by_cases ho : j = outputNative
      · simp [familyView, ho] at h
      · have ht : j = t := by simpa [familyView, hi, ho] using h
        subst t; simp [familyTape, hi, ho]

def sourceProgram (H : SmallTable) : MachinePaddedExpanderFamily.Label →
    TM2.Stmt (fun _ : NativeTape => Bool) MachinePaddedExpanderFamily.Label State :=
  MachineStateEquiv.program stateEquiv (MachinePaddedExpanderFamily.program (ρ := Unit) H)

inductive Label
  | start
  | family (label : MachinePaddedExpanderFamily.Label)
  | drainPower | drainSize | drainLevel
  deriving DecidableEq, Fintype

theorem update_working_power (core : CoreTape → List Bool) (p s l p' : List Bool) :
    Function.update (working core p s l) powerTape p' = working core p' s l := by
  funext t
  cases t with
  | inl i => simp [working, powerTape]
  | inr t => by_cases h : t = powerNative <;> simp [working, powerTape, h]

theorem update_working_size (core : CoreTape → List Bool) (p s l s' : List Bool) :
    Function.update (working core p s l) sizeTape s' = working core p s' l := by
  funext t
  cases t with
  | inl i => simp [working, sizeTape]
  | inr t =>
    by_cases h : t = sizeNative
    · subst t; simp [working, sizeTape, powerNative, sizeNative]
    · simp [working, sizeTape, h]

theorem update_working_level (core : CoreTape → List Bool) (p s l l' : List Bool) :
    Function.update (working core p s l) levelTape l' = working core p s l' := by
  funext t
  cases t with
  | inl i => simp [working, levelTape]
  | inr t =>
    by_cases h : t = levelNative
    · subst t; simp [working, levelTape, powerNative, sizeNative, levelNative]
    · simp [working, levelTape, h]

theorem initial_other_inline_MachineRegularFamily (k : Nat) (t : NativeTape) (h : t ≠ inputNative) :
    MachinePaddedExpanderFamily.initialTapes k t = [] := by
  cases t with
  | inl t => rfl
  | inr t => cases t <;> simp_all [MachinePaddedExpanderFamily.initialTapes, inputNative]

/-- The only retained native work words are the two sizes and the exhausted level. -/
theorem final_other_inline_MachineRegularFamily (H : SmallTable) (k : Nat) (t : NativeTape)
    (hi : t ≠ inputNative) (ho : t ≠ outputNative) (hp : t ≠ powerNative)
    (hs : t ≠ sizeNative) (hl : t ≠ levelNative) :
    MachinePaddedExpanderFamily.finalTapes H k t = [] := by
  rcases t with ((row | tableExtra) | familyExtra) | ceiling
  · cases row <;>
      simp_all [inputNative, outputNative, MachineExpanderFamily.tableTape,
        MachinePaddedExpanderFamily.finalTapes, MachineExpanderFamily.toBoolTapes,
        MachineExpanderFamily.toBoolWord, MachineExpanderFamily.familyTapes,
        MachineExpanderFamily.boundaryTapes, MachineExpanderFamily.tableFrame,
        MachineEmbedding.tapes]
  · cases tableExtra <;> rfl
  · cases familyExtra <;>
      simp_all [sizeNative, levelNative, MachinePaddedExpanderFamily.finalTapes,
        MachineExpanderFamily.toBoolTapes, MachineExpanderFamily.toBoolWord,
        MachineExpanderFamily.familyTapes, MachineExpanderFamily.boundaryTapes,
        MachineExpanderFamily.extraFrame, MachineEmbedding.tapes]
  · cases ceiling <;>
      simp_all [inputNative, powerNative, MachinePaddedExpanderFamily.finalTapes,
        MachinePaddedExpanderFamily.retainedCeilingTapes, MachineCeilingPower.memory]

theorem initial_placement (k : Nat) (core : CoreTape → List Bool)
    (hinput : core 4 = encodeWord k) (houtput : core 7 = []) :
    Placement.tapes familyView (MachinePaddedExpanderFamily.initialTapes k) (frame core) =
      frame core := by
  funext t
  cases t with
  | inl i =>
    by_cases hi : i = 4
    · subst i; simp [Placement.tapes, familyView, frame, inputNative, hinput]
    · by_cases ho : i = 7
      · subst i
        simp [Placement.tapes, familyView, frame, outputNative,
          MachinePaddedExpanderFamily.initialTapes, houtput]
      · simp [Placement.tapes, familyView, frame, hi, ho]
  | inr t =>
    by_cases hi : t = inputNative
    · simp [Placement.tapes, familyView, frame, hi]
    · by_cases ho : t = outputNative
      · simp [Placement.tapes, familyView, frame, ho]
      · simp [Placement.tapes, familyView, frame, hi, ho, initial_other_inline_MachineRegularFamily k t hi]

noncomputable def timePolynomial : Polynomial Nat :=
  MachinePaddedExpanderFamilyBounds.timePolynomial +
    Polynomial.C (2 * PCP.ExpanderFamily.growth) * Polynomial.X + 7

end MaxCutGames.Foundations.Complexity.MachineRegularFamily

/-! Physical comparison of two unary fields. Matched true bits are saved on
two empty scratch stacks. The first delimiter determines the comparison, then
both saved prefixes are restored. All input suffixes and other tapes survive. -/

namespace MaxCutGames.Foundations.Complexity.MachineUnaryLessAt

open Turing MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

theorem scan_step_zero_left (slots : Fin 4 ↪ K) (scanLabel restoreLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atScan : program scanLabel = scan slots scanLabel restoreLabel)
    (base : K → List Bool) (b : Nat) (leftSuffix rightSuffix savedLeft savedRight : List Bool)
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    TM2.step program ⟨some scanLabel, ((ambient, flag), register),
      tapes slots base (encodeWord 0 ++ leftSuffix) (encodeWord b ++ rightSuffix) savedLeft savedRight⟩ =
      some ⟨some restoreLabel, ((ambient, decide (0 < b)), none),
        tapes slots base (encodeWord 0 ++ leftSuffix) (encodeWord b ++ rightSuffix) savedLeft savedRight⟩ := by
  change some (TM2.stepAux (program scanLabel) _ _) = _
  rw [atScan]
  cases b <;> simp [scan, stop, TM2.stepAux, encodeWord, List.replicate_succ]

theorem scan_step_zero_right (slots : Fin 4 ↪ K) (scanLabel restoreLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atScan : program scanLabel = scan slots scanLabel restoreLabel)
    (base : K → List Bool) (a : Nat) (leftSuffix rightSuffix savedLeft savedRight : List Bool)
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    TM2.step program ⟨some scanLabel, ((ambient, flag), register),
      tapes slots base (encodeWord (a + 1) ++ leftSuffix) (encodeWord 0 ++ rightSuffix) savedLeft savedRight⟩ =
      some ⟨some restoreLabel, ((ambient, false), none),
        tapes slots base (encodeWord (a + 1) ++ leftSuffix) (encodeWord 0 ++ rightSuffix) savedLeft savedRight⟩ := by
  change some (TM2.stepAux (program scanLabel) _ _) = _
  rw [atScan]
  simp [scan, stop, TM2.stepAux, encodeWord, List.replicate_succ]

theorem scan_step_succ (slots : Fin 4 ↪ K) (scanLabel restoreLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atScan : program scanLabel = scan slots scanLabel restoreLabel)
    (base : K → List Bool) (a b : Nat) (leftSuffix rightSuffix savedLeft savedRight : List Bool)
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    TM2.step program ⟨some scanLabel, ((ambient, flag), register),
      tapes slots base (encodeWord (a + 1) ++ leftSuffix) (encodeWord (b + 1) ++ rightSuffix)
        savedLeft savedRight⟩ =
      some ⟨some scanLabel, ((ambient, flag), some true),
        tapes slots base (encodeWord a ++ leftSuffix) (encodeWord b ++ rightSuffix)
          (true :: savedLeft) (true :: savedRight)⟩ := by
  change some (TM2.stepAux (program scanLabel) _ _) = _
  rw [atScan]
  simp [scan, TM2.stepAux, encodeWord, List.replicate_succ]

theorem scanTrace (slots : Fin 4 ↪ K) (scanLabel restoreLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atScan : program scanLabel = scan slots scanLabel restoreLabel)
    (base : K → List Bool) (a b : Nat) (leftSuffix rightSuffix savedLeft savedRight : List Bool)
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    (advance (TM2.step program))^[min a b + 1]
      (some ⟨some scanLabel, ((ambient, flag), register),
        tapes slots base (encodeWord a ++ leftSuffix) (encodeWord b ++ rightSuffix) savedLeft savedRight⟩) =
      some ⟨some restoreLabel, ((ambient, decide (a < b)), none),
        tapes slots base (encodeWord (a - b) ++ leftSuffix) (encodeWord (b - a) ++ rightSuffix)
          (List.replicate (min a b) true ++ savedLeft) (List.replicate (min a b) true ++ savedRight)⟩ := by
  induction a generalizing b savedLeft savedRight register with
  | zero =>
    simpa using scan_step_zero_left slots scanLabel restoreLabel program atScan base b
      leftSuffix rightSuffix savedLeft savedRight ambient flag register
  | succ a ih =>
    cases b with
    | zero =>
      simpa using scan_step_zero_right slots scanLabel restoreLabel program atScan base a
        leftSuffix rightSuffix savedLeft savedRight ambient flag register
    | succ b =>
      have hm : min (a + 1) (b + 1) = min a b + 1 := by omega
      rw [hm, Function.iterate_succ_apply]
      simp only [advance_some]
      rw [scan_step_succ slots scanLabel restoreLabel program atScan, ih]
      have hsave (xs : List Bool) :
          List.replicate (min a b) true ++ true :: xs =
            List.replicate (min a b + 1) true ++ xs := by
        simp [List.replicate_add, List.append_assoc]
      simp only [hsave, Nat.add_sub_add_right, Nat.add_lt_add_iff_right]

instance instFintypeLabel : Fintype Label where
  elems := { .scan, .restoreLeft, .restoreRight }
  complete l := by cases l <;> simp

theorem comparisonTrace (slots : Fin 4 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ l, program (labels l) = statement slots labels exit l)
    (base : K → List Bool) (a b : Nat) (leftSuffix rightSuffix : List Bool)
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    (advance (TM2.step program))^[steps a b]
      (some ⟨some (labels .scan), ((ambient, flag), register),
        tapes slots base (encodeWord a ++ leftSuffix) (encodeWord b ++ rightSuffix) [] []⟩) =
      some ⟨exit, ((ambient, decide (a < b)), none),
        tapes slots base (encodeWord a ++ leftSuffix) (encodeWord b ++ rightSuffix) [] []⟩ := by
  have hscan := scanTrace slots (labels .scan) (labels .restoreLeft) program (atLabels .scan)
    base a b leftSuffix rightSuffix [] [] ambient flag register
  simp only [List.append_nil] at hscan
  have hwordLeft : List.replicate (min a b) true ++ (encodeWord (a - b) ++ leftSuffix) =
      encodeWord a ++ leftSuffix := by
    rw [MachineUnaryAffineAt.prepend_replicate_word,
      show min a b + (a - b) = a by omega]
  have hwordRight : List.replicate (min a b) true ++ (encodeWord (b - a) ++ rightSuffix) =
      encodeWord b ++ rightSuffix := by
    rw [MachineUnaryAffineAt.prepend_replicate_word,
      show min a b + (b - a) = b by omega]
  let middle := tapes slots base (encodeWord (a - b) ++ leftSuffix)
    (encodeWord (b - a) ++ rightSuffix) (List.replicate (min a b) true) (List.replicate (min a b) true)
  have hleft := Reduction.MachineTransfer.transferAt_fromTapes
    (Γ := fun _ : K => Bool) (σ := σ × Bool) (slots 2) (slots 0)
    (slots.injective.ne (by decide)) id false (labels .restoreLeft) (some (labels .restoreRight))
    program (by simpa only [statement] using atLabels .restoreLeft)
    middle (ambient, decide (a < b)) none
  change (advance (TM2.step program))^[(middle (slots 2)).length + 1]
    (some ⟨some (labels .restoreLeft), ((ambient, decide (a < b)), none), middle⟩) = _ at hleft
  simp only [middle, tapes_savedLeft, tapes_left, List.length_replicate, List.reverse_replicate,
    List.map_id, hwordLeft, transferLeft_tapes] at hleft
  let afterLeft := tapes slots base (encodeWord a ++ leftSuffix)
    (encodeWord (b - a) ++ rightSuffix) [] (List.replicate (min a b) true)
  have hright := Reduction.MachineTransfer.transferAt_fromTapes
    (Γ := fun _ : K => Bool) (σ := σ × Bool) (slots 3) (slots 1)
    (slots.injective.ne (by decide)) id false (labels .restoreRight) exit
    program (by simpa only [statement] using atLabels .restoreRight)
    afterLeft (ambient, decide (a < b)) none
  change (advance (TM2.step program))^[(afterLeft (slots 3)).length + 1]
    (some ⟨some (labels .restoreRight), ((ambient, decide (a < b)), none), afterLeft⟩) = _ at hright
  simp only [afterLeft, tapes_savedRight, tapes_right, List.length_replicate, List.reverse_replicate,
    List.map_id, hwordRight, transferRight_tapes] at hright
  have hfirst : (advance (TM2.step program))^[(min a b + 1) + (min a b + 1)]
      (some ⟨some (labels .scan), ((ambient, flag), register),
        tapes slots base (encodeWord a ++ leftSuffix) (encodeWord b ++ rightSuffix) [] []⟩) =
      some ⟨some (labels .restoreRight), ((ambient, decide (a < b)), none), afterLeft⟩ := by
    rw [Function.iterate_add_apply, hscan]
    exact hleft
  rw [show steps a b = (min a b + 1) + ((min a b + 1) + (min a b + 1)) by
    unfold steps; omega, Function.iterate_add_apply, hfirst]
  exact hright

end MaxCutGames.Foundations.Complexity.MachineUnaryLessAt

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_Alphabet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Physical construction of an internal regularization row

The input values belong on unary tapes. The cloud degree and the queried port
are the only arithmetic parameters fixed in finite control. The stored cloud
rotation supplies both the destination's local index and the return port.
The final row contains the full fixed equality predicate.
-/

namespace MaxCutGames.Foundations.Complexity.MachineRegularInternalRow

open Turing MachineComposition
open PCP
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)

variable {K Λ σ : Type} [DecidableEq K]

/-- This literal is independent of the graph input. -/
def equalityBits : List Bool :=
  encodeWords (GraphTables.relationWords PreprocessingInternalRows.equalityRelation)

theorem equalityBits_length_le : equalityBits.length ≤ 8192 :=
  GraphTables.relationBits_length_le _

def emittedBits (q x z r : Nat) : List Bool :=
  encodeWord x ++ encodeWord ((q + 1) * z + r) ++ equalityBits

theorem emittedBits_length (q x z r : Nat) :
    (emittedBits q x z r).length = x + ((q + 1) * z + r) + equalityBits.length + 2 := by
  simp only [emittedBits, List.length_append, encodeWord_length]
  omega

/-- The address supplied to the physical lookup is the actual port-table row. -/
theorem selected_rotation {n q : Nat} (table : ExpanderTables.Table n q)
    (i : Fin n) (p : Fin q) :
    (ExpanderTableWords.rotationWords table)[q * i.val + p.val]? =
      some (q * (ExpanderTables.lookup table (i, p)).1.val +
        (ExpanderTables.lookup table (i, p)).2.val) := by
  simpa only [Nat.add_comm] using ExpanderTableWords.rotationWords_row_order table (i, p)

theorem selected_rotation_div {n q : Nat} (positive : 0 < q)
    (table : ExpanderTables.Table n q) (i : Fin n) (p : Fin q) :
    (q * (ExpanderTables.lookup table (i, p)).1.val +
      (ExpanderTables.lookup table (i, p)).2.val) / q =
        (ExpanderTables.lookup table (i, p)).1.val := by
  rw [Nat.add_comm, Nat.add_mul_div_left _ _ positive,
    Nat.div_eq_of_lt (ExpanderTables.lookup table (i, p)).2.isLt, Nat.zero_add]

theorem selected_rotation_mod {n q : Nat} (_positive : 0 < q)
    (table : ExpanderTables.Table n q) (i : Fin n) (p : Fin q) :
    (q * (ExpanderTables.lookup table (i, p)).1.val +
      (ExpanderTables.lookup table (i, p)).2.val) % q =
        (ExpanderTables.lookup table (i, p)).2.val := by
  rw [Nat.mul_add_mod_self_left,
    Nat.mod_eq_of_lt (ExpanderTables.lookup table (i, p)).2.isLt]

/-- The return port is copied from its physical unary tape before fixed-slope
arithmetic adds the actual selected global target. -/
def finishInstruction (q : Nat) (tape : Fin 8 → K) (labels : FinishLabel → Λ)
    (exit : Option Λ) : FinishLabel → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)
  | .seedReturn => MachineUnaryAffineAt.seed (tape 4) 0 (labels .copyReturn)
  | .copyReturn => MachineUnaryAffineAt.scan (tape 2) (tape 3) (tape 4) 1
      (labels .copyReturn) (labels .restoreReturn)
  | .restoreReturn => Reduction.MachineTransfer.loopAt (tape 3) (tape 2) id false
      (labels .restoreReturn) (some (labels .affine))
  | .affine => MachineUnaryAffineAt.scan (tape 1) (tape 3) (tape 4) (q + 1)
      (labels .affine) (labels .restoreTarget)
  | .restoreTarget => Reduction.MachineTransfer.loopAt (tape 3) (tape 1) id false
      (labels .restoreTarget) (some (labels .equality))
  | .equality => pushWord (tape 5) equalityBits.reverse
      (.goto fun _ => labels (.row .relationRead))
  | .row stage => MachineTableRows.routine (finishFields tape) (tape 6) (tape 7) (tape 3)
      (fun l => labels (.row l)) (some (labels .clearReverse)) stage
  | .clearReverse => MachineDrain.drain (tape 4) (labels .clearReverse)
      (some (labels .clearEquality))
  | .clearEquality => MachineDrain.drain (tape 5) (labels .clearEquality) exit

def finishSteps (q x z r outputLength : Nat) : Nat :=
  (2 * (r + 1) + 1) + 2 * (z + 1) + 1 +
    (4 * (x + ((q + 1) * z + r) + equalityBits.length + 2) + 2 * outputLength + 9) +
    (((q + 1) * z + r) + 2) + (equalityBits.length + 1)

/-- Actual final arithmetic, full relation emission, row append and cleanup.
The only changed tape is the accumulated output; both physical target fields
and all metadata are preserved. No execution hypothesis is supplied. -/
theorem finishTrace (q : Nat) (tape : Fin 8 → K) (distinct : Function.Injective tape)
    (labels : FinishLabel → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (code : ∀ l, program (labels l) = finishInstruction q tape labels exit l)
    (base : K → List Bool) (x z r : Nat)
    (tailWord : base (tape 0) = encodeWord x)
    (targetWord : base (tape 1) = encodeWord z)
    (returnWord : base (tape 2) = encodeWord r)
    (scratchEmpty : base (tape 3) = []) (reverseEmpty : base (tape 4) = [])
    (equalityEmpty : base (tape 5) = []) (rowEmpty : base (tape 6) = [])
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[finishSteps q x z r (base (tape 7)).length]
      (some ⟨some (labels .seedReturn), (ambient, register), base⟩) =
      some ⟨exit, (ambient, none),
        Function.update base (tape 7) (base (tape 7) ++ emittedBits q x z r)⟩ := by
  have hd (i j : Fin 8) (h : i ≠ j) : tape i ≠ tape j := fun e => h (distinct e)
  let w := (q + 1) * z + r
  let copied := Function.update base (tape 4) (encodeWord r)
  let computed := Function.update base (tape 4) (encodeWord w)
  let initialized := Function.update computed (tape 5) equalityBits
  let appended := Function.update initialized (tape 7)
    (base (tape 7) ++ emittedBits q x z r)
  let drained := Function.update appended (tape 4) []
  have copyRun : (advance (TM2.step program))^[2 * (r + 1) + 1]
      (some ⟨some (labels .seedReturn), (ambient, register), base⟩) =
      some ⟨some (labels .affine), (ambient, none), copied⟩ := by
    simpa only [copied, Nat.one_mul, Nat.add_zero, reverseEmpty, List.append_nil] using
      MachineUnaryAffineAt.seededAffineTrace (tape 2) (tape 3) (tape 4)
        (hd 2 3 (by decide)) (hd 2 4 (by decide)) (hd 3 4 (by decide)) 1 0
        (labels .seedReturn) (labels .copyReturn) (labels .restoreReturn)
        (some (labels .affine)) program (code .seedReturn) (code .copyReturn)
        (code .restoreReturn) base r [] (by simpa using returnWord) scratchEmpty ambient register
  have affineFrame (u : Nat) :
      MachineUnaryAffineAt.tapes (tape 1) (tape 3) (tape 4) base
        (encodeWord z ++ []) [] (encodeWord u ++ []) =
        Function.update base (tape 4) (encodeWord u) := by
    simp only [List.append_nil]
    rw [← targetWord, ← scratchEmpty]
    simp only [MachineUnaryAffineAt.tapes, MachineCopy.forkTapes, Function.update_eq_self]
  have affineRun : (advance (TM2.step program))^[2 * (z + 1)]
      (some ⟨some (labels .affine), (ambient, none), copied⟩) =
      some ⟨some (labels .equality), (ambient, none), computed⟩ := by
    simpa only [affineFrame, copied, computed, w] using
      MachineUnaryAffineAt.affineTrace (tape 1) (tape 3) (tape 4)
        (hd 1 3 (by decide)) (hd 1 4 (by decide)) (hd 3 4 (by decide)) (q + 1)
        (labels .affine) (labels .restoreTarget) (some (labels .equality)) program
        (code .affine) (code .restoreTarget) base z r [] [] ambient none
  have initRun : (advance (TM2.step program))^[1]
      (some ⟨some (labels .equality), (ambient, none), computed⟩) =
      some ⟨some (labels (.row .relationRead)), (ambient, none), initialized⟩ := by
    change some (TM2.stepAux (program (labels .equality)) _ _) = _
    rw [code]
    simp [finishInstruction, stepAux_pushWord, TM2.stepAux, computed, initialized,
      hd 5 4 (by decide), equalityEmpty]
  have hfields : ∀ i, finishFields tape i ≠ tape 6 ∧ finishFields tape i ≠ tape 3 := by
    intro i
    fin_cases i <;> simp only []
    all_goals exact ⟨hd _ _ (by decide), hd _ _ (by decide)⟩
  have hbits : MachineTableRows.fieldBits (finishFields tape) initialized =
      emittedBits q x z r := by
    simp [MachineTableRows.fieldBits, initialized, computed, finishFields, tailWord,
      hd 0 4 (by decide), hd 0 5 (by decide), hd 4 5 (by decide), emittedBits, w]
  have hsize : MachineTableRows.fieldSize (finishFields tape) initialized =
      x + w + equalityBits.length + 2 := by
    rw [← MachineTableRows.fieldBits_length, hbits, emittedBits_length]
  have hout : initialized (tape 7) = base (tape 7) := by
    simp [initialized, computed, hd 7 4 (by decide), hd 7 5 (by decide)]
  have rowRun : (advance (TM2.step program))^[
      4 * (x + w + equalityBits.length + 2) + 2 * (base (tape 7)).length + 9]
      (some ⟨some (labels (.row .relationRead)), (ambient, none), initialized⟩) =
      some ⟨some (labels .clearReverse), (ambient, none), appended⟩ := by
    simpa only [hbits, hsize, hout, appended] using
      MachineTableRows.appendTrace (finishFields tape) (tape 6) (tape 7) (tape 3)
        hfields (hd 6 7 (by decide)) (hd 6 3 (by decide)) (hd 7 3 (by decide))
        (fun l => labels (.row l)) (some (labels .clearReverse)) program
        (fun l => code (.row l)) initialized
        (by simp [initialized, computed, hd 6 4 (by decide), hd 6 5 (by decide), rowEmpty])
        (by simp [initialized, computed, hd 3 4 (by decide), hd 3 5 (by decide), scratchEmpty])
        ambient none
  have hreverse : appended (tape 4) = encodeWord w := by
    simp [appended, initialized, computed, hd 4 7 (by decide), hd 4 5 (by decide)]
  have reverseRun : (advance (TM2.step program))^[w + 2]
      (some ⟨some (labels .clearReverse), (ambient, none), appended⟩) =
      some ⟨some (labels .clearEquality), (ambient, none), drained⟩ := by
    have h := MachineDrain.drainTrace (tape 4) (labels .clearReverse)
      (some (labels .clearEquality)) program (code .clearReverse)
      appended (appended (tape 4)) ambient none
    rw [Function.update_eq_self, hreverse, encodeWord_length] at h
    exact h
  have hequality : drained (tape 5) = equalityBits := by
    simp [drained, appended, initialized, hd 5 4 (by decide), hd 5 7 (by decide)]
  have finalFrame : Function.update drained (tape 5) [] =
      Function.update base (tape 7) (base (tape 7) ++ emittedBits q x z r) := by
    funext k
    by_cases h4 : k = tape 4
    · subst k
      simp [drained, hd 4 5 (by decide), hd 4 7 (by decide), reverseEmpty]
    · by_cases h5 : k = tape 5
      · subst k
        simp [hd 5 7 (by decide), equalityEmpty]
      · by_cases h7 : k = tape 7
        · subst k
          simp [drained, appended, h4, h5]
        · simp [drained, appended, initialized, computed, h4, h5, h7]
  have equalityRun : (advance (TM2.step program))^[equalityBits.length + 1]
      (some ⟨some (labels .clearEquality), (ambient, none), drained⟩) =
      some ⟨exit, (ambient, none),
        Function.update base (tape 7) (base (tape 7) ++ emittedBits q x z r)⟩ := by
    have h := MachineDrain.drainTrace (tape 5) (labels .clearEquality) exit program
      (code .clearEquality) drained (drained (tape 5)) ambient none
    rw [Function.update_eq_self, hequality, finalFrame] at h
    exact h
  exact joinTrace_inline_MachineRegularInternalRow (joinTrace_inline_MachineRegularInternalRow (joinTrace_inline_MachineRegularInternalRow (joinTrace_inline_MachineRegularInternalRow (joinTrace_inline_MachineRegularInternalRow
    copyRun affineRun) initRun) rowRun) reverseRun) equalityRun

def rotorFinalTapes {n q : Nat} (table : ExpanderTables.Table n q) (i : Fin n) (p : Fin q)
    (tape : Fin 8 → K) (base : K → List Bool) : K → List Bool :=
  MachineFixedDivMod.unaryTapes (tape 4) (tape 6) (tape 7)
    (MachineAffineLookup.finalTapes (rotorLookupTapes tape) base
      (ExpanderTableWords.rotationWords table) (q * i.val + p.val)
      (q * (ExpanderTables.lookup table (i, p)).1.val +
        (ExpanderTables.lookup table (i, p)).2.val))
    0 (ExpanderTables.lookup table (i, p)).1.val
      (ExpanderTables.lookup table (i, p)).2.val [] [] []

def rotorSteps {n q : Nat} (table : ExpanderTables.Table n q) (i : Fin n) (p : Fin q) : Nat :=
  MachineAffineLookup.steps (ExpanderTableWords.rotationWords table) i.val q p.val +
    1 + (q * (ExpanderTables.lookup table (i, p)).1.val +
      (ExpanderTables.lookup table (i, p)).2.val + 2)

inductive SelectControl
  | compare (stage : MachineUnaryLessAt.Label)
  | choose
  | copy (kind : SelectCopy) (stage : MachineUnaryAffineAt.Label)
  | subtract
  | add (kind : SelectAdd) (stage : SelectAddStage)
  | cleanup (i : Fin 5)
  deriving DecidableEq, Fintype

abbrev SelectLabel := MachineCloudSelect.Label ⊕ SelectControl

def afterCopy : SelectCopy → SelectLabel
  | .oldLocal => .inr (.copy .oldOwner .seed)
  | .oldOwner => .inl (.inr .initialize_)
  | .dummyLocal => .inr (.copy .dummySize .seed)
  | .dummySize => .inr .subtract
  | .dummyDifference => .inr (.add .prefixOffset .scan)

def afterAdd : SelectAdd → SelectLabel
  | .prefixOffset => .inr (.add .darts .scan)
  | .darts => .inr (.cleanup 0)

def afterCleanup (i : Fin 5) : Option SelectLabel :=
  if h : i.val + 1 < 5 then some (.inr (.cleanup ⟨i.val + 1, h⟩)) else none

def selectControl : SelectControl → TM2.Stmt SelectAlphabet SelectLabel (SelectState σ)
  | .compare stage => MachineUnaryLessAt.statement compareSlots
      (fun s => .inr (.compare s)) (some (.inr .choose)) stage
  | .choose => .branch (fun s => s.1.2)
      (.load (fun s => ((s.1.1, false), none))
        (.goto fun _ => .inr (.copy .oldLocal .seed)))
      (.load (fun s => ((s.1.1, false), none))
        (.goto fun _ => .inr (.copy .dummyLocal .seed)))
  | .copy kind .seed => MachineUnaryAffineAt.seed (copyDestination kind) 0
      (.inr (.copy kind .scan))
  | .copy kind .scan => MachineUnaryAffineAt.scan (copySource kind) selectScratch
      (copyDestination kind) 1 (.inr (.copy kind .scan)) (.inr (.copy kind .restore))
  | .copy kind .restore => Reduction.MachineTransfer.loopAt selectScratch (copySource kind)
      id false (.inr (.copy kind .restore)) (some (afterCopy kind))
  | .subtract => MachineUnaryLessAt.scan subtractSlots (.inr .subtract)
      (.inr (.copy .dummyDifference .seed))
  | .add kind .scan => MachineUnaryAffineAt.scan (addSource kind) selectScratch selectOutput 1
      (.inr (.add kind .scan)) (.inr (.add kind .restore))
  | .add kind .restore => Reduction.MachineTransfer.loopAt selectScratch (addSource kind)
      id false (.inr (.add kind .restore)) (some (afterAdd kind))
  | .cleanup i => MachineDrain.drain (cleanupTape i) (.inr (.cleanup i)) (afterCleanup i)

/-- All arithmetic is on extra tapes. The old-dart branch literally contains
the shared selector program, with only static tape, label and state transport. -/
def rawSelectProgram : SelectLabel → TM2.Stmt RawSelectAlphabet SelectLabel (SelectState σ) :=
  MachineStateEquiv.program (selectStateEquiv σ)
    (MachineEmbedding.program (some (.inr (.cleanup 0))) MachineCloudSelect.program
      (fun control => MachineStateEquiv.statement (selectStateEquiv σ).symm
        (MachineAlphabetTransport.statement selectAlphabet_eq.symm (selectControl control))))

def selectProgram : SelectLabel → TM2.Stmt SelectAlphabet SelectLabel (SelectState σ) :=
  MachineAlphabetTransport.program selectAlphabet_eq rawSelectProgram

@[simp] theorem selectProgram_control (l : SelectControl) :
    selectProgram (σ := σ) (.inr l) = selectControl l := by
  change MachineAlphabetTransport.statement selectAlphabet_eq
    (MachineStateEquiv.statement (selectStateEquiv σ)
      (MachineStateEquiv.statement (selectStateEquiv σ).symm
        (MachineAlphabetTransport.statement selectAlphabet_eq.symm (selectControl l)))) = _
  have h := MachineStateEquiv.statement_symm_statement (selectStateEquiv σ).symm
    (MachineAlphabetTransport.statement selectAlphabet_eq.symm (selectControl (σ := σ) l))
  simp only [Equiv.symm_symm] at h
  rw [h]
  exact MachineAlphabetTransport.statement_roundtrip selectAlphabet_eq _

def selectCleanState (ambient : σ) (register : Option Bool) : SelectState σ :=
  (((ambient, .checking), false), register)

inductive CoreLabel (q : Nat)
  | rotor (stage : RotorLabel q)
  | select (stage : SelectLabel)
  | finish (stage : FinishLabel)
  | cleanup (i : Fin 10)
  deriving DecidableEq, Fintype

def coreEntry (q : Nat) : CoreLabel q := .rotor (.lookup .seed)

def selectExtraMemory (j v k offset m : Nat)
    (savedLeft savedRight localWork sizeWork : List Bool) :
    SelectExtraTape → List Bool
  | .localIndex => encodeWord j
  | .owner => encodeWord v
  | .cloudSize => encodeWord k
  | .prefixOffset => encodeWord offset
  | .darts => encodeWord m
  | .savedLeft => savedLeft
  | .savedRight => savedRight
  | .localWork => localWork
  | .sizeWork => sizeWork

def selectMemory (graph : List Bool) (j v k offset m : Nat)
    (query output savedLeft savedRight localWork sizeWork : List Bool) :
    SelectTape → List Bool :=
  selectToBoolTapes (MachineEmbedding.tapes
    (MachineCloudSelect.memory graph [] query [] [] [] output)
    (selectExtraMemory j v k offset m savedLeft savedRight localWork sizeWork))

@[simp] theorem selectMemory_query (graph : List Bool) (j v k o m : Nat)
    (query output a b c d : List Bool) :
    selectMemory graph j v k o m query output a b c d selectQuery = query := rfl

@[simp] theorem selectMemory_output (graph : List Bool) (j v k o m : Nat)
    (query output a b c d : List Bool) :
    selectMemory graph j v k o m query output a b c d selectOutput = output := rfl

@[simp] theorem selectMemory_scratch (graph : List Bool) (j v k o m : Nat)
    (query output a b c d : List Bool) :
    selectMemory graph j v k o m query output a b c d selectScratch = [] := rfl

@[simp] theorem selectMemory_extra (graph : List Bool) (j v k o m : Nat)
    (query output a b c d : List Bool) (z : SelectExtraTape) :
    selectMemory graph j v k o m query output a b c d (.inr z) =
      selectExtraMemory j v k o m a b c d z := rfl

@[simp] theorem update_selectMemory_query (graph : List Bool) (j v k o m : Nat)
    (query output a b c d word : List Bool) :
    Function.update (selectMemory graph j v k o m query output a b c d) selectQuery word =
      selectMemory graph j v k o m word output a b c d := by
  funext z
  cases z with
  | inl z =>
    cases z with
    | inl z => cases z <;> rfl
    | inr z => cases z; rfl
  | inr z => cases z <;> rfl

@[simp] theorem update_selectMemory_output (graph : List Bool) (j v k o m : Nat)
    (query output a b c d word : List Bool) :
    Function.update (selectMemory graph j v k o m query output a b c d) selectOutput word =
      selectMemory graph j v k o m query word a b c d := by
  funext z
  cases z with
  | inl z =>
    cases z with
    | inl z => cases z <;> rfl
    | inr z => cases z; rfl
  | inr z => cases z <;> rfl

@[simp] theorem update_selectMemory_local (graph : List Bool) (j v k o m : Nat)
    (query output a b c d word : List Bool) :
    Function.update (selectMemory graph j v k o m query output a b c d) (.inr .localWork) word =
      selectMemory graph j v k o m query output a b word d := by
  funext z
  cases z with
  | inl z =>
    cases z with
    | inl z => cases z <;> rfl
    | inr z => cases z; rfl
  | inr z => cases z <;> rfl

@[simp] theorem update_selectMemory_size (graph : List Bool) (j v k o m : Nat)
    (query output a b c d word : List Bool) :
    Function.update (selectMemory graph j v k o m query output a b c d) (.inr .sizeWork) word =
      selectMemory graph j v k o m query output a b c word := by
  funext z
  cases z with
  | inl z =>
    cases z with
    | inl z => cases z <;> rfl
    | inr z => cases z; rfl
  | inr z => cases z <;> rfl

@[simp] theorem update_selectMemory_left (graph : List Bool) (j v k o m : Nat)
    (query output a b c d word : List Bool) :
    Function.update (selectMemory graph j v k o m query output a b c d) (.inr .savedLeft) word =
      selectMemory graph j v k o m query output word b c d := by
  funext z
  cases z with
  | inl z =>
    cases z with
    | inl z => cases z <;> rfl
    | inr z => cases z; rfl
  | inr z => cases z <;> rfl

@[simp] theorem update_selectMemory_right (graph : List Bool) (j v k o m : Nat)
    (query output a b c d word : List Bool) :
    Function.update (selectMemory graph j v k o m query output a b c d) (.inr .savedRight) word =
      selectMemory graph j v k o m query output a word c d := by
  funext z
  cases z with
  | inl z =>
    cases z with
    | inl z => cases z <;> rfl
    | inr z => cases z; rfl
  | inr z => cases z <;> rfl

end MaxCutGames.Foundations.Complexity.MachineRegularInternalRow

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachinePortReindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Complexity.MachinePortReindex

open Turing MachineComposition
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)

variable {K Λ A : Type} [DecidableEq K]

abbrev State (A : Type) (d : Nat) := MachineFixedDivMod.State A d

def clean (d : Nat) (positive : 0 < d) (ambient : A) : State A d :=
  ((ambient, MachineFixedDivMod.residue d positive 0), none)

def exitAt {d : Nat} (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A d) :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

/-- A residue-indexed literal instruction; its length is bounded by `d+b`. -/
def emit (d : Nat) (positive : 0 < d) (output : K) (b : Nat)
    (r : Fin d) (next : Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A d) :=
  pushWord output (List.replicate (r.val + b) true)
    (.load (fun s => clean d positive s.1.1) (.goto fun _ => next))

def instruction (d : Nat) (positive : 0 < d) (c b : Nat)
    (tape : Fin 5 → K) (labels : Label d → Λ) (exit : Option Λ) :
    Label d → TM2.Stmt (Alphabet (K := K)) Λ (State A d)
  | .copySeed => MachineUnaryAffineAt.seed (tape 2) 0 (labels .copyScan)
  | .copyScan => MachineUnaryAffineAt.scan (tape 0) (tape 1) (tape 2) 1
      (labels .copyScan) (labels .copyRestore)
  | .copyRestore => Reduction.MachineTransfer.loopAt (tape 1) (tape 0) id false
      (labels .copyRestore) (some (labels .initialize_))
  | .initialize_ => .push (tape 3) (fun _ => false)
      (.push (tape 4) (fun _ => false) (.goto fun _ => labels .divide))
  | .divide => MachineFixedDivMod.scanLoop d positive (tape 2) (tape 3)
      (labels .divide) (fun r => labels (.emit r))
  | .emit r => emit d positive (tape 4) b r (labels .affineScan)
  | .affineScan => MachineUnaryAffineAt.scan (tape 3) (tape 1) (tape 4) c
      (labels .affineScan) (labels .affineRestore)
  | .affineRestore => Reduction.MachineTransfer.loopAt (tape 1) (tape 3) id false
      (labels .affineRestore) (some (labels .drainQuotient))
  | .drainQuotient => MachineDrain.drain (tape 3) (labels .drainQuotient)
      (some (labels .finish))
  | .finish => .pop (tape 2) (fun s _ => clean d positive s.1.1) (exitAt exit)

/-- Exact execution in any caller containing these finite instructions. The
only changed caller tape is the output; the input field and all three initially
empty work tapes are preserved exactly. -/
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

end MaxCutGames.Foundations.Complexity.MachinePortReindex

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_PreprocessingLazyWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact codec expansion of the executable lazy graph table. Each vertex
contributes its `d` always-accepting selfloops, followed by its `d` stored
constraints with the reverse field changed by the displayed div/mod map. -/

namespace MaxCutGames.Foundations.PCP.PreprocessingLazyWords

open PortTables GraphTables PreprocessingOverlayTables
open MaxCutGames.Foundations.Complexity

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

theorem row_lazy_stay (table : PortTables.Table n d) (v : Fin n) (p : Fin d) :
    row (lazy table) v (lazyPorts d (false, p)) = stayRow d v p := by
  have hr : (lazy table).reverseIndex[rowIndex n (2 * d) (v, lazyPorts d (false, p))] =
      rowIndex n (2 * d) (v, lazyPorts d (false, p)) := by
    rw [← rowIndex_rotation, lazy_rotation_false]
  have hp : (lazy table).relations[rowIndex n (2 * d) (v, lazyPorts d (false, p))] =
      trueRelation := by
    apply relation_ext_inline_PreprocessingLazyWords
    intro a b
    simpa only [PortTables.accepts, relationAt, trueRelation, Fin.getElem_fin,
      Vector.getElem_replicate] using lazy_accepts_false table v p a b
  exact congrArg₂ (DartRow.mk v) hr hp

theorem row_lazy_move (table : PortTables.Table n d) (v : Fin n) (p : Fin d) :
    row (lazy table) v (lazyPorts d (true, p)) = moveRow table v p := by
  have hr : (lazy table).reverseIndex[rowIndex n (2 * d) (v, lazyPorts d (true, p))] =
      rowIndex n (2 * d) ((rotation table (v, p)).1,
        lazyPorts d (true, (rotation table (v, p)).2)) := by
    rw [← rowIndex_rotation, lazy_rotation_true]
  have hp : (lazy table).relations[rowIndex n (2 * d) (v, lazyPorts d (true, p))] =
      table.relations[rowIndex n d (v, p)] := by
    apply relation_ext_inline_PreprocessingLazyWords
    intro a b
    exact lazy_accepts_true table v p a b
  exact congrArg₂ (DartRow.mk v) hr hp

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

theorem flatRows_list (table : PortTables.Table n d) :
    (flatRows table).toList =
      (List.ofFn fun v : Fin n => List.ofFn (row table v)).flatten := by
  rw [flatRows, Vector.toList_ofFn, ofFn_rowIndex]
  simp only [Equiv.symm_apply_apply]
  rfl

/-- Boolean false precedes true in the executable lazy port numbering. -/
theorem ofFn_lazyPorts {α : Type*} (f : Fin (2 * d) → α) :
    List.ofFn f = List.ofFn (fun p => f (lazyPorts d (false, p))) ++
      List.ofFn (fun p => f (lazyPorts d (true, p))) := by
  have hf (p : Fin d) : rowIndex 2 d (0, p) = lazyPorts d (false, p) := by
    apply Fin.ext
    simp only [rowIndex_val, Fin.val_zero, Nat.mul_zero, Nat.add_zero, lazyPorts_false_val]
  have ht (p : Fin d) : rowIndex 2 d ((0 : Fin 1).succ, p) = lazyPorts d (true, p) := by
    apply Fin.ext
    simp only [rowIndex_val, Fin.val_succ, Fin.val_zero, Nat.zero_add,
      Nat.mul_one, lazyPorts_true_val]
  simpa only [List.ofFn_succ, List.ofFn_zero, List.flatten_cons, List.flatten_nil,
    List.append_nil, hf, ht] using (ofFn_rowIndex (n := 2) (d := d) f)

def vertexRows (table : PortTables.Table n d) (v : Fin n) :
    List (DartRow n (n * (2 * d))) :=
  List.ofFn (stayRow d v) ++ List.ofFn (moveRow table v)

/-- Every stored lazy row, with no permutation or multiset quotient. -/
theorem flatRows_lazy (table : PortTables.Table n d) :
    (flatRows (lazy table)).toList = (List.ofFn (vertexRows table)).flatten := by
  rw [flatRows_list]
  apply congrArg List.flatten
  congr 1
  funext v
  rw [ofFn_lazyPorts]
  simp only [row_lazy_stay, row_lazy_move]
  rfl

/-- The full existing word codec, including both graph header fields. -/
theorem tableWords_lazy (table : PortTables.Table n d) :
    PortTables.tableWords (lazy table) =
      [n, n * (2 * d)] ++ (List.ofFn (vertexRows table)).flatten.flatMap rowWords := by
  rw [PortTables.tableWords_eq, flatRows_lazy]

/-- The same statement for the exact unary-delimited Boolean input/output codec. -/
theorem tableBits_lazy (table : PortTables.Table n d) :
    PortTables.tableBits (lazy table) =
      encodeWords ([n, n * (2 * d)] ++
        (List.ofFn (vertexRows table)).flatten.flatMap rowWords) := by
  change encodeWords (PortTables.tableWords (lazy table)) = _
  rw [tableWords_lazy]

end MaxCutGames.Foundations.PCP.PreprocessingLazyWords

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineLazyRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Complexity.MachineLazyRows

open Turing MachineComposition PCP.GraphTables
open PCP.PreprocessingLazyWords (reverseMap moveRow moveRow_words)

variable {K Λ A : Type} [DecidableEq K]

abbrev State (A : Type) (d : Nat) := MachinePortReindex.State A d

/-- The program depends on the fixed degree and tape placement, never on
input-dependent vertices, reverse indices, or predicate values. -/
def reindexInstruction (d : Nat) (positive : 0 < d) (c b : Nat) (tape : Fin 9 → K)
    (labels : Label d → Λ) (exit : Option Λ) :
    Label d → TM2.Stmt (fun _ : K => Bool) Λ (State A d)
  | .inl stage => MachinePortReindex.instruction d positive c b
      (tape ∘ addressIndex) (fun stage => labels (.inl stage))
      (some (labels (.inr .relationRead))) stage
  | .inr stage => MachineTableRows.routine (fields tape) (tape 8) (tape 7) (tape 3)
      (fun stage => labels (.inr stage)) exit stage

def reindexRowBits (d c b v j : Nat) (relation : RelationTable) : List Bool :=
  encodeWord v ++ encodeWord (MachinePortReindex.value d c b j) ++
    encodeWords (relationWords relation)

def reindexMappedTapes (d c b j : Nat) (tape : Fin 9 → K)
    (base : K → List Bool) : K → List Bool :=
  Function.update base (tape 6) (encodeWord (MachinePortReindex.value d c b j))

def reindexResultTapes (d c b v j : Nat) (relation : RelationTable)
    (tape : Fin 9 → K) (base : K → List Bool) : K → List Bool :=
  Function.update (reindexMappedTapes d c b j tape base) (tape 7)
    (base (tape 7) ++ reindexRowBits d c b v j relation)

def reindexSteps (d c b v j : Nat) (relation : RelationTable) (output : List Bool) : Nat :=
  MachinePortReindex.steps d j + 4 * (reindexRowBits d c b v j relation).length +
    2 * output.length + 9

def rowBits (d v j : Nat) (relation : RelationTable) : List Bool :=
  encodeWord v ++ encodeWord (reverseMap d j) ++ encodeWords (relationWords relation)

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

/-- The body emits exactly the moving row of the actual lazy table. -/
theorem rowBits_eq_moveRow {n d : Nat} (table : PCP.PortTables.Table n d)
    (v : Fin n) (p : Fin d) :
    rowBits d v.val (PCP.PreprocessingLazyWords.row table v p).reverseIndex.val
        (PCP.PreprocessingLazyWords.row table v p).relation =
      encodeWords (rowWords (moveRow table v p)) := by
  rw [moveRow_words]
  simp [rowBits, encodeWords]

abbrev StreamState (A : Type) (d : Nat) := State (A × Buffer) d

def streamClean (d : Nat) (positive : 0 < d) (ambient : A) : StreamState A d :=
  MachinePortReindex.clean d positive (ambient, MachineRegularOriginalRow.zeroBuffer)

/-- Only finite register coordinates change; all tapes remain fixed. -/
def relationStateEquiv (A : Type) (d : Nat) :
    MachineRegularOriginalRow.State (A × Fin d) ≃ StreamState A d where
  toFun s := (((s.1.1.1, s.1.2), s.1.1.2), s.2)
  invFun s := (((s.1.1.1, s.1.2), s.1.1.2), s.2)
  left_inv _ := rfl
  right_inv _ := rfl

def streamRelationCopy (d : Nat) (source destination : K) (exit : Option Λ) :
    TM2.Stmt (fun _ : K => Bool) Λ (StreamState A d) :=
  MachineStateEquiv.statement (relationStateEquiv A d)
    (MachineRegularOriginalRow.relationCopyAt source destination exit)

theorem streamRelationCopy_step (d : Nat) (positive : 0 < d)
    (source destination : K) (different : source ≠ destination)
    (label : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (StreamState A d))
    (code : program label = streamRelationCopy d source destination exit)
    (relation : RelationTable) (suffix : List Bool) (base : K → List Bool)
    (input : base source = encodeWords (relationWords relation) ++ suffix) (ambient : A) :
    TM2.step program ⟨some label, streamClean d positive ambient, base⟩ =
      some ⟨exit, streamClean d positive ambient,
        Function.update (Function.update base source suffix) destination
          (encodeWords (relationWords relation) ++ base destination)⟩ := by
  have hraw := MachineRegularOriginalRow.relationCopy_step source destination different label exit
    (fun _ => MachineRegularOriginalRow.relationCopyAt source destination exit) rfl
    relation suffix base input (ambient, MachineFixedDivMod.residue d positive 0)
    MachineRegularOriginalRow.zeroBuffer none
  have haux := Option.some.inj hraw
  change some (TM2.stepAux (program label) (streamClean d positive ambient) base) = _
  rw [code, streamRelationCopy, MachineStateEquiv.stepAux_transport_symm]
  change some (MachineStateEquiv.configuration (relationStateEquiv A d)
    (TM2.stepAux (MachineRegularOriginalRow.relationCopyAt source destination exit)
      (((ambient, MachineFixedDivMod.residue d positive 0),
        MachineRegularOriginalRow.zeroBuffer), none) base)) = _
  rw [haux]
  rfl

def streamInstruction (d : Nat) (positive : 0 < d) (c b : Nat) (tape : Fin 10 → K)
    (labels : StreamLabel d → Λ) (exit : Option Λ) :
    StreamLabel d → TM2.Stmt (fun _ : K => Bool) Λ (StreamState A d)
  | .tailStart => Hastad.SourceMachine.fieldStart (tape 0) (labels .tailRead)
  | .tailRead => Hastad.SourceMachine.fieldLoop (tape 9) (tape 0) (labels .tailRead)
      (some (labels .reverseStart))
  | .reverseStart => Hastad.SourceMachine.fieldStart (tape 1) (labels .reverseRead)
  | .reverseRead => Hastad.SourceMachine.fieldLoop (tape 9) (tape 1) (labels .reverseRead)
      (some (labels .copyRelation))
  | .copyRelation => streamRelationCopy d (tape 9) (tape 2)
      (some (labels (.row (.inl .copySeed))))
  | .row stage => reindexInstruction d positive c b (tape ∘ bodyIndex)
      (fun stage => labels (.row stage)) (some (labels .clearTail)) stage
  | .clearTail => MachineDrain.drain (tape 0) (labels .clearTail) (some (labels .clearOld))
  | .clearOld => MachineDrain.drain (tape 1) (labels .clearOld) (some (labels .clearRelation))
  | .clearRelation => MachineDrain.drain (tape 2) (labels .clearRelation) (some (labels .clearNew))
  | .clearNew => MachineDrain.drain (tape 6) (labels .clearNew) exit

def inputRowBits (v j : Nat) (relation : RelationTable) : List Bool :=
  encodeWord v ++ encodeWord j ++ encodeWords (relationWords relation)

def streamRowSteps (d c b v j : Nat) (relation : RelationTable) (output : List Bool) : Nat :=
  (v + 2) + (j + 2) + 1 + reindexSteps d c b v j relation output +
    (v + 2) + (j + 2) + ((encodeWords (relationWords relation)).length + 1) +
    (MachinePortReindex.value d c b j + 2)

def streamResultTapes (d c b v j : Nat) (relation : RelationTable)
    (tape : Fin 10 → K) (base : K → List Bool) (suffix : List Bool) : K → List Bool :=
  Function.update (Function.update base (tape 9) suffix) (tape 7)
    (base (tape 7) ++ reindexRowBits d c b v j relation)

theorem streamRowTrace (d : Nat) (positive : 0 < d) (c b : Nat) (tape : Fin 10 → K)
    (distinct : Function.Injective tape) (labels : StreamLabel d → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (StreamState A d))
    (atLabels : ∀ l, program (labels l) = streamInstruction d positive c b tape labels exit l)
    (base : K → List Bool) (v j : Nat) (relation : RelationTable) (suffix : List Bool)
    (input : base (tape 9) = inputRowBits v j relation ++ suffix)
    (empty : ∀ i : Fin 10, i ≠ 7 → i ≠ 9 → base (tape i) = []) (ambient : A) :
    (advance (TM2.step program))^[streamRowSteps d c b v j relation (base (tape 7))]
      (some ⟨some (labels .tailStart), streamClean d positive ambient, base⟩) =
      some ⟨exit, streamClean d positive ambient,
        streamResultTapes d c b v j relation tape base suffix⟩ := by
  have hd (i k : Fin 10) (h : i ≠ k) : tape i ≠ tape k := fun x => h (distinct x)
  have hb6 : bodyIndex 6 = 6 := rfl
  have hb7 : bodyIndex 7 = 7 := rfl
  have h₀ := empty 0 (by decide) (by decide)
  have h₁ := empty 1 (by decide) (by decide)
  have h₂ := empty 2 (by decide) (by decide)
  have h₃ := empty 3 (by decide) (by decide)
  have h₄ := empty 4 (by decide) (by decide)
  have h₅ := empty 5 (by decide) (by decide)
  have h₆ := empty 6 (by decide) (by decide)
  have h₈ := empty 8 (by decide) (by decide)
  let relationBits := encodeWords (relationWords relation)
  let tailLoaded := Function.update (Function.update base (tape 9)
    (encodeWord j ++ (relationBits ++ suffix))) (tape 0) (encodeWord v)
  let reverseLoaded := Function.update (Function.update tailLoaded (tape 9)
    (relationBits ++ suffix)) (tape 1) (encodeWord j)
  let loaded := Function.update (Function.update reverseLoaded (tape 9) suffix) (tape 2) relationBits
  let rowed := reindexResultTapes d c b v j relation (tape ∘ bodyIndex) loaded
  let tailCleared := Function.update rowed (tape 0) []
  let oldCleared := Function.update tailCleared (tape 1) []
  let relationCleared := Function.update oldCleared (tape 2) []
  have tailRun : (advance (TM2.step program))^[v + 2]
      (some ⟨some (labels .tailStart), streamClean d positive ambient, base⟩) =
      some ⟨some (labels .reverseStart), streamClean d positive ambient, tailLoaded⟩ := by
    have h := (Hastad.SourceMachine.fieldInTime (tape 9) (tape 0) (hd 9 0 (by decide))
      (labels .tailStart) (labels .tailRead) (some (labels .reverseStart)) program
      (atLabels .tailStart) (atLabels .tailRead) base v
      (encodeWord j ++ (relationBits ++ suffix))
      (by simpa only [inputRowBits, List.append_assoc] using input)
      ((ambient, MachineRegularOriginalRow.zeroBuffer),
        MachineFixedDivMod.residue d positive 0) none).evals_in_steps
    simp only [Hastad.SourceMachine.fieldInTime, Hastad.SourceMachine.fieldTapes,
      h₀, List.append_nil] at h
    convert h using 1 <;> rfl
  have reverseRun : (advance (TM2.step program))^[j + 2]
      (some ⟨some (labels .reverseStart), streamClean d positive ambient, tailLoaded⟩) =
      some ⟨some (labels .copyRelation), streamClean d positive ambient, reverseLoaded⟩ := by
    have hstart : tailLoaded (tape 1) = [] := by
      simp [tailLoaded, hd 1 0 (by decide), hd 1 9 (by decide), h₁]
    have h := (Hastad.SourceMachine.fieldInTime (tape 9) (tape 1) (hd 9 1 (by decide))
      (labels .reverseStart) (labels .reverseRead) (some (labels .copyRelation)) program
      (atLabels .reverseStart) (atLabels .reverseRead) tailLoaded j (relationBits ++ suffix)
      (by simp [tailLoaded, hd 9 0 (by decide)])
      ((ambient, MachineRegularOriginalRow.zeroBuffer),
        MachineFixedDivMod.residue d positive 0) none).evals_in_steps
    simp only [Hastad.SourceMachine.fieldInTime, Hastad.SourceMachine.fieldTapes,
      hstart, List.append_nil] at h
    convert h using 1 <;> rfl
  have copyRun : (advance (TM2.step program))^[1]
      (some ⟨some (labels .copyRelation), streamClean d positive ambient, reverseLoaded⟩) =
      some ⟨some (labels (.row (.inl .copySeed))), streamClean d positive ambient, loaded⟩ := by
    have hempty : reverseLoaded (tape 2) = [] := by
      simp [reverseLoaded, tailLoaded, hd 2 1 (by decide), hd 2 9 (by decide),
        hd 2 0 (by decide), h₂]
    have h := streamRelationCopy_step d positive (tape 9) (tape 2) (hd 9 2 (by decide))
      (labels .copyRelation) (some (labels (.row (.inl .copySeed)))) program
      (atLabels .copyRelation) relation suffix reverseLoaded
      (by simp [reverseLoaded, relationBits, hd 9 1 (by decide)]) ambient
    simpa only [Function.iterate_one, advance_some, hempty, List.append_nil, loaded] using h
  have hs (i : Fin 10) (hi : i ≠ 0) (hi' : i ≠ 1) (hi'' : i ≠ 2) (hi''' : i ≠ 9) :
      loaded (tape i) = base (tape i) := by
    simp [loaded, reverseLoaded, tailLoaded, hd i 0 hi, hd i 1 hi',
      hd i 2 hi'', hd i 9 hi''']
  have loadedTail : loaded (tape 0) = encodeWord v := by
    simp [loaded, reverseLoaded, tailLoaded, hd 0 2 (by decide), hd 0 9 (by decide),
      hd 0 1 (by decide)]
  have loadedReverse : loaded (tape 1) = encodeWord j := by
    simp [loaded, reverseLoaded, hd 1 2 (by decide), hd 1 9 (by decide)]
  have loadedRelation : loaded (tape 2) = relationBits := by simp [loaded]
  have bodyRun := reindexRowTrace d positive c b (tape ∘ bodyIndex)
    (distinct.comp bodyIndex_injective) (fun stage => labels (.row stage))
    (some (labels .clearTail)) program (fun stage => atLabels (.row stage)) loaded v j relation
    loadedTail loadedReverse loadedRelation
    ((hs 3 (by decide) (by decide) (by decide) (by decide)).trans h₃)
    ((hs 4 (by decide) (by decide) (by decide) (by decide)).trans h₄)
    ((hs 5 (by decide) (by decide) (by decide) (by decide)).trans h₅)
    ((hs 6 (by decide) (by decide) (by decide) (by decide)).trans h₆)
    ((hs 8 (by decide) (by decide) (by decide) (by decide)).trans h₈)
    (ambient, MachineRegularOriginalRow.zeroBuffer)
  have hout : loaded ((tape ∘ bodyIndex) 7) = base (tape 7) :=
    hs 7 (by decide) (by decide) (by decide) (by decide)
  rw [hout] at bodyRun
  change (advance (TM2.step program))^[reindexSteps d c b v j relation (base (tape 7))]
    (some ⟨some (labels (.row (.inl .copySeed))), streamClean d positive ambient, loaded⟩) =
    some ⟨some (labels .clearTail), streamClean d positive ambient, rowed⟩ at bodyRun
  have rowedTail : rowed (tape 0) = encodeWord v := by
    simp only [rowed, reindexResultTapes, reindexMappedTapes, Function.comp_apply, hb6, hb7]
    simpa only [Function.update_of_ne (hd 0 7 (by decide)),
      Function.update_of_ne (hd 0 6 (by decide))] using loadedTail
  have rowedOld : tailCleared (tape 1) = encodeWord j := by
    simp only [tailCleared, rowed, reindexResultTapes, reindexMappedTapes,
      Function.comp_apply, hb6, hb7]
    simpa only [Function.update_of_ne (hd 1 0 (by decide)),
      Function.update_of_ne (hd 1 7 (by decide)), Function.update_of_ne (hd 1 6 (by decide))]
      using loadedReverse
  have rowedRelation : oldCleared (tape 2) = relationBits := by
    simp only [oldCleared, tailCleared, rowed, reindexResultTapes, reindexMappedTapes,
      Function.comp_apply, hb6, hb7]
    simpa only [Function.update_of_ne (hd 2 1 (by decide)),
      Function.update_of_ne (hd 2 0 (by decide)), Function.update_of_ne (hd 2 7 (by decide)),
      Function.update_of_ne (hd 2 6 (by decide))] using loadedRelation
  have rowedNew : relationCleared (tape 6) = encodeWord (MachinePortReindex.value d c b j) := by
    simp [relationCleared, oldCleared, tailCleared, rowed, reindexResultTapes,
      reindexMappedTapes, Function.comp_apply, bodyIndex, hd 6 2 (by decide),
      hd 6 1 (by decide), hd 6 0 (by decide), hd 6 7 (by decide)]
  have clearTail := (MachineDrain.drainInTime (tape 0) (labels .clearTail)
    (some (labels .clearOld)) program (atLabels .clearTail) rowed
    ((ambient, MachineRegularOriginalRow.zeroBuffer),
      MachineFixedDivMod.residue d positive 0) none).evals_in_steps
  change (advance (TM2.step program))^[(rowed (tape 0)).length + 1]
    (some ⟨some (labels .clearTail), streamClean d positive ambient, rowed⟩) =
    some ⟨some (labels .clearOld), streamClean d positive ambient, tailCleared⟩ at clearTail
  rw [rowedTail, encodeWord_length] at clearTail
  have clearOld := (MachineDrain.drainInTime (tape 1) (labels .clearOld)
    (some (labels .clearRelation)) program (atLabels .clearOld) tailCleared
    ((ambient, MachineRegularOriginalRow.zeroBuffer),
      MachineFixedDivMod.residue d positive 0) none).evals_in_steps
  change (advance (TM2.step program))^[(tailCleared (tape 1)).length + 1]
    (some ⟨some (labels .clearOld), streamClean d positive ambient, tailCleared⟩) =
    some ⟨some (labels .clearRelation), streamClean d positive ambient, oldCleared⟩ at clearOld
  rw [rowedOld, encodeWord_length] at clearOld
  have clearRelation := (MachineDrain.drainInTime (tape 2) (labels .clearRelation)
    (some (labels .clearNew)) program (atLabels .clearRelation) oldCleared
    ((ambient, MachineRegularOriginalRow.zeroBuffer),
      MachineFixedDivMod.residue d positive 0) none).evals_in_steps
  change (advance (TM2.step program))^[(oldCleared (tape 2)).length + 1]
    (some ⟨some (labels .clearRelation), streamClean d positive ambient, oldCleared⟩) =
    some ⟨some (labels .clearNew), streamClean d positive ambient, relationCleared⟩ at clearRelation
  rw [rowedRelation] at clearRelation
  have clearNew := (MachineDrain.drainInTime (tape 6) (labels .clearNew)
    exit program (atLabels .clearNew) relationCleared
    ((ambient, MachineRegularOriginalRow.zeroBuffer),
      MachineFixedDivMod.residue d positive 0) none).evals_in_steps
  change (advance (TM2.step program))^[(relationCleared (tape 6)).length + 1]
    (some ⟨some (labels .clearNew), streamClean d positive ambient, relationCleared⟩) =
    some ⟨exit, streamClean d positive ambient,
      Function.update relationCleared (tape 6) []⟩ at clearNew
  rw [rowedNew, encodeWord_length] at clearNew
  have finalFrame : Function.update relationCleared (tape 6) [] =
      streamResultTapes d c b v j relation tape base suffix := by
    funext k
    by_cases h6 : k = tape 6
    · subst k
      simp [streamResultTapes, hd 6 7 (by decide), hd 6 9 (by decide), h₆]
    · by_cases h2 : k = tape 2
      · subst k
        simp [relationCleared, streamResultTapes, hd 2 6 (by decide),
          hd 2 7 (by decide), hd 2 9 (by decide), h₂]
      · by_cases h1 : k = tape 1
        · subst k
          simp [relationCleared, oldCleared, streamResultTapes,
            hd 1 6 (by decide), hd 1 2 (by decide), hd 1 7 (by decide),
            hd 1 9 (by decide), h₁]
        · by_cases h0 : k = tape 0
          · subst k
            simp [relationCleared, oldCleared, tailCleared, streamResultTapes,
              hd 0 6 (by decide), hd 0 2 (by decide), hd 0 1 (by decide),
              hd 0 7 (by decide), hd 0 9 (by decide), h₀]
          · by_cases h7 : k = tape 7
            · subst k
              simp [relationCleared, oldCleared, tailCleared, rowed, reindexResultTapes,
                reindexMappedTapes, Function.comp_apply, bodyIndex, streamResultTapes,
                loaded, reverseLoaded, tailLoaded, hd 7 6 (by decide), hd 7 2 (by decide),
                hd 7 1 (by decide), hd 7 0 (by decide), hd 7 9 (by decide)]
            · by_cases h9 : k = tape 9
              · subst k
                simp [relationCleared, oldCleared, tailCleared, rowed, reindexResultTapes,
                  reindexMappedTapes, Function.comp_apply, bodyIndex, loaded, reverseLoaded,
                  tailLoaded, streamResultTapes, hd 9 6 (by decide), hd 9 2 (by decide),
                  hd 9 1 (by decide), hd 9 0 (by decide), hd 9 7 (by decide)]
              · simp [relationCleared, oldCleared, tailCleared, rowed, reindexResultTapes,
                  reindexMappedTapes, Function.comp_apply, bodyIndex, loaded, reverseLoaded,
                  tailLoaded, streamResultTapes, h6, h2, h1, h0, h7, h9]
  rw [finalFrame] at clearNew
  exact joinTrace_inline_MachineLazyRows (joinTrace_inline_MachineLazyRows (joinTrace_inline_MachineLazyRows (joinTrace_inline_MachineLazyRows (joinTrace_inline_MachineLazyRows (joinTrace_inline_MachineLazyRows
    (joinTrace_inline_MachineLazyRows tailRun reverseRun) copyRun) bodyRun) clearTail) clearOld) clearRelation) clearNew

def vertexInstruction (d : Nat) (positive : 0 < d) (c b : Nat) (tape : Fin 10 → K)
    (labels : VertexLabel d → Λ) (exit : Option Λ) :
    VertexLabel d → TM2.Stmt (fun _ : K => Bool) Λ (StreamState A d)
  | (i, none) => if i.val < d then .goto fun _ => labels (i, some .tailStart)
      else MachinePortReindex.exitAt exit
  | (i, some stage) => if h : i.val < d then
      streamInstruction d positive c b tape (fun stage => labels (i, some stage))
        (some (labels (⟨i.val + 1, by omega⟩, none))) stage
      else MachinePortReindex.exitAt exit

def recordsInput {n m : Nat} (rows : List (DartRow n m)) : List Bool :=
  rows.flatMap (fun r => inputRowBits r.tail.val r.reverseIndex.val r.relation)

def recordsOutput {n m : Nat} (d c b : Nat) (rows : List (DartRow n m)) : List Bool :=
  rows.flatMap (fun r => reindexRowBits d c b r.tail.val r.reverseIndex.val r.relation)

def streamFrame {n m : Nat} (tape : Fin 10 → K) (base : K → List Bool)
    (rows : List (DartRow n m)) (output : List Bool) : K → List Bool :=
  Function.update (Function.update base (tape 9) (recordsInput rows ++ base (tape 9)))
    (tape 7) output

def vertexSteps {n m : Nat} (d c b : Nat) : List (DartRow n m) → List Bool → Nat
  | [], _ => 1
  | r :: rows, output => 1 + streamRowSteps d c b r.tail.val r.reverseIndex.val r.relation output +
      vertexSteps d c b rows
        (output ++ reindexRowBits d c b r.tail.val r.reverseIndex.val r.relation)

theorem streamFrame_afterRow_inline_MachineLazyRows {n m : Nat} (d c b : Nat) (r : DartRow n m)
    (tape : Fin 10 → K) (distinct : Function.Injective tape) (base : K → List Bool)
    (rows : List (DartRow n m)) (output : List Bool) :
    streamResultTapes d c b r.tail.val r.reverseIndex.val r.relation tape
      (streamFrame tape base (r :: rows) output) (recordsInput rows ++ base (tape 9)) =
      streamFrame tape base rows
        (output ++ reindexRowBits d c b r.tail.val r.reverseIndex.val r.relation) := by
  have h79 : tape 7 ≠ tape 9 := fun h => (by decide : (7 : Fin 10) ≠ 9) (distinct h)
  funext k
  by_cases h7 : k = tape 7
  · subst k
    simp [streamResultTapes, streamFrame]
  · by_cases h9 : k = tape 9
    · subst k
      simp [streamResultTapes, streamFrame, Ne.symm h79]
    · simp [streamResultTapes, streamFrame, h7, h9]

/-- Every port executes its actual loader, mapper, emitter, and cleanup.
The trace is proved from the concrete program, with no per-row run premise. -/
theorem vertexSuffixTrace {n m : Nat} (d : Nat) (positive : 0 < d) (c b : Nat)
    (tape : Fin 10 → K) (distinct : Function.Injective tape)
    (labels : VertexLabel d → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (StreamState A d))
    (atLabels : ∀ l, program (labels l) = vertexInstruction d positive c b tape labels exit l)
    (base : K → List Bool) (rows : Fin d → DartRow n m)
    (empty : ∀ i : Fin 10, i ≠ 7 → i ≠ 9 → base (tape i) = []) (ambient : A)
    (remaining : Nat) (i : Fin (d + 1)) (count : i.val + remaining = d) (output : List Bool) :
    (advance (TM2.step program))^[vertexSteps d c b ((List.ofFn rows).drop i.val) output]
      (some ⟨some (labels (i, none)), streamClean d positive ambient,
        streamFrame tape base ((List.ofFn rows).drop i.val) output⟩) =
      some ⟨exit, streamClean d positive ambient,
        streamFrame (n := n) (m := m) tape base []
          (output ++ recordsOutput d c b ((List.ofFn rows).drop i.val))⟩ := by
  have hd (a k : Fin 10) (h : a ≠ k) : tape a ≠ tape k := fun x => h (distinct x)
  induction remaining generalizing i output with
  | zero =>
      have hi : i.val = d := by omega
      have hdrop : (List.ofFn rows).drop i.val = [] := by
        apply List.drop_eq_nil_of_le
        simp only [List.length_ofFn, hi, le_refl]
      rw [hdrop]
      simp only [vertexSteps, recordsOutput, List.flatMap_nil, List.append_nil]
      change some (TM2.stepAux (program (labels (i, none))) _ _) = _
      rw [atLabels]
      cases exit <;> simp [vertexInstruction, hi, MachinePortReindex.exitAt, TM2.stepAux]
  | succ remaining ih =>
      have hi : i.val < d := by omega
      let port : Fin d := ⟨i.val, hi⟩
      let next : Fin (d + 1) := ⟨i.val + 1, by omega⟩
      let rest := (List.ofFn rows).drop (i.val + 1)
      have split : (List.ofFn rows).drop i.val = rows port :: rest := by
        have h := List.getElem_cons_drop (as := List.ofFn rows)
          (i := i.val) (by simpa only [List.length_ofFn] using hi)
        simpa only [List.getElem_ofFn, port, rest] using h.symm
      let initial := streamFrame tape base (rows port :: rest) output
      have boundary : (advance (TM2.step program))^[1]
          (some ⟨some (labels (i, none)), streamClean d positive ambient, initial⟩) =
          some ⟨some (labels (i, some .tailStart)), streamClean d positive ambient, initial⟩ := by
        change some (TM2.stepAux (program (labels (i, none))) _ _) = _
        rw [atLabels]
        simp [vertexInstruction, hi, TM2.stepAux]
      have body := streamRowTrace d positive c b tape distinct
        (fun stage => labels (i, some stage)) (some (labels (next, none))) program
        (by
          intro stage
          simpa only [vertexInstruction, hi, dite_true, next] using (atLabels (i, some stage)))
        initial (rows port).tail.val (rows port).reverseIndex.val (rows port).relation
        (recordsInput rest ++ base (tape 9))
        (by simp [initial, streamFrame, hd 9 7 (by decide), recordsInput, List.append_assoc])
        (by
          intro k hk7 hk9
          simp [initial, streamFrame, hd k 7 hk7, hd k 9 hk9, empty k hk7 hk9]) ambient
      have initialOutput : initial (tape 7) = output := by simp [initial, streamFrame]
      rw [initialOutput] at body
      change (advance (TM2.step program))^[streamRowSteps d c b
        (rows port).tail.val (rows port).reverseIndex.val (rows port).relation output]
        (some ⟨some (labels (i, some .tailStart)), streamClean d positive ambient, initial⟩) =
        some ⟨some (labels (next, none)), streamClean d positive ambient,
          streamResultTapes d c b (rows port).tail.val (rows port).reverseIndex.val
            (rows port).relation tape initial (recordsInput rest ++ base (tape 9))⟩ at body
      rw [show streamResultTapes d c b (rows port).tail.val (rows port).reverseIndex.val
        (rows port).relation tape initial (recordsInput rest ++ base (tape 9)) =
        streamFrame tape base rest
          (output ++ reindexRowBits d c b (rows port).tail.val
            (rows port).reverseIndex.val (rows port).relation) from
          streamFrame_afterRow_inline_MachineLazyRows d c b (rows port) tape distinct base rest output] at body
      have nextCount : next.val + remaining = d := by dsimp [next]; omega
      have tail := ih next nextCount
        (output ++ reindexRowBits d c b (rows port).tail.val
          (rows port).reverseIndex.val (rows port).relation)
      change (advance (TM2.step program))^[vertexSteps d c b rest
        (output ++ reindexRowBits d c b (rows port).tail.val
          (rows port).reverseIndex.val (rows port).relation)]
        (some ⟨some (labels (next, none)), streamClean d positive ambient,
          streamFrame tape base rest (output ++ reindexRowBits d c b (rows port).tail.val
            (rows port).reverseIndex.val (rows port).relation)⟩) =
        some ⟨exit, streamClean d positive ambient,
          streamFrame (n := n) (m := m) tape base [] ((output ++ reindexRowBits d c b (rows port).tail.val
            (rows port).reverseIndex.val (rows port).relation) ++ recordsOutput d c b rest)⟩ at tail
      rw [split]
      have all := joinTrace_inline_MachineLazyRows (joinTrace_inline_MachineLazyRows boundary body) tail
      simpa only [vertexSteps, initial, recordsOutput, List.flatMap_cons, List.append_assoc] using all

theorem vertexTrace {n m : Nat} (d : Nat) (positive : 0 < d) (c b : Nat)
    (tape : Fin 10 → K) (distinct : Function.Injective tape)
    (labels : VertexLabel d → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (StreamState A d))
    (atLabels : ∀ l, program (labels l) = vertexInstruction d positive c b tape labels exit l)
    (base : K → List Bool) (rows : Fin d → DartRow n m)
    (empty : ∀ i : Fin 10, i ≠ 7 → i ≠ 9 → base (tape i) = [])
    (ambient : A) (output : List Bool) :
    (advance (TM2.step program))^[vertexSteps d c b (List.ofFn rows) output]
      (some ⟨some (labels (0, none)), streamClean d positive ambient,
        streamFrame tape base (List.ofFn rows) output⟩) =
      some ⟨exit, streamClean d positive ambient,
        streamFrame (n := n) (m := m) tape base [] (output ++ recordsOutput d c b (List.ofFn rows))⟩ := by
  simpa only [Fin.val_zero, List.drop_zero] using vertexSuffixTrace d positive c b tape distinct
    labels exit program atLabels base rows empty ambient d 0 (by simp) output

theorem encodeWords_flatMap_inline_MachineLazyRows {α : Type*} (items : List α) (words : α → List Nat) :
    encodeWords (items.flatMap words) = items.flatMap (fun x => encodeWords (words x)) := by
  induction items with
  | nil => rfl
  | cons item items ih => simp only [List.flatMap_cons, encodeWords_append, ih]

/-- The computed moving-row block is exactly the actual lazy table's codec. -/
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

/-- The bound comes from all loader, mapper, emitter, and cleanup transitions. -/
theorem streamRowSteps_le {n m : Nat} (d c b : Nat) (r : DartRow n m) (output : List Bool) :
    streamRowSteps d c b r.tail.val r.reverseIndex.val r.relation output ≤
      rowCostBound c b n m + 2 * output.length := by
  have htail := r.tail.isLt.le
  have hj := r.reverseIndex.isLt.le
  have hdiv := (Nat.div_le_self r.reverseIndex.val d).trans hj
  have hvalue := reindexValue_le d c b r
  have hrelation := relationBits_length_le r.relation
  have hsize := reindexRowBits_length_le d c b r
  unfold streamRowSteps reindexSteps MachinePortReindex.steps rowCostBound
  omega

theorem vertexSteps_le_capacity_inline_MachineLazyRows {n m : Nat} (d c b capacity : Nat)
    (rows : List (DartRow n m)) (output : List Bool)
    (room : output.length + rows.length * rowSizeBound c b n m ≤ capacity) :
    vertexSteps d c b rows output ≤
      rows.length * (rowCostBound c b n m + 2 * capacity + 1) + 1 := by
  induction rows generalizing output with
  | nil => simp [vertexSteps]
  | cons r rows ih =>
      have hsize := reindexRowBits_length_le d c b r
      have hcost := streamRowSteps_le d c b r output
      have hout : output.length ≤ capacity := by omega
      have hroom : (output ++ reindexRowBits d c b r.tail.val r.reverseIndex.val r.relation).length +
          rows.length * rowSizeBound c b n m ≤ capacity := by
        rw [List.length_append]
        simp only [List.length_cons, Nat.succ_mul] at room
        omega
      have htail := ih
        (output ++ reindexRowBits d c b r.tail.val r.reverseIndex.val r.relation) hroom
      change 1 + streamRowSteps d c b r.tail.val r.reverseIndex.val r.relation output +
        vertexSteps d c b rows
          (output ++ reindexRowBits d c b r.tail.val r.reverseIndex.val r.relation) ≤
        (rows.length + 1) * (rowCostBound c b n m + 2 * capacity + 1) + 1
      rw [Nat.add_mul, Nat.one_mul]
      omega

theorem vertexSteps_le {n m : Nat} (d c b : Nat) (rows : List (DartRow n m))
    (output : List Bool) :
    vertexSteps d c b rows output ≤ rows.length * (rowCostBound c b n m +
      2 * (output.length + rows.length * rowSizeBound c b n m) + 1) + 1 :=
  vertexSteps_le_capacity_inline_MachineLazyRows d c b _ rows output (Nat.le_refl _)

end MaxCutGames.Foundations.Complexity.MachineLazyRows

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_PreprocessingOverlayWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact stored-row and codec expansion of the executable overlay. Within
each vertex block, all original ports precede all expander ports. -/

namespace MaxCutGames.Foundations.PCP.PreprocessingOverlayWords

open PortTables GraphTables PreprocessingOverlayTables
open Complexity

variable {n d e : Nat}

abbrev row := @PreprocessingLazyWords.row

def oldRow (G : PortTables.Table n d) (e : Nat) (v : Fin n) (p : Fin d) :
    DartRow n (n * (d + e)) :=
  ⟨v, rowIndex n (d + e) ((rotation G (v, p)).1,
    overlayPorts d e (.inl (rotation G (v, p)).2)),
    G.relations[rowIndex n d (v, p)]⟩

def expanderRow (d : Nat) (H : ExpanderTables.Table n e) (v : Fin n) (p : Fin e) :
    DartRow n (n * (d + e)) :=
  ⟨v, rowIndex n (d + e) ((ExpanderTables.lookup H (v, p)).1,
    overlayPorts d e (.inr (ExpanderTables.lookup H (v, p)).2)), trueRelation⟩

theorem row_overlay_old (G : PortTables.Table n d) (H : ExpanderTables.Table n e)
    (v : Fin n) (p : Fin d) :
    row (overlay G H) v (overlayPorts d e (.inl p)) = oldRow G e v p := by
  have hr : (overlay G H).reverseIndex[rowIndex n (d + e) (v, overlayPorts d e (.inl p))] =
      rowIndex n (d + e) ((rotation G (v, p)).1,
        overlayPorts d e (.inl (rotation G (v, p)).2)) := by
    rw [← rowIndex_rotation, overlay_rotation_old]
  have hp : (overlay G H).relations[rowIndex n (d + e) (v, overlayPorts d e (.inl p))] =
      G.relations[rowIndex n d (v, p)] := by
    apply relation_ext_inline_PreprocessingOverlayWords
    exact overlay_accepts_old G H v p
  exact congrArg₂ (DartRow.mk v) hr hp

theorem row_overlay_expander (G : PortTables.Table n d) (H : ExpanderTables.Table n e)
    (v : Fin n) (p : Fin e) :
    row (overlay G H) v (overlayPorts d e (.inr p)) = expanderRow d H v p := by
  have hr : (overlay G H).reverseIndex[rowIndex n (d + e) (v, overlayPorts d e (.inr p))] =
      rowIndex n (d + e) ((ExpanderTables.lookup H (v, p)).1,
        overlayPorts d e (.inr (ExpanderTables.lookup H (v, p)).2)) := by
    rw [← rowIndex_rotation, overlay_rotation_expander]
  have hp : (overlay G H).relations[rowIndex n (d + e) (v, overlayPorts d e (.inr p))] =
      trueRelation := by
    apply relation_ext_inline_PreprocessingOverlayWords
    intro a b
    simpa only [PortTables.accepts, relationAt, trueRelation,
      PreprocessingLazyWords.trueRelation, Fin.getElem_fin, Vector.getElem_replicate] using
      overlay_accepts_expander G H v p a b
  exact congrArg₂ (DartRow.mk v) hr hp

theorem oldRow_reverse_val (G : PortTables.Table n d) (v : Fin n) (p : Fin d) :
    (oldRow G e v p).reverseIndex.val = oldReverseMap d e (row G v p).reverseIndex.val := by
  simp only [oldRow, rowIndex_val, overlayPorts_inl_val, oldReverseMap, row,
    PreprocessingLazyWords.row]
  change (G.reverseIndex[rowIndex n d (v, p)]).val % d +
      (d + e) * ((G.reverseIndex[rowIndex n d (v, p)]).val / d) = _
  omega

theorem expanderRow_reverse_val (H : ExpanderTables.Table n e) (v : Fin n) (p : Fin e) :
    (expanderRow d H v p).reverseIndex.val =
      expanderReverseMap d e (ExpanderTables.reverseIndex H (ExpanderTables.rowIndex n e (v, p))).val := by
  simp only [expanderRow, rowIndex_val, overlayPorts_inr_val, expanderReverseMap]
  change d + (ExpanderTables.reverseIndex H (ExpanderTables.rowIndex n e (v, p))).val % e +
      (d + e) * ((ExpanderTables.reverseIndex H (ExpanderTables.rowIndex n e (v, p))).val / e) = _
  omega

theorem oldRow_words (G : PortTables.Table n d) (v : Fin n) (p : Fin d) :
    rowWords (oldRow G e v p) =
      [v.val, oldReverseMap d e (row G v p).reverseIndex.val] ++
        relationWords (row G v p).relation := by
  rw [rowWords, oldRow_reverse_val]
  rfl

theorem expanderRow_words (H : ExpanderTables.Table n e) (v : Fin n) (p : Fin e) :
    rowWords (expanderRow d H v p) =
      [v.val, expanderReverseMap d e
        (ExpanderTables.reverseIndex H (ExpanderTables.rowIndex n e (v, p))).val] ++
        List.replicate 4096 1 := by
  rw [rowWords, expanderRow_reverse_val]
  exact congrArg (fun rs => [v.val, expanderReverseMap d e
    (ExpanderTables.reverseIndex H (ExpanderTables.rowIndex n e (v, p))).val] ++ rs)
      PreprocessingLazyWords.relationWords_true

theorem ofFn_overlayPorts {α : Type*} (f : Fin (d + e) → α) :
    List.ofFn f = List.ofFn (fun p => f (overlayPorts d e (.inl p))) ++
      List.ofFn (fun p => f (overlayPorts d e (.inr p))) := by
  rw [List.ofFn_add]
  rfl

def vertexRows (G : PortTables.Table n d) (H : ExpanderTables.Table n e) (v : Fin n) :
    List (DartRow n (n * (d + e))) :=
  List.ofFn (oldRow G e v) ++ List.ofFn (expanderRow d H v)

theorem flatRows_overlay (G : PortTables.Table n d) (H : ExpanderTables.Table n e) :
    (flatRows (overlay G H)).toList = (List.ofFn (vertexRows G H)).flatten := by
  rw [PreprocessingLazyWords.flatRows_list]
  apply congrArg List.flatten
  congr 1
  funext v
  rw [ofFn_overlayPorts]
  simp only [row_overlay_old, row_overlay_expander]
  rfl

theorem tableWords_overlay (G : PortTables.Table n d) (H : ExpanderTables.Table n e) :
    PortTables.tableWords (overlay G H) =
      [n, n * (d + e)] ++ (List.ofFn (vertexRows G H)).flatten.flatMap rowWords := by
  rw [PortTables.tableWords_eq, flatRows_overlay]

theorem tableBits_overlay (G : PortTables.Table n d) (H : ExpanderTables.Table n e) :
    PortTables.tableBits (overlay G H) = encodeWords
      ([n, n * (d + e)] ++ (List.ofFn (vertexRows G H)).flatten.flatMap rowWords) := by
  change encodeWords (PortTables.tableWords (overlay G H)) = _
  rw [tableWords_overlay]

/-- The expander's raw stream has the same exact per-vertex port order. -/
theorem rotationWords_vertices (H : ExpanderTables.Table n e) :
    ExpanderTableWords.rotationWords H =
      (List.ofFn fun v : Fin n => List.ofFn fun p : Fin e =>
        (ExpanderTables.reverseIndex H (ExpanderTables.rowIndex n e (v, p))).val).flatten := by
  have hflat : ExpanderTableWords.rotationWords H =
      List.ofFn (fun i : Fin (n * e) => (ExpanderTables.reverseIndex H i).val) := by
    apply List.ext_getElem
    · simp [ExpanderTableWords.rotationWords_length]
    · intro i hi hj
      rw [ExpanderTableWords.rotationWords_getElem H i (by simpa using hi)]
      simp only [List.getElem_ofFn]
  rw [hflat, PreprocessingLazyWords.ofFn_rowIndex]
  rfl

end MaxCutGames.Foundations.PCP.PreprocessingOverlayWords

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineOverlayRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Complexity.MachineOverlayRows

open Turing MachineComposition
open PCP.GraphTables PCP.PreprocessingOverlayWords
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)

variable {K Λ A : Type} [DecidableEq K]

abbrev State (A : Type) (e : Nat) := MachinePortReindex.State A e

def trueBits : List Bool := encodeWords (relationWords trueRelation)

def instruction (d e : Nat) (positive : 0 < e) (tape : Fin 10 → K)
    (labels : Label e → Λ) (exit : Option Λ) :
    Label e → TM2.Stmt (fun _ : K => Bool) Λ (State A e)
  | .loadStart => Hastad.SourceMachine.fieldStart (tape 1) (labels .loadLoop)
  | .loadLoop => Hastad.SourceMachine.fieldLoop (tape 9) (tape 1)
      (labels .loadLoop) (some (labels .seedRelation))
  | .seedRelation => pushWord (tape 2) trueBits.reverse
      (.goto fun _ => labels (.row (.inl .copySeed)))
  | .row stage => MachineLazyRows.reindexInstruction e positive (d + e) d
      (tape ∘ bodyIndex) (fun stage => labels (.row stage))
      (some (labels .drainOld)) stage
  | .drainOld => MachineDrain.drain (tape 1) (labels .drainOld) (some (labels .drainNew))
  | .drainNew => MachineDrain.drain (tape 6) (labels .drainNew) (some (labels .drainRelation))
  | .drainRelation => MachineDrain.drain (tape 2) (labels .drainRelation) exit

def rowBits (d e v j : Nat) : List Bool :=
  MachineLazyRows.reindexRowBits e (d + e) d v j trueRelation

def rowSteps (d e v j : Nat) (output : List Bool) : Nat :=
  (j + 2) + 1 + MachineLazyRows.reindexSteps e (d + e) d v j trueRelation output +
    (j + 2) + (MachinePortReindex.value e (d + e) d j + 2) + (trueBits.length + 1)

def resultTapes (d e v j : Nat) (tape : Fin 10 → K) (base : K → List Bool)
    (suffix : List Bool) : K → List Bool :=
  Function.update (Function.update base (tape 9) suffix) (tape 7)
    (base (tape 7) ++ rowBits d e v j)

/-- Load the actual next expander index, execute the arithmetic and complete
4096-bit row emitter, then clear the three isolated temporary fields. -/
theorem rowTrace (d e : Nat) (positive : 0 < e) (tape : Fin 10 → K)
    (distinct : Function.Injective tape) (labels : Label e → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State A e))
    (atLabels : ∀ l, program (labels l) = instruction d e positive tape labels exit l)
    (base : K → List Bool) (v j : Nat) (suffix : List Bool)
    (tailWord : base (tape 0) = encodeWord v)
    (inputWord : base (tape 9) = encodeWord j ++ suffix)
    (empty : ∀ i : Fin 10, i ≠ 0 → i ≠ 7 → i ≠ 9 → base (tape i) = [])
    (ambient : A) :
    (advance (TM2.step program))^[rowSteps d e v j (base (tape 7))]
      (some ⟨some (labels .loadStart), MachinePortReindex.clean e positive ambient, base⟩) =
      some ⟨exit, MachinePortReindex.clean e positive ambient,
        resultTapes d e v j tape base suffix⟩ := by
  have hd (i k : Fin 10) (h : i ≠ k) : tape i ≠ tape k := fun x => h (distinct x)
  have h₁ := empty 1 (by decide) (by decide) (by decide)
  have h₂ := empty 2 (by decide) (by decide) (by decide)
  have h₃ := empty 3 (by decide) (by decide) (by decide)
  have h₄ := empty 4 (by decide) (by decide) (by decide)
  have h₅ := empty 5 (by decide) (by decide) (by decide)
  have h₆ := empty 6 (by decide) (by decide) (by decide)
  have h₈ := empty 8 (by decide) (by decide) (by decide)
  have hi0 : bodyIndex 0 = 0 := rfl
  have hi3 : bodyIndex 3 = 3 := rfl
  have hi4 : bodyIndex 4 = 4 := rfl
  have hi5 : bodyIndex 5 = 5 := rfl
  have hi6 : bodyIndex 6 = 6 := rfl
  have hi8 : bodyIndex 8 = 8 := rfl
  let loaded := Function.update (Function.update base (tape 9) suffix) (tape 1) (encodeWord j)
  let seeded := Function.update loaded (tape 2) trueBits
  let rowed := MachineLazyRows.reindexResultTapes e (d + e) d v j trueRelation
    (tape ∘ bodyIndex) seeded
  let oldCleared := Function.update rowed (tape 1) []
  let newCleared := Function.update oldCleared (tape 6) []
  have loadRun : (advance (TM2.step program))^[j + 2]
      (some ⟨some (labels .loadStart), MachinePortReindex.clean e positive ambient, base⟩) =
      some ⟨some (labels .seedRelation), MachinePortReindex.clean e positive ambient, loaded⟩ := by
    have h := (Hastad.SourceMachine.fieldInTime (tape 9) (tape 1) (hd 9 1 (by decide))
      (labels .loadStart) (labels .loadLoop) (some (labels .seedRelation)) program
      (atLabels .loadStart) (atLabels .loadLoop) base j suffix inputWord
      (ambient, MachineFixedDivMod.residue e positive 0) none).evals_in_steps
    change (advance (TM2.step program))^[j + 2]
      (some ⟨some (labels .loadStart), MachinePortReindex.clean e positive ambient, base⟩) =
      some ⟨some (labels .seedRelation), MachinePortReindex.clean e positive ambient,
        Hastad.SourceMachine.fieldTapes (tape 9) (tape 1) base suffix
          (encodeWord j ++ base (tape 1))⟩ at h
    simpa only [Hastad.SourceMachine.fieldTapes,
      h₁, List.append_nil, MachinePortReindex.clean, loaded] using h
  have seedRun : (advance (TM2.step program))^[1]
      (some ⟨some (labels .seedRelation), MachinePortReindex.clean e positive ambient, loaded⟩) =
      some ⟨some (labels (.row (.inl .copySeed))),
        MachinePortReindex.clean e positive ambient, seeded⟩ := by
    change some (TM2.stepAux (program (labels .seedRelation)) _ _) = _
    rw [atLabels]
    simp [instruction, stepAux_pushWord, TM2.stepAux, seeded, loaded,
      hd 2 1 (by decide), hd 2 9 (by decide), h₂]
  have hs (i : Fin 10) (hi : i ≠ 1) (hi' : i ≠ 2) (hi'' : i ≠ 9) :
      seeded (tape i) = base (tape i) := by
    simp [seeded, loaded, hd i 1 hi, hd i 2 hi', hd i 9 hi'']
  have bodyRun := MachineLazyRows.reindexRowTrace e positive (d + e) d
    (tape ∘ bodyIndex) (distinct.comp bodyIndex_injective) (fun s => labels (.row s))
    (some (labels .drainOld)) program (fun s => atLabels (.row s)) seeded v j trueRelation
    (by simpa only [Function.comp_apply, hi0] using
      (hs 0 (by decide) (by decide) (by decide)).trans tailWord)
    (by simp [seeded, loaded, Function.comp_apply, bodyIndex, hd 1 2 (by decide)])
    (by simp [seeded, Function.comp_apply, bodyIndex, trueBits])
    (by simpa only [Function.comp_apply, hi3] using
      (hs 3 (by decide) (by decide) (by decide)).trans h₃)
    (by simpa only [Function.comp_apply, hi4] using
      (hs 4 (by decide) (by decide) (by decide)).trans h₄)
    (by simpa only [Function.comp_apply, hi5] using
      (hs 5 (by decide) (by decide) (by decide)).trans h₅)
    (by simpa only [Function.comp_apply, hi6] using
      (hs 6 (by decide) (by decide) (by decide)).trans h₆)
    (by simpa only [Function.comp_apply, hi8] using
      (hs 8 (by decide) (by decide) (by decide)).trans h₈) ambient
  have hout : seeded ((tape ∘ bodyIndex) 7) = base (tape 7) :=
    hs 7 (by decide) (by decide) (by decide)
  rw [hout] at bodyRun
  change (advance (TM2.step program))^[MachineLazyRows.reindexSteps e (d + e) d v j
      trueRelation (base (tape 7))]
    (some ⟨some (labels (.row (.inl .copySeed))), MachinePortReindex.clean e positive ambient, seeded⟩) =
    some ⟨some (labels .drainOld), MachinePortReindex.clean e positive ambient, rowed⟩ at bodyRun
  have rowedOld : rowed (tape 1) = encodeWord j := by
    simp [rowed, MachineLazyRows.reindexResultTapes, MachineLazyRows.reindexMappedTapes,
      Function.comp_apply, bodyIndex, seeded, loaded, hd 1 7 (by decide),
      hd 1 6 (by decide), hd 1 2 (by decide)]
  have rowedNew : oldCleared (tape 6) = encodeWord (MachinePortReindex.value e (d + e) d j) := by
    simp [oldCleared, rowed, MachineLazyRows.reindexResultTapes,
      MachineLazyRows.reindexMappedTapes, Function.comp_apply, bodyIndex,
      hd 6 1 (by decide), hd 6 7 (by decide)]
  have rowedRelation : newCleared (tape 2) = trueBits := by
    simp [newCleared, oldCleared, rowed, MachineLazyRows.reindexResultTapes,
      MachineLazyRows.reindexMappedTapes, Function.comp_apply, bodyIndex, seeded,
      hd 2 6 (by decide), hd 2 1 (by decide), hd 2 7 (by decide)]
  have drainOld := (MachineDrain.drainInTime (tape 1) (labels .drainOld)
    (some (labels .drainNew)) program (atLabels .drainOld) rowed
    (ambient, MachineFixedDivMod.residue e positive 0) none).evals_in_steps
  change (advance (TM2.step program))^[(rowed (tape 1)).length + 1]
    (some ⟨some (labels .drainOld), MachinePortReindex.clean e positive ambient, rowed⟩) =
    some ⟨some (labels .drainNew), MachinePortReindex.clean e positive ambient, oldCleared⟩ at drainOld
  rw [rowedOld, encodeWord_length] at drainOld
  have drainNew := (MachineDrain.drainInTime (tape 6) (labels .drainNew)
    (some (labels .drainRelation)) program (atLabels .drainNew) oldCleared
    (ambient, MachineFixedDivMod.residue e positive 0) none).evals_in_steps
  change (advance (TM2.step program))^[(oldCleared (tape 6)).length + 1]
    (some ⟨some (labels .drainNew), MachinePortReindex.clean e positive ambient, oldCleared⟩) =
    some ⟨some (labels .drainRelation), MachinePortReindex.clean e positive ambient, newCleared⟩ at drainNew
  rw [rowedNew, encodeWord_length] at drainNew
  have drainRelation := (MachineDrain.drainInTime (tape 2) (labels .drainRelation)
    exit program (atLabels .drainRelation) newCleared
    (ambient, MachineFixedDivMod.residue e positive 0) none).evals_in_steps
  change (advance (TM2.step program))^[(newCleared (tape 2)).length + 1]
    (some ⟨some (labels .drainRelation), MachinePortReindex.clean e positive ambient, newCleared⟩) =
    some ⟨exit, MachinePortReindex.clean e positive ambient,
      Function.update newCleared (tape 2) []⟩ at drainRelation
  rw [rowedRelation] at drainRelation
  have finalFrame : Function.update newCleared (tape 2) [] = resultTapes d e v j tape base suffix := by
    funext k
    by_cases h2 : k = tape 2
    · subst k
      simp [resultTapes, hd 2 7 (by decide), hd 2 9 (by decide), h₂]
    · by_cases h6 : k = tape 6
      · subst k
        simp [newCleared, resultTapes, hd 6 2 (by decide), hd 6 7 (by decide),
          hd 6 9 (by decide), h₆]
      · by_cases h1 : k = tape 1
        · subst k
          simp [newCleared, oldCleared, resultTapes, hd 1 2 (by decide),
            hd 1 6 (by decide), hd 1 7 (by decide), hd 1 9 (by decide), h₁]
        · by_cases h7 : k = tape 7
          · subst k
            simp [newCleared, oldCleared, rowed, MachineLazyRows.reindexResultTapes,
              MachineLazyRows.reindexMappedTapes, Function.comp_apply, bodyIndex,
              resultTapes, rowBits, seeded, loaded, hd 7 2 (by decide),
              hd 7 6 (by decide), hd 7 1 (by decide), hd 7 9 (by decide)]
          · simp [newCleared, oldCleared, rowed, MachineLazyRows.reindexResultTapes,
              MachineLazyRows.reindexMappedTapes, Function.comp_apply, bodyIndex,
              seeded, loaded, resultTapes, h2, h6, h1, h7]
  rw [finalFrame] at drainRelation
  exact joinTrace_inline_MachineOverlayRows (joinTrace_inline_MachineOverlayRows (joinTrace_inline_MachineOverlayRows (joinTrace_inline_MachineOverlayRows (joinTrace_inline_MachineOverlayRows loadRun seedRun) bodyRun)
    drainOld) drainNew) drainRelation

theorem rowBits_eq_expanderRow {n e : Nat} (d : Nat) (H : PCP.ExpanderTables.Table n e)
    (v : Fin n) (p : Fin e) :
    rowBits d e v.val (PCP.ExpanderTables.reverseIndex H
        (PCP.ExpanderTables.rowIndex n e (v, p))).val =
      encodeWords (rowWords (expanderRow d H v p)) := by
  rw [expanderRow_words]
  have h (j : Nat) : MachinePortReindex.value e (d + e) d j = expanderReverseMap d e j := by
    unfold MachinePortReindex.value expanderReverseMap
    omega
  simp only [rowBits, MachineLazyRows.reindexRowBits, h,
    PCP.PreprocessingLazyWords.relationWords_true, List.cons_append,
    List.nil_append, encodeWords, List.append_assoc]

/-! The fixed-degree vertex loop has one finite label block per port, plus
one terminal boundary. The stored row values do not occur in its program. -/

def vertexInstruction (d e : Nat) (positive : 0 < e) (tape : Fin 10 → K)
    (labels : VertexLabel e → Λ) (exit : Option Λ) :
    VertexLabel e → TM2.Stmt (fun _ : K => Bool) Λ (State A e)
  | (i, none) => if i.val < e then .goto fun _ => labels (i, some .loadStart)
      else MachinePortReindex.exitAt exit
  | (i, some stage) => if h : i.val < e then
      instruction d e positive tape (fun stage => labels (i, some stage))
        (some (labels (⟨i.val + 1, by omega⟩, none))) stage
      else MachinePortReindex.exitAt exit

def streamFrame (tape : Fin 10 → K) (base : K → List Bool)
    (words : List Nat) (output : List Bool) : K → List Bool :=
  Function.update (Function.update base (tape 9) (encodeWords words ++ base (tape 9)))
    (tape 7) output

def streamOutput (d e v : Nat) (words : List Nat) : List Bool :=
  words.flatMap (rowBits d e v)

def vertexSteps (d e v : Nat) : List Nat → List Bool → Nat
  | [], _ => 1
  | j :: words, output => 1 + rowSteps d e v j output +
      vertexSteps d e v words (output ++ rowBits d e v j)

def rowSizeBound (d e v B : Nat) : Nat := v + valueBound d e B + trueBits.length + 2
def rowCostBound (d e v B : Nat) : Nat :=
  8 * B + 4 * rowSizeBound d e v B + valueBound d e B + trueBits.length + 28

theorem rowBits_length (d e v j : Nat) :
    (rowBits d e v j).length = v + MachinePortReindex.value e (d + e) d j + trueBits.length + 2 := by
  simp only [rowBits, MachineLazyRows.reindexRowBits, List.length_append, encodeWord_length,
    trueBits]
  omega

theorem rowBits_length_le (d e v j B : Nat) (hj : j ≤ B) :
    (rowBits d e v j).length ≤ rowSizeBound d e v B := by
  rw [rowBits_length]
  have h := value_le d e j B hj
  unfold rowSizeBound
  omega

theorem rowSteps_le (d e v j B : Nat) (hj : j ≤ B) (output : List Bool) :
    rowSteps d e v j output ≤ rowCostBound d e v B + 2 * output.length := by
  have hdiv := (Nat.div_le_self j e).trans hj
  have hval := value_le d e j B hj
  have hsize := rowBits_length_le d e v j B hj
  change (MachineLazyRows.reindexRowBits e (d + e) d v j trueRelation).length ≤
    rowSizeBound d e v B at hsize
  unfold rowSteps MachineLazyRows.reindexSteps MachinePortReindex.steps rowCostBound
  omega

theorem vertexSteps_le_capacity_inline_MachineOverlayRows (d e v B capacity : Nat)
    (words : List Nat) (bounded : ∀ j ∈ words, j ≤ B) (output : List Bool)
    (room : output.length + words.length * rowSizeBound d e v B ≤ capacity) :
    vertexSteps d e v words output ≤
      words.length * (rowCostBound d e v B + 2 * capacity + 1) + 1 := by
  induction words generalizing output with
  | nil => simp [vertexSteps]
  | cons j words ih =>
      have hj := bounded j (by simp)
      have hb : ∀ k ∈ words, k ≤ B := fun k hk => bounded k (by simp [hk])
      have hsize := rowBits_length_le d e v j B hj
      have hcost := rowSteps_le d e v j B hj output
      have hout : output.length ≤ capacity := by omega
      have hroom : (output ++ rowBits d e v j).length +
          words.length * rowSizeBound d e v B ≤ capacity := by
        rw [List.length_append]
        simp only [List.length_cons, Nat.succ_mul] at room
        omega
      have htail := ih hb (output ++ rowBits d e v j) hroom
      change 1 + rowSteps d e v j output +
        vertexSteps d e v words (output ++ rowBits d e v j) ≤
        (words.length + 1) * (rowCostBound d e v B + 2 * capacity + 1) + 1
      rw [Nat.add_mul, Nat.one_mul]
      omega

/-- Explicit polynomial budget for the finite port loop, including repeated
output append costs and all real loader and cleanup transitions. -/
theorem vertexSteps_le (d e v B : Nat) (words : List Nat)
    (bounded : ∀ j ∈ words, j ≤ B) (output : List Bool) :
    vertexSteps d e v words output ≤
      words.length * (rowCostBound d e v B +
        2 * (output.length + words.length * rowSizeBound d e v B) + 1) + 1 :=
  vertexSteps_le_capacity_inline_MachineOverlayRows d e v B _ words bounded output (Nat.le_refl _)

theorem streamFrame_afterRow_inline_MachineOverlayRows (d e v j : Nat) (tape : Fin 10 → K)
    (distinct : Function.Injective tape) (base : K → List Bool)
    (words : List Nat) (output : List Bool) :
    resultTapes d e v j tape (streamFrame tape base (j :: words) output)
      (encodeWords words ++ base (tape 9)) =
      streamFrame tape base words (output ++ rowBits d e v j) := by
  have h79 : tape 7 ≠ tape 9 := fun h => (by decide : (7 : Fin 10) ≠ 9) (distinct h)
  funext k
  by_cases h7 : k = tape 7
  · subst k
    simp [resultTapes, streamFrame]
  · by_cases h9 : k = tape 9
    · subst k
      simp [resultTapes, streamFrame, Ne.symm h79]
    · simp [resultTapes, streamFrame, h7, h9]

/-- A suffix of the actual fixed-degree port loop. Each row execution is
derived from `rowTrace`; no row-execution premise is accepted. -/
theorem vertexSuffixTrace (d e : Nat) (positive : 0 < e) (tape : Fin 10 → K)
    (distinct : Function.Injective tape) (labels : VertexLabel e → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State A e))
    (atLabels : ∀ l, program (labels l) = vertexInstruction d e positive tape labels exit l)
    (base : K → List Bool) (v : Nat) (values : Fin e → Nat)
    (tailWord : base (tape 0) = encodeWord v)
    (empty : ∀ i : Fin 10, i ≠ 0 → i ≠ 7 → i ≠ 9 → base (tape i) = [])
    (ambient : A) (remaining : Nat) (i : Fin (e + 1)) (count : i.val + remaining = e)
    (output : List Bool) :
    (advance (TM2.step program))^[vertexSteps d e v ((List.ofFn values).drop i.val) output]
      (some ⟨some (labels (i, none)), MachinePortReindex.clean e positive ambient,
        streamFrame tape base ((List.ofFn values).drop i.val) output⟩) =
      some ⟨exit, MachinePortReindex.clean e positive ambient,
        streamFrame tape base [] (output ++ streamOutput d e v ((List.ofFn values).drop i.val))⟩ := by
  have hd (a b : Fin 10) (h : a ≠ b) : tape a ≠ tape b := fun x => h (distinct x)
  induction remaining generalizing i output with
  | zero =>
      have hi : i.val = e := by omega
      have hdrop : (List.ofFn values).drop i.val = [] := by
        apply List.drop_eq_nil_of_le
        simp only [List.length_ofFn, hi, le_refl]
      rw [hdrop]
      simp only [vertexSteps, streamOutput, List.flatMap_nil, List.append_nil]
      change some (TM2.stepAux (program (labels (i, none))) _ _) = _
      rw [atLabels]
      cases exit <;> simp [vertexInstruction, hi, MachinePortReindex.exitAt, TM2.stepAux]
  | succ remaining ih =>
      have hi : i.val < e := by omega
      let port : Fin e := ⟨i.val, hi⟩
      let next : Fin (e + 1) := ⟨i.val + 1, by omega⟩
      let rest := (List.ofFn values).drop (i.val + 1)
      have split : (List.ofFn values).drop i.val = values port :: rest := by
        have h := List.getElem_cons_drop (as := List.ofFn values)
          (i := i.val) (by simpa only [List.length_ofFn] using hi)
        simpa only [List.getElem_ofFn, port, rest] using h.symm
      let initial := streamFrame tape base (values port :: rest) output
      have boundary : (advance (TM2.step program))^[1]
          (some ⟨some (labels (i, none)), MachinePortReindex.clean e positive ambient, initial⟩) =
          some ⟨some (labels (i, some .loadStart)), MachinePortReindex.clean e positive ambient, initial⟩ := by
        change some (TM2.stepAux (program (labels (i, none))) _ _) = _
        rw [atLabels]
        simp [vertexInstruction, hi, TM2.stepAux]
      have body := rowTrace d e positive tape distinct (fun stage => labels (i, some stage))
        (some (labels (next, none))) program
        (by
          intro stage
          simpa only [vertexInstruction, hi, dite_true, next] using
            (atLabels (i, some stage))) initial v (values port)
        (encodeWords rest ++ base (tape 9))
        (by simp [initial, streamFrame, hd 0 7 (by decide), hd 0 9 (by decide), tailWord])
        (by simp [initial, streamFrame, hd 9 7 (by decide), encodeWords, List.append_assoc])
        (by
          intro k hk0 hk7 hk9
          simp [initial, streamFrame, hd k 7 hk7, hd k 9 hk9, empty k hk0 hk7 hk9]) ambient
      have initialOutput : initial (tape 7) = output := by simp [initial, streamFrame]
      rw [initialOutput] at body
      change (advance (TM2.step program))^[rowSteps d e v (values port) output]
        (some ⟨some (labels (i, some .loadStart)), MachinePortReindex.clean e positive ambient, initial⟩) =
        some ⟨some (labels (next, none)), MachinePortReindex.clean e positive ambient,
          resultTapes d e v (values port) tape initial (encodeWords rest ++ base (tape 9))⟩ at body
      rw [show resultTapes d e v (values port) tape initial (encodeWords rest ++ base (tape 9)) =
        streamFrame tape base rest (output ++ rowBits d e v (values port)) from
          streamFrame_afterRow_inline_MachineOverlayRows d e v (values port) tape distinct base rest output] at body
      have nextCount : next.val + remaining = e := by dsimp [next]; omega
      have tail := ih next nextCount (output ++ rowBits d e v (values port))
      change (advance (TM2.step program))^[vertexSteps d e v rest (output ++ rowBits d e v (values port))]
        (some ⟨some (labels (next, none)), MachinePortReindex.clean e positive ambient,
          streamFrame tape base rest (output ++ rowBits d e v (values port))⟩) =
        some ⟨exit, MachinePortReindex.clean e positive ambient,
          streamFrame tape base [] ((output ++ rowBits d e v (values port)) ++ streamOutput d e v rest)⟩ at tail
      rw [split]
      have all := joinTrace_inline_MachineOverlayRows (joinTrace_inline_MachineOverlayRows boundary body) tail
      simpa only [vertexSteps, initial, streamOutput, List.flatMap_cons, List.append_assoc] using all

theorem vertexTrace (d e : Nat) (positive : 0 < e) (tape : Fin 10 → K)
    (distinct : Function.Injective tape) (labels : VertexLabel e → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State A e))
    (atLabels : ∀ l, program (labels l) = vertexInstruction d e positive tape labels exit l)
    (base : K → List Bool) (v : Nat) (values : Fin e → Nat)
    (tailWord : base (tape 0) = encodeWord v)
    (empty : ∀ i : Fin 10, i ≠ 0 → i ≠ 7 → i ≠ 9 → base (tape i) = [])
    (ambient : A) (output : List Bool) :
    (advance (TM2.step program))^[vertexSteps d e v (List.ofFn values) output]
      (some ⟨some (labels (0, none)), MachinePortReindex.clean e positive ambient,
        streamFrame tape base (List.ofFn values) output⟩) =
      some ⟨exit, MachinePortReindex.clean e positive ambient,
        streamFrame tape base [] (output ++ streamOutput d e v (List.ofFn values))⟩ := by
  simpa only [Fin.val_zero, List.drop_zero] using vertexSuffixTrace d e positive tape distinct
    labels exit program atLabels base v values tailWord empty ambient e 0 (by simp) output

theorem encodeWords_flatMap_inline_MachineOverlayRows {α : Type*} (items : List α) (words : α → List Nat) :
    encodeWords (items.flatMap words) = items.flatMap (fun x => encodeWords (words x)) := by
  induction items with
  | nil => rfl
  | cons item items ih => simp only [List.flatMap_cons, encodeWords_append, ih]

theorem streamOutput_expanderRows {n e : Nat} (d : Nat) (H : PCP.ExpanderTables.Table n e)
    (v : Fin n) :
    streamOutput d e v.val (List.ofFn fun p : Fin e =>
      (PCP.ExpanderTables.reverseIndex H (PCP.ExpanderTables.rowIndex n e (v, p))).val) =
      encodeWords ((List.ofFn (expanderRow d H v)).flatMap rowWords) := by
  rw [encodeWords_flatMap_inline_MachineOverlayRows]
  simp only [streamOutput, List.flatMap_def, List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext p
  exact rowBits_eq_expanderRow d H v p

theorem expanderValues_bounded {n e : Nat} (H : PCP.ExpanderTables.Table n e) (v : Fin n)
    (p : Fin e) :
    (PCP.ExpanderTables.reverseIndex H (PCP.ExpanderTables.rowIndex n e (v, p))).val ≤ n * e :=
  (PCP.ExpanderTables.reverseIndex H (PCP.ExpanderTables.rowIndex n e (v, p))).isLt.le

end MaxCutGames.Foundations.Complexity.MachineOverlayRows

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_SelectorMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Complexity.MachineRegularInternalRow
open Turing MachineComposition
open PCP
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)
variable {K Λ σ : Type} [DecidableEq K]

def coreSelectTape : SelectTape → CoreTape
  | .inl (.inl .original) => 0
  | .inl (.inl .work) => 17
  | .inl (.inl .target) => 16
  | .inl (.inl .scratch) => 9
  | .inl (.inl .count) => 18
  | .inl (.inl .spare) => 19
  | .inl (.inr ()) => 15
  | .inr .localIndex => 13
  | .inr .owner => 2
  | .inr .cloudSize => 4
  | .inr .prefixOffset => 5
  | .inr .darts => 6
  | .inr .savedLeft => 20
  | .inr .savedRight => 21
  | .inr .localWork => 22
  | .inr .sizeWork => 23

def coreSelectView : CoreTape → Option SelectTape :=
  ![some (.inl (.inl .original)), none, some (.inr .owner), none,
    some (.inr .cloudSize), some (.inr .prefixOffset), some (.inr .darts), none, none,
    some (.inl (.inl .scratch)), none, none, none, some (.inr .localIndex), none,
    some (.inl (.inr ())), some (.inl (.inl .target)), some (.inl (.inl .work)),
    some (.inl (.inl .count)), some (.inl (.inl .spare)),
    some (.inr .savedLeft), some (.inr .savedRight),
    some (.inr .localWork), some (.inr .sizeWork), none, none, none]

theorem coreSelectView_left (k : SelectTape) : coreSelectView (coreSelectTape k) = some k := by
  cases k with
  | inl k =>
    cases k with
    | inl k => cases k <;> rfl
    | inr k => cases k; rfl
  | inr k => cases k <;> rfl

theorem coreSelectView_right (j : CoreTape) (k : SelectTape)
    (h : coreSelectView j = some k) : coreSelectTape k = j := by
  fin_cases j <;> simp [coreSelectView] at h
  all_goals subst k; rfl

def coreRotorStateEquiv (σ : Type) (q : Nat) :
    MachineFixedDivMod.State
      ((σ × MachineFixedBlockMap.Buffer 4096) × (Bool × MachineCloudSelect.Phase)) q ≃
        CoreState σ q where
  toFun s := ((s.1.1.1.1, (s.1.1.1.2, (s.1.2, s.1.1.2))), s.2)
  invFun s := ((((s.1.1, s.1.2.1), s.1.2.2.2), s.1.2.2.1), s.2)
  left_inv s := by rcases s with ⟨⟨⟨⟨a,b⟩,⟨c,d⟩⟩,e⟩,f⟩; rfl
  right_inv s := by rcases s with ⟨⟨a,⟨b,⟨c,⟨d,e⟩⟩⟩⟩,f⟩; rfl

def coreSelectStateEquiv (σ : Type) (q : Nat) :
    SelectState (σ × (MachineFixedBlockMap.Buffer 4096 × Fin q)) ≃ CoreState σ q where
  toFun s := ((s.1.1.1.1, (s.1.1.1.2.1, (s.1.1.1.2.2, (s.1.2, s.1.1.2)))), s.2)
  invFun s := ((((s.1.1, (s.1.2.1, s.1.2.2.1)), s.1.2.2.2.2), s.1.2.2.2.1), s.2)
  left_inv s := by rcases s with ⟨⟨⟨⟨a,⟨b,c⟩⟩,d⟩,e⟩,f⟩; rfl
  right_inv s := by rcases s with ⟨⟨a,⟨b,⟨c,⟨d,e⟩⟩⟩⟩,f⟩; rfl

def coreAfterCleanup {q : Nat} (labels : CoreLabel q → Λ) (exit : Option Λ) (i : Fin 10) :
    Option Λ :=
  if h : i.val + 1 < 10 then some (labels (.cleanup ⟨i.val + 1,h⟩)) else exit

def coreMemory (graph : List Bool) (x v i k o m : Nat) (rotor output : List Bool)
    (query scan flat localIndex returnPort selected : List Bool) : CoreTape → List Bool :=
  ![graph, encodeWord x, encodeWord v, encodeWord i, encodeWord k, encodeWord o,
    encodeWord m, rotor, output, [], query, scan, flat, localIndex, returnPort, selected,
    [], [], [], [], [], [], [], [], [], [], []]

@[simp] theorem coreMemory_update_output (graph : List Bool) (x v i k o m : Nat)
    (rotor output query scan flat localIndex returnPort selected newOutput : List Bool) :
    Function.update (coreMemory graph x v i k o m rotor output query scan flat
      localIndex returnPort selected) (8 : CoreTape) newOutput =
      coreMemory graph x v i k o m rotor newOutput query scan flat localIndex returnPort selected := by
  funext z
  fin_cases z <;> rfl

theorem coreRotorTapes_injective : Function.Injective coreRotorTapes := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [coreRotorTapes]

theorem coreFinishTapes_injective : Function.Injective coreFinishTapes := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [coreFinishTapes]

def coreCleaned (base : CoreTape → List Bool) : CoreTape → List Bool :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update
      (Function.update base 10 []) 11 []) 12 []) 13 []) 14 []) 15 []) 9 []) 16 []) 17 []) 18 []

def coreCleanupSteps (base : CoreTape → List Bool) : Nat :=
  (base 10).length + (base 11).length + (base 12).length + (base 13).length +
  (base 14).length + (base 15).length + (base 9).length + (base 16).length +
  (base 17).length + (base 18).length + 10

theorem coreCleaned_memory (graph : List Bool) (x v i k o m : Nat)
    (rotor output query scan flat localIndex returnPort selected : List Bool) :
    coreCleaned (coreMemory graph x v i k o m rotor output query scan flat
      localIndex returnPort selected) =
      coreMemory graph x v i k o m rotor output [] [] [] [] [] [] := by
  funext z
  fin_cases z <;> rfl

theorem coreCleanupSteps_memory (graph : List Bool) (x v i k o m : Nat)
    (rotor output scan : List Bool) (j r z : Nat) :
    coreCleanupSteps (coreMemory graph x v i k o m rotor output
      (encodeWord 0) scan (encodeWord 0) (encodeWord j) (encodeWord r) (encodeWord z)) =
      scan.length + j + r + z + 15 := by
  change (encodeWord 0).length + scan.length + (encodeWord 0).length +
    (encodeWord j).length + (encodeWord r).length + (encodeWord z).length +
    ([] : List Bool).length + ([] : List Bool).length + ([] : List Bool).length +
    ([] : List Bool).length + 10 = _
  simp only [encodeWord_length, List.length_nil]
  omega

theorem coreRotorFinalFrame {n q : Nat} (table : ExpanderTables.Table n q) (i : Fin n) (p : Fin q)
    (graph : List Bool) (x v k o m : Nat) (output : List Bool) :
    rotorFinalTapes table i p coreRotorTapes
      (coreMemory graph x v i.val k o m
        (encodeWords (ExpanderTableWords.rotationWords table)) output [] [] [] [] [] []) =
    coreMemory graph x v i.val k o m
      (encodeWords (ExpanderTableWords.rotationWords table)) output (encodeWord 0)
      (encodeWords ((ExpanderTableWords.rotationWords table).drop (q * i.val + p.val + 1)))
      (encodeWord 0) (encodeWord (ExpanderTables.lookup table (i, p)).1.val)
      (encodeWord (ExpanderTables.lookup table (i, p)).2.val) [] := by
  funext z
  fin_cases z <;>
    simp [rotorFinalTapes, coreRotorTapes, rotorLookupTapes, coreMemory,
      MachineFixedDivMod.unaryTapes, MachineFixedDivMod.tapes, MachineCopy.forkTapes,
      MachineAffineLookup.finalTapes, MachinePreservingLookup.finalTapes, MachineLookup.tapes]

theorem coreSelectFrame (graph : List Bool) (x v i k o m j : Nat)
    (rotor output query scan flat returnPort selected : List Bool) :
    MachineCloudPadding.Placement.tapes coreSelectView
      (selectMemory graph j v k o m [] selected [] [] [] [])
      (coreMemory graph x v i k o m rotor output query scan flat (encodeWord j) returnPort []) =
      coreMemory graph x v i k o m rotor output query scan flat (encodeWord j) returnPort selected := by
  funext z
  fin_cases z <;> rfl

def coreInputTapes (t : GraphTables.Table) (padding : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table (PreprocessingCloudIndex.cloudSize t v + padding v) q)
    (v : Fin t.vertices) (x : PreprocessingCloudIndex.PaddedCloud t padding v)
    (output : List Bool) : CoreTape → List Bool :=
  coreMemory (GraphTables.tableBits t)
    (PreprocessingRegularTables.vertexOrder t padding x.val).val v.val
    (PreprocessingCloudIndex.paddedCloudRank t padding v x).val
    (PreprocessingCloudIndex.cloudSize t v) (PreprocessingPaddingOffsets.offset padding v.val) t.darts
    (encodeWords (ExpanderTableWords.rotationWords (tables v))) output [] [] [] [] [] []

end MaxCutGames.Foundations.Complexity.MachineRegularInternalRow

/-!
# Reusable inherited-row execution with actual cleanup

Five concrete drain loops remove the query delimiter, unread scan suffix,
raw reverse field, computed reverse field, and copied relation. With initially
empty work tapes, the only final tape change is the appended output row. The
index on tape zero and input table on tape one are both preserved.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_PreprocessingPaddingWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact serialization of whole-vertex padding

The original dart rows remain in their original order, with every old tail,
reverse index, and relation bit unchanged. The suffix is exactly the bit stream
emitted by the checked dummy-vertex machine, starting at vertex `n` and dart
`n*d`. This is an equality for the actual table codec, with no runtime premise.
-/

namespace MaxCutGames.Foundations.PCP.PreprocessingPaddingWords

open Complexity PortTables

variable {n m d : Nat}

theorem encodeWords_flatMap_inline_PreprocessingPaddingWords {α : Type*} (xs : List α) (words : α → List Nat) :
    encodeWords (xs.flatMap words) = xs.flatMap (fun x => encodeWords (words x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, encodeWords_append, ih]

/-- The old encoded rows, without their two header words. -/
def rowsBits (table : Table n d) : List Bool :=
  encodeWords ((flatRows table).toList.flatMap GraphTables.rowWords)

end MaxCutGames.Foundations.PCP.PreprocessingPaddingWords

/-!
# Complete serialization of the actual regularized table

Each global vertex emits its internal ports in increasing order, then its
inherited port. Original darts are the first global vertices. Dummy vertices
follow in increasing owner and local-dummy order. These are identities for the
actual stored rows and existing codec, with arbitrary actual cloud tables.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineRegularTableTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial bounds for the actual regularization subcalls. These lemmas
bound the established step counts; they do not assume any machine execution. -/
namespace MaxCutGames.Foundations.Complexity.MachineRegularExecutionBounds

open Turing MachineComposition PCP PCP.PreprocessingRegularTables PCP.PreprocessingCloudIndex
open PCP.PreprocessingMachineBounds MachineRegularInternalRow

noncomputable def familyPolynomial : Polynomial Nat :=
  MachinePaddedExpanderFamilyBounds.timePolynomial.comp (Polynomial.X + 1) +
    Polynomial.C (2 * ExpanderFamily.growth) * (Polynomial.X + 1) + 7

end MaxCutGames.Foundations.Complexity.MachineRegularExecutionBounds

/-! Polynomial runtime for the actual original-vertex body. The size parameter
includes the already accumulated output, so no output-prefix premise is used. -/

/-!
# Bounds for actual dummy-owner execution

The size parameter includes the old output length. During the owner loop,
newly emitted dummy blocks are bounded by the actual complete regularized
table codec. No hypothesis about a machine body's execution supplies a bound.
-/

/-! A polynomial cap for the actual two regularization loops, their header,
and all seven final drain loops. Per-call sizes include the complete stored
output prefix. -/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_PreprocessingStageMaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Executable, codec-compatible stage maps for the actual preprocessing
constructor. The decomposition below is an equality of its existing functions;
runtime certificates must be supplied by the respective concrete machines. -/
namespace MaxCutGames.Foundations.PCP.PreprocessingStageMaps
open PreprocessingRegularTables

def lazy (d : Nat) (input : PortTables.Input d) : PortTables.Input (2 * d) :=
  ⟨input.1, PreprocessingOverlayTables.lazy input.2⟩

end MaxCutGames.Foundations.PCP.PreprocessingStageMaps

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineRegularTableRuntime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
A fixed five-tape machine physically copies a graph table, preserves the
original input, and splits its two unary header fields from the copied rows.
The exact trace is ambient-state polymorphic for static machine placement.
-/

/-! Polynomial bounds for the actual outer padding-loop recurrence. No
execution or cost premise is introduced: the recurrence is the one matched
to the concrete machine by `MachinePaddingRows.loopTrace`. -/

/-! Polynomial-time certificate for the actual varying-length padding loop,
including its one-time relation initialization. The input vertex, reverse
index, fuel, and accumulated output are all measured as physically stored
bits. This is a reusable stage of the graph-table transformation. -/

/-! Exact table-codec endpoint of the polynomial padding-row routine.
The caller supplies the physical unary counters and copied old-row buffer
with the updated headers. This theorem executes every added row and proves
that the resulting output is exactly the existing full table encoding. -/

/-!
# Vertex padding from the original serialized port graph

Header counters, the geometric padding count, and the initial row buffer
are generated by physical tape operations before the checked row emitter.
-/

namespace MaxCutGames.Foundations.Complexity.MachineVertexPadding

open Turing MachineComposition
open MaxCutGames.Foundations.PCP
open MachineCloudPadding

inductive Label (d : Nat)
  | splitCode (l : MachineTableSplit.Label)
  | powerCode (l : MachineCeilingPower.Label)
  | dartSeed | dartScan | dartRestore | vertexSeed | vertexScan | vertexRestore
  | copyFirst | copySecond | subtractCode (l : MachineCloudPadding.Label)
  | rowsCode (l : MachinePaddingRows.Label d)
  | cleanVertex | cleanEdge | cleanPower | cleanRelation | cleanFuel
  deriving DecidableEq, Fintype

def powerTape : MachineCeilingPower.Tape → Tape
  | .input => .vertex
  | .work => .work
  | .power => .power
  | .saved => .saved
  | .level => .level
  | .fuel => .fuel
  | .spare => .scratch
  | .product => .product
def powerView : Tape → Option MachineCeilingPower.Tape
  | .vertex => some .input
  | .work => some .work
  | .power => some .power
  | .saved => some .saved
  | .level => some .level
  | .fuel => some .fuel
  | .scratch => some .spare
  | .product => some .product
  | _ => none

theorem powerView_left (k : MachineCeilingPower.Tape) : powerView (powerTape k) = some k := by
  cases k <;> rfl
theorem powerView_right (j : Tape) (k : MachineCeilingPower.Tape)
    (h : powerView j = some k) : powerTape k = j := by
  cases j <;> cases k <;> simp_all [powerView, powerTape]

theorem powerTapes (input output vertex edge power level : List Bool) :
    Placement.tapes powerView (MachineCeilingPower.memory vertex [] power [] level [] [] [])
      (memory input output [] edge [] [] [] []) = memory input output vertex edge power level [] [] := by
  funext k; cases k <;> rfl

theorem transport_tapes_apply_inline_MachineVertexPadding {K : Type} {Γ Δ : K → Type}
    (h : Γ = Δ) (base : (k : K) → List (Γ k)) (k : K) :
    MachineAlphabetTransport.tapes h base k =
      Eq.mp (congrArg (fun alphabet => List (alphabet k)) h) (base k) := by
  cases h
  rfl

theorem rowCastTapes (base : (k : MachinePaddingRows.Tape) → List (MachinePaddingRows.Alphabet k)) :
    MachineAlphabetTransport.tapes rowAlphabet_eq base = rowBoolTapes base := by
  funext k
  rw [transport_tapes_apply_inline_MachineVertexPadding]
  cases k <;> rfl

end MaxCutGames.Foundations.Complexity.MachineVertexPadding

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineOverlayTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Complexity.MachineOverlayTable

open Turing MachineComposition
open PCP PCP.GraphTables PCP.PreprocessingOverlayWords
open MachineCloudPadding

variable {A : Type} {d e : Nat}

def clean (d e : Nat) (hd : 0 < d) (he : 0 < e) (a : A) : State A d e :=
  MachineLazyRows.streamClean d hd (a, MachineFixedDivMod.residue e he 0)

def expanderState (A : Type) (d e : Nat) :
    MachineOverlayRows.State ((A × MachineLazyRows.Buffer) × Fin d) e ≃ State A d e where
  toFun
    | ((((a, buffer), rd), re), bit) => ((((a, re), buffer), rd), bit)
  invFun
    | ((((a, re), buffer), rd), bit) => ((((a, buffer), rd), re), bit)
  left_inv := by rintro ⟨⟨⟨⟨a, buffer⟩, rd⟩, re⟩, bit⟩; rfl
  right_inv := by rintro ⟨⟨⟨⟨a, re⟩, buffer⟩, rd⟩, bit⟩; rfl

theorem expanderState_clean (d e : Nat) (hd : 0 < d) (he : 0 < e) (a : A) :
    expanderState A d e (MachinePortReindex.clean e he
      ((a, MachineRegularOriginalRow.zeroBuffer), MachineFixedDivMod.residue d hd 0)) =
      clean d e hd he a := rfl

/-- Fixed degree control, including two actual independent working streams. -/
def mainInstruction (d e : Nat) (hd : 0 < d) (he : 0 < e) :
    MainLabel d e → TM2.Stmt (fun _ : Tape => Bool) (Label d e) (State A d e)
  | .copyHFirst => Reduction.MachineTransfer.loopAt expanderArchive scratch id false
      (.inr .copyHFirst) (next .copyHSecond)
  | .copyHSecond => MachineCopy.forkLoop scratch expanderArchive expanderStream false
      (.inr .copyHSecond) (next .countSeed)
  | .countSeed => MachineUnaryAffineAt.seed output 0 (.inr .countScan)
  | .countScan => MachineUnaryAffineAt.scan vertexCount scratch output (d + e)
      (.inr .countScan) (.inr .countRestore)
  | .countRestore => Reduction.MachineTransfer.loopAt scratch vertexCount id false
      (.inr .countRestore) (next .headerSeed)
  | .headerSeed => MachineUnaryAffineAt.seed output 0 (.inr .headerScan)
  | .headerScan => MachineUnaryAffineAt.scan vertexCount scratch output 1
      (.inr .headerScan) (.inr .headerRestore)
  | .headerRestore => Reduction.MachineTransfer.loopAt scratch vertexCount id false
      (.inr .headerRestore) (next .fuelSeed)
  | .fuelSeed => MachineUnaryAffineAt.seed fuel 0 (.inr .fuelScan)
  | .fuelScan => MachineUnaryAffineAt.scan vertexCount scratch fuel 1
      (.inr .fuelScan) (.inr .fuelRestore)
  | .fuelRestore => Reduction.MachineTransfer.loopAt scratch vertexCount id false
      (.inr .fuelRestore) (next .vertexSeed)
  | .vertexSeed => .push vertex (fun _ => false) (.goto fun _ => .inr .guard)
  | .guard => MachineUnaryCounter.guard fuel (.inr (.old (0, none))) (.inr .drainFuel)
  | .old stage => MachineLazyRows.vertexInstruction d hd (d + e) 0 oldTapes
      (fun stage => .inr (.old stage)) (next .tailSeed) stage
  | .tailSeed => MachineUnaryAffineAt.seed tail 0 (.inr .tailScan)
  | .tailScan => MachineUnaryAffineAt.scan vertex scratch tail 1
      (.inr .tailScan) (.inr .tailRestore)
  | .tailRestore => Reduction.MachineTransfer.loopAt scratch vertex id false
      (.inr .tailRestore) (next (.expander (0, none)))
  | .expander stage => MachineStateEquiv.statement (expanderState A d e)
      (MachineOverlayRows.vertexInstruction d e he expanderTapes
        (fun stage => .inr (.expander stage)) (next .drainTail) stage)
  | .drainTail => MachineDrain.drain tail (.inr .drainTail) (next .increment)
  | .increment => .push vertex (fun _ => true) (.goto fun _ => .inr .guard)
  | .drainFuel => MachineDrain.drain fuel (.inr .drainFuel) (next .drainVertex)
  | .drainVertex => MachineDrain.drain vertex (.inr .drainVertex) (next .drainVertexCount)
  | .drainVertexCount => MachineDrain.drain vertexCount (.inr .drainVertexCount) (next .drainDartCount)
  | .drainDartCount => MachineDrain.drain dartCount (.inr .drainDartCount) none

def expanderSize (d e n : Nat) : Nat := MachineOverlayRows.rowSizeBound d e n (n * e)
def blockSize (d e n : Nat) : Nat := d * oldSize d e n + e * expanderSize d e n

def outputCapacity (d e n : Nat) : Nat := n + n * (d + e) + 2 + n * blockSize d e n

def pairBudget (d e n : Nat) : Nat :=
  (d * (MachineLazyRows.rowCostBound (d + e) 0 n (n * d) +
    2 * (outputCapacity d e n + d * oldSize d e n) + 1) + 1) +
  (e * (MachineOverlayRows.rowCostBound d e n (n * e) +
    2 * (outputCapacity d e n + d * oldSize d e n + e * expanderSize d e n) + 1) + 1) +
  (3 * n + 6)

/-- Polynomial formed from the actual per-row and counted-loop transition
budgets. Fixed degree parameters determine its coefficients. -/
noncomputable def phasePolynomial (d e : Nat) : Polynomial Nat :=
  let x := Polynomial.X
  let C := Polynomial.C (R := Nat)
  let oldValue := C (d + e) * (x * C d) + x * C d + C 0
  let os := x + oldValue + C 8194
  let newValue := C (d + e) * (x * C e) + x * C e + C d
  let es := x + newValue + C MachineOverlayRows.trueBits.length + C 2
  let block := C d * os + C e * es
  let cap := x + x * C (d + e) + C 2 + x * block
  let oldCost := C 2 * x + C 8 * (x * C d) + oldValue + C 4 * os + C 8224
  let newCost := C 8 * (x * C e) + C 4 * es + newValue + C MachineOverlayRows.trueBits.length + C 28
  let pair := (C d * (oldCost + C 2 * (cap + C d * os) + C 1) + C 1) +
    (C e * (newCost + C 2 * (cap + C d * os + C e * es) + C 1) + C 1) +
    (C 3 * x + C 6)
  x * (pair + C 1) + C 1 + (C 2 * x + x * C d + C 8)

@[simp] theorem phasePolynomial_eval (d e n : Nat) :
    (phasePolynomial d e).eval n = n * (pairBudget d e n + 1) + 1 + cleanupSteps n (n * d) := by
  simp only [phasePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, pairBudget, outputCapacity, blockSize, oldSize, expanderSize,
    MachineLazyRows.rowSizeBound, MachineLazyRows.rowCostBound, MachineLazyRows.valueBound,
    MachineOverlayRows.rowSizeBound, MachineOverlayRows.rowCostBound,
    MachineOverlayRows.valueBound, cleanupSteps]

noncomputable def timePolynomial (d e : Nat) : Polynomial Nat :=
  Polynomial.C 12 * Polynomial.X + Polynomial.C 18 + phasePolynomial d e

end MaxCutGames.Foundations.Complexity.MachineOverlayTable

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachinePaddedOverlay
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Physical composition of vertex padding, expander generation, and overlay

The level produced by vertex padding is the family machine's actual input
stack. The two resulting archives are the overlay machine's actual archive
stacks. Static tape placement and finite-state framing preserve the original
input; no copying or recomputation is hidden in a phase boundary.
-/

namespace MaxCutGames.Foundations.Complexity.MachinePaddedOverlay

open Turing MachineComposition MachineCloudPadding
open PCP

variable {d : Nat}

abbrev Tape := MachineVertexPadding.Tape ⊕ (MachineExpanderFamily.Tape ⊕ MachineOverlayTable.Tape)
abbrev Alphabet (_ : Tape) := Bool
abbrev Label (d : Nat) := MachineVertexPadding.Label d ⊕ (MachineExpanderFamily.Label baseDegree ⊕ MachineOverlayTable.Label d overlayDegree)
abbrev State (d : Nat) := MachineVertexPadding.State (MachineExpanderFamily.State Unit baseDegree × MachineOverlayTable.State Unit d overlayDegree)

theorem overlayDegree_positive : 0 < overlayDegree :=
  Nat.mul_pos MachineExpanderFamily.baseDegree_positive MachineExpanderFamily.baseDegree_positive

def paddingTape (k : MachineVertexPadding.Tape) : Tape := .inl k

def paddingView : Tape → Option MachineVertexPadding.Tape
  | .inl k => some k
  | .inr _ => none

@[simp] theorem paddingView_left (k : MachineVertexPadding.Tape) : paddingView (paddingTape k) = some k := rfl

theorem paddingView_right (j : Tape) (k : MachineVertexPadding.Tape)
    (h : paddingView j = some k) : paddingTape k = j := by
  cases j with
  | inl j => cases Option.some.inj h; rfl
  | inr j => simp [paddingView] at h

/-- The family unary guard consumes the padding machine's existing level. -/
def familyTape (k : MachineExpanderFamily.Tape) : Tape :=
  if k = .inr .remainingLevel then .inl .level else .inr (.inl k)

def familyView : Tape → Option MachineExpanderFamily.Tape
  | .inl .level => some (.inr .remainingLevel)
  | .inr (.inl k) => if k = .inr .remainingLevel then none else some k
  | _ => none

@[simp] theorem familyView_left (k : MachineExpanderFamily.Tape) : familyView (familyTape k) = some k := by
  by_cases h : k = .inr .remainingLevel
  · subst k; rfl
  · simp [familyTape, familyView, h]

theorem familyView_right (j : Tape) (k : MachineExpanderFamily.Tape)
    (h : familyView j = some k) : familyTape k = j := by
  rcases j with j | j
  · cases j <;> simp_all [familyView, familyTape]
  · rcases j with j | j
    · by_cases hj : j = .inr .remainingLevel <;> simp_all [familyView, familyTape]
    · simp [familyView] at h

/-- Overlay reads exactly the two archives written by the previous phases. -/
def overlayTape (k : MachineOverlayTable.Tape) : Tape :=
  if k = MachineOverlayTable.graphArchive then .inl .output
  else if k = MachineOverlayTable.expanderArchive then .inr (.inl MachineExpanderFamily.tableTape)
  else .inr (.inr k)

def overlayView : Tape → Option MachineOverlayTable.Tape
  | .inl .output => some MachineOverlayTable.graphArchive
  | .inr (.inl k) => if k = MachineExpanderFamily.tableTape then some MachineOverlayTable.expanderArchive else none
  | .inr (.inr k) =>
      if k = MachineOverlayTable.graphArchive ∨ k = MachineOverlayTable.expanderArchive then none else some k
  | _ => none

@[simp] theorem overlayView_left (k : MachineOverlayTable.Tape) : overlayView (overlayTape k) = some k := by
  by_cases hg : k = MachineOverlayTable.graphArchive
  · subst k; rfl
  · by_cases he : k = MachineOverlayTable.expanderArchive
    · subst k; rfl
    · simp [overlayTape, overlayView, hg, he]

theorem overlayView_right (j : Tape) (k : MachineOverlayTable.Tape)
    (h : overlayView j = some k) : overlayTape k = j := by
  rcases j with j | j
  · cases j <;> simp_all [overlayView, overlayTape, MachineOverlayTable.graphArchive]
  · rcases j with j | j
    · by_cases hj : j = MachineExpanderFamily.tableTape
      · subst j
        have hk : MachineOverlayTable.expanderArchive = k := by
          simpa [overlayView] using h
        subst k
        rfl
      · simp [overlayView, hj] at h
    · by_cases hg : j = MachineOverlayTable.graphArchive
      · simp [overlayView, hg] at h
      · by_cases he : j = MachineOverlayTable.expanderArchive
        · simp [overlayView, he] at h
        · simp_all [overlayView, overlayTape]

def paddingLabel (l : MachineVertexPadding.Label d) : Label d := .inl l
def familyLabel (l : MachineExpanderFamily.Label baseDegree) : Label d := .inr (.inl l)
def overlayLabel (l : MachineOverlayTable.Label d overlayDegree) : Label d := .inr (.inr l)
def main : Label d := paddingLabel (.splitCode .copyFirst)
def familyEntry : Label d := familyLabel (.inr .initialize_)
def overlayEntry : Label d := overlayLabel (.inl .copyFirst)

def familyStates (d : Nat) :
    (MachineExpanderFamily.State Unit baseDegree × ((MachineOverlayTable.State Unit d overlayDegree × Bool) × Option Bool)) ≃
      State d where
  toFun s := (((s.1, s.2.1.1), s.2.1.2), s.2.2)
  invFun s := (s.1.1.1, ((s.1.1.2, s.1.2), s.2))
  left_inv := by rintro ⟨f, ⟨⟨o, b⟩, r⟩⟩; rfl
  right_inv := by rintro ⟨⟨⟨f, o⟩, b⟩, r⟩; rfl

def overlayStates (d : Nat) :
    (MachineOverlayTable.State Unit d overlayDegree × ((MachineExpanderFamily.State Unit baseDegree × Bool) × Option Bool)) ≃
      State d where
  toFun s := (((s.2.1.1, s.1), s.2.1.2), s.2.2)
  invFun s := (s.1.1.2, ((s.1.1.1, s.1.2), s.2))
  left_inv := by rintro ⟨o, ⟨⟨f, b⟩, r⟩⟩; rfl
  right_inv := by rintro ⟨⟨⟨f, o⟩, b⟩, r⟩; rfl

def familySource (H : BaseTable) (d : Nat) : MachineExpanderFamily.Label baseDegree →
    TM2.Stmt MachineExpanderFamily.BoolAlphabet (MachineExpanderFamily.Label baseDegree) (State d) :=
  MachineStateEquiv.program (familyStates d) (MachineStateFrame.frameProgram
    (MachineExpanderFamily.boolView MachineExpanderFamily.baseDegree_positive H MachineExpanderFamily.baseDegree_cloud_gt_one))

def clean (H : BaseTable) (d : Nat) (hd : 0 < d) : State d :=
  (((MachineExpanderFamily.initialState MachineExpanderFamily.baseDegree_positive H (),
    MachineOverlayTable.clean d overlayDegree hd overlayDegree_positive ()), false), none)

/-- The archives, family count, and level residue are the only retained
non-output stacks. Work stacks, including unused duplicate slots, are empty. -/
def memory (input padded level rotor count output : List Bool) : Tape → List Bool
  | .inl k => MachineVertexPadding.memory input padded [] [] [] level [] [] k
  | .inr (.inl (.inl (.inl .table))) => rotor
  | .inr (.inl (.inr .currentSize)) => count
  | .inr (.inl _) => []
  | .inr (.inr k) => if k = MachineOverlayTable.output then output else []

def placeExecution_inline_MachinePaddedOverlay {K Λ S : Type} [DecidableEq K]
    (tape : K → Tape) (view : Tape → Option K)
    (left : ∀ k, view (tape k) = some k)
    (right : ∀ j k, view j = some k → tape k = j)
    (labels : Λ → Label d) (exit : Option (Label d)) (extra : Tape → List Bool)
    (source : Λ → TM2.Stmt (fun _ : K => Bool) Λ S)
    (target : Label d → TM2.Stmt Alphabet (Label d) S)
    (atLabels : ∀ l, target (labels l) = Placement.statement tape labels exit (source l))
    {a b : TM2.Cfg (fun _ : K => Bool) Λ S} {budget : Nat}
    (run : StateTransition.EvalsToInTime (TM2.step source) a (some b) budget) :
    StateTransition.EvalsToInTime (TM2.step target)
      (Placement.configuration view labels exit extra a)
      (some (Placement.configuration view labels exit extra b)) budget :=
  liftExecutionInTime _ _ _
    (Placement.step_simulation tape view left right labels exit extra source target atLabels) run

theorem padding_initial_memory (input : List Bool) :
    Placement.tapes paddingView (MachineVertexPadding.memory input [] [] [] [] [] [] []) (fun _ => []) =
      memory input [] [] [] [] [] := by
  funext k
  rcases k with k | k
  · rfl
  · rcases k with k | k
    · rcases k with k | k
      · rcases k with k | k <;> cases k <;> rfl
      · cases k <;> rfl
    · simp [Placement.tapes, paddingView, memory]

theorem padding_final_memory (input output level : List Bool) :
    Placement.tapes paddingView (MachineVertexPadding.memory input output [] [] [] level [] []) (fun _ => []) =
      memory input output level [] [] [] := by
  funext k
  rcases k with k | k
  · rfl
  · rcases k with k | k
    · rcases k with k | k
      · rcases k with k | k <;> cases k <;> rfl
      · cases k <;> rfl
    · simp [Placement.tapes, paddingView, memory]

noncomputable def familyPolynomial : Polynomial Nat :=
  Polynomial.C MachineExpanderFamilyBounds.inputCoefficient * (Polynomial.X + 1)^5

noncomputable def timePolynomial (d : Nat) : Polynomial Nat :=
  MachineVertexPadding.timePolynomial d + familyPolynomial +
    (MachineOverlayTable.timePolynomial d overlayDegree).comp (archivePolynomial d)

end MaxCutGames.Foundations.Complexity.MachinePaddedOverlay

namespace MaxCutGames.Foundations.Complexity.MachinePaddedOverlayRuntime

open Turing
open PCP
open MachinePaddedOverlay (BaseTable Tape Label State)

/-- A fixed finite list of every non-output stack. This includes both
retained archives, the original input, and the physically consumed level. -/
noncomputable def cleanupTapes : List Tape :=
  (Finset.univ.erase (.inr (.inr MachineOverlayTable.output) : Tape)).toList

end MaxCutGames.Foundations.Complexity.MachinePaddedOverlayRuntime

/-! Exact dummy-block codec used by the complete lazy-table machine. -/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineLazyTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual whole-table lazy-graph machine, with fixed positive old degree.
All unbounded counts and addresses reside on unary tapes. -/

namespace MaxCutGames.Foundations.Complexity.MachineLazyTable

open Turing MachineComposition PCP
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)

abbrev State (d : Nat) := MachineLazyRows.StreamState Unit d

def clean (d : Nat) (positive : 0 < d) : State d :=
  MachineLazyRows.streamClean d positive ()

theorem clean_pair (d : Nat) (positive : 0 < d) :
    ((clean d positive).1, (none : Option Bool)) = clean d positive := rfl

end MaxCutGames.Foundations.Complexity.MachineLazyTable

end OAI
end


