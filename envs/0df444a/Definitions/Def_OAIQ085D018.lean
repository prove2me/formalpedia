-- Prove2me | Definitions.Def_OAIQ085D018
-- name    : OAIQ085D018
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T16:10:31.888327+00:00
-- url     : https://prove2.me/theorems/ab297ba3-df6f-449d-a990-ac4acc8287ac
-- title:
--   Definitions bundle OAIQ085D018 of the split of OpenAI, Constant-factor hardness of directed feedback vertex set (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DirectedFeedback.main`, carved from OpenAI's openai/math development (OpenAI, *Constant-factor hardness of directed feedback vertex set (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 538 declarations of OpenAI's Lean: 257 definitions, 2 inductive types or structures, 6 instances and 273 theorems. The definitions and types are `OAI.DFVSGames.Appendix.A13Index.BoundedPositiveTriple`, `OAI.DFVSGames.Appendix.A13Index.PositiveTriple`, `OAI.DFVSGames.Appendix.A13Index.PositiveWitness`, `OAI.DFVSGames.Appendix.A13Index.Triple`, `OAI.DFVSGames.Appendix.A13Index.WeakPositive`, `OAI.DFVSGames.Appendix.A13Index.boundedPositiveTripleFintype`, `OAI.DFVSGames.Appendix.A13Index.geometricIndexFintype`, `OAI.DFVSGames.Appendix.A13Index.positiveEquiv`, `OAI.DFVSGames.Appendix.A13Index.positiveInverse`, `OAI.DFVSGames.Appendix.A13Index.positiveMap`, `OAI.DFVSGames.Appendix.A13Index.positiveTripleFintype`, `OAI.DFVSGames.Appendix.A13Index.positiveWitnessFintype`, `OAI.DFVSGames.Appendix.A13Index.size`, `OAI.DFVSGames.Appendix.A13Index.tripleFintype`, `OAI.DFVSGames.Appendix.A13Index.weakA`, `OAI.DFVSGames.Appendix.A13Index.weakB`, `OAI.DFVSGames.Appendix.A13Index.weakPositiveFintype`, `OAI.DFVSGames.Appendix.A13Reduction.boundedPositiveTripleSum`, `OAI.DFVSGames.Appendix.A13Reduction.positiveTripleSum`, `OAI.DFVSGames.Appendix.A13Reduction.tripleMoment`, `OAI.DFVSGames.Appendix.A13Reduction.tripleTerm`, `OAI.DFVSGames.Appendix.A1Reduction.weakFourthSum`, `OAI.DFVSGames.Appendix.A5ForwardIndex.Fiber`, `OAI.DFVSGames.Appendix.A5ForwardIndex.Index`, `OAI.DFVSGames.Appendix.A5ForwardIndex.descendant`, `OAI.DFVSGames.Appendix.A5ForwardIndex.earlierTriple`, `OAI.DFVSGames.Appendix.A5ForwardIndex.encode`, `OAI.DFVSGames.Appendix.A5ForwardIndex.indexFintype`, `OAI.DFVSGames.Appendix.A5ForwardIndex.sourceI`, `OAI.DFVSGames.Appendix.A5ForwardIndex.sourceJ`, `OAI.DFVSGames.Appendix.A5ForwardIndex.targetRank`, `OAI.DFVSGames.Appendix.A5IndexCount.encode`, `OAI.DFVSGames.Appendix.A5IndexCount.fullRange`, `OAI.DFVSGames.Appendix.A5IndexCount.insideEquiv`, `OAI.DFVSGames.Appendix.A5IndexCount.projectionA0`, `OAI.DFVSGames.Appendix.A5IndexCount.sectionB0`, `OAI.DFVSGames.Appendix.A5Induction.BoundAtDegree`, `OAI.DFVSGames.Appendix.A5Induction.dampedHybridMoment`, `OAI.DFVSGames.Appendix.A5Induction.dampedMapMoment`, `OAI.DFVSGames.Appendix.A5Induction.postA5Sum` and 219 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `DirectedFeedback_Encoding_ActualGoodRows`, `DirectedFeedback_Encoding_CanonicalWordTemplate`, `DirectedFeedback_Encoding_SelectedPolicies`, `DirectedFeedback_Games_A4IndexCount`, `DirectedFeedback_Games_A5ForwardIndex`, `DirectedFeedback_Games_A5Scalar`, `DirectedFeedback_Games_AddressTupleBody`, `DirectedFeedback_Games_AddressTupleLoaded`, `DirectedFeedback_Games_AffineWitnessNormalization`, `DirectedFeedback_Games_CoordinateTransport`, `DirectedFeedback_Games_Derivatives`, `DirectedFeedback_Games_KMSAnalyticCodomainTransport`, `DirectedFeedback_Games_KMSAnalyticHybridEnergyMixed`, `DirectedFeedback_Games_KMSAnalyticHyperplaneExtensions`, `DirectedFeedback_Games_KMSAnalyticSmallTransport`, `DirectedFeedback_Games_NaturalTransport`, `DirectedFeedback_Games_RowErasureSliceUniform`, `DirectedFeedback_Games_SubmoduleInterval`, `DirectedFeedback_Games_UniformReduction`, `DirectedFeedback_Games_UpperMobius`, `DirectedFeedback_Games_VisibleTransfer`, `DirectedFeedback_Machines_AddressMachineInitial`, `DirectedFeedback_Machines_MachineAddressHeaders`, `DirectedFeedback_Machines_MachineBinaryLiteralMachine`, `DirectedFeedback_Machines_MachineBinaryRenameMachine`, `DirectedFeedback_Machines_MachineBinaryTokenMachine`, `DirectedFeedback_Machines_MachineBinaryTotalInputMachine`, `DirectedFeedback_Machines_MachineExpanderFamilyLoop`, `DirectedFeedback_Machines_MachineOutcomeRows`, `DirectedFeedback_Machines_MachinePaddedExpanderFamily`, `DirectedFeedback_Machines_MachineSingleOrbitBridge`, `DirectedFeedback_Machines_MachineSingleOrbitCodec`, `DirectedFeedback_Machines_MachineTemplateAddress`, `DirectedFeedback_Machines_MachineTuple`, `DirectedFeedback_Machines_OutputSize`, `DirectedFeedback_Machines_RuntimeFinish`, `DirectedFeedback_Probability_A13Reduction`, `DirectedFeedback_Probability_KMSFourthMomentZoomTransport`.
--
--   **Imports.** It imports the bundles `OAIQ085D012` and `OAIQ085D013` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ085D024`, `OAIQ085D025`, `OAIQ085D026` and `OAIQ085D027`; the statement `OAI.DFVSGames.Appendix.A13Reduction.degree_reduction_truncated`; the proof of `OAI.DFVSGames.Appendix.A13Reduction.degree_reduction_truncated`.
-- source:
--   OpenAI, Constant-factor hardness of directed feedback vertex set (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Constant-factor-hardness-of-directed-feedback-vertex-set-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ085D012
import Definitions.Def_OAIQ085D013

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_RuntimeFinish
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Hastad.SourceRuntimeFinish

open Turing Complexity

variable {K Λ σ : Type} [DecidableEq K]

def statement (clearKeys : List K) (accumulator output : K) (canonical : σ)
    (labels : Label clearKeys → Λ) (exit : Option Λ) :
    Label clearKeys → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool)
  | .inl label => MachineDrainMany.instruction clearKeys (fun l => labels (.inl l))
      (some (labels (.inr false))) label
  | .inr false => Reduction.MachineTransfer.loopAt accumulator output id false
      (labels (.inr false)) (some (labels (.inr true)))
  | .inr true => .load (fun _ => (canonical, none)) (Reduction.MachineTransfer.exitAt output exit)

open scoped BigOperators


end DFVSGames.Foundations.Hastad.SourceRuntimeFinish


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineExpanderFamilyLoop
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

namespace DFVSGames.Foundations.Complexity.MachinePaddedExpanderFamily

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl

variable {ρ : Type} [Fintype ρ]

def initialState (state : MachineExpanderFamily.State ρ fixedDegree)
    (register : Option Bool) : State ρ := (state, (false, register))

def finalState (H : SmallTable) (state : MachineExpanderFamily.State ρ fixedDegree) : State ρ :=
  (MachineExpanderFamily.initialState MachineExpanderFamily.baseDegree_positive H
    (MachineExpanderFamily.caller state), (false, none))

end DFVSGames.Foundations.Complexity.MachinePaddedExpanderFamily
end

section

namespace DFVSGames.Foundations.Complexity.MachinePaddedExpanderFamilyBounds

open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords

def outputWord
    (H : Table (cloudSize PCP.Expanders.baseDegree) PCP.Expanders.baseDegree) (k : Nat) :
    List Bool :=
  encodeWords (rotationWords (family H (PCP.PreprocessingLevels.boundedLevel k)))

end DFVSGames.Foundations.Complexity.MachinePaddedExpanderFamilyBounds

end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachinePaddedExpanderFamily
attribute [-instance] _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
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

namespace DFVSGames.Foundations.Complexity.MachineRegularFamily

open Turing MachineComposition
open MachineCloudPadding

abbrev Tape := CoreTape ⊕ NativeTape
abbrev SmallTable := MachinePaddedExpanderFamily.SmallTable
abbrev FamilyState := MachineExpanderFamily.State Unit MachinePaddedExpanderFamily.fixedDegree
abbrev State := (FamilyState × Bool) × Option Bool

def inputNative : NativeTape := .inr .input
def outputNative : NativeTape := .inl MachineExpanderFamily.tableTape
def powerNative : NativeTape := .inr .power
def sizeNative : NativeTape := .inl (.inr .currentSize)
def levelNative : NativeTape := .inl (.inr .remainingLevel)

def powerTape : Tape := .inr powerNative
def sizeTape : Tape := .inr sizeNative
def levelTape : Tape := .inr levelNative

def familyView : Tape → Option NativeTape
  | .inl i => if i = 4 then some inputNative else if i = 7 then some outputNative else none
  | .inr t => if t = inputNative then none else if t = outputNative then none else some t

def stateEquiv : MachinePaddedExpanderFamily.State Unit ≃ State :=
  (Equiv.prodAssoc FamilyState Bool (Option Bool)).symm

def seedState (H : SmallTable) : FamilyState :=
  MachineExpanderFamily.initialState MachineExpanderFamily.baseDegree_positive H ()

def readyState (H : SmallTable) : State := ((seedState H, false), none)

def frame (core : CoreTape → List Bool) : Tape → List Bool
  | .inl i => core i
  | .inr _ => []

def rotor (H : SmallTable) (k : Nat) : List Bool :=
  MachinePaddedExpanderFamilyBounds.outputWord H k

def resultCore (H : SmallTable) (k : Nat) (core : CoreTape → List Bool) :
    CoreTape → List Bool := Function.update core 7 (rotor H k)

def working (core : CoreTape → List Bool) (power size level : List Bool) : Tape → List Bool
  | .inl i => core i
  | .inr t => if t = powerNative then power
      else if t = sizeNative then size else if t = levelNative then level else []

@[simp] theorem working_power (core : CoreTape → List Bool) (p s l : List Bool) :
    working core p s l powerTape = p := by simp [working, powerTape]

@[simp] theorem working_size (core : CoreTape → List Bool) (p s l : List Bool) :
    working core p s l sizeTape = s := by
  simp [working, sizeTape, powerNative, sizeNative]

@[simp] theorem working_level (core : CoreTape → List Bool) (p s l : List Bool) :
    working core p s l levelTape = l := by
  simp [working, levelTape, powerNative, sizeNative, levelNative]

@[simp] theorem working_empty (core : CoreTape → List Bool) :
    working core [] [] [] = frame core := by
  funext t; cases t <;> simp [working, frame]

@[simp] theorem source_initial_state (H : SmallTable) :
    stateEquiv (MachinePaddedExpanderFamily.initialState (seedState H) none) =
      readyState H := rfl

@[simp] theorem source_final_state (H : SmallTable) :
    stateEquiv (MachinePaddedExpanderFamily.finalState H (seedState H)) =
      readyState H := by
  simp [stateEquiv, MachinePaddedExpanderFamily.finalState, readyState, seedState]

@[simp] theorem result_output (H : SmallTable) (k : Nat) (core : CoreTape → List Bool) :
    frame (resultCore H k core) (.inl 7) = rotor H k := by simp [frame, resultCore]

@[simp] theorem result_private_empty (H : SmallTable) (k : Nat)
    (core : CoreTape → List Bool) (t : NativeTape) :
    frame (resultCore H k core) (.inr t) = [] := rfl

end DFVSGames.Foundations.Complexity.MachineRegularFamily
end

section

namespace DFVSGames.Foundations.Complexity.MachineUnaryLessAt

open Turing MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

@[simp] theorem tapes_left (slots : Fin 4 ↪ K) (base : K → List Bool)
    (left right savedLeft savedRight : List Bool) :
    tapes slots base left right savedLeft savedRight (slots 0) = left := by
  simp [tapes, slots.injective.eq_iff]

@[simp] theorem tapes_right (slots : Fin 4 ↪ K) (base : K → List Bool)
    (left right savedLeft savedRight : List Bool) :
    tapes slots base left right savedLeft savedRight (slots 1) = right := by
  simp [tapes, slots.injective.eq_iff]

@[simp] theorem tapes_savedLeft (slots : Fin 4 ↪ K) (base : K → List Bool)
    (left right savedLeft savedRight : List Bool) :
    tapes slots base left right savedLeft savedRight (slots 2) = savedLeft := by
  simp [tapes, slots.injective.eq_iff]

@[simp] theorem tapes_savedRight (slots : Fin 4 ↪ K) (base : K → List Bool)
    (left right savedLeft savedRight : List Bool) :
    tapes slots base left right savedLeft savedRight (slots 3) = savedRight := by
  simp [tapes]

@[simp] theorem update_tapes (slots : Fin 4 ↪ K) (base : K → List Bool)
    (left right savedLeft savedRight replacement : List Bool) (i : Fin 4) :
    Function.update (tapes slots base left right savedLeft savedRight) (slots i) replacement =
      tapes slots base (if i = 0 then replacement else left)
        (if i = 1 then replacement else right) (if i = 2 then replacement else savedLeft)
        (if i = 3 then replacement else savedRight) := by
  fin_cases i <;> funext k
  all_goals
    by_cases h₀ : k = slots 0
    · subst k; simp [tapes, slots.injective.eq_iff]
    · by_cases h₁ : k = slots 1
      · subst k; simp [tapes, slots.injective.eq_iff]
      · by_cases h₂ : k = slots 2
        · subst k; simp [tapes, slots.injective.eq_iff]
        · by_cases h₃ : k = slots 3
          · subst k; simp [tapes, slots.injective.eq_iff]
          · simp [tapes, h₀, h₁, h₂, h₃]

@[simp] theorem tapes_self (slots : Fin 4 ↪ K) (base : K → List Bool) :
    tapes slots base (base (slots 0)) (base (slots 1)) (base (slots 2)) (base (slots 3)) = base := by
  simp [tapes]

@[simp] theorem transferLeft_tapes (slots : Fin 4 ↪ K) (base : K → List Bool)
    (left right savedLeft savedRight replacementSaved replacementLeft : List Bool) :
    Reduction.MachineTransfer.tapesAt (slots 2) (slots 0)
      (tapes slots base left right savedLeft savedRight) replacementSaved replacementLeft =
      tapes slots base replacementLeft right replacementSaved savedRight := by
  simp [Reduction.MachineTransfer.tapesAt]

@[simp] theorem transferRight_tapes (slots : Fin 4 ↪ K) (base : K → List Bool)
    (left right savedLeft savedRight replacementSaved replacementRight : List Bool) :
    Reduction.MachineTransfer.tapesAt (slots 3) (slots 1)
      (tapes slots base left right savedLeft savedRight) replacementSaved replacementRight =
      tapes slots base left replacementRight savedLeft replacementSaved := by
  simp [Reduction.MachineTransfer.tapesAt]

end DFVSGames.Foundations.Complexity.MachineUnaryLessAt
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineBinaryTotalInputMachine
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

namespace DFVSGames.BinaryNameCompare

open Turing
open DFVSGames.Foundations.Complexity
open MachineComposition

variable {K Λ A : Type} [DecidableEq K]

theorem compareTrace (tape : Fin 5 → K) (distinct : Function.Injective tape)
    (labels : Label → Λ) (equalExit differentExit malformedExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ l, program (labels l) =
      instruction tape labels equalExit differentExit malformedExit l)
    (base : K → List Bool) (bits suffix key : List Bool)
    (canonical : BinaryNameMachine.canonical bits = true)
    (sourceWord : base (tape 0) = BinaryNameMachine.frame bits ++ suffix)
    (keyWord : base (tape 1) = key)
    (candidateEmpty : base (tape 2) = []) (copyEmpty : base (tape 3) = [])
    (scratchEmpty : base (tape 4) = []) (ambient : A) :
    (advance (TM2.step program))^[steps bits.length key.length]
      (some ⟨some (labels .scan), clean ambient, base⟩) =
      some ⟨if bits.reverse = key then equalExit else differentExit,
        clean ambient, Function.update base (tape 0) suffix⟩ := by
  have hd (i j : Fin 5) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  let finalBase := Function.update base (tape 0) suffix
  let afterScan := Function.update finalBase (tape 2) bits.reverse
  let afterCopy := Function.update afterScan (tape 3) key
  have scanRun : (advance (TM2.step program))^[bits.length + 1]
      (some ⟨some (labels .scan), clean ambient, base⟩) =
      some ⟨some (labels .copyOut), clean ambient, afterScan⟩ := by
    let back := MachineStateEquiv.program (scanStateEquiv A).symm program
    have atScan : back (labels .scan) =
        BinaryNameMachine.scan (tape 0) (tape 2) (labels .scan)
          (some (labels .copyOut)) malformedExit := by
      change MachineStateEquiv.statement (scanStateEquiv A).symm
        (program (labels .scan)) = _
      rw [atLabels .scan]
      exact MachineStateEquiv.statement_symm_statement (scanStateEquiv A) _
    have backForward : MachineStateEquiv.program (scanStateEquiv A) back = program := by
      funext l
      change MachineStateEquiv.statement (scanStateEquiv A)
        (MachineStateEquiv.statement (scanStateEquiv A).symm (program l)) = _
      simpa only [Equiv.symm_symm] using
        MachineStateEquiv.statement_symm_statement (scanStateEquiv A).symm (program l)
    have initialTapes : DFVSGames.Reduction.MachineTransfer.tapesAt (tape 0) (tape 2)
        base (BinaryNameMachine.frame bits ++ suffix) [] = base := by
      rw [← sourceWord, ← candidateEmpty]
      exact DFVSGames.Reduction.MachineTransfer.tapesAt_self _ _ _
    have native := BinaryNameMachine.framedTrace (tape 0) (tape 2) (hd 0 2 (by decide))
      (labels .scan) (some (labels .copyOut)) malformedExit back atScan base (ambient, false)
      bits suffix [] none
    simp only [canonical, ↓reduceIte, initialTapes, List.append_nil] at native
    have transported := MachineStateEquiv.trace (scanStateEquiv A) back _ _ _ native
    rw [backForward] at transported
    simpa only [MachineStateEquiv.configuration, scanStateEquiv, Equiv.coe_fn_mk, BinaryNameMachine.clean,
      clean, afterScan, finalBase, DFVSGames.Reduction.MachineTransfer.tapesAt] using transported
  have afterScanKey : afterScan (tape 1) = key := by
    simpa [afterScan, finalBase, hd 1 2 (by decide), hd 1 0 (by decide)] using keyWord
  have afterScanCopy : afterScan (tape 3) = [] := by
    simpa [afterScan, finalBase, hd 3 2 (by decide), hd 3 0 (by decide)] using copyEmpty
  have afterScanScratch : afterScan (tape 4) = [] := by
    simpa [afterScan, finalBase, hd 4 2 (by decide), hd 4 0 (by decide)] using scratchEmpty
  have copyRun : (advance (TM2.step program))^[2 * (key.length + 1)]
      (some ⟨some (labels .copyOut), clean ambient, afterScan⟩) =
      some ⟨some (labels .compare), clean ambient, afterCopy⟩ := by
    have h := MachineCopy.copyTrace (tape 1) (tape 3) (tape 4)
      (hd 1 3 (by decide)) (hd 1 4 (by decide)) (hd 3 4 (by decide)) false
      (labels .copyOut) (labels .copyBack) (some (labels .compare)) program
      (atLabels .copyOut) (atLabels .copyBack) afterScan afterScanScratch
      (ambient, false, none) none
    simpa only [afterScanKey, afterScanCopy, List.append_nil, clean, afterCopy] using h
  have candidateWord : afterCopy (tape 2) = bits.reverse := by
    simp [afterCopy, afterScan, hd 2 3 (by decide)]
  have copiedWord : afterCopy (tape 3) = key := by simp [afterCopy]
  have restored : DFVSGames.Reduction.MachineTransfer.tapesAt (tape 2) (tape 3)
      afterCopy [] [] = finalBase := by
    funext k
    by_cases hc : k = tape 2
    · subst k
      simp [DFVSGames.Reduction.MachineTransfer.tapesAt, afterCopy, afterScan, finalBase,
        hd 2 3 (by decide), hd 2 0 (by decide), candidateEmpty]
    · by_cases hk : k = tape 3
      · subst k
        simp [DFVSGames.Reduction.MachineTransfer.tapesAt, afterCopy, afterScan, finalBase,
          hd 3 0 (by decide), copyEmpty]
      · simp [DFVSGames.Reduction.MachineTransfer.tapesAt, afterCopy, afterScan, hc, hk]
  have comparisonRun : (advance (TM2.step program))^[max bits.length key.length + 1]
      (some ⟨some (labels .compare), clean ambient, afterCopy⟩) =
      some ⟨if bits.reverse = key then equalExit else differentExit,
        clean ambient, finalBase⟩ := by
    let back := MachineStateEquiv.program (compareStateEquiv A).symm program
    have atCompare : back (labels .compare) =
        MachineCompare.loop (tape 2) (tape 3) (labels .compare) equalExit differentExit := by
      change MachineStateEquiv.statement (compareStateEquiv A).symm
        (program (labels .compare)) = _
      rw [atLabels .compare]
      exact MachineStateEquiv.statement_symm_statement (compareStateEquiv A) _
    have backForward : MachineStateEquiv.program (compareStateEquiv A) back = program := by
      funext l
      change MachineStateEquiv.statement (compareStateEquiv A)
        (MachineStateEquiv.statement (compareStateEquiv A).symm (program l)) = _
      simpa only [Equiv.symm_symm] using
        MachineStateEquiv.statement_symm_statement (compareStateEquiv A).symm (program l)
    have native := MachineCompare.compareTrace_fromTapes (tape 2) (tape 3)
      (hd 2 3 (by decide)) (labels .compare) equalExit differentExit back atCompare afterCopy
      ambient none none
    rw [candidateWord, copiedWord, restored, List.length_reverse] at native
    have transported := MachineStateEquiv.trace (compareStateEquiv A) back _ _ _ native
    rw [backForward] at transported
    simpa only [MachineStateEquiv.configuration, compareStateEquiv, Equiv.coe_fn_mk, clean] using transported
  exact joinTrace_inline_MachineBinaryNameCompare (joinTrace_inline_MachineBinaryNameCompare scanRun copyRun) comparisonRun

end DFVSGames.BinaryNameCompare

end

section

namespace DFVSGames.BinaryNameSearch

open Turing
open DFVSGames.Foundations.Complexity
open MachineComposition
open DFVSGames.Reduction.MachineTransfer

section Program

variable {K Λ A : Type} [DecidableEq K]

theorem update_source_inline_MachineBinaryNameSearch (source counter : K) (distinct : source ≠ counter)
    (base : K → List Bool) (input count replacement : List Bool) :
    Function.update (tapesAt source counter base input count) source replacement =
      tapesAt source counter base replacement count := by
  funext k
  by_cases hs : k = source
  · subst k; simp [tapesAt, distinct]
  · by_cases hc : k = counter
    · subst k; simp [tapesAt, Ne.symm distinct]
    · simp [tapesAt, hs, hc]

theorem update_counter_inline_MachineBinaryNameSearch (source counter : K)
    (base : K → List Bool) (input count replacement : List Bool) :
    Function.update (tapesAt source counter base input count) counter replacement =
      tapesAt source counter base input replacement := by
  simp [tapesAt]

variable (tape : Fin 6 → K) (distinct : Function.Injective tape)
variable (labels : Label → Λ) (foundExit missingExit malformedExit : Option Λ)
variable (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
variable (atLabels : ∀ l, program (labels l) =
  instruction tape labels foundExit missingExit malformedExit l)
variable (base : K → List Bool) (ambient : A)

include distinct atLabels

theorem signStep (sign : Bool) (input counter : List Bool) :
    TM2.step program
      ⟨some (labels .sign), clean ambient,
        tapesAt (tape 0) (tape 5) base (sign :: input) counter⟩ =
      some ⟨some (labels (.comparison .scan)), clean ambient,
        tapesAt (tape 0) (tape 5) base input counter⟩ := by
  have hd : tape 0 ≠ tape 5 := fun h => (by decide : (0 : Fin 6) ≠ 5) (distinct h)
  change some (TM2.stepAux (program (labels .sign)) _ _) = _
  rw [atLabels .sign]
  simp [instruction, TM2.stepAux, clean, BinaryNameCompare.clean, hd, update_source_inline_MachineBinaryNameSearch]

omit distinct in
theorem incrementStep (input counter : List Bool) :
    TM2.step program
      ⟨some (labels .increment), clean ambient,
        tapesAt (tape 0) (tape 5) base input counter⟩ =
      some ⟨some (labels .sign), clean ambient,
        tapesAt (tape 0) (tape 5) base input (true :: counter)⟩ := by
  change some (TM2.stepAux (program (labels .increment)) _ _) = _
  rw [atLabels .increment]
  simp [instruction, TM2.stepAux, update_counter_inline_MachineBinaryNameSearch]

theorem tokenTrace (token : Token) (key suffix counter : List Bool)
    (canonical : BinaryNameMachine.canonical token.2 = true)
    (keyWord : base (tape 1) = key.reverse)
    (candidateEmpty : base (tape 2) = []) (copyEmpty : base (tape 3) = [])
    (scratchEmpty : base (tape 4) = []) :
    (advance (TM2.step program))^[1 + BinaryNameCompare.steps token.2.length key.length]
      (some ⟨some (labels .sign), clean ambient,
        tapesAt (tape 0) (tape 5) base (tokenBits token ++ suffix) counter⟩) =
      some ⟨if token.2 = key then foundExit else some (labels .increment), clean ambient,
        tapesAt (tape 0) (tape 5) base suffix counter⟩ := by
  have hd (i j : Fin 6) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  let initial := tapesAt (tape 0) (tape 5) base
    (BinaryNameMachine.frame token.2 ++ suffix) counter
  have first : (advance (TM2.step program))^[1]
      (some ⟨some (labels .sign), clean ambient,
        tapesAt (tape 0) (tape 5) base (tokenBits token ++ suffix) counter⟩) =
      some ⟨some (labels (.comparison .scan)), clean ambient, initial⟩ := by
    simpa only [Function.iterate_one, advance_some, tokenBits, List.cons_append] using
      signStep tape distinct labels foundExit missingExit malformedExit program atLabels
        base ambient token.1 (BinaryNameMachine.frame token.2 ++ suffix) counter
  have second := BinaryNameCompare.compareTrace (compareTapes tape)
    (compareTapes_injective tape distinct) (fun l => labels (.comparison l))
    foundExit (some (labels .increment)) malformedExit program
    (fun l => atLabels (.comparison l)) initial token.2 suffix key.reverse canonical
    (by simp [initial, compareTapes, hd 0 5 (by decide)])
    (by simpa [initial, compareTapes, tapesAt,
      hd 1 0 (by decide), hd 1 5 (by decide)] using keyWord)
    (by simpa [initial, compareTapes, tapesAt, hd 2 0 (by decide), hd 2 5 (by decide)]
      using candidateEmpty)
    (by simpa [initial, compareTapes, tapesAt,
      hd 3 0 (by decide), hd 3 5 (by decide)] using copyEmpty)
    (by simpa [initial, compareTapes, tapesAt,
      hd 4 0 (by decide), hd 4 5 (by decide)] using scratchEmpty)
    ambient
  have heq : token.2.reverse = key.reverse ↔ token.2 = key := by
    constructor
    · intro h
      have := congrArg List.reverse h
      simpa only [List.reverse_reverse] using this
    · intro h; rw [h]
  simp only [List.length_reverse, heq] at second
  rw [show Function.update initial (compareTapes tape 0) suffix =
      tapesAt (tape 0) (tape 5) base suffix counter by
    exact update_source_inline_MachineBinaryNameSearch _ _ (hd 0 5 (by decide)) base _ counter suffix] at second
  exact joinTrace_inline_MachineBinaryNameSearch first second

theorem searchTrace (tokens : List Token) (key suffix counter : List Bool)
    (canonical : ∀ token ∈ tokens, BinaryNameMachine.canonical token.2 = true)
    (present : key ∈ payloads tokens)
    (keyWord : base (tape 1) = key.reverse)
    (candidateEmpty : base (tape 2) = []) (copyEmpty : base (tape 3) = [])
    (scratchEmpty : base (tape 4) = []) :
    (advance (TM2.step program))^[steps tokens key]
      (some ⟨some (labels .sign), clean ambient,
        tapesAt (tape 0) (tape 5) base (stream tokens ++ suffix) counter⟩) =
      some ⟨foundExit, clean ambient,
        tapesAt (tape 0) (tape 5) base (stream (afterMatch tokens key) ++ suffix)
          (List.replicate ((payloads tokens).idxOf key) true ++ counter)⟩ := by
  induction tokens generalizing counter with
  | nil => simp at present
  | cons token tokens ih =>
      have headCanonical := canonical token (by simp)
      have tailCanonical : ∀ t ∈ tokens, BinaryNameMachine.canonical t.2 = true :=
        fun t ht => canonical t (by simp [ht])
      have first := tokenTrace tape distinct labels foundExit missingExit malformedExit
        program atLabels base ambient token key (stream tokens ++ suffix) counter
        headCanonical keyWord candidateEmpty copyEmpty scratchEmpty
      by_cases same : token.2 = key
      · simpa only [steps, same, ite_true, if_true, Nat.add_zero, stream_cons,
          List.append_assoc, afterMatch, payloads_cons, List.idxOf_cons_self,
          List.replicate_zero, List.nil_append] using first
      · have remaining : key ∈ payloads tokens := by
          rcases List.mem_cons.mp present with equal | remaining
          · exact False.elim (same equal.symm)
          · exact remaining
        have increment : (advance (TM2.step program))^[1]
            (some ⟨some (labels .increment), clean ambient,
              tapesAt (tape 0) (tape 5) base (stream tokens ++ suffix) counter⟩) =
            some ⟨some (labels .sign), clean ambient,
              tapesAt (tape 0) (tape 5) base (stream tokens ++ suffix) (true :: counter)⟩ := by
          simpa only [Function.iterate_one, advance_some] using
            incrementStep tape labels foundExit missingExit malformedExit program
              atLabels base ambient (stream tokens ++ suffix) counter
        have rest := ih (true :: counter) tailCanonical remaining
        simp only [same, ite_false] at first
        have full := joinTrace_inline_MachineBinaryNameSearch first (joinTrace_inline_MachineBinaryNameSearch increment rest)
        have counterEq : List.replicate ((payloads tokens).idxOf key) true ++
            (true :: counter) =
            List.replicate ((payloads tokens).idxOf key + 1) true ++ counter := by
          rw [List.replicate_succ']
          simp only [List.append_assoc, List.singleton_append]
        have indexEq : (token.2 :: payloads tokens).idxOf key =
            (payloads tokens).idxOf key + 1 := by
          exact List.idxOf_cons_ne _ same
        simpa only [steps, same, ite_false, stream_cons, List.append_assoc, afterMatch,
          payloads_cons, indexEq, counterEq] using full

end Program

end DFVSGames.BinaryNameSearch

end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineBinaryLiteralMachine
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

namespace DFVSGames.BinaryLiteralMachine

open Turing
open DFVSGames.Foundations.Complexity
open MachineComposition
open DFVSGames.Reduction.MachineTransfer

variable {K Λ A : Type} [DecidableEq K]

def signWord (sign : Bool) : List Bool := encodeWord (if sign then 1 else 0)

def outputWord (tokens : List BinaryNameSearch.Token) (bits : List Bool) (sign : Bool) :
    List Bool := encodeWord (index tokens bits) ++ signWord sign

theorem literalTrace (tape : Fin 9 → K) (distinct : Function.Injective tape)
    (labels : Label → Λ) (exit malformed : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ l, program (labels l) = instruction tape labels exit malformed l)
    (base : K → List Bool) (tokens : List BinaryNameSearch.Token)
    (sign : Bool) (bits suffix : List Bool)
    (canonical : BinaryNameMachine.canonical bits = true)
    (tokensCanonical : ∀ token ∈ tokens, BinaryNameMachine.canonical token.2 = true)
    (present : bits ∈ BinaryNameSearch.payloads tokens)
    (cursor : base (tape 0) = sign :: (BinaryNameMachine.frame bits ++ suffix))
    (permanent : base (tape 1) = BinaryNameSearch.stream tokens)
    (empty : ∀ i : Fin 9, 2 ≤ i.val → i.val ≤ 7 → base (tape i) = [])
    (ambient : A) :
    (advance (TM2.step program))^[steps tokens bits]
      (some ⟨some (labels .readSign), clean ambient, base⟩) =
      some ⟨exit, clean ambient,
        Function.update (Function.update base (tape 0) suffix) (tape 8)
          ((outputWord tokens bits sign).reverse ++ base (tape 8))⟩ := by
  have hd (i j : Fin 9) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  have he (i : Fin 9) (hlo : 2 ≤ i.val := by decide) (hhi : i.val ≤ 7 := by decide) :
      base (tape i) = [] := empty i hlo hhi
  let s₁ := Function.update (Function.update base (tape 7) [false]) (tape 0)
    (BinaryNameMachine.frame bits ++ suffix)
  let s₂ := Function.update (Function.update s₁ (tape 0) suffix) (tape 2) bits.reverse
  let s₃ := Function.update s₂ (tape 3) (BinaryNameSearch.stream tokens)
  let tail := BinaryNameSearch.stream (BinaryNameSearch.afterMatch tokens bits)
  let s₄ := tapesAt (tape 3) (tape 7) s₃ tail (encodeWord (index tokens bits))
  let s₅ := Function.update s₄ (tape 3) []
  let s₆ := Function.update s₅ (tape 2) []
  let s₇ := tapesAt (tape 7) (tape 8) s₆ []
    ((encodeWord (index tokens bits)).reverse ++ s₆ (tape 8))
  let s₈ := Function.update s₇ (tape 8) ((signWord sign).reverse ++ s₇ (tape 8))
  have signRun : (advance (TM2.step program))^[1]
      (some ⟨some (labels .readSign), clean ambient, base⟩) =
      some ⟨some (labels .scanKey), clean ambient sign, s₁⟩ := by
    change some (TM2.stepAux (program (labels .readSign)) _ _) = _
    rw [atLabels .readSign]
    simp [instruction, readSign, TM2.stepAux, clean, BinaryNameCompare.clean,
      cursor, he 7, hd 0 7 (by decide), s₁]
  have s₁cursor : s₁ (tape 0) = BinaryNameMachine.frame bits ++ suffix := by simp [s₁]
  have s₁key : s₁ (tape 2) = [] := by
    simp [s₁, hd 2 0 (by decide), hd 2 7 (by decide), he 2]
  have keyRun : (advance (TM2.step program))^[bits.length + 1]
      (some ⟨some (labels .scanKey), clean ambient sign, s₁⟩) =
      some ⟨some (labels .copyOut), clean ambient sign, s₂⟩ := by
    let e := BinaryNameCompare.scanStateEquiv (A × Bool)
    let back := MachineStateEquiv.program e.symm program
    have atScan : back (labels .scanKey) =
        BinaryNameMachine.scan (tape 0) (tape 2) (labels .scanKey)
          (some (labels .copyOut)) malformed := by
      change MachineStateEquiv.statement e.symm (program (labels .scanKey)) = _
      rw [atLabels .scanKey]
      exact MachineStateEquiv.statement_symm_statement e _
    have backForward : MachineStateEquiv.program e back = program := by
      funext l
      change MachineStateEquiv.statement e (MachineStateEquiv.statement e.symm (program l)) = _
      exact MachineStateEquiv.statement_symm_statement e.symm _
    have initial : tapesAt (tape 0) (tape 2) s₁
        (BinaryNameMachine.frame bits ++ suffix) [] = s₁ := by
      rw [← s₁cursor, ← s₁key]
      exact tapesAt_self _ _ _
    have native := BinaryNameMachine.framedTrace (tape 0) (tape 2) (hd 0 2 (by decide))
      (labels .scanKey) (some (labels .copyOut)) malformed back atScan s₁
      ((ambient, sign), false) bits suffix [] none
    simp only [canonical, ↓reduceIte, initial, List.append_nil] at native
    have transported := MachineStateEquiv.trace e back _ _ _ native
    rw [backForward] at transported
    simpa only [MachineStateEquiv.configuration, e, BinaryNameCompare.scanStateEquiv, Equiv.coe_fn_mk,
      BinaryNameMachine.clean, clean, BinaryNameCompare.clean, s₂, tapesAt] using transported
  have s₂permanent : s₂ (tape 1) = BinaryNameSearch.stream tokens := by
    simpa [s₂, s₁, hd 1 0 (by decide), hd 1 2 (by decide), hd 1 7 (by decide)] using permanent
  have s₂empty (i : Fin 9) (hi : i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) : s₂ (tape i) = [] := by
    rcases hi with rfl | rfl | rfl | rfl <;>
      simp [s₂, s₁, hd, he]
  have copyRun : (advance (TM2.step program))^[2 * ((BinaryNameSearch.stream tokens).length + 1)]
      (some ⟨some (labels .copyOut), clean ambient sign, s₂⟩) =
      some ⟨some (labels (.search .sign)), clean ambient sign, s₃⟩ := by
    have h := MachineCopy.copyTrace (tape 1) (tape 3) (tape 6)
      (hd 1 3 (by decide)) (hd 1 6 (by decide)) (hd 3 6 (by decide)) false
      (labels .copyOut) (labels .copyBack) (some (labels (.search .sign))) program
      (atLabels .copyOut) (atLabels .copyBack) s₂
      (s₂empty 6 (by simp)) ((ambient, sign), false, none) none
    simpa only [s₂permanent, s₂empty 3 (by simp), List.append_nil,
      clean, BinaryNameCompare.clean, s₃] using h
  have s₃key : s₃ (tape 2) = bits.reverse := by
    simp [s₃, s₂, hd 2 3 (by decide)]
  have s₃counter : s₃ (tape 7) = [false] := by
    simp [s₃, s₂, s₁, hd 7 3 (by decide), hd 7 2 (by decide), hd 7 0 (by decide)]
  have s₃stream : s₃ (tape 3) = BinaryNameSearch.stream tokens := by simp [s₃]
  have searchRun : (advance (TM2.step program))^[BinaryNameSearch.steps tokens bits]
      (some ⟨some (labels (.search .sign)), clean ambient sign, s₃⟩) =
      some ⟨some (labels .drainSearch), clean ambient sign, s₄⟩ := by
    have h := BinaryNameSearch.searchTrace (searchTapes tape)
      (searchTapes_injective tape distinct) (fun l => labels (.search l))
      (some (labels .drainSearch)) malformed malformed program
      (fun l => atLabels (.search l)) s₃ (ambient, sign) tokens bits [] [false]
      tokensCanonical present s₃key
      (by simpa [s₃, searchTapes, hd 4 3 (by decide)] using s₂empty 4 (by simp))
      (by simpa [s₃, searchTapes, hd 5 3 (by decide)] using s₂empty 5 (by simp))
      (by simpa [s₃, searchTapes, hd 6 3 (by decide)] using s₂empty 6 (by simp))
    have initial : tapesAt (tape 3) (tape 7) s₃ (BinaryNameSearch.stream tokens) [false] = s₃ := by
      rw [← s₃stream, ← s₃counter]
      exact tapesAt_self _ _ _
    simpa only [searchTapes, List.append_nil, initial, clean, BinaryNameSearch.clean,
      s₄, tail, encodeWord, index] using h
  have s₄stream : s₄ (tape 3) = tail := by simp [s₄, hd 3 7 (by decide)]
  have drainSearchRun : (advance (TM2.step program))^[tail.length + 1]
      (some ⟨some (labels .drainSearch), clean ambient sign, s₄⟩) =
      some ⟨some (labels .drainKey), clean ambient sign, s₅⟩ := by
    have h := MachineDrain.drainTrace (tape 3) (labels .drainSearch)
      (some (labels .drainKey)) program (atLabels .drainSearch) s₄ tail
      ((ambient, sign), false, none) none
    have initial : Function.update s₄ (tape 3) tail = s₄ := by
      rw [← s₄stream]; exact Function.update_eq_self _ _
    simpa only [initial, clean, BinaryNameCompare.clean, s₅] using h
  have s₅key : s₅ (tape 2) = bits.reverse := by
    simp [s₅, s₄, tapesAt, hd 2 3 (by decide), hd 2 7 (by decide), s₃key]
  have drainKeyRun : (advance (TM2.step program))^[bits.length + 1]
      (some ⟨some (labels .drainKey), clean ambient sign, s₅⟩) =
      some ⟨some (labels .emitIndex), clean ambient sign, s₆⟩ := by
    have h := MachineDrain.drainTrace (tape 2) (labels .drainKey)
      (some (labels .emitIndex)) program (atLabels .drainKey) s₅ bits.reverse
      ((ambient, sign), false, none) none
    have initial : Function.update s₅ (tape 2) bits.reverse = s₅ := by
      rw [← s₅key]; exact Function.update_eq_self _ _
    simpa only [initial, List.length_reverse, clean, BinaryNameCompare.clean, s₆] using h
  have s₆index : s₆ (tape 7) = encodeWord (index tokens bits) := by
    simp [s₆, s₅, s₄, hd 7 2 (by decide), hd 7 3 (by decide)]
  have indexRun : (advance (TM2.step program))^[index tokens bits + 2]
      (some ⟨some (labels .emitIndex), clean ambient sign, s₆⟩) =
      some ⟨some (labels .emitSign), clean ambient sign, s₇⟩ := by
    change (nextAt (Γ := Alphabet) (tape 8) program)^[index tokens bits + 2]
      (some ⟨some (labels .emitIndex), (((ambient, sign), false, none), none), s₆⟩) =
      some ⟨some (labels .emitSign), (((ambient, sign), false, none), none), s₇⟩
    have h := transferAt_fromTapes (Γ := Alphabet) (tape 7) (tape 8)
      (hd 7 8 (by decide)) id false (labels .emitIndex) (some (labels .emitSign)) program
      (atLabels .emitIndex) s₆ ((ambient, sign), false, none) none
    have time : index tokens bits + 1 + 1 = index tokens bits + 2 := by omega
    simpa only [s₆index, encodeWord_length, List.map_id_fun, id_eq, time, s₇] using h
  have emitRun : (advance (TM2.step program))^[1]
      (some ⟨some (labels .emitSign), clean ambient sign, s₇⟩) =
      some ⟨exit, clean ambient, s₈⟩ := by
    change some (TM2.stepAux (program (labels .emitSign)) _ _) = _
    rw [atLabels .emitSign]
    cases sign <;> simp [instruction, emitSign, clean, BinaryNameCompare.clean,
      TM2.stepAux, signWord, encodeWord, s₈, Function.update_idem]
  have full := joinTrace_inline_MachineBinaryLiteralMachine (joinTrace_inline_MachineBinaryLiteralMachine (joinTrace_inline_MachineBinaryLiteralMachine (joinTrace_inline_MachineBinaryLiteralMachine (joinTrace_inline_MachineBinaryLiteralMachine (joinTrace_inline_MachineBinaryLiteralMachine
    (joinTrace_inline_MachineBinaryLiteralMachine signRun keyRun) copyRun) searchRun) drainSearchRun) drainKeyRun) indexRun) emitRun
  have finalTapes : s₈ = Function.update (Function.update base (tape 0) suffix) (tape 8)
      ((outputWord tokens bits sign).reverse ++ base (tape 8)) := by
    funext k
    by_cases h8 : k = tape 8
    · subst k
      simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, tapesAt, outputWord,
        List.reverse_append, List.append_assoc, hd]
    · by_cases h0 : k = tape 0
      · subst k
        simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, tapesAt, hd]
      · by_cases h2 : k = tape 2
        · subst k
          simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, tapesAt, hd, he 2]
        · by_cases h3 : k = tape 3
          · subst k
            simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, tapesAt, hd, he 3]
          · by_cases h7 : k = tape 7
            · subst k
              simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, tapesAt, hd, he 7]
            · simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, tapesAt, h8, h0, h2, h3, h7]
  simpa only [steps, tail, finalTapes] using full

end DFVSGames.BinaryLiteralMachine

end

section

namespace DFVSGames.BinaryRenameLoop

open Turing
open DFVSGames.Foundations.Complexity
open MachineComposition

def outputBody (tokens input : List Token) : List Bool :=
  input.flatMap (fun token => BinaryLiteralMachine.outputWord tokens token.2 token.1)

@[simp] theorem outputBody_nil (tokens : List Token) : outputBody tokens [] = [] := rfl

@[simp] theorem outputBody_cons (tokens : List Token) (token : Token) (input : List Token) :
    outputBody tokens (token :: input) =
      BinaryLiteralMachine.outputWord tokens token.2 token.1 ++ outputBody tokens input := rfl

def steps (tokens : List Token) : List Token → Nat
  | [] => 1
  | token :: input => BinaryLiteralMachine.steps tokens token.2 + 2 + steps tokens input

section Program

variable {K Λ A : Type} [DecidableEq K]

theorem loopTapes_cursor (tape : Fin 11 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (cursor output variableCounter clauses : List Bool) :
    loopTapes tape base cursor output variableCounter clauses (tape 0) = cursor := by
  have hd (i j : Fin 11) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  simp [loopTapes, hd]

theorem loopTapes_variables (tape : Fin 11 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (cursor output variableCounter clauses : List Bool) :
    loopTapes tape base cursor output variableCounter clauses (tape 9) = variableCounter := by
  have hd (i j : Fin 11) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  simp [loopTapes, hd]

theorem loopTapes_clauses (tape : Fin 11 → K)
    (base : K → List Bool) (cursor output variableCounter clauses : List Bool) :
    loopTapes tape base cursor output variableCounter clauses (tape 10) = clauses := by
  simp [loopTapes]

theorem update_cursor_inline_MachineBinaryRenameLoop (tape : Fin 11 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (cursor output variableCounter clauses replacement : List Bool) :
    Function.update (loopTapes tape base cursor output variableCounter clauses) (tape 0) replacement =
      loopTapes tape base replacement output variableCounter clauses := by
  have hd (i j : Fin 11) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  funext k
  by_cases h : k = tape 0
  · subst k; simp [loopTapes, hd]
  · simp [loopTapes, h, Function.update_apply]

theorem update_output_inline_MachineBinaryRenameLoop (tape : Fin 11 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (cursor output variableCounter clauses replacement : List Bool) :
    Function.update (loopTapes tape base cursor output variableCounter clauses) (tape 8) replacement =
      loopTapes tape base cursor replacement variableCounter clauses := by
  have hd (i j : Fin 11) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  funext k
  by_cases h : k = tape 8
  · subst k; simp [loopTapes, hd]
  · simp [loopTapes, h, Function.update_apply]

theorem update_variables_inline_MachineBinaryRenameLoop (tape : Fin 11 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (cursor output variableCounter clauses replacement : List Bool) :
    Function.update (loopTapes tape base cursor output variableCounter clauses) (tape 9) replacement =
      loopTapes tape base cursor output replacement clauses := by
  have hd (i j : Fin 11) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  funext k
  by_cases h : k = tape 9
  · subst k; simp [loopTapes, hd]
  · simp [loopTapes, h, Function.update_apply]

theorem update_clauses_inline_MachineBinaryRenameLoop (tape : Fin 11 → K)
    (base : K → List Bool) (cursor output variableCounter clauses replacement : List Bool) :
    Function.update (loopTapes tape base cursor output variableCounter clauses) (tape 10) replacement =
      loopTapes tape base cursor output variableCounter replacement := by
  simp [loopTapes]

@[simp] theorem stepAux_finish (exit : Option Λ) (state : State A) (base : K → List Bool) :
    TM2.stepAux (finish exit) state base =
      ⟨exit, clean state.1.1.1.1 state.1.1.1.2, base⟩ := by
  cases exit <;> rfl

variable (tape : Fin 11 → K) (distinct : Function.Injective tape)
variable (labels : Label → Λ) (done malformed : Option Λ)
variable (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
variable (atLabels : ∀ l, program (labels l) = instruction tape labels done malformed l)
variable (base : K → List Bool) (ambient : A)

include distinct atLabels

theorem peekStep (slot : Fin 3) (head : Bool) (tail output variableCounter clauses : List Bool) :
    TM2.step program
      ⟨some (labels .entry), clean ambient slot,
        loopTapes tape base (head :: tail) output variableCounter clauses⟩ =
      some ⟨some (labels (.literal .readSign)), clean ambient slot,
        loopTapes tape base (head :: tail) output variableCounter clauses⟩ := by
  have hd (i j : Fin 11) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  change some (TM2.stepAux (program (labels .entry)) _ _) = _
  rw [atLabels .entry]
  simp [instruction, TM2.stepAux, clean, BinaryLiteralMachine.clean, BinaryNameCompare.clean,
    loopTapes_cursor tape distinct, update_cursor_inline_MachineBinaryRenameLoop tape distinct]

theorem emptyStep (slot : Fin 3) (output variableCounter clauses : List Bool) :
    TM2.step program
      ⟨some (labels .entry), clean ambient slot,
        loopTapes tape base [] output variableCounter clauses⟩ =
      some ⟨done, clean ambient slot, loopTapes tape base [] output variableCounter clauses⟩ := by
  have hd (i j : Fin 11) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  change some (TM2.stepAux (program (labels .entry)) _ _) = _
  rw [atLabels .entry]
  simp [instruction, TM2.stepAux, clean, BinaryLiteralMachine.clean, BinaryNameCompare.clean,
    loopTapes_cursor tape distinct, update_cursor_inline_MachineBinaryRenameLoop tape distinct]

theorem tallyStep (slot : Fin 3) (cursor output variableCounter clauses : List Bool) :
    TM2.step program
      ⟨some (labels .tally), clean ambient slot,
        loopTapes tape base cursor output variableCounter clauses⟩ =
      some ⟨some (labels .entry), clean ambient (nextSlot slot),
        loopTapes tape base cursor output (true :: variableCounter)
          (List.replicate (clauseIncrement slot) true ++ clauses)⟩ := by
  have hd (i j : Fin 11) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  change some (TM2.stepAux (program (labels .tally)) _ _) = _
  rw [atLabels .tally]
  fin_cases slot <;>
    simp [instruction, TM2.stepAux, clean, BinaryLiteralMachine.clean, BinaryNameCompare.clean,
      next, nextSlot, clauseIncrement, loopTapes_variables tape distinct, loopTapes_clauses,
      update_variables_inline_MachineBinaryRenameLoop tape distinct, update_clauses_inline_MachineBinaryRenameLoop]

theorem bodyTrace (tokens : List Token) (token : Token) (slot : Fin 3)
    (suffix output variableCounter clauses : List Bool)
    (canonical : BinaryNameMachine.canonical token.2 = true)
    (tokensCanonical : ∀ t ∈ tokens, BinaryNameMachine.canonical t.2 = true)
    (present : token.2 ∈ BinaryNameSearch.payloads tokens)
    (permanent : base (tape 1) = BinaryNameSearch.stream tokens)
    (empty : ∀ i : Fin 11, 2 ≤ i.val → i.val ≤ 7 → base (tape i) = []) :
    (advance (TM2.step program))^[BinaryLiteralMachine.steps tokens token.2 + 2]
      (some ⟨some (labels .entry), clean ambient slot,
        loopTapes tape base (BinaryNameSearch.tokenBits token ++ suffix) output variableCounter clauses⟩) =
      some ⟨some (labels .entry), clean ambient (nextSlot slot),
        loopTapes tape base suffix
          ((BinaryLiteralMachine.outputWord tokens token.2 token.1).reverse ++ output)
          (true :: variableCounter) (List.replicate (clauseIncrement slot) true ++ clauses)⟩ := by
  have hd (i j : Fin 11) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  let initial := loopTapes tape base (BinaryNameSearch.tokenBits token ++ suffix)
    output variableCounter clauses
  have first : (advance (TM2.step program))^[1]
      (some ⟨some (labels .entry), clean ambient slot, initial⟩) =
      some ⟨some (labels (.literal .readSign)), clean ambient slot, initial⟩ := by
    simpa only [Function.iterate_one, advance_some, initial,
      BinaryNameSearch.tokenBits, List.cons_append] using
      peekStep tape distinct labels done malformed program atLabels base ambient slot token.1
        (BinaryNameMachine.frame token.2 ++ suffix) output variableCounter clauses
  have workEmpty (i : Fin 11) (lo : 2 ≤ i.val) (hi : i.val ≤ 7) :
      initial (tape i) = [] := by
    have h0 : i ≠ 0 := by intro h; subst i; omega
    have h8 : i ≠ 8 := by intro h; subst i; omega
    have h9 : i ≠ 9 := by intro h; subst i; omega
    have h10 : i ≠ 10 := by intro h; subst i; omega
    simpa [initial, loopTapes, hd i 0 h0, hd i 8 h8, hd i 9 h9, hd i 10 h10]
      using empty i lo hi
  have literal := BinaryLiteralMachine.literalTrace (literalTapes tape)
    (literalTapes_injective tape distinct) (fun l => labels (.literal l))
    (some (labels .tally)) malformed program (fun l => atLabels (.literal l))
    initial tokens token.1 token.2 suffix canonical tokensCanonical present
    (by simp [initial, literalTapes, loopTapes, BinaryNameSearch.tokenBits, hd])
    (by simpa [initial, literalTapes, loopTapes, hd] using permanent)
    (fun i lo hi => workEmpty i.castSucc.castSucc lo hi) (ambient, slot)
  have finalTapes :
      Function.update (Function.update initial (literalTapes tape 0) suffix)
        (literalTapes tape 8)
        ((BinaryLiteralMachine.outputWord tokens token.2 token.1).reverse ++
          initial (literalTapes tape 8)) =
      loopTapes tape base suffix
        ((BinaryLiteralMachine.outputWord tokens token.2 token.1).reverse ++ output)
        variableCounter clauses := by
    have out : initial (literalTapes tape 8) = output := by
      simp [initial, literalTapes, loopTapes, hd]
    rw [out]
    change Function.update (Function.update
      (loopTapes tape base (BinaryNameSearch.tokenBits token ++ suffix) output variableCounter clauses)
      (tape 0) suffix) (tape 8) _ = _
    rw [update_cursor_inline_MachineBinaryRenameLoop tape distinct, update_output_inline_MachineBinaryRenameLoop tape distinct]
  rw [finalTapes] at literal
  have tally : (advance (TM2.step program))^[1]
      (some ⟨some (labels .tally), clean ambient slot,
        loopTapes tape base suffix
          ((BinaryLiteralMachine.outputWord tokens token.2 token.1).reverse ++ output)
          variableCounter clauses⟩) =
      some ⟨some (labels .entry), clean ambient (nextSlot slot),
        loopTapes tape base suffix
          ((BinaryLiteralMachine.outputWord tokens token.2 token.1).reverse ++ output)
          (true :: variableCounter) (List.replicate (clauseIncrement slot) true ++ clauses)⟩ := by
    simpa only [Function.iterate_one, advance_some] using
      tallyStep tape distinct labels done malformed program atLabels base ambient slot suffix
        ((BinaryLiteralMachine.outputWord tokens token.2 token.1).reverse ++ output)
        variableCounter clauses
  have full := joinTrace_inline_MachineBinaryRenameLoop (joinTrace_inline_MachineBinaryRenameLoop first literal) tally
  simpa only [show 1 + BinaryLiteralMachine.steps tokens token.2 + 1 =
    BinaryLiteralMachine.steps tokens token.2 + 2 by omega] using full

theorem loopTrace (tokens input : List Token) (slot : Fin 3)
    (output variableCounter clauses : List Bool)
    (tokensCanonical : ∀ t ∈ tokens, BinaryNameMachine.canonical t.2 = true)
    (included : ∀ t ∈ input, t ∈ tokens)
    (permanent : base (tape 1) = BinaryNameSearch.stream tokens)
    (empty : ∀ i : Fin 11, 2 ≤ i.val → i.val ≤ 7 → base (tape i) = []) :
    (advance (TM2.step program))^[steps tokens input]
      (some ⟨some (labels .entry), clean ambient slot,
        loopTapes tape base (BinaryNameSearch.stream input) output variableCounter clauses⟩) =
      some ⟨done, clean ambient (finalSlot input.length slot),
        loopTapes tape base [] ((outputBody tokens input).reverse ++ output)
          (List.replicate input.length true ++ variableCounter)
          (List.replicate (completedClauses input.length slot) true ++ clauses)⟩ := by
  induction input generalizing slot output variableCounter clauses with
  | nil =>
      simpa only [steps, Function.iterate_one, advance_some, BinaryNameSearch.stream_nil,
        List.length_nil, outputBody_nil, List.reverse_nil, List.nil_append,
        finalSlot, completedClauses, List.replicate_zero] using
        emptyStep tape distinct labels done malformed program atLabels base ambient
          slot output variableCounter clauses
  | cons token input ih =>
      have member := included token (by simp)
      have present : token.2 ∈ BinaryNameSearch.payloads tokens :=
        List.mem_map.mpr ⟨token, member, rfl⟩
      have first := bodyTrace tape distinct labels done malformed program atLabels base ambient
        tokens token slot (BinaryNameSearch.stream input) output variableCounter clauses
        (tokensCanonical token member) tokensCanonical present permanent empty
      have rest := ih (nextSlot slot)
        ((BinaryLiteralMachine.outputWord tokens token.2 token.1).reverse ++ output)
        (true :: variableCounter) (List.replicate (clauseIncrement slot) true ++ clauses)
        (fun t ht => included t (by simp [ht]))
      have full := joinTrace_inline_MachineBinaryRenameLoop first rest
      have variableEq : List.replicate input.length true ++ (true :: variableCounter) =
          List.replicate (input.length + 1) true ++ variableCounter := by
        rw [List.replicate_succ']
        simp only [List.append_assoc, List.singleton_append]
      have clauseEq : List.replicate (completedClauses input.length (nextSlot slot)) true ++
          (List.replicate (clauseIncrement slot) true ++ clauses) =
          List.replicate (completedClauses (input.length + 1) slot) true ++ clauses := by
        rw [← List.append_assoc, ← List.replicate_add]
        rfl
      simpa only [steps, BinaryNameSearch.stream_cons, List.length_cons, finalSlot,
        outputBody_cons, List.reverse_append, List.append_assoc, variableEq, clauseEq] using full

theorem triplesTrace (tokens input : List Token) (count : Nat)
    (length_eq : input.length = 3 * count) (output variableCounter clauses : List Bool)
    (tokensCanonical : ∀ t ∈ tokens, BinaryNameMachine.canonical t.2 = true)
    (included : ∀ t ∈ input, t ∈ tokens)
    (permanent : base (tape 1) = BinaryNameSearch.stream tokens)
    (empty : ∀ i : Fin 11, 2 ≤ i.val → i.val ≤ 7 → base (tape i) = []) :
    (advance (TM2.step program))^[steps tokens input]
      (some ⟨some (labels .entry), clean ambient 0,
        loopTapes tape base (BinaryNameSearch.stream input) output variableCounter clauses⟩) =
      some ⟨done, clean ambient 0,
        loopTapes tape base [] ((outputBody tokens input).reverse ++ output)
          (List.replicate (3 * count) true ++ variableCounter)
          (List.replicate count true ++ clauses)⟩ := by
  have h := loopTrace tape distinct labels done malformed program atLabels base ambient
    tokens input 0 output variableCounter clauses tokensCanonical included permanent empty
  simpa only [length_eq, finalSlot_triples, completedClauses_triples] using h

end Program

end DFVSGames.BinaryRenameLoop

end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineBinaryTokenMachine
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

namespace DFVSGames.BinaryTokenMachine

open Turing
open DFVSGames.Foundations.Complexity
open MachineComposition
open DFVSGames.Reduction.MachineTransfer
open BinaryFormula BinaryEncoding

theorem restoreTrace (input unread output : List Bool) (register : Option Bool) :
    (advance machine.step)^[input.length + 1]
      (some (cfg (some .restore) unread input.reverse output register)) =
      some (cfg (some .accept) unread [] (input ++ output)) := by
  have h := transferAt_fromTapes (Γ := Alphabet) (σ := Unit) 1 2 (by decide)
    id false .restore (some .accept) program rfl
    (tapes unread input.reverse output) () register
  have ht : tapesAt 1 2 (tapes unread input.reverse output) [] (input ++ output) =
      tapes unread [] (input ++ output) := by
    funext k
    fin_cases k <;> simp [tapesAt, tapes]
  change (nextAt 2 program)^[input.length + 1]
    (some (cfg (some .restore) unread input.reverse output register)) = _
  simp only [tapes_one, tapes_two, List.length_reverse, List.reverse_reverse,
    List.map_id_fun, id_eq, ht] at h
  exact h

theorem acceptTrace (formula : Formula) :
    (advance machine.step)^[13 * formula.clauses.length +
        3 * namesBitSize formula.clauses + 2]
      (some (initList machine (formulaBits formula))) =
      some (cfg (some .accept) [] [] (tokens formula.clauses)) := by
  have first := stripTrace formula.clauses [] [] [] none
  simp only [List.append_nil] at first
  have second := restoreTrace (tokens formula.clauses) [] [] none
  simp only [List.append_nil] at second
  have full := joinTrace_inline_MachineBinaryTokenMachine first second
  have htime : (7 * formula.clauses.length + namesBitSize formula.clauses + 1) +
      ((tokens formula.clauses).length + 1) =
      13 * formula.clauses.length + 3 * namesBitSize formula.clauses + 2 := by
    rw [tokens_length]
    omega
  rw [htime] at full
  simpa only [initList_eq, BinaryEncoding.formulaBits] using full

theorem tokenTrace (formula : Formula) :
    (advance machine.step)^[13 * formula.clauses.length +
        3 * namesBitSize formula.clauses + 3]
      (some (initList machine (formulaBits formula))) =
      some (haltList machine (tokens formula.clauses)) := by
  rw [show 13 * formula.clauses.length + 3 * namesBitSize formula.clauses + 3 =
    (13 * formula.clauses.length + 3 * namesBitSize formula.clauses + 2) + 1 by omega,
    Function.iterate_succ_apply', acceptTrace, advance_some, haltStep, haltList_eq]

def outputsInTime (formula : Formula) :
    TM2OutputsInTime machine (formulaBits formula) (some (tokens formula.clauses))
      (3 * (formulaBits formula).length + 3) where
  steps := 13 * formula.clauses.length + 3 * namesBitSize formula.clauses + 3
  evals_in_steps := tokenTrace formula
  steps_le_m := tokenSteps_le formula

noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime BinaryEncoding.formulaBits (id : List Bool → List Bool)
      (fun formula => tokens formula.clauses) where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.C 3 * Polynomial.X + Polynomial.C 3
  outputsFun formula := by
    change TM2OutputsInTime machine ((formulaBits formula).map id)
      (some ((tokens formula.clauses).map id))
      ((Polynomial.C 3 * Polynomial.X + Polynomial.C 3 : Polynomial Nat).eval
        (formulaBits formula).length)
    simpa only [List.map_id_fun, id_eq, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X] using outputsInTime formula

end DFVSGames.BinaryTokenMachine

end

section

namespace DFVSGames.BinaryRenameWords

open BinaryFormula DFVSGames.Foundations

def outputLiteral (names : List Nat) (literal : Literal) : List Bool :=
  Complexity.encodeWord (names.idxOf literal.name) ++
    Complexity.encodeWord (if literal.positive then 1 else 0)

def body (F : Formula) : List Bool :=
  (literals F.clauses).flatMap (outputLiteral (sourceNames F))

theorem encoded_clause (F : Formula) (c : Clause) (mem : c ∈ F.clauses) :
    Complexity.encodeWords (Complexity.clauseWords (BinaryOccurrenceRename.clause F c mem)) =
      (clauseLiterals c).flatMap (outputLiteral (sourceNames F)) := by
  simp [Complexity.clauseWords, Complexity.literalWords, Complexity.encodeWords,
    BinaryOccurrenceRename.clause, BinaryOccurrenceRename.literal,
    BinaryOccurrenceRename.nameIndex, clauseLiterals, outputLiteral, List.append_assoc]
  rfl

end DFVSGames.BinaryRenameWords

end

section

namespace DFVSGames.BinaryHeaderMachine

open Turing
open DFVSGames.Foundations.Complexity
open MachineComposition
open DFVSGames.Reduction.MachineTransfer

section Placement

variable {K Λ A : Type} [DecidableEq K]

variable (variableTape clauses destination : K)
variable (vc : variableTape ≠ clauses) (vd : variableTape ≠ destination) (cd : clauses ≠ destination)
variable (clauseStart clauseLoop variableStart variableLoop : Λ) (exit : Option Λ)
variable (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
variable (atClauseStart : program clauseStart = delimiter destination clauseLoop)
variable (atClauseLoop : program clauseLoop =
  loopAt clauses destination id false clauseLoop (some variableStart))
variable (atVariableStart : program variableStart = delimiter destination variableLoop)
variable (atVariableLoop : program variableLoop =
  loopAt variableTape destination id false variableLoop exit)
variable (base : K → List Bool) (ambient : A)

include cd atClauseLoop in
theorem clauseCounterTrace (m : Nat) (variableCounter output : List Bool)
    (register : Option Bool) :
    (advance (TM2.step program))^[m + 1]
      (some ⟨some clauseLoop, (ambient, register),
        tapes variableTape clauses destination base variableCounter (List.replicate m true) output⟩) =
      some ⟨some variableStart, (ambient, none),
        tapes variableTape clauses destination base variableCounter [] (List.replicate m true ++ output)⟩ := by
  have h := transferAt_fromTapes (Γ := Alphabet) clauses destination cd id false
    clauseLoop (some variableStart) program atClauseLoop
    (tapes variableTape clauses destination base variableCounter (List.replicate m true) output)
    ambient register
  change (nextAt destination program)^[m + 1]
    (some ⟨some clauseLoop, (ambient, register),
      tapes variableTape clauses destination base variableCounter (List.replicate m true) output⟩) = _
  simpa only [tapes_clauses variableTape clauses destination cd, tapes_destination,
    List.length_replicate, List.reverse_replicate, List.map_id_fun, id_eq,
    tapesAt, update_clauses_inline_MachineBinaryHeaderMachine variableTape clauses destination cd, update_destination_inline_MachineBinaryHeaderMachine,
    nextAt, advance] using h

include vc vd atVariableLoop in
theorem variableCounterTrace (n : Nat) (clauseCounter output : List Bool)
    (register : Option Bool) :
    (advance (TM2.step program))^[n + 1]
      (some ⟨some variableLoop, (ambient, register),
        tapes variableTape clauses destination base (List.replicate n true) clauseCounter output⟩) =
      some ⟨exit, (ambient, none),
        tapes variableTape clauses destination base [] clauseCounter (List.replicate n true ++ output)⟩ := by
  have h := transferAt_fromTapes (Γ := Alphabet) variableTape destination vd id false
    variableLoop exit program atVariableLoop
    (tapes variableTape clauses destination base (List.replicate n true) clauseCounter output)
    ambient register
  change (nextAt destination program)^[n + 1]
    (some ⟨some variableLoop, (ambient, register),
      tapes variableTape clauses destination base (List.replicate n true) clauseCounter output⟩) = _
  simpa only [tapes_variables variableTape clauses destination vc vd, tapes_destination,
    List.length_replicate, List.reverse_replicate, List.map_id_fun, id_eq,
    tapesAt, update_variables_inline_MachineBinaryHeaderMachine variableTape clauses destination vc vd, update_destination_inline_MachineBinaryHeaderMachine,
    nextAt, advance] using h

include vc vd cd atClauseStart atClauseLoop atVariableStart atVariableLoop

theorem headerTrace (n m : Nat) (body : List Bool) (register : Option Bool) :
    (advance (TM2.step program))^[n + m + 4]
      (some ⟨some clauseStart, (ambient, register),
        tapes variableTape clauses destination base
          (List.replicate n true) (List.replicate m true) body⟩) =
      some ⟨exit, (ambient, none),
        tapes variableTape clauses destination base [] [] (encodeWord n ++ encodeWord m ++ body)⟩ := by
  have first := clauseDelimiterStep variableTape clauses destination clauseStart clauseLoop program
    atClauseStart base ambient (List.replicate n true) (List.replicate m true) body register
  change (advance (TM2.step program))^[1]
    (some ⟨some clauseStart, (ambient, register),
      tapes variableTape clauses destination base (List.replicate n true) (List.replicate m true) body⟩) = _ at first
  have second := clauseCounterTrace variableTape clauses destination cd clauseLoop variableStart program
    atClauseLoop base ambient m (List.replicate n true) (false :: body) none
  have third := variableDelimiterStep variableTape clauses destination variableStart variableLoop program
    atVariableStart base ambient (List.replicate n true) []
    (List.replicate m true ++ false :: body) none
  change (advance (TM2.step program))^[1]
    (some ⟨some variableStart, (ambient, none),
      tapes variableTape clauses destination base (List.replicate n true) []
        (List.replicate m true ++ false :: body)⟩) = _ at third
  have fourth := variableCounterTrace variableTape clauses destination vc vd variableLoop exit program
    atVariableLoop base ambient n [] (false :: (List.replicate m true ++ false :: body)) none
  have full := joinTrace_inline_MachineBinaryHeaderMachine (joinTrace_inline_MachineBinaryHeaderMachine (joinTrace_inline_MachineBinaryHeaderMachine first second) third) fourth
  have htime : ((1 + (m + 1)) + 1) + (n + 1) = n + m + 4 := by omega
  rw [htime] at full
  simpa only [encodeWord, List.append_assoc, List.singleton_append,
    List.cons_append, List.nil_append] using full

end Placement

end DFVSGames.BinaryHeaderMachine

end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineBinaryRenameMachine
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

namespace DFVSGames.BinaryRenameMachine

open Turing DFVSGames.Foundations
open Complexity Complexity.MachineComposition
open DFVSGames.Reduction.MachineTransfer

abbrev State := BinaryRenameLoop.State Unit

def program : Label → TM2.Stmt Alphabet Label State
  | .copyOut => loopAt 1 6 id false .copyOut (some .copyBack)
  | .copyBack => MachineCopy.forkLoop 6 1 0 false .copyBack (some (.loop .entry))
  | .loop label => BinaryRenameLoop.instruction loopTapes Label.loop
      (some .restore) (some .reject) label
  | .restore => loopAt 8 11 id false .restore (some .clauseStart)
  | .clauseStart => BinaryHeaderMachine.delimiter 11 .clauseLoop
  | .clauseLoop => loopAt 10 11 id false .clauseLoop (some .variableStart)
  | .variableStart => BinaryHeaderMachine.delimiter 11 .variableLoop
  | .variableLoop => loopAt 9 11 id false .variableLoop (some .cleanup)
  | .cleanup => MachineDrain.drain 1 .cleanup none
  | .reject => .halt

abbrev machine : FinTM2 where
  K := Tape
  k₀ := 1
  k₁ := 11
  Γ := Alphabet
  Λ := Label
  main := .copyOut
  σ := State
  initialState := BinaryRenameLoop.clean () 0
  m := program

def cfg (label : Option Label)
    (permanent cursor reversed variableCounter clauseCounter output : List Bool) : machine.Cfg :=
  ⟨label, BinaryRenameLoop.clean () 0,
    tapes permanent cursor reversed variableCounter clauseCounter output⟩

theorem initList_eq (input : List Bool) :
    initList machine input = cfg (some .copyOut) input [] [] [] [] [] := by
  unfold initList cfg
  congr 1
  funext k
  fin_cases k <;> simp [tapes, machine]

theorem haltList_eq (output : List Bool) :
    haltList machine output = cfg none [] [] [] [] [] output := by
  unfold haltList cfg
  congr 1
  funext k
  fin_cases k <;> simp [tapes, machine]

theorem copyTrace (input : List Bool) :
    (advance machine.step)^[2 * (input.length + 1)]
      (some (cfg (some .copyOut) input [] [] [] [] [])) =
      some (cfg (some (.loop .entry)) input input [] [] [] []) := by
  have updated : Function.update (tapes input [] [] [] [] []) 0 input =
      tapes input input [] [] [] [] := by
    funext k
    fin_cases k <;> simp [tapes]
  have h := MachineCopy.copyTrace (1 : Tape) 0 6 (by decide) (by decide) (by decide)
    false .copyOut .copyBack (some (.loop .entry)) program rfl rfl
    (tapes input [] [] [] [] []) (by simp [tapes])
    (BinaryRenameLoop.clean () 0).1 none
  have first : tapes input [] [] [] [] [] 1 = input := rfl
  have second : tapes input [] [] [] [] [] 0 = [] := rfl
  rw [first, second, List.append_nil, updated] at h
  exact h

theorem restoreTrace (input body variableCounter clauseCounter : List Bool) :
    (advance machine.step)^[body.length + 1]
      (some (cfg (some .restore) input [] body.reverse variableCounter clauseCounter [])) =
      some (cfg (some .clauseStart) input [] [] variableCounter clauseCounter body) := by
  change (nextAt (11 : Tape) program)^[body.length + 1]
    (some (cfg (some .restore) input [] body.reverse variableCounter clauseCounter [])) = _
  have updated : tapesAt (8 : Tape) 11
      (tapes input [] body.reverse variableCounter clauseCounter []) [] body =
      tapes input [] [] variableCounter clauseCounter body := by
    funext k
    fin_cases k <;> simp [tapesAt, tapes]
  have h := transferAt_fromTapes (Γ := Alphabet) (8 : Tape) 11 (by decide) id false
    .restore (some .clauseStart) program rfl
    (tapes input [] body.reverse variableCounter clauseCounter [])
    (BinaryRenameLoop.clean () 0).1 none
  have source : tapes input [] body.reverse variableCounter clauseCounter [] 8 = body.reverse := rfl
  have output : tapes input [] body.reverse variableCounter clauseCounter [] 11 = [] := rfl
  rw [source, output, List.length_reverse, List.reverse_reverse, List.map_id_fun,
    List.append_nil, id_eq, updated] at h
  exact h

theorem headerTrace (input body : List Bool) (n m : Nat) :
    (advance machine.step)^[n + m + 4]
      (some (cfg (some .clauseStart) input [] []
        (List.replicate n true) (List.replicate m true) body)) =
      some (cfg (some .cleanup) input [] [] [] []
        (encodeWord n ++ encodeWord m ++ body)) := by
  change (advance (TM2.step program))^[n + m + 4]
    (some ⟨some .clauseStart, ((BinaryRenameLoop.clean () 0).1, none),
      tapes input [] [] (List.replicate n true) (List.replicate m true) body⟩) =
    some ⟨some .cleanup, ((BinaryRenameLoop.clean () 0).1, none),
      tapes input [] [] [] [] (encodeWord n ++ encodeWord m ++ body)⟩
  have updated (variableWord clauses output : List Bool) :
      BinaryHeaderMachine.tapes (9 : Tape) 10 11 (tapes input [] [] [] [] [])
        variableWord clauses output = tapes input [] [] variableWord clauses output := by
    funext k
    fin_cases k <;> simp [BinaryHeaderMachine.tapes, tapes]
  have h := BinaryHeaderMachine.headerTrace (9 : Tape) 10 11
    (by decide) (by decide) (by decide)
    .clauseStart .clauseLoop .variableStart .variableLoop (some .cleanup) program
    rfl rfl rfl rfl (tapes input [] [] [] [] [])
    (BinaryRenameLoop.clean () 0).1 n m body none
  simp only [updated] at h
  exact h

theorem cleanupTrace (input output : List Bool) :
    (advance machine.step)^[input.length + 1]
      (some (cfg (some .cleanup) input [] [] [] [] output)) =
      some (cfg none [] [] [] [] [] output) := by
  change (advance (TM2.step program))^[input.length + 1]
    (some ⟨some .cleanup, ((BinaryRenameLoop.clean () 0).1, none),
      tapes input [] [] [] [] output⟩) =
    some ⟨none, ((BinaryRenameLoop.clean () 0).1, none), tapes [] [] [] [] [] output⟩
  have updated (word : List Bool) :
      Function.update (tapes [] [] [] [] [] output) 1 word =
        tapes word [] [] [] [] output := by
    funext k
    fin_cases k <;> simp [tapes]
  have h := MachineDrain.drainTrace (1 : Tape) .cleanup none program rfl
    (tapes [] [] [] [] [] output) input (BinaryRenameLoop.clean () 0).1 none
  simp only [updated] at h
  exact h

theorem outputBody_eq (formula : BinaryFormula.Formula) :
    BinaryRenameLoop.outputBody (BinaryRenameWords.tokens formula.clauses)
      (BinaryRenameWords.tokens formula.clauses) = BinaryRenameWords.body formula := by
  change ((BinaryRenameWords.literals formula.clauses).map BinaryRenameWords.token).flatMap
    (fun t => BinaryLiteralMachine.outputWord (BinaryRenameWords.tokens formula.clauses)
      t.2 t.1) = (BinaryRenameWords.literals formula.clauses).flatMap
        (BinaryRenameWords.outputLiteral (BinaryFormula.sourceNames formula))
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro literal _
  simp only [BinaryRenameWords.token, BinaryLiteralMachine.outputWord,
    BinaryLiteralMachine.index, BinaryLiteralMachine.signWord,
    BinaryRenameWords.payload_index, BinaryRenameWords.outputLiteral]
  rfl

theorem loopTrace (formula : BinaryFormula.Formula) :
    (advance machine.step)^[BinaryRenameLoop.steps (BinaryRenameWords.tokens formula.clauses)
        (BinaryRenameWords.tokens formula.clauses)]
      (some (cfg (some (.loop .entry)) (BinaryTokenMachine.tokens formula.clauses)
        (BinaryTokenMachine.tokens formula.clauses) [] [] [] [])) =
      some (cfg (some .restore) (BinaryTokenMachine.tokens formula.clauses) []
        (BinaryRenameWords.body formula).reverse (List.replicate (3 * formula.clauses.length) true)
        (List.replicate formula.clauses.length true) []) := by
  change (advance (TM2.step program))^[BinaryRenameLoop.steps
      (BinaryRenameWords.tokens formula.clauses) (BinaryRenameWords.tokens formula.clauses)]
    (some ⟨some (.loop .entry), BinaryRenameLoop.clean () 0,
      tapes (BinaryTokenMachine.tokens formula.clauses) (BinaryTokenMachine.tokens formula.clauses)
        [] [] [] []⟩) =
    some ⟨some .restore, BinaryRenameLoop.clean () 0,
      tapes (BinaryTokenMachine.tokens formula.clauses) [] (BinaryRenameWords.body formula).reverse
        (List.replicate (3 * formula.clauses.length) true)
        (List.replicate formula.clauses.length true) []⟩
  let input := BinaryTokenMachine.tokens formula.clauses
  have updated (cursor output variableWord clauseWord : List Bool) :
      BinaryRenameLoop.loopTapes loopTapes (tapes input [] [] [] [] [])
        cursor output variableWord clauseWord =
      tapes input cursor output variableWord clauseWord [] := by
    funext k
    fin_cases k <;> simp [BinaryRenameLoop.loopTapes, loopTapes, tapes]
  have scratch (i : Fin 11) (lo : 2 ≤ i.val) (hi : i.val ≤ 7) :
      tapes input [] [] [] [] [] (loopTapes i) = [] := by
    have n0 : loopTapes i ≠ 0 := by intro h; have := congrArg Fin.val h; simp [loopTapes] at this; omega
    have n1 : loopTapes i ≠ 1 := by intro h; have := congrArg Fin.val h; simp [loopTapes] at this; omega
    have n8 : loopTapes i ≠ 8 := by intro h; have := congrArg Fin.val h; simp [loopTapes] at this; omega
    have n9 : loopTapes i ≠ 9 := by intro h; have := congrArg Fin.val h; simp [loopTapes] at this; omega
    have n10 : loopTapes i ≠ 10 := by intro h; have := congrArg Fin.val h; simp [loopTapes] at this; omega
    have n11 : loopTapes i ≠ 11 := by intro h; have := congrArg Fin.val h; simp [loopTapes] at this; omega
    simp [tapes, n0, n1, n8, n9, n10, n11]
  have run := BinaryRenameLoop.triplesTrace loopTapes loopTapes_injective Label.loop
    (some .restore) (some .reject) program (fun _ => rfl)
    (tapes input [] [] [] [] []) ()
    (BinaryRenameWords.tokens formula.clauses) (BinaryRenameWords.tokens formula.clauses)
    formula.clauses.length (BinaryRenameWords.tokens_length formula.clauses) [] [] []
    (BinaryRenameWords.tokens_canonical formula.clauses) (fun _ h => h)
    (by change input = _; rw [BinaryRenameWords.tokens_stream]) scratch
  simp only [updated, BinaryRenameWords.tokens_stream, outputBody_eq, List.append_nil, input] at run
  exact run

def steps (formula : BinaryFormula.Formula) : Nat :=
  2 * ((BinaryTokenMachine.tokens formula.clauses).length + 1) +
    BinaryRenameLoop.steps (BinaryRenameWords.tokens formula.clauses)
      (BinaryRenameWords.tokens formula.clauses) +
    ((BinaryRenameWords.body formula).length + 1) + (4 * formula.clauses.length + 4) +
    ((BinaryTokenMachine.tokens formula.clauses).length + 1)

noncomputable def preprocessing :
    TM2ComputableInPolyTime BinaryEncoding.formulaBits
      (fun formula : BinaryFormula.Formula => BinaryTokenMachine.tokens formula.clauses)
      (id : BinaryFormula.Formula → BinaryFormula.Formula) where
  tm := BinaryTokenMachine.computableInPolyTime.tm
  inputAlphabet := BinaryTokenMachine.computableInPolyTime.inputAlphabet
  outputAlphabet := BinaryTokenMachine.computableInPolyTime.outputAlphabet
  time := BinaryTokenMachine.computableInPolyTime.time
  outputsFun := BinaryTokenMachine.computableInPolyTime.outputsFun

theorem machine_finiteAlphabet (k : machine.K) : Finite (machine.Γ k) := by
  change Finite Bool
  infer_instance

end DFVSGames.BinaryRenameMachine

end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineSingleOrbitCodec
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

namespace DFVSGames.Reduction.SourceEquationLookup

open Turing
open DFVSGames.Foundations.Complexity
open DFVSGames.Foundations.Hastad
open MachineComposition SourceMachine SourceEncoding
open SourceClauseLookup (discardFieldsTrace)

variable {σ : Type}

def program : Label → TM2.Stmt (fun _ : Tape => Bool) Label (σ × Option Bool)
  | .copyOut => Reduction.MachineTransfer.loopAt .source .scratch id false
      .copyOut (some .copyBack)
  | .copyBack => MachineCopy.forkLoop .scratch .source .work false
      .copyBack (some .headerFirst)
  | .headerFirst => MachineLookup.discard .work .headerFirst .headerSecond
  | .headerSecond => MachineLookup.discard .work .headerSecond .guard
  | .guard => MachineUnaryCounter.guard .index (skipLabel 0) (readStart 0)
  | .skip slot => MachineLookup.discard .work (.skip slot) (skipLabel (slot.val + 1))
  | .read slot =>
      if slot.1.val < 4 then
        if slot.2 then
          fieldLoop .work (fieldDestination slot.1.val) (.read (slot.1, true))
            (some (readStart (slot.1.val + 1)))
        else fieldStart (fieldDestination slot.1.val) (.read (slot.1, true))
      else SourceFieldArray.finish .work none

end DFVSGames.Reduction.SourceEquationLookup
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineTuple
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

namespace DFVSGames.Reduction.MachineSourceTuple

open Turing DFVSGames.Foundations.Complexity
open SourceEncoding
open MachineComposition

variable {width : Nat} {Extra σ : Type}

variable [DecidableEq Extra]

def placedStatement (j : Fin width) :
    TM2.Stmt (fun _ : SourceEquationLookup.Tape => Bool)
      SourceEquationLookup.Label ((σ × Unit) × Option Bool) →
    TM2.Stmt (fun _ : Tape width Extra => Bool) (Label width) ((σ × Unit) × Option Bool)
  | .push k f next => .push (place j k) f (placedStatement j next)
  | .peek k f next => .peek (place j k) f (placedStatement j next)
  | .pop k f next => .pop (place j k) f (placedStatement j next)
  | .load f next => .load f (placedStatement j next)
  | .branch f yes no => .branch f (placedStatement j yes) (placedStatement j no)
  | .goto f => .goto (fun state => .lookup j (f state))
  | .halt => .goto (fun _ => .clearWork j)

def program : Label width → TM2.Stmt (fun _ : Tape width Extra => Bool)
    (Label width) ((σ × Unit) × Option Bool)
  | .copyOut j => Reduction.MachineTransfer.loopAt (.savedIndex j) .copyScratch id false
      (.copyOut j) (some (.copyBack j))
  | .copyBack j => MachineCopy.forkLoop .copyScratch (.savedIndex j) .index false
      (.copyBack j) (some (.lookup j .copyOut))
  | .lookup j l => placedStatement j (SourceEquationLookup.program l)
  | .clearWork j => MachineDrain.drain .work (.clearWork j) (some (.clearIndex j))
  | .clearIndex j => MachineDrain.drain .index (.clearIndex j) (some (nextLabel j))
  | .done => .halt

end DFVSGames.Reduction.MachineSourceTuple
end

section

namespace DFVSGames.Reduction.CloneMachineModel

open Turing
open DFVSGames.Foundations.Complexity
open DFVSGames.Foundations.Hastad

def affineEmit (scale offset : Nat) : Bool → List Bool
  | true => List.replicate scale true
  | false => encodeWord offset

end DFVSGames.Reduction.CloneMachineModel
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineAddressHeaders
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

namespace DFVSGames.Reduction.MachineAddressHeaders

open Turing
open DFVSGames.Foundations.Complexity
open DFVSGames.Foundations.Hastad
open MachineComposition

noncomputable section

namespace Arithmetic

variable {k s d noiseCount : Nat} {K Λ σ : Type}

inductive Label (k s d noiseCount : Nat)
  | copyNOut | copyNBack | copyMOut | copyMBack | addM | seedBase
  | evaluate (kind : Kind) (localLabel : SourceHeaderCounts.Eval.Label (polynomial k s d noiseCount kind))
  | doubleScan | doubleEmit (symbol : Bool) | doubleRestore | alphabet | edgeTransfer
  deriving DecidableEq, Fintype

def evalStart (kind : Kind) : Label k s d noiseCount :=
  .evaluate kind (SourceHeaderCounts.Eval.start (polynomial k s d noiseCount kind))

def afterEval : Kind → Label k s d noiseCount
  | .capacity => .doubleScan | .edges => .edgeTransfer

variable [DecidableEq K]

def statement (slots : Layout k s d noiseCount ↪ K) (labels : Label k s d noiseCount → Λ)
    (exit : Option Λ) :
    Label k s d noiseCount → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ)
  | .copyNOut => MachineTransfer.loopAt (control slots .variableCount) (control slots .scratch)
      id false (labels .copyNOut) (some (labels .copyNBack))
  | .copyNBack => MachineCopy.forkLoop (control slots .scratch) (control slots .variableCount)
      (control slots .baseValue) false (labels .copyNBack) (some (labels .copyMOut))
  | .copyMOut => MachineTransfer.loopAt (control slots .occurrenceCount) (control slots .scratch)
      id false (labels .copyMOut) (some (labels .copyMBack))
  | .copyMBack => MachineCopy.forkLoop (control slots .scratch) (control slots .occurrenceCount)
      (control slots .temporary) false (labels .copyMBack) (some (labels .addM))
  | .addM => MachineUnaryAddAt.loop (control slots .temporary) (control slots .baseValue)
      (labels .addM) (some (labels .seedBase))
  | .seedBase => .pop (control slots .temporary) (fun state _ => state)
      (MachineSubstitution.pushWord (control slots .baseValue) (List.replicate (baseConstant s d) true)
        (.goto fun _ => labels (evalStart .capacity)))
  | .evaluate kind localLabel => SourceHeaderCounts.Eval.statement
      (polynomial k s d noiseCount kind) (evalSlots slots kind)
      (fun label => labels (.evaluate kind label)) (some (labels (afterEval kind))) localLabel
  | .doubleScan => MachineTransducerCopy.scanLoop (control slots .capacity) (control slots .scratch)
      () (fun _ symbol => labels (.doubleEmit symbol)) (labels .doubleRestore)
  | .doubleEmit symbol => MachineTransducerCopy.emitter (control slots .reversed)
      (fun q _ => q) (fun _ : Unit => CloneMachineModel.affineEmit 2 0)
      (labels .doubleScan) () symbol
  | .doubleRestore => MachineTransfer.loopAt (control slots .scratch) (control slots .capacity)
      id false (labels .doubleRestore) (some (labels .alphabet))
  | .alphabet => MachineSubstitution.pushWord (control slots .reversed) (encodeWord (2 ^ s))
      (.goto fun _ => labels (evalStart .edges))
  | .edgeTransfer => MachineTransfer.loopAt (control slots .temporary) (control slots .reversed)
      id false (labels .edgeTransfer) exit

end Arithmetic

variable {k s d noiseCount : Nat} {K Λ σ : Type} [DecidableEq K]

abbrev Label (k s d noiseCount : Nat) := Prefix.Label ⊕ Arithmetic.Label k s d noiseCount

def statement (slots : Layout k s d noiseCount ↪ K) (labels : Label k s d noiseCount → Λ)
    (exit : Option Λ) : Label k s d noiseCount →
      TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ)
  | .inl label => Prefix.statement (prefixSlots slots) (fun l => labels (.inl l))
      (some (labels (.inr .copyNOut))) label
  | .inr label => Arithmetic.statement (arithmeticSlots slots) (fun l => labels (.inr l)) exit label

theorem resultTapes_other (slots : Layout k s d noiseCount ↪ K)
    (base : K → List Bool) (n m : Nat) (tape : K)
    (hread : tape ≠ slots (.inl 1))
    (hn : tape ≠ Arithmetic.control (arithmeticSlots slots) .variableCount)
    (hm : tape ≠ Arithmetic.control (arithmeticSlots slots) .occurrenceCount)
    (hB : tape ≠ Arithmetic.control (arithmeticSlots slots) .baseValue)
    (hcap : tape ≠ Arithmetic.control (arithmeticSlots slots) .capacity)
    (hout : tape ≠ Arithmetic.control (arithmeticSlots slots) .reversed) :
    resultTapes slots base n m tape = base tape := by
  simp only [resultTapes, Arithmetic.resultTapes, Function.update_of_ne hout,
    Function.update_of_ne hcap, Function.update_of_ne hB]
  apply Prefix.resultTapes_other <;> assumption

end

end DFVSGames.Reduction.MachineAddressHeaders
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineTemplateAddress
attribute [-instance] _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
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

namespace DFVSGames.Reduction.MachineTemplateAddress

open Turing
open DFVSGames.Foundations.Complexity
open DFVSGames.Foundations.Hastad

variable {q width : Nat} {K Λ σ : Type} [DecidableEq K]

def instruction (tokens : List (MachineFieldTemplate.Token q)) (slots : Tape q width ↪ K)
    (place : Label tokens.length width (chosen slots) → Λ) (exit : Option Λ) :
    Label tokens.length width (chosen slots) → TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .inl l => MachineFieldTemplate.instruction tokens (fun j => slots (.field j))
      (slots .copyScratch) (slots .reversed) (fun l => place (emitLabel l))
      (some (place reverseLabel)) l
  | .inr (.inl _) => MachineTransfer.loopAt (slots .reversed) (slots .forward) id false
      (place reverseLabel) (some (place (parseLabel (SourceFieldArray.startLabel width 0))))
  | .inr (.inr (.inl l)) =>
      if h : l.1.val < width then
        if l.2 then
          SourceMachine.fieldLoop (slots .forward) (slots (.digit ⟨l.1.val, h⟩))
            (place (parseLabel (l.1, true)))
            (some (place (parseLabel (SourceFieldArray.startLabel width (l.1.val + 1)))))
        else SourceMachine.fieldStart (slots (.digit ⟨l.1.val, h⟩))
          (place (parseLabel (l.1, true)))
      else SourceFieldArray.finish (slots .forward) (some (place (hornerLabel .start)))
  | .inr (.inr (.inr (.inl l))) => MachineHorner.statement (hornerSlots slots)
      (fun l => place (hornerLabel l))
      (MachineDrainMany.entry (chosen slots) (fun l => place (cleanupLabel l)) exit) l
  | .inr (.inr (.inr (.inr l))) => MachineDrainMany.instruction (chosen slots)
      (fun l => place (cleanupLabel l)) exit l

end DFVSGames.Reduction.MachineTemplateAddress
end

section

namespace DFVSGames.Reduction.MachineAddressEdge

open Turing
open DFVSGames.Foundations.Complexity
open MachineSubstitution (pushWord stepAux_pushWord)

variable {q width : Nat} {K Λ σ : Type} [DecidableEq K]

def instruction (left right : List (MachineFieldTemplate.Token q))
    (permutation : List Bool) (slots : Tape q width ↪ K)
    (place : Label left.length right.length width (MachineTemplateAddress.chosen (addressSlots slots)) → Λ)
    (exit : Option Λ) :
    Label left.length right.length width (MachineTemplateAddress.chosen (addressSlots slots)) →
      TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .inl label => MachineTemplateAddress.instruction left (addressSlots slots) (fun l => place (leftLabel l))
      (some (place (plumbing 0))) label
  | .inr (.inl label) => MachineTemplateAddress.instruction right (addressSlots slots)
      (fun l => place (rightLabel l)) (some (place (plumbing 1))) label
  | .inr (.inr 0) => MachineTransfer.loopAt (workTape slots) (outputTape slots) id false
      (place (plumbing 0))
      (some (place (rightLabel (MachineTemplateAddress.emitLabel (MachineFieldTemplate.startAt right.length 0)))))
  | .inr (.inr 1) => MachineTransfer.loopAt (capacityTape slots) (scratchTape slots) id false
      (place (plumbing 1)) (some (place (plumbing 2)))
  | .inr (.inr 2) => MachineCopy.forkLoop (scratchTape slots) (capacityTape slots)
      (tempTape slots) false (place (plumbing 2)) (some (place (plumbing 3)))
  | .inr (.inr 3) => MachineUnaryAddAt.loop (tempTape slots) (workTape slots)
      (place (plumbing 3)) (some (place (plumbing 4)))
  | .inr (.inr 4) => MachineDrain.drain (tempTape slots)
      (place (plumbing 4)) (some (place (plumbing 5)))
  | .inr (.inr 5) => MachineTransfer.loopAt (workTape slots) (outputTape slots) id false
      (place (plumbing 5)) (some (place (plumbing 6)))
  | .inr (.inr 6) => .load MachineFieldTemplate.reset
      (pushWord (outputTape slots) permutation (MachineFieldTemplate.jump exit))

end DFVSGames.Reduction.MachineAddressEdge
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_CanonicalWordTemplate
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

namespace DFVSGames.Reduction.AddressMachineSpace

open DFVSGames.Foundations.Complexity

variable (k s d noiseCount : Nat)

def rhsField (position : Fin k) : Tape k s d noiseCount := .field position 3

theorem current_ne_remaining (j l : Fin k) :
    current k s d noiseCount j ≠ remaining k s d noiseCount l := by simp [current, remaining]
theorem current_ne_finalOutput (j : Fin k) :
    current k s d noiseCount j ≠ finalOutput k s d noiseCount := by simp [current, finalOutput]
theorem remaining_ne_finalOutput (j : Fin k) :
    remaining k s d noiseCount j ≠ finalOutput k s d noiseCount := by simp [remaining, finalOutput]

theorem headerTape_ne_finalOutput (c : MachineAddressHeaders.Arithmetic.Control) :
    headerTape k s d noiseCount c ≠ finalOutput k s d noiseCount := by
  simp [headerTape, finalOutput]

theorem headerTape_ne_current (c : MachineAddressHeaders.Arithmetic.Control) (j : Fin k) :
    headerTape k s d noiseCount c ≠ current k s d noiseCount j := by
  simp [headerTape, current]

theorem headerTape_ne_remaining (c : MachineAddressHeaders.Arithmetic.Control) (j : Fin k) :
    headerTape k s d noiseCount c ≠ remaining k s d noiseCount j := by
  simp [headerTape, remaining]

end DFVSGames.Reduction.AddressMachineSpace
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_AddressTupleLoaded
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

namespace DFVSGames.Integration.AddressTupleCleanup

open Turing DFVSGames.Reduction DFVSGames.Foundations.Complexity

variable (k s d noiseCount : Nat)

variable {Λ : Type}

abbrev entry (labels : Label k s d noiseCount → Λ) (exit : Option Λ) :=
  MachineDrainMany.entry (loadedFields k s d noiseCount) labels exit

def instruction (labels : Label k s d noiseCount → Λ) (exit : Option Λ) :
    Label k s d noiseCount → TM2.Stmt
      (fun _ : AddressMachineSpace.Tape k s d noiseCount => Bool) Λ (AddressMachineSpace.State k) :=
  MachineDrainMany.instruction (loadedFields k s d noiseCount) labels exit

end DFVSGames.Integration.AddressTupleCleanup
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineOutcomeRows
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

namespace DFVSGames.Reduction.MachineOutcomeRows

open Turing
open DFVSGames.Foundations.Complexity

variable {k q width : Nat} {K Λ σ : Type} [DecidableEq K]

def localMain (slots : MachineAddressEdge.Tape q width ↪ K) (row : Spec q width) :
    LocalLabel slots row :=
  MachineAddressEdge.leftLabel (MachineTemplateAddress.emitLabel
    (MachineFieldTemplate.startAt row.left.length 0))

def localInstruction (slots : MachineAddressEdge.Tape q width ↪ K)
    (row : Spec q width) (place : LocalLabel slots row → Λ) (exit : Option Λ) :
    LocalLabel slots row → TM2.Stmt (Alphabet (K := K)) Λ (MachineAddressEdge.State σ) :=
  MachineAddressEdge.instruction row.left row.right row.permutation slots place exit

def sequenceInstruction (slots : MachineAddressEdge.Tape q width ↪ K)
    (rows : List (Spec q width))
    (place : MachineFiniteSequence.Label (LocalLabel slots) rows → Λ) (exit : Option Λ) :=
  MachineFiniteSequence.instruction (LocalLabel slots) (localMain slots)
    (localInstruction (σ := σ) slots) rows place exit

instance localLabelFintype (slots : MachineAddressEdge.Tape q width ↪ K) (row : Spec q width) :
    Fintype (LocalLabel slots row) := by unfold LocalLabel; infer_instance

instance localLabelDecidableEq (slots : MachineAddressEdge.Tape q width ↪ K) (row : Spec q width) :
    DecidableEq (LocalLabel slots row) := by
  letI : DecidableEq (MachineTemplateAddress.Label row.left.length width
      (MachineTemplateAddress.chosen (MachineAddressEdge.addressSlots slots))) := by
    infer_instance
  letI : DecidableEq (MachineTemplateAddress.Label row.right.length width
      (MachineTemplateAddress.chosen (MachineAddressEdge.addressSlots slots))) := by
    infer_instance
  dsimp only [LocalLabel, MachineAddressEdge.Label]
  infer_instance

instance labelFintype (slots : MachineAddressEdge.Tape q width ↪ K) (rows : List (Row k q width)) :
    Fintype (Label slots rows) := by unfold Label; infer_instance

instance labelDecidableEq (slots : MachineAddressEdge.Tape q width ↪ K) (rows : List (Row k q width)) :
    DecidableEq (Label slots rows) := by unfold Label; infer_instance

def dispatcher (slots : MachineAddressEdge.Tape q width ↪ K) :
    (rows : List (Row k q width)) → (Label slots rows → Λ) → Option Λ →
      TM2.Stmt (Alphabet (K := K)) Λ (State k σ)
  | [], _, exit => .load MachineFieldTemplate.reset (MachineFieldTemplate.jump exit)
  | row :: _rows, place, _ => .load MachineFieldTemplate.reset
      (.goto fun state => place (.inr ⟨MachineRhsLoad.rhs state,
        .inl (localMain slots (row (MachineRhsLoad.rhs state)))⟩))

def instruction (slots : MachineAddressEdge.Tape q width ↪ K)
    (rows : List (Row k q width)) (place : Label slots rows → Λ) (exit : Option Λ) :
    Label slots rows → TM2.Stmt (Alphabet (K := K)) Λ (State k σ)
  | .inl _ => dispatcher slots rows place exit
  | .inr ⟨rhs, label⟩ => sequenceInstruction slots (selected rows rhs)
      (fun l => place (.inr ⟨rhs, l⟩)) exit label

end DFVSGames.Reduction.MachineOutcomeRows
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_UniformReduction
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

namespace DFVSGames.Reduction.FixedOutcomes

open Integration.BinaryLinear ActualHomogeneous ActualSource
open ActualEnumeration _root_.OAI.DFVSGames.Reduction.Explicit

variable {N : Type*}

def assemble {m k s d : Nat} (U : Fin k → Fin m) (p : Parameter k s d N) :
    Query m k s d × (N × (E k →ₗ[F2] F2)) :=
  ((U, p.1), p.2)

end DFVSGames.Reduction.FixedOutcomes
end

section

namespace DFVSGames.Reduction.AddressOutcomeSpecs

open Integration.BinaryLinear Foundations.Complexity ActualSource
open Integration

def tupleBits (S : Source) (k : Nat) {s d : Nat} (T : NoiseTables.Table s d)
    (U : ActualGame.Question S k) : List Bool :=
  (FixedOutcomes.tableParams k T).flatMap (fun p =>
    encodeWords (constraintWords (AddressGame.addressEdge S k (TableReduction.tableSkeleton T)
      (FixedOutcomes.assemble U p))))

end DFVSGames.Reduction.AddressOutcomeSpecs
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_AddressTupleBody
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

namespace DFVSGames.Integration.AddressTupleBody

open Turing Reduction Foundations.Complexity
open AddressMachineSpace

variable {k s d noiseCount : Nat} {Λ : Type}

instance labelFintype (rows : Rows k) : Fintype (Label k s d noiseCount rows) := by
  unfold Label CleanupLabel RowLabel
  infer_instance

variable {rows : Rows k}

def sourceLabels (labels : Label k s d noiseCount rows → Λ) : MachineSourceTuple.Label k → Λ :=
  fun l => labels (.inl l)
def rowLabels (labels : Label k s d noiseCount rows → Λ) : RowLabel k s d noiseCount rows → Λ :=
  fun l => labels (.inr (.inr (.inl l)))

def main (rows : Rows k) : Label k s d noiseCount rows := .inl (MachineSourceTuple.labelAt 0)

def instruction (rows : Rows k) (labels : Label k s d noiseCount rows → Λ) (exit : Option Λ) :
    Label k s d noiseCount rows →
      TM2.Stmt (fun _ : Arena k s d noiseCount => Bool) Λ (BodyState k)
  | .inl l => MachineSubroutine.statement (sourceLabels labels) (some (rhsLabel labels))
      (MachineSourceTuple.program l)
  | .inr (.inl _) => MachineRhsLoad.statement (rhsField k s d noiseCount)
      (some (rowLabels labels (.inl ())))
  | .inr (.inr (.inl l)) => MachineOutcomeRows.instruction (Slots k s d noiseCount) rows
      (rowLabels labels)
      (AddressTupleCleanup.entry k s d noiseCount (cleanupLabels labels) (some (resetLabel labels))) l
  | .inr (.inr (.inr (.inl l))) => AddressTupleCleanup.instruction k s d noiseCount
      (cleanupLabels labels) (some (resetLabel labels)) l
  | .inr (.inr (.inr (.inr _))) => reset exit

end DFVSGames.Integration.AddressTupleBody
end

section

namespace DFVSGames.Reduction.AddressMachineProgram

open Turing Foundations.Complexity Foundations.Hastad Integration
open MachineComposition

noncomputable section

variable (k : Nat) {s d : Nat} (T : NoiseTables.Table s d)

@[simp] theorem output_not_mem_clearKeys : output k T ∉ clearKeys k T := by simp

abbrev HeaderLabel := MachineAddressHeaders.Label k s d T.vectors.length
abbrev BodyLabel := Integration.AddressTupleBody.Label k s d T.vectors.length
  (AddressOutcomeSpecs.rows k T)
abbrev FinishLabel := SourceRuntimeFinish.Label (clearKeys k T)

inductive Label (k : Nat) {s d : Nat} (T : NoiseTables.Table s d)
  | header (localLabel : HeaderLabel k T)
  | initialize_ (localLabel : MachineOdometerInit.Label k)
  | body (localLabel : BodyLabel k T)
  | check (digit : Fin k)
  | reset (digit : Fin k)
  | finishStart
  | finish (localLabel : FinishLabel k T)
  deriving DecidableEq, Fintype

def headerLabels : HeaderLabel k T → Label k T := Label.header
def initializeLabels : MachineOdometerInit.Label k → Label k T := Label.initialize_
def bodyLabels : BodyLabel k T → Label k T := Label.body
def finishLabels : FinishLabel k T → Label k T := Label.finish

def start : Label k T := .header (.inl .copyOut)
def initializeStart : Label k T := MachineOdometerInit.labelAt (initializeLabels k T) 0
def bodyStart : Label k T := .body (Integration.AddressTupleBody.main (AddressOutcomeSpecs.rows k T))
def checkLabel (j : Fin k) : Label k T := .check j
def resetLabel (j : Fin k) : Label k T := .reset j
def finishStart : Label k T := .finishStart

def next (r : Nat) : Label k T :=
  if h : r < k then checkLabel k T ⟨r,h⟩ else finishStart k T

def resetAt (r : Nat) : Label k T :=
  if h : r < k then resetLabel k T ⟨r,h⟩ else finishStart k T

@[simp] theorem next_lt (r : Nat) (h : r < k) :
    next k T r = checkLabel k T ⟨r,h⟩ := by simp [next,h]
@[simp] theorem next_ge (r : Nat) (h : k ≤ r) : next k T r = finishStart k T := by
  simp [next, Nat.not_lt.mpr h]
@[simp] theorem resetAt_lt (r : Nat) (h : r < k) :
    resetAt k T r = resetLabel k T ⟨r,h⟩ := by simp [resetAt,h]

def program : Label k T → TM2.Stmt (fun _ : Tape k T => Bool) (Label k T) (State k)
  | .header l => MachineAddressHeaders.statement
      (AddressMachineSpace.fullHeaderSlots k s d T.vectors.length)
      (headerLabels k T) (some (initializeStart k T)) l
  | .initialize_ l => MachineOdometerInit.statement
      (AddressMachineSpace.odometerSlots k s d T.vectors.length)
      (initializeLabels k T) (some (bodyStart k T)) l
  | .body l => Integration.AddressTupleBody.instruction (AddressOutcomeSpecs.rows k T)
      (bodyLabels k T) (some (next k T 0)) l
  | .check j => MachineTupleOdometer.increment
      (AddressMachineSpace.current k s d T.vectors.length j)
      (AddressMachineSpace.remaining k s d T.vectors.length j)
      (bodyStart k T) (resetLabel k T j)
  | .reset j => MachineTupleOdometer.reset
      (AddressMachineSpace.current k s d T.vectors.length j)
      (AddressMachineSpace.remaining k s d T.vectors.length j)
      (resetLabel k T j) (next k T (j.val+1))
  | .finishStart => MachineFieldTemplate.jump
      (SourceRuntimeFinish.entry (clearKeys k T) (finishLabels k T))
  | .finish l => SourceRuntimeFinish.statement (clearKeys k T) (accumulator k T) (output k T)
      (AddressMachineSpace.initialState k).1 (finishLabels k T) none l

@[simp] theorem atHeader (l : HeaderLabel k T) : program k T (headerLabels k T l) =
    MachineAddressHeaders.statement (AddressMachineSpace.fullHeaderSlots k s d T.vectors.length)
      (headerLabels k T) (some (initializeStart k T)) l := rfl

@[simp] theorem atInitialize (l : MachineOdometerInit.Label k) :
    program k T (initializeLabels k T l) =
      MachineOdometerInit.statement (AddressMachineSpace.odometerSlots k s d T.vectors.length)
        (initializeLabels k T) (some (bodyStart k T)) l := rfl

@[simp] theorem atBody (l : BodyLabel k T) : program k T (bodyLabels k T l) =
    Integration.AddressTupleBody.instruction (AddressOutcomeSpecs.rows k T)
      (bodyLabels k T) (some (next k T 0)) l := rfl

@[simp] theorem atCheck (j : Fin k) : program k T (checkLabel k T j) =
    MachineTupleOdometer.increment (AddressMachineSpace.current k s d T.vectors.length j)
      (AddressMachineSpace.remaining k s d T.vectors.length j)
      (bodyStart k T) (resetLabel k T j) := rfl

@[simp] theorem atReset (j : Fin k) : program k T (resetLabel k T j) =
    MachineTupleOdometer.reset (AddressMachineSpace.current k s d T.vectors.length j)
      (AddressMachineSpace.remaining k s d T.vectors.length j)
      (resetLabel k T j) (next k T (j.val+1)) := rfl

@[simp] theorem atFinish (l : FinishLabel k T) : program k T (finishLabels k T l) =
    SourceRuntimeFinish.statement (clearKeys k T) (accumulator k T) (output k T)
      (AddressMachineSpace.initialState k).1 (finishLabels k T) none l := rfl

def machine : FinTM2 where
  K := Tape k T
  k₀ := .source
  k₁ := output k T
  Γ := fun _ => Bool
  Λ := Label k T
  main := start k T
  σ := State k
  initialState := AddressMachineSpace.initialState k
  m := program k T

@[simp] theorem machine_main : (machine k T).main = start k T := rfl
@[simp] theorem machine_program : (machine k T).m = program k T := rfl
@[simp] theorem machine_initialState : (machine k T).initialState = AddressMachineSpace.initialState k := rfl
@[simp] theorem machine_input : (machine k T).k₀ = (MachineSourceTuple.Tape.source : Tape k T) := rfl
@[simp] theorem machine_output : (machine k T).k₁ = output k T := rfl

def inputTapes (bits : List Bool) : Tape k T → List Bool :=
  Function.update (fun _ => []) .source bits

def outputTapes (bits : List Bool) : Tape k T → List Bool :=
  SourceRuntimeFinish.canonicalTapes (output k T) bits

@[simp] theorem inputTapes_source (bits : List Bool) : inputTapes k T bits .source = bits := by
  simp [inputTapes]

@[simp] theorem inputTapes_other (bits : List Bool) (tape : Tape k T) (h : tape ≠ .source) :
    inputTapes k T bits tape = [] := by simp [inputTapes,h]

@[simp] theorem outputTapes_output (bits : List Bool) : outputTapes k T bits (output k T) = bits := by
  simp [outputTapes, SourceRuntimeFinish.canonicalTapes]

@[simp] theorem outputTapes_other (bits : List Bool) (tape : Tape k T) (h : tape ≠ output k T) :
    outputTapes k T bits tape = [] := by simp [outputTapes,SourceRuntimeFinish.canonicalTapes,h]

end
end DFVSGames.Reduction.AddressMachineProgram
end

section

namespace DFVSGames.Reduction.AddressOdometerSchedule

open Turing
open DFVSGames.Foundations.Complexity MachineTupleOdometer
open DFVSGames.Foundations.Hastad
open MachineTransfer

noncomputable section

abbrev Tape := AddressMachineSpace.Tape

variable {k s d noiseCount m : ℕ} {Λ σ : Type}

def current (k s d noiseCount : Nat) (i : Fin k) : Tape k s d noiseCount :=
  AddressMachineSpace.current k s d noiseCount i

def remaining (k s d noiseCount : Nat) (i : Fin k) : Tape k s d noiseCount :=
  AddressMachineSpace.remaining k s d noiseCount i

def accumulator (k s d noiseCount : Nat) : Tape k s d noiseCount :=
  AddressMachineSpace.headerTape k s d noiseCount .reversed

@[simp] theorem current_eq_iff (i j : Fin k) :
    current k s d noiseCount i = current k s d noiseCount j ↔ i = j := by
  simp [current, AddressMachineSpace.current]
@[simp] theorem remaining_eq_iff (i j : Fin k) :
    remaining k s d noiseCount i = remaining k s d noiseCount j ↔ i = j := by
  simp [remaining, AddressMachineSpace.remaining]
@[simp] theorem current_ne_remaining (i j : Fin k) :
    current k s d noiseCount i ≠ remaining k s d noiseCount j :=
  AddressMachineSpace.current_ne_remaining k s d noiseCount i j
@[simp] theorem remaining_ne_current (i j : Fin k) :
    remaining k s d noiseCount i ≠ current k s d noiseCount j :=
  Ne.symm (current_ne_remaining j i)
@[simp] theorem accumulator_ne_current (i : Fin k) :
    accumulator k s d noiseCount ≠ current k s d noiseCount i :=
  AddressMachineSpace.headerTape_ne_current k s d noiseCount .reversed i
@[simp] theorem accumulator_ne_remaining (i : Fin k) :
    accumulator k s d noiseCount ≠ remaining k s d noiseCount i :=
  AddressMachineSpace.headerTape_ne_remaining k s d noiseCount .reversed i
@[simp] theorem current_ne_accumulator (i : Fin k) :
    current k s d noiseCount i ≠ accumulator k s d noiseCount := Ne.symm (accumulator_ne_current i)
@[simp] theorem remaining_ne_accumulator (i : Fin k) :
    remaining k s d noiseCount i ≠ accumulator k s d noiseCount := Ne.symm (accumulator_ne_remaining i)

def setDigits (m : ℕ) {q : ℕ} (digits : Fin q → ℕ)
    (base : Tape k s d noiseCount → List Bool) : Tape k s d noiseCount → List Bool
  | .savedIndex i => if h : i.rev.val < q then encodeWord (digits ⟨i.rev.val, h⟩)
      else base (.savedIndex i)
  | .extra (.inr (.inr (.inl i))) => if h : i.val < q then encodeWord (m - 1 - digits ⟨i.val, h⟩)
      else base (.extra (.inr (.inr (.inl i))))
  | tape => base tape

def setAcc (base : Tape k s d noiseCount → List Bool) (bits : List Bool) :
    Tape k s d noiseCount → List Bool := Function.update base (accumulator k s d noiseCount) bits

def putDigit (i : Fin k) (base : Tape k s d noiseCount → List Bool) (a r : Nat) :
    Tape k s d noiseCount → List Bool :=
  digitTapes (current k s d noiseCount i) (remaining k s d noiseCount i) base a r [] []

@[simp] theorem setDigits_current (m : Nat) {q : Nat} (digits : Fin q → Nat)
    (base : Tape k s d noiseCount → List Bool) (i : Fin k) :
    setDigits m digits base (current k s d noiseCount i) =
      if h : i.val < q then encodeWord (digits ⟨i.val, h⟩) else base (current k s d noiseCount i) := by
  simp [setDigits, current, AddressMachineSpace.current]
@[simp] theorem setDigits_remaining (m : Nat) {q : Nat} (digits : Fin q → Nat)
    (base : Tape k s d noiseCount → List Bool) (i : Fin k) :
    setDigits m digits base (remaining k s d noiseCount i) =
      if h : i.val < q then encodeWord (m - 1 - digits ⟨i.val, h⟩)
      else base (remaining k s d noiseCount i) := rfl

theorem setDigits_other (m : Nat) {q : Nat} (digits : Fin q → Nat)
    (base : Tape k s d noiseCount → List Bool) (tape : Tape k s d noiseCount)
    (hc : ∀ i, tape ≠ current k s d noiseCount i)
    (hr : ∀ i, tape ≠ remaining k s d noiseCount i) : setDigits m digits base tape = base tape := by
  cases tape with
  | savedIndex i => exact (hc i.rev (by simp [current, AddressMachineSpace.current])).elim
  | extra e =>
    rcases e with a | a
    · rfl
    · rcases a with a | a
      · rfl
      · rcases a with i | unused
        · exact (hr i rfl).elim
        · rfl
  | _ => rfl

theorem digitCases_inline_AddressOdometerSchedule {P : Tape k s d noiseCount → Prop} (tape : Tape k s d noiseCount)
    (hc : ∀ i, P (current k s d noiseCount i))
    (hr : ∀ i, P (remaining k s d noiseCount i))
    (other : ∀ tape, (∀ i, tape ≠ current k s d noiseCount i) →
      (∀ i, tape ≠ remaining k s d noiseCount i) → P tape) : P tape := by
  classical
  by_cases h : ∃ i, tape = current k s d noiseCount i
  · obtain ⟨i, rfl⟩ := h; exact hc i
  · by_cases h' : ∃ i, tape = remaining k s d noiseCount i
    · obtain ⟨i, rfl⟩ := h'; exact hr i
    · exact other tape (fun i hi => h ⟨i, hi⟩) (fun i hi => h' ⟨i, hi⟩)

@[simp] theorem setDigits_zero (m : Nat) (digits : Fin 0 → Nat)
    (base : Tape k s d noiseCount → List Bool) : setDigits m digits base = base := by
  funext tape
  apply digitCases_inline_AddressOdometerSchedule tape
  · intro i; simp
  · intro i; simp
  · intro tape hc hr; exact setDigits_other m digits base tape hc hr

@[simp] theorem setDigits_accumulator (m : Nat) {q : Nat} (digits : Fin q → Nat)
    (base : Tape k s d noiseCount → List Bool) :
    setDigits m digits base (accumulator k s d noiseCount) = base (accumulator k s d noiseCount) := rfl

@[simp] theorem setAcc_self (base : Tape k s d noiseCount → List Bool) :
    setAcc base (base (accumulator k s d noiseCount)) = base := by simp [setAcc]
@[simp] theorem setAcc_setAcc (base : Tape k s d noiseCount → List Bool) (first second : List Bool) :
    setAcc (setAcc base first) second = setAcc base second := by simp [setAcc]
@[simp] theorem setAcc_apply (base : Tape k s d noiseCount → List Bool) (bits : List Bool) :
    setAcc base bits (accumulator k s d noiseCount) = bits := by simp [setAcc]

@[simp] theorem putDigit_current (j : Fin k) (base : Tape k s d noiseCount → List Bool)
    (a r : Nat) (i : Fin k) :
    putDigit j base a r (current k s d noiseCount i) =
      if i = j then encodeWord a else base (current k s d noiseCount i) := by
  simp [putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt, Function.update_apply]
@[simp] theorem putDigit_remaining (j : Fin k) (base : Tape k s d noiseCount → List Bool)
    (a r : Nat) (i : Fin k) :
    putDigit j base a r (remaining k s d noiseCount i) =
      if i = j then encodeWord r else base (remaining k s d noiseCount i) := by
  simp [putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt, Function.update_apply]

theorem putDigit_other (j : Fin k) (base : Tape k s d noiseCount → List Bool)
    (a r : Nat) (tape : Tape k s d noiseCount)
    (hc : tape ≠ current k s d noiseCount j) (hr : tape ≠ remaining k s d noiseCount j) :
    putDigit j base a r tape = base tape := by
  simp [putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt, hc, hr]

@[simp] theorem putDigit_accumulator (j : Fin k) (base : Tape k s d noiseCount → List Bool)
    (a r : Nat) : putDigit j base a r (accumulator k s d noiseCount) =
      base (accumulator k s d noiseCount) := by
  apply putDigit_other <;> simp

@[simp] theorem setDigits_savedIndex (m : Nat) (digits : Fin k → Nat)
    (base : Tape k s d noiseCount → List Bool) (j : Fin k) :
    setDigits m digits base (.savedIndex j) = encodeWord (digits j.rev) := by
  have h : j.rev.val < k := j.rev.isLt
  simp only [setDigits, h, dite_eq_left]

@[simp] theorem setAcc_other (base : Tape k s d noiseCount → List Bool)
    (bits : List Bool) (tape : Tape k s d noiseCount)
    (h : tape ≠ accumulator k s d noiseCount) : setAcc base bits tape = base tape := by
  simp [setAcc, h]

def configuration (label : Λ) (canonical : σ) (tapes : Tape k s d noiseCount → List Bool) :
    Configuration (Tape k s d noiseCount) Λ σ := ⟨some label, (canonical, none), tapes⟩

def initialConfiguration (q : ℕ) (bodyLabel : Λ) (canonical : σ)
    (base : Tape k s d noiseCount → List Bool) : Configuration (Tape k s d noiseCount) Λ σ :=
  configuration bodyLabel canonical (setDigits m (fun _ : Fin q => 0) base)

def finalConfiguration {q : ℕ} (exitLabel : Λ) (canonical : σ)
    (base : Tape k s d noiseCount → List Bool) (bits : (Fin q → Fin m) → List Bool) :
    Configuration (Tape k s d noiseCount) Λ σ :=
  configuration exitLabel canonical (setDigits m (fun _ : Fin q => 0)
    (setAcc base ((allBits bits).reverse ++ base (accumulator k s d noiseCount))))

@[simp] theorem initial_current (base : Tape k s d noiseCount → List Bool)
    (bodyLabel : Λ) (canonical : σ) (i : Fin k) :
    (initialConfiguration (m := m) k bodyLabel canonical base).stk (current k s d noiseCount i) =
      encodeWord 0 := by simp [initialConfiguration, configuration]

@[simp] theorem initial_remaining (base : Tape k s d noiseCount → List Bool)
    (bodyLabel : Λ) (canonical : σ) (i : Fin k) :
    (initialConfiguration (m := m) k bodyLabel canonical base).stk (remaining k s d noiseCount i) =
      encodeWord (m - 1) := by simp [initialConfiguration, configuration]

@[simp] theorem final_current (base : Tape k s d noiseCount → List Bool)
    (exitLabel : Λ) (canonical : σ)
    (bits : (Fin k → Fin m) → List Bool) (i : Fin k) :
    (finalConfiguration exitLabel canonical base bits).stk (current k s d noiseCount i) =
      encodeWord 0 := by simp [finalConfiguration, configuration]

@[simp] theorem final_remaining (base : Tape k s d noiseCount → List Bool)
    (exitLabel : Λ) (canonical : σ)
    (bits : (Fin k → Fin m) → List Bool) (i : Fin k) :
    (finalConfiguration exitLabel canonical base bits).stk (remaining k s d noiseCount i) =
      encodeWord (m - 1) := by simp [finalConfiguration, configuration]

@[simp] theorem final_accumulator (base : Tape k s d noiseCount → List Bool)
    (exitLabel : Λ) (canonical : σ)
    (bits : (Fin k → Fin m) → List Bool) :
    (finalConfiguration exitLabel canonical base bits).stk (accumulator k s d noiseCount) =
      ((tupleOrder m k).flatMap bits).reverse ++ base (accumulator k s d noiseCount) := by
  simp [finalConfiguration, configuration, allBits]

theorem final_other (base : Tape k s d noiseCount → List Bool)
    (exitLabel : Λ) (canonical : σ) (bits : (Fin k → Fin m) → List Bool)
    (tape : Tape k s d noiseCount)
    (hc : ∀ i, tape ≠ current k s d noiseCount i)
    (hr : ∀ i, tape ≠ remaining k s d noiseCount i)
    (ha : tape ≠ accumulator k s d noiseCount) :
    (finalConfiguration exitLabel canonical base bits).stk tape = base tape := by
  simp only [finalConfiguration, configuration, setDigits_other m _ _ tape hc hr,
    setAcc_other _ _ tape ha]

end
end DFVSGames.Reduction.AddressOdometerSchedule
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_AddressMachineInitial
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

namespace DFVSGames.Reduction.AddressMachineInitial

open Turing DFVSGames.Foundations.Complexity

noncomputable section

variable (k : Nat) {s d : Nat} (T : Integration.NoiseTables.Table s d)

def afterHeaders (F : SourceEncoding.Input) : AddressMachineProgram.Tape k T → List Bool :=
  MachineAddressHeaders.resultTapes (AddressMachineSpace.fullHeaderSlots k s d T.vectors.length)
    (AddressMachineProgram.inputTapes k T (SourceEncoding.inputBits F))
    F.«variables» F.equations.length

def initialized (F : SourceEncoding.Input) : AddressMachineProgram.Tape k T → List Bool :=
  MachineOdometerInit.stageTapes (AddressMachineSpace.odometerSlots k s d T.vectors.length)
    F.equations.length (afterHeaders k T F) k

theorem input_header_inline_AddressMachineInitial (F : SourceEncoding.Input)
    (c : MachineAddressHeaders.Arithmetic.Control) :
    AddressMachineProgram.inputTapes k T (SourceEncoding.inputBits F)
      (AddressMachineSpace.headerTape k s d T.vectors.length c) = [] := by
  apply AddressMachineProgram.inputTapes_other
  simp [AddressMachineSpace.headerTape]

theorem afterHeaders_frame (F : SourceEncoding.Input) (p : AddressMachineProgram.Tape k T)
    (hw : p ≠ .work)
    (hn : p ≠ AddressMachineSpace.headerTape k s d T.vectors.length .variableCount)
    (hm : p ≠ AddressMachineSpace.headerTape k s d T.vectors.length .occurrenceCount)
    (hb : p ≠ AddressMachineSpace.headerTape k s d T.vectors.length .baseValue)
    (hc : p ≠ AddressMachineSpace.headerTape k s d T.vectors.length .capacity)
    (hr : p ≠ AddressMachineSpace.headerTape k s d T.vectors.length .reversed) :
    afterHeaders k T F p = AddressMachineProgram.inputTapes k T (SourceEncoding.inputBits F) p :=
  MachineAddressHeaders.resultTapes_other _ _ _ _ p hw hn hm hb hc hr

theorem afterHeaders_empty (F : SourceEncoding.Input) (p : AddressMachineProgram.Tape k T)
    (hs : p ≠ .source) (hw : p ≠ .work)
    (hn : p ≠ AddressMachineSpace.headerTape k s d T.vectors.length .variableCount)
    (hm : p ≠ AddressMachineSpace.headerTape k s d T.vectors.length .occurrenceCount)
    (hb : p ≠ AddressMachineSpace.headerTape k s d T.vectors.length .baseValue)
    (hc : p ≠ AddressMachineSpace.headerTape k s d T.vectors.length .capacity)
    (hr : p ≠ AddressMachineSpace.headerTape k s d T.vectors.length .reversed) :
    afterHeaders k T F p = [] :=
  (afterHeaders_frame k T F p hw hn hm hb hc hr).trans
    (AddressMachineProgram.inputTapes_other k T _ p hs)

@[simp] theorem afterHeaders_source (F : SourceEncoding.Input) :
    afterHeaders k T F .source = SourceEncoding.inputBits F := by
  exact (MachineAddressHeaders.resultTapes_source _ _ F.«variables» F.equations.length).trans
    (AddressMachineProgram.inputTapes_source k T _)

@[simp] theorem afterHeaders_variables (F : SourceEncoding.Input) :
    afterHeaders k T F (AddressMachineSpace.headerTape k s d T.vectors.length .variableCount) =
      encodeWord F.«variables» := by
  change MachineAddressHeaders.resultTapes _ _ _ _
    (MachineAddressHeaders.Arithmetic.control
      (MachineAddressHeaders.arithmeticSlots (AddressMachineSpace.fullHeaderSlots k s d T.vectors.length))
      .variableCount) = _
  rw [MachineAddressHeaders.resultTapes_n]
  change encodeWord F.«variables» ++ AddressMachineProgram.inputTapes k T (SourceEncoding.inputBits F)
    (AddressMachineSpace.headerTape k s d T.vectors.length .variableCount) = _
  rw [input_header_inline_AddressMachineInitial, List.append_nil]

@[simp] theorem afterHeaders_occurrences (F : SourceEncoding.Input) :
    afterHeaders k T F (AddressMachineSpace.headerTape k s d T.vectors.length .occurrenceCount) =
      encodeWord F.equations.length := by
  change MachineAddressHeaders.resultTapes _ _ _ _
    (MachineAddressHeaders.Arithmetic.control
      (MachineAddressHeaders.arithmeticSlots (AddressMachineSpace.fullHeaderSlots k s d T.vectors.length))
      .occurrenceCount) = _
  rw [MachineAddressHeaders.resultTapes_m]
  change encodeWord F.equations.length ++ AddressMachineProgram.inputTapes k T (SourceEncoding.inputBits F)
    (AddressMachineSpace.headerTape k s d T.vectors.length .occurrenceCount) = _
  rw [input_header_inline_AddressMachineInitial, List.append_nil]

@[simp] theorem afterHeaders_base (F : SourceEncoding.Input) :
    afterHeaders k T F (AddressMachineSpace.headerTape k s d T.vectors.length .baseValue) =
      encodeWord (MachineAddressHeaders.radix s d F.«variables» F.equations.length) :=
  MachineAddressHeaders.resultTapes_base _ _ _ _

@[simp] theorem afterHeaders_capacity (F : SourceEncoding.Input) :
    afterHeaders k T F (AddressMachineSpace.headerTape k s d T.vectors.length .capacity) =
      encodeWord (MachineAddressHeaders.capacity k s d F.«variables» F.equations.length) :=
  MachineAddressHeaders.resultTapes_capacity _ _ _ _

@[simp] theorem afterHeaders_reversed (F : SourceEncoding.Input) :
    afterHeaders k T F (AddressMachineSpace.headerTape k s d T.vectors.length .reversed) =
      (MachineAddressHeaders.Arithmetic.headerBits k s d T.vectors.length
        F.«variables» F.equations.length).reverse := by
  change MachineAddressHeaders.resultTapes _ _ _ _
    (MachineAddressHeaders.Arithmetic.control
      (MachineAddressHeaders.arithmeticSlots (AddressMachineSpace.fullHeaderSlots k s d T.vectors.length))
      .reversed) = _
  rw [MachineAddressHeaders.resultTapes_reversed]
  change (MachineAddressHeaders.Arithmetic.headerBits k s d T.vectors.length
    F.«variables» F.equations.length).reverse ++ AddressMachineProgram.inputTapes k T
      (SourceEncoding.inputBits F) (AddressMachineSpace.headerTape k s d T.vectors.length .reversed) = _
  rw [input_header_inline_AddressMachineInitial, List.append_nil]

@[simp] theorem afterHeaders_work (F : SourceEncoding.Input) : afterHeaders k T F .work = [] :=
  MachineAddressHeaders.resultTapes_readCopy _ _ _ _

@[simp] theorem afterHeaders_current (F : SourceEncoding.Input) (j : Fin k) :
    afterHeaders k T F (AddressMachineSpace.current k s d T.vectors.length j) = [] := by
  apply afterHeaders_empty <;> simp [AddressMachineSpace.current, AddressMachineSpace.headerTape]

@[simp] theorem afterHeaders_remaining (F : SourceEncoding.Input) (j : Fin k) :
    afterHeaders k T F (AddressMachineSpace.remaining k s d T.vectors.length j) = [] := by
  apply afterHeaders_empty <;> simp [AddressMachineSpace.remaining, AddressMachineSpace.headerTape]

@[simp] theorem afterHeaders_copyScratch (F : SourceEncoding.Input) :
    afterHeaders k T F .copyScratch = [] := by
  apply afterHeaders_empty <;> simp [AddressMachineSpace.headerTape]

theorem initialized_frame (F : SourceEncoding.Input) (p : AddressMachineProgram.Tape k T)
    (hc : ∀ j, p ≠ AddressMachineSpace.current k s d T.vectors.length j)
    (hr : ∀ j, p ≠ AddressMachineSpace.remaining k s d T.vectors.length j) :
    initialized k T F p = afterHeaders k T F p :=
  MachineOdometerInit.stageTapes_frame _ _ _ _ p hc hr

@[simp] theorem initialized_header (F : SourceEncoding.Input)
    (c : MachineAddressHeaders.Arithmetic.Control) :
    initialized k T F (AddressMachineSpace.headerTape k s d T.vectors.length c) =
      afterHeaders k T F (AddressMachineSpace.headerTape k s d T.vectors.length c) :=
  initialized_frame k T F _
    (AddressMachineSpace.headerTape_ne_current k s d T.vectors.length c)
    (AddressMachineSpace.headerTape_ne_remaining k s d T.vectors.length c)

@[simp] theorem initialized_source (F : SourceEncoding.Input) :
    initialized k T F .source = SourceEncoding.inputBits F := by
  rw [initialized_frame k T F .source
    (by intro j; simp [AddressMachineSpace.current])
    (by intro j; simp [AddressMachineSpace.remaining])]
  exact afterHeaders_source k T F

@[simp] theorem initialized_variables (F : SourceEncoding.Input) :
    initialized k T F (AddressMachineSpace.headerTape k s d T.vectors.length .variableCount) =
      encodeWord F.«variables» := by rw [initialized_header, afterHeaders_variables]
@[simp] theorem initialized_occurrences (F : SourceEncoding.Input) :
    initialized k T F (AddressMachineSpace.headerTape k s d T.vectors.length .occurrenceCount) =
      encodeWord F.equations.length := by rw [initialized_header, afterHeaders_occurrences]
@[simp] theorem initialized_base (F : SourceEncoding.Input) :
    initialized k T F (AddressMachineSpace.headerTape k s d T.vectors.length .baseValue) =
      encodeWord (MachineAddressHeaders.radix s d F.«variables» F.equations.length) := by
  rw [initialized_header, afterHeaders_base]
@[simp] theorem initialized_capacity (F : SourceEncoding.Input) :
    initialized k T F (AddressMachineSpace.headerTape k s d T.vectors.length .capacity) =
      encodeWord (MachineAddressHeaders.capacity k s d F.«variables» F.equations.length) := by
  rw [initialized_header, afterHeaders_capacity]
@[simp] theorem initialized_reversed (F : SourceEncoding.Input) :
    initialized k T F (AddressMachineSpace.headerTape k s d T.vectors.length .reversed) =
      (MachineAddressHeaders.Arithmetic.headerBits k s d T.vectors.length
        F.«variables» F.equations.length).reverse := by
  rw [initialized_header, afterHeaders_reversed]

@[simp] theorem initialized_current (F : SourceEncoding.Input) (j : Fin k) :
    initialized k T F (AddressMachineSpace.current k s d T.vectors.length j) = encodeWord 0 :=
  MachineOdometerInit.output_current _ (AddressMachineSpace.odometerSlots k s d T.vectors.length).injective
    F.equations.length (afterHeaders k T F) j

@[simp] theorem initialized_remaining (F : SourceEncoding.Input) (j : Fin k) :
    initialized k T F (AddressMachineSpace.remaining k s d T.vectors.length j) =
      encodeWord (F.equations.length - 1) :=
  MachineOdometerInit.output_remaining _ (AddressMachineSpace.odometerSlots k s d T.vectors.length).injective
    F.equations.length (afterHeaders k T F) j

@[simp] theorem initialized_savedIndex (F : SourceEncoding.Input) (j : Fin k) :
    initialized k T F (.savedIndex j) = encodeWord 0 := by
  simpa only [AddressMachineSpace.current_rev] using initialized_current k T F j.rev

theorem initialized_empty (F : SourceEncoding.Input) (p : AddressMachineProgram.Tape k T)
    (hbefore : afterHeaders k T F p = [])
    (hc : ∀ j, p ≠ AddressMachineSpace.current k s d T.vectors.length j)
    (hr : ∀ j, p ≠ AddressMachineSpace.remaining k s d T.vectors.length j) :
    initialized k T F p = [] := (initialized_frame k T F p hc hr).trans hbefore

@[simp] theorem initialized_work (F : SourceEncoding.Input) : initialized k T F .work = [] := by
  apply initialized_empty k T F _ (afterHeaders_work k T F) <;>
    intro j <;> simp [AddressMachineSpace.current, AddressMachineSpace.remaining]

@[simp] theorem initialized_index (F : SourceEncoding.Input) : initialized k T F .index = [] := by
  apply initialized_empty
  · apply afterHeaders_empty <;> simp [AddressMachineSpace.headerTape]
  all_goals
    intro j
    simp [AddressMachineSpace.current, AddressMachineSpace.remaining]

@[simp] theorem initialized_scratch (F : SourceEncoding.Input) : initialized k T F .scratch = [] := by
  apply initialized_empty
  · apply afterHeaders_empty <;> simp [AddressMachineSpace.headerTape]
  all_goals
    intro j
    simp [AddressMachineSpace.current, AddressMachineSpace.remaining]

@[simp] theorem initialized_copyScratch (F : SourceEncoding.Input) :
    initialized k T F .copyScratch = [] := by
  apply initialized_empty k T F _ (afterHeaders_copyScratch k T F) <;>
    intro j <;> simp [AddressMachineSpace.current, AddressMachineSpace.remaining]

@[simp] theorem initialized_field (F : SourceEncoding.Input) (j : Fin k) (slot : Fin 4) :
    initialized k T F (.field j slot) = [] := by
  apply initialized_empty
  · apply afterHeaders_empty <;> simp [AddressMachineSpace.headerTape]
  all_goals
    intro i
    simp [AddressMachineSpace.current, AddressMachineSpace.remaining]

@[simp] theorem initialized_finalOutput (F : SourceEncoding.Input) :
    initialized k T F (AddressMachineSpace.finalOutput k s d T.vectors.length) = [] := by
  apply initialized_empty
  · apply afterHeaders_empty <;>
      simp [AddressMachineSpace.finalOutput, AddressMachineSpace.headerTape]
  all_goals
    intro i
    simp [AddressMachineSpace.finalOutput, AddressMachineSpace.current, AddressMachineSpace.remaining]

@[simp] theorem initialized_privateAddress (F : SourceEncoding.Input)
    (tape : MachineTemplateAddress.Tape (4 * k) (1 + 9 * k)) :
    initialized k T F (AddressMachineSpace.privateAddress k s d T.vectors.length tape) = [] := by
  apply initialized_empty
  · apply afterHeaders_empty <;>
      simp [AddressMachineSpace.privateAddress, AddressMachineSpace.headerTape]
  all_goals
    intro i
    simp [AddressMachineSpace.privateAddress, AddressMachineSpace.current, AddressMachineSpace.remaining]

end
end DFVSGames.Reduction.AddressMachineInitial
end

section

namespace DFVSGames.Reduction.OccurrenceTupleOrder

open Turing
open DFVSGames.Foundations.Complexity
open MachineTupleOdometer

variable {α : Type*}

theorem tupleOrder_readCoordinates (m k : Nat) :
    (MachineTupleOdometer.tupleOrder m k).map readCoordinates =
      ActualEnumeration.functions (List.finRange m) k := by
  induction k with
  | zero =>
    rw [MachineTupleOdometer.tupleOrder_dimension_zero]
    change [readCoordinates (fun i : Fin 0 => Fin.elim0 i)] = [Fin.elim0]
    congr 1
  | succ k ih =>
    have each (d : Fin m) :
        ((MachineTupleOdometer.tupleOrder m k).map (fun tail => Fin.snoc tail d)).map
          readCoordinates =
        (ActualEnumeration.functions (List.finRange m) k).map (Fin.cons d) := by
      calc
        _ = ((MachineTupleOdometer.tupleOrder m k).map readCoordinates).map (Fin.cons d) := by
          simp only [List.map_map, Function.comp_def, readCoordinates_snoc]
        _ = _ := by rw [ih]
    rw [MachineTupleOdometer.tupleOrder_snoc]
    change ((List.finRange m).flatMap (fun d =>
      (MachineTupleOdometer.tupleOrder m k).map (fun tail => Fin.snoc tail d))).map
      readCoordinates = _
    simp only [List.map_flatMap, each]
    simp only [ActualEnumeration.functions, Explicit.pairs, List.map_flatMap,
      List.map_map, Function.comp_def]

theorem functions_flatMap (m k : Nat) (emit : (Fin k → Fin m) → List α) :
    (ActualEnumeration.functions (List.finRange m) k).flatMap emit =
      (MachineTupleOdometer.tupleOrder m k).flatMap
        (fun digits => emit (readCoordinates digits)) := by
  rw [← tupleOrder_readCoordinates]
  exact List.flatMap_map readCoordinates emit _

end DFVSGames.Reduction.OccurrenceTupleOrder
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_OutputSize
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

namespace DFVSGames.Reduction.AddressMachineLoop

open Turing Foundations.Complexity Integration

noncomputable section

variable (k : Nat) {s d : Nat} (T : NoiseTables.Table s d)

def bits (F : SourceEncoding.Input)
    (digits : Fin k → Fin F.equations.length) : List Bool :=
  AddressOutcomeSpecs.tupleBits (AddressTupleBody.source F) k T
    (OccurrenceTupleOrder.readCoordinates digits)

def stateTapes (F : SourceEncoding.Input)
    (digits : Fin k → Fin F.equations.length) (output : List Bool) :
    AddressMachineProgram.Tape k T → List Bool :=
  AddressOdometerSchedule.setDigits F.equations.length (fun j => (digits j).val)
    (AddressOdometerSchedule.setAcc (AddressMachineInitial.initialized k T F) output)

theorem stateTapes_frame (F : SourceEncoding.Input)
    (digits : Fin k → Fin F.equations.length) (output : List Bool)
    (tape : AddressMachineProgram.Tape k T)
    (hc : ∀j, tape ≠ AddressMachineSpace.current k s d T.vectors.length j)
    (hr : ∀j, tape ≠ AddressMachineSpace.remaining k s d T.vectors.length j)
    (ha : tape ≠ AddressMachineSpace.headerTape k s d T.vectors.length .reversed) :
    stateTapes k T F digits output tape = AddressMachineInitial.initialized k T F tape := by
  rw [stateTapes, AddressOdometerSchedule.setDigits_other _ _ _ tape hc hr]
  exact AddressOdometerSchedule.setAcc_other _ _ tape ha

@[simp] theorem stateTapes_savedIndex (F : SourceEncoding.Input)
    (digits : Fin k → Fin F.equations.length) (output : List Bool) (j : Fin k) :
    stateTapes k T F digits output (.savedIndex j) = encodeWord (digits j.rev).val := by
  exact AddressOdometerSchedule.setDigits_savedIndex _ _ _ j

@[simp] theorem stateTapes_private (F : SourceEncoding.Input)
    (digits : Fin k → Fin F.equations.length) (output : List Bool)
    (tape : MachineTemplateAddress.Tape (4*k) (1+9*k)) :
    stateTapes k T F digits output (AddressMachineSpace.privateAddress k s d T.vectors.length tape) = [] := by
  rw [stateTapes_frame]
  · exact AddressMachineInitial.initialized_privateAddress k T F tape
  all_goals simp [AddressMachineSpace.privateAddress, AddressMachineSpace.current, AddressMachineSpace.remaining, AddressMachineSpace.headerTape]

@[simp] theorem stateTapes_header (F : SourceEncoding.Input)
    (digits : Fin k → Fin F.equations.length) (output : List Bool)
    (c : MachineAddressHeaders.Arithmetic.Control) (hc : c ≠ .reversed) :
    stateTapes k T F digits output (AddressMachineSpace.headerTape k s d T.vectors.length c) =
      AddressMachineInitial.initialized k T F (AddressMachineSpace.headerTape k s d T.vectors.length c) := by
  apply stateTapes_frame
  · exact AddressMachineSpace.headerTape_ne_current k s d T.vectors.length c
  · exact AddressMachineSpace.headerTape_ne_remaining k s d T.vectors.length c
  · intro h
    exact hc ((AddressMachineSpace.headerTape_eq_iff k s d T.vectors.length c .reversed).mp h)

def finalTapes (F : SourceEncoding.Input) : AddressMachineProgram.Tape k T → List Bool :=
  (AddressOdometerSchedule.finalConfiguration (AddressMachineProgram.next k T k) (AddressMachineSpace.initialState k).1
    (AddressMachineInitial.initialized k T F) (bits k T F)).stk

theorem allBits_eq (F : SourceEncoding.Input) :
    AddressOdometerSchedule.allBits (bits k T F) =
      (FixedOutcomes.occurrenceTuples F.equations.length k).flatMap
        (AddressOutcomeSpecs.tupleBits (AddressTupleBody.source F) k T) := by
  exact (OccurrenceTupleOrder.functions_flatMap F.equations.length k _).symm

@[simp] theorem final_reversed (F : SourceEncoding.Input) :
    finalTapes k T F (AddressMachineSpace.headerTape k s d T.vectors.length .reversed) =
      ((FixedOutcomes.occurrenceTuples F.equations.length k).flatMap
        (AddressOutcomeSpecs.tupleBits (AddressTupleBody.source F) k T)).reverse ++
      (MachineAddressHeaders.Arithmetic.headerBits k s d T.vectors.length
        F.«variables» F.equations.length).reverse := by
  change (AddressOdometerSchedule.finalConfiguration _ _ _ _).stk (AddressOdometerSchedule.accumulator _ _ _ _) = _
  rw [AddressOdometerSchedule.final_accumulator]
  change (AddressOdometerSchedule.allBits (bits k T F)).reverse ++ _ = _
  rw [allBits_eq]
  congr 1
  exact AddressMachineInitial.initialized_reversed k T F

theorem final_other (F : SourceEncoding.Input) (tape : AddressMachineProgram.Tape k T)
    (hc : ∀j, tape ≠ AddressMachineSpace.current k s d T.vectors.length j)
    (hr : ∀j, tape ≠ AddressMachineSpace.remaining k s d T.vectors.length j)
    (ha : tape ≠ AddressMachineSpace.headerTape k s d T.vectors.length .reversed) :
    finalTapes k T F tape = AddressMachineInitial.initialized k T F tape :=
  AddressOdometerSchedule.final_other _ _ _ _ tape hc hr ha

@[simp] theorem final_outputEmpty (F : SourceEncoding.Input) :
    finalTapes k T F (AddressMachineProgram.output k T) = [] := by
  rw [final_other]
  · exact AddressMachineInitial.initialized_finalOutput k T F
  · intro j
    exact Ne.symm (AddressMachineSpace.current_ne_finalOutput k s d T.vectors.length j)
  · intro j
    exact Ne.symm (AddressMachineSpace.remaining_ne_finalOutput k s d T.vectors.length j)
  · exact Ne.symm (AddressMachineSpace.headerTape_ne_finalOutput k s d T.vectors.length .reversed)

@[simp] theorem final_current (F : SourceEncoding.Input) (j : Fin k) :
    finalTapes k T F (AddressMachineSpace.current k s d T.vectors.length j) = encodeWord 0 :=
  AddressOdometerSchedule.final_current _ _ _ _ j

@[simp] theorem final_remaining (F : SourceEncoding.Input) (j : Fin k) :
    finalTapes k T F (AddressMachineSpace.remaining k s d T.vectors.length j) =
      encodeWord (F.equations.length-1) :=
  AddressOdometerSchedule.final_remaining _ _ _ _ j

end
end DFVSGames.Reduction.AddressMachineLoop
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineSingleOrbitBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Appendix.CompressionCount

open Module
open DFVSGames.Integration.BinaryLinear (F2)

universe u v w

variable (U : Type u) (K : Type v) (C : Type w)
variable [AddCommGroup U] [Module F2 U]
variable [AddCommGroup K] [Module F2 K]
variable [AddCommGroup C] [Module F2 C]

variable {U K C}

def Fiber (Z : K →ₗ[F2] C) :=
  {Y : (U × K) →ₗ[F2] (U × C) //
    finrank F2 Y.range = finrank F2 U + finrank F2 (Y - base U K C).range ∧
      compress Y = Z}

def inclusion (Z : K →ₗ[F2] C) : (U × Z.range) →ₗ[F2] (U × C) :=
  (LinearMap.id : U →ₗ[F2] U).prodMap Z.range.subtype

theorem graph_injective (Z : K →ₗ[F2] C) (F : Z.range →ₗ[F2] U) :
    Function.Injective (graph Z F) := by
  intro a b h
  exact Subtype.ext (congrArg Prod.snd h)

theorem inclusion_injective (Z : K →ₗ[F2] C) :
    Function.Injective (inclusion (U := U) Z) := by
  intro a b h
  exact Prod.ext (by simpa [inclusion] using congrArg Prod.fst h)
    (Subtype.ext (by simpa [inclusion] using congrArg Prod.snd h))

theorem lower_surjective (Z : K →ₗ[F2] C) (H : U →ₗ[F2] Z.range) :
    Function.Surjective (lower Z H) := by
  intro c
  obtain ⟨k, hk⟩ := Z.surjective_rangeRestrict c
  refine ⟨(0, k), ?_⟩
  simpa [lower] using hk

theorem range_lift_sub_base (Z : K →ₗ[F2] C) (P : Parameters (U := U) Z) :
    (lift Z P - base U K C).range = (graph Z P.1).range := by
  rw [lift, add_sub_cancel_left]
  exact LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.mpr (lower_surjective Z P.2))

theorem range_lift (Z : K →ₗ[F2] C) (P : Parameters (U := U) Z) :
    (lift Z P).range = (inclusion (U := U) Z).range := by
  apply le_antisymm
  · rintro _ ⟨p, rfl⟩
    refine ⟨(p.1 + P.1 (P.2 p.1 + Z.rangeRestrict p.2),
      P.2 p.1 + Z.rangeRestrict p.2), ?_⟩
    simp [inclusion]
  · rintro _ ⟨⟨u, c⟩, rfl⟩
    obtain ⟨k, hk⟩ := Z.surjective_rangeRestrict (c - P.2 (u - P.1 c))
    refine ⟨(u - P.1 c, k), ?_⟩
    have hc : P.2 (u - P.1 c) + Z.rangeRestrict k = c := by rw [hk]; abel
    apply Prod.ext
    · change u - P.1 c + P.1 (P.2 (u - P.1 c) + Z.rangeRestrict k) = u
      rw [hc]
      abel
    · simpa [inclusion] using congrArg Subtype.val hc

variable [FiniteDimensional F2 U] [FiniteDimensional F2 K] [FiniteDimensional F2 C]

omit [FiniteDimensional F2 U] [FiniteDimensional F2 K] [FiniteDimensional F2 C] in
theorem finrank_base : finrank F2 (base U K C).range = finrank F2 U := by
  rw [base, LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.mpr LinearMap.fst_surjective)]
  exact LinearMap.finrank_range_of_inj LinearMap.inl_injective

omit [FiniteDimensional F2 C] in
theorem lift_rank_order (Z : K →ₗ[F2] C) (P : Parameters (U := U) Z) :
    finrank F2 (lift Z P).range =
      finrank F2 U + finrank F2 (lift Z P - base U K C).range := by
  rw [range_lift, range_lift_sub_base,
    LinearMap.finrank_range_of_inj (inclusion_injective (U := U) Z),
    LinearMap.finrank_range_of_inj (graph_injective Z P.1), Module.finrank_prod]

def toFiber (Z : K →ₗ[F2] C) (P : Parameters (U := U) Z) : Fiber (U := U) Z :=
  ⟨lift Z P, lift_rank_order Z P, compress_lift Z P⟩

omit [FiniteDimensional F2 U] [FiniteDimensional F2 K] [FiniteDimensional F2 C] in
theorem lift_injective (Z : K →ₗ[F2] C) :
    Function.Injective (lift (U := U) Z) := by
  rintro ⟨F, H⟩ ⟨G, J⟩ h
  have hH : H = J := by
    ext u
    have he := congrArg (fun f => (f (u, 0)).2) h
    simpa using he
  have hF : F = G := by
    ext c
    obtain ⟨k, hk⟩ := Z.surjective_rangeRestrict c
    have he := congrArg (fun f => (f (0, k)).1) h
    simpa [hk] using he
  exact Prod.ext hF hH

omit [FiniteDimensional F2 C] in

theorem fiber_geometry (Z : K →ₗ[F2] C) (Y : Fiber (U := U) Z) :
    Disjoint (base U K C).range (Y.val - base U K C).range ∧
      (base U K C).ker ⊔ (Y.val - base U K C).ker = ⊤ := by
  apply (RankAdditivity.finrank_add_eq_iff (base U K C) (Y.val - base U K C)).mp
  have heq : base U K C + (Y.val - base U K C) = Y.val := by abel
  rw [heq, finrank_base]
  exact Y.property.1

omit [FiniteDimensional F2 C] in
theorem snd_mem_range (Z : K →ₗ[F2] C) (Y : Fiber (U := U) Z) (p : U × K) :
    (Y.val p).2 ∈ Z.range := by
  have hp : p ∈ (base U K C).ker ⊔ (Y.val - base U K C).ker := by
    rw [(fiber_geometry Z Y).2]
    trivial
  rcases Submodule.mem_sup.mp hp with ⟨a, ha, b, hb, hab⟩
  have ha0 : a.1 = 0 := congrArg Prod.fst ha
  have haeq : a = (0, a.2) := Prod.ext ha0 rfl
  have hDb : Y.val b = base U K C b := sub_eq_zero.mp hb
  refine ⟨a.2, ?_⟩
  have hcomp := LinearMap.congr_fun Y.property.2 a.2
  calc
    Z a.2 = (Y.val (0, a.2)).2 := hcomp.symm
    _ = (Y.val a).2 := congrArg (fun q => (Y.val q).2) haeq.symm
    _ = (Y.val (a + b)).2 := by simp [map_add, hDb]
    _ = (Y.val p).2 := congrArg (fun q => (Y.val q).2) hab

noncomputable def linearSection (Z : K →ₗ[F2] C) : Z.range →ₗ[F2] K :=
  Classical.choose
    (Z.rangeRestrict.exists_rightInverse_of_surjective Z.range_rangeRestrict)

omit [FiniteDimensional F2 C] in
theorem section_spec (Z : K →ₗ[F2] C) (c : Z.range) :
    Z.rangeRestrict (linearSection Z c) = c :=
  LinearMap.congr_fun (Classical.choose_spec
    (Z.rangeRestrict.exists_rightInverse_of_surjective Z.range_rangeRestrict)) c

noncomputable def extractedF (Z : K →ₗ[F2] C) (Y : Fiber (U := U) Z) :
    Z.range →ₗ[F2] U :=
  (LinearMap.fst F2 U C).comp
    (Y.val.comp ((LinearMap.inr F2 U K).comp (linearSection Z)))

def extractedH (Z : K →ₗ[F2] C) (Y : Fiber (U := U) Z) :
    U →ₗ[F2] Z.range :=
  ((LinearMap.snd F2 U C).comp (Y.val.comp (LinearMap.inl F2 U K))).codRestrict
    Z.range (fun u => snd_mem_range Z Y (u, 0))

omit [FiniteDimensional F2 C] in
theorem extracted_lower (Z : K →ₗ[F2] C) (Y : Fiber (U := U) Z) (p : U × K) :
    extractedH Z Y p.1 + Z.rangeRestrict p.2 =
      ⟨(Y.val p).2, snd_mem_range Z Y p⟩ := by
  apply Subtype.ext
  change (Y.val (p.1, 0)).2 + Z p.2 = (Y.val p).2
  rw [← LinearMap.congr_fun Y.property.2 p.2]
  change (Y.val (p.1, 0)).2 + (Y.val (0, p.2)).2 = (Y.val p).2
  rw [← Prod.snd_add, ← map_add]
  simp

omit [FiniteDimensional F2 C] in
theorem difference_ext_snd (Z : K →ₗ[F2] C) (Y : Fiber (U := U) Z)
    (p q : U × K) (h : (Y.val p).2 = (Y.val q).2) :
    (Y.val - base U K C) p = (Y.val - base U K C) q := by
  let D := Y.val - base U K C
  have hbottom : (D (p - q)).2 = 0 := by
    change ((Y.val - base U K C) (p - q)).2 = 0
    simp only [LinearMap.sub_apply, map_sub, Prod.snd_sub, base_apply]
    simpa using sub_eq_zero.mpr h
  have hzero : D (p - q) = 0 := by
    apply Submodule.disjoint_def.mp (fiber_geometry Z Y).1 (D (p - q))
    · refine ⟨((D (p - q)).1, 0), ?_⟩
      exact Prod.ext rfl hbottom.symm
    · exact ⟨p - q, rfl⟩
  exact sub_eq_zero.mp (by simpa only [map_sub] using hzero)

omit [FiniteDimensional F2 C] in
theorem lift_extracted (Z : K →ₗ[F2] C) (Y : Fiber (U := U) Z) :
    lift Z (extractedF Z Y, extractedH Z Y) = Y.val := by
  apply LinearMap.ext
  intro p
  let c : Z.range := ⟨(Y.val p).2, snd_mem_range Z Y p⟩
  have hq : (Y.val (0, linearSection Z c)).2 = (Y.val p).2 := by
    calc
      (Y.val (0, linearSection Z c)).2 = Z (linearSection Z c) :=
        LinearMap.congr_fun Y.property.2 (linearSection Z c)
      _ = (c : C) := congrArg Subtype.val (section_spec Z c)
      _ = (Y.val p).2 := rfl
  have hd := congrArg Prod.fst (difference_ext_snd Z Y p (0, linearSection Z c) hq.symm)
  change (Y.val p).1 - p.1 = (Y.val (0, linearSection Z c)).1 - 0 at hd
  apply Prod.ext
  · change p.1 + extractedF Z Y
      (extractedH Z Y p.1 + Z.rangeRestrict p.2) = (Y.val p).1
    rw [extracted_lower]
    change p.1 + (Y.val (0, linearSection Z c)).1 = (Y.val p).1
    rw [sub_zero] at hd
    rw [← hd]
    abel
  · simpa using congrArg Subtype.val (extracted_lower Z Y p)

omit [FiniteDimensional F2 C]

theorem toFiber_bijective (Z : K →ₗ[F2] C) :
    Function.Bijective (toFiber (U := U) Z) := by
  constructor
  · intro P Q h
    exact lift_injective Z (congrArg Subtype.val h)
  · intro Y
    exact ⟨(extractedF Z Y, extractedH Z Y), Subtype.ext (lift_extracted Z Y)⟩

noncomputable def fiberEquiv (Z : K →ₗ[F2] C) :
    Parameters (U := U) Z ≃ Fiber (U := U) Z :=
  Equiv.ofBijective (toFiber Z) (toFiber_bijective Z)

end DFVSGames.Appendix.CompressionCount

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_AffineWitnessNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Decoder.MatrixCoordinates

open Integration.BinaryLinear Reduction
open scoped BigOperators Classical

noncomputable section
attribute [local instance] Classical.propDecidable

local instance homFintype_r589c63_1 {D F : Type*}
    [AddCommGroup D] [Module F2 D] [AddCommGroup F] [Module F2 F]
    [Fintype D] [Fintype F] : Fintype (D →ₗ[F2] F) :=
  Fintype.ofInjective (fun M : D →ₗ[F2] F => (M : D → F)) DFunLike.coe_injective
theorem mapEquiv_rankOne (k ell : ℕ) (l : ActualHomogeneous.E k →ₗ[F2] F2)
    (a : Fin ell → F2) :
    mapEquiv k ell (l.smulRight a) = Inverse.Shortcode.rankOne a (functionalEquiv k l) := by
  ext i j
  simp [Inverse.Shortcode.rankOne, mul_comm]

theorem mapEquiv_symm_add_rankOne (k ell : ℕ)
    (M : Inverse.Shortcode.Mat ell (1 + 2 * k))
    (l : ActualHomogeneous.E k →ₗ[F2] F2) (a : Fin ell → F2) :
    (mapEquiv k ell).symm (M + Inverse.Shortcode.rankOne a (functionalEquiv k l)) =
      (mapEquiv k ell).symm M + l.smulRight a := by
  apply (mapEquiv k ell).injective
  rw [LinearEquiv.apply_symm_apply, map_add, LinearEquiv.apply_symm_apply, mapEquiv_rankOne]

def coordinateTau (k : ℕ) : (Fin (1 + 2 * k) → F2) →ₗ[F2] F2 :=
  ActualHomogeneous.tau.comp (domainCoordinates k).symm.toLinearMap

theorem functionalEquiv_tau (k : ℕ) :
    functionalEquiv k ActualHomogeneous.tau =
      Inverse.Shortcode.functionalRow (coordinateTau k) := by
  ext j
  rw [functionalEquiv_apply]
  rfl

theorem mapEquiv_symm_firstBit_shift (k ell : ℕ)
    (M : Inverse.Shortcode.Mat ell (1 + 2 * k)) (a : Fin ell → F2) :
    (mapEquiv k ell).symm
        (M + Inverse.Shortcode.rankOne a (Inverse.Shortcode.functionalRow (coordinateTau k))) =
      (mapEquiv k ell).symm M + ActualHomogeneous.tau.smulRight a := by
  rw [← functionalEquiv_tau]
  exact mapEquiv_symm_add_rankOne k ell M ActualHomogeneous.tau a

theorem mapEquiv_rowAdvice (k ell r : ℕ)
    (A : (Fin ell → F2) →ₗ[F2] (Fin r → F2))
    (M : ActualHomogeneous.E k →ₗ[F2] (Fin ell → F2)) :
    mapEquiv k r (A.comp M) =
      Inverse.RowErasureMatrix.rowAdvice (LinearMap.toMatrix' A) (mapEquiv k ell M) := by
  change LinearMap.toMatrix' (A.comp (M.comp (domainCoordinates k).symm.toLinearMap)) = _
  rw [LinearMap.toMatrix'_comp]
  rfl

end
end DFVSGames.Decoder.MatrixCoordinates

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_ActualGoodRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Decoder.ActualGoodRows

open Integration.BinaryLinear Reduction ActualSource
open Inverse Inverse.RowErasure
open Inverse.Shortcode (Mat HasAffineSlice)
open scoped BigOperators Classical

noncomputable section

local instance homFintype_r589c63_2 {D F : Type*}
    [AddCommGroup D] [Module F2 D] [AddCommGroup F] [Module F2 F]
    [Fintype D] [Fintype F] : Fintype (D →ₗ[F2] F) :=
  Fintype.ofInjective (fun M : D →ₗ[F2] F => (M : D → F)) DFunLike.coe_injective
def table (S : Source) (k s d : ℕ)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (U : ActualGame.Question S k) (T : ActualHomogeneous.E k →ₗ[F2] Vector d)
    (M : Mat s (1 + 2 * k)) : Vector s :=
  TableKeysGame.unfolded S k s d labeling
    (U, ((MatrixCoordinates.mapEquiv k s).symm M).prod T)

end
end DFVSGames.Decoder.ActualGoodRows

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_RowErasureSliceUniform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Inverse.Shortcode.Slice

noncomputable section
open scoped BigOperators Matrix

variable {ell m : ℕ}

theorem difference_row_zero (S : Slice ell m) {M M₀ : Mat ell m}
    (hM : S.Contains M) (h₀ : S.Contains M₀) :
    S.rowMap.comp (Matrix.toLin' (M - M₀)) = 0 := by
  apply LinearMap.toMatrix'.injective
  rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin']
  have hrow : LinearMap.toMatrix' S.rowMap = S.rowCoefficient :=
    LinearMap.toMatrix'_toLin' S.rowCoefficient
  rw [hrow]
  ext i j
  change (∑ a, S.rowCoefficient i a * (M - M₀) a j) = 0
  simp only [Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib]
  rw [hM.1 i j, h₀.1 i j, sub_self]

theorem difference_range_le (S : Slice ell m) {M M₀ : Mat ell m}
    (hM : S.Contains M) (h₀ : S.Contains M₀) :
    LinearMap.range (Matrix.toLin' (M - M₀)) ≤ S.rowMap.ker := by
  rintro _ ⟨v, rfl⟩
  have h := LinearMap.congr_fun (S.difference_row_zero hM h₀) v
  exact h

theorem difference_vanishes_columns (S : Slice ell m) {M M₀ : Mat ell m}
    (hM : S.Contains M) (h₀ : S.Contains M₀) :
    S.columnSpan ≤ LinearMap.ker (Matrix.toLin' (M - M₀)) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  change Matrix.toLin' (M - M₀) (S.columnCoefficient i) = 0
  have he : Matrix.toLin' (M - M₀) (S.columnCoefficient i) =
      evaluate M (S.columnCoefficient i) - evaluate M₀ (S.columnCoefficient i) := by
    rw [map_sub, LinearMap.sub_apply]
    rfl
  rw [he, hM.2 i, h₀.2 i, sub_self]

theorem directionEmbedding_surjective (S : Slice ell m)
    (M₀ : Mat ell m) (h₀ : S.Contains M₀) :
    Function.Surjective (S.directionEmbedding M₀ h₀) := by
  intro M
  have hM : S.Contains M.val := by
    simpa only [points, Finset.mem_filter, Finset.mem_univ, true_and] using M.property
  obtain ⟨N, hN⟩ :=
    RowErasureSliceQuotient.exists_direction_of_row_and_column
      S.rowMap S.columnSpan (Matrix.toLin' (M.val - M₀))
      (S.difference_vanishes_columns hM h₀) (S.difference_range_le hM h₀)
  have hdir : S.directionMap N = Matrix.toLin' (M.val - M₀) := hN
  have hmat : S.directionMatrix N = M.val - M₀ := by
    unfold directionMatrix
    rw [hdir, LinearMap.toMatrix'_toLin']
  refine ⟨N, ?_⟩
  apply Subtype.ext
  change M₀ + S.directionMatrix N = M.val
  rw [hmat]
  abel

def directionEquiv (S : Slice ell m) (M₀ : Mat ell m) (h₀ : S.Contains M₀) :
    S.Directions ≃ S.points :=
  Equiv.ofBijective (S.directionEmbedding M₀ h₀)
    ⟨(S.directionEmbedding M₀ h₀).injective, S.directionEmbedding_surjective M₀ h₀⟩

@[simp] theorem directionEquiv_val (S : Slice ell m) (M₀ : Mat ell m)
    (h₀ : S.Contains M₀) (N : S.Directions) :
    (S.directionEquiv M₀ h₀ N).val = M₀ + S.directionMatrix N := rfl

end
end DFVSGames.Inverse.Shortcode.Slice

namespace DFVSGames.Inverse.RowErasureDescriptionColumnMass

noncomputable section
open DFVSGames.Inverse.Shortcode
open DFVSGames.Inverse.RowErasureDescriptions
open DFVSGames.Inverse.RowErasureMatrix
open scoped BigOperators Classical

def rowFiber {ell m r : ℕ} (A : RowMap ell r) (s : Mat r m) :
    Finset (Mat ell m) :=
  Finset.univ.filter fun M => rowAdvice A M = s

@[simp] theorem mem_rowFiber {ell m r : ℕ} (A : RowMap ell r) (s : Mat r m)
    (M : Mat ell m) : M ∈ rowFiber A s ↔ rowAdvice A M = s := by
  simp [rowFiber]

end
end DFVSGames.Inverse.RowErasureDescriptionColumnMass

namespace DFVSGames.Decoder.ActualEvents

open Integration.BinaryLinear Reduction ActualSource Foundations.Games
open Inverse Inverse.RowErasure
open Inverse.Shortcode (Mat)
open scoped BigOperators Classical

noncomputable section

local instance homFintype_r589c63_3 {D F : Type*}
    [AddCommGroup D] [Module F2 D] [AddCommGroup F] [Module F2 F]
    [Fintype D] [Fintype F] : Fintype (D →ₗ[F2] F) :=
  Fintype.ofInjective (fun M : D →ₗ[F2] F => (M : D → F)) DFunLike.coe_injective
abbrev Context (S : Source) (k d : ℕ) :=
  ActualGame.Question S k × (ActualHomogeneous.E k →ₗ[F2] Vector d)

abbrev Sample (S : Source) (k s d r : ℕ) :=
  Context S k d × (RowErasureDescriptions.RowMap s r × Mat s (1 + 2 * k))

abbrev FullTableSample (S : Source) (k s d r : ℕ) :=
  (ActualGame.Question S k × (Alphabet s →ₗ[F2] Vector r)) × ActualGame.Map k s d

def fullTableEquiv (S : Source) (k s d r : ℕ) :
    FullTableSample S k s d r ≃ Sample S k s d r where
  toFun p := ((p.1.1, (LinearMap.snd F2 (Alphabet s) (Vector d)).comp p.2),
    (LinearMap.toMatrix' p.1.2,
      MatrixCoordinates.mapEquiv k s ((LinearMap.fst F2 (Alphabet s) (Vector d)).comp p.2)))
  invFun q := ((q.1.1, Matrix.toLin' q.2.1),
    ((MatrixCoordinates.mapEquiv k s).symm q.2.2).prod q.1.2)
  left_inv p := by
    rcases p with ⟨⟨U, A⟩, P⟩
    apply Prod.ext
    · simp
    · apply LinearMap.ext
      intro x
      simp only [LinearEquiv.symm_apply_apply, LinearMap.prod_apply]
      rfl
  right_inv q := by
    rcases q with ⟨⟨U, T⟩, A, M⟩
    apply Prod.ext
    · apply Prod.ext rfl
      apply LinearMap.ext
      intro x
      rfl
    · apply Prod.ext
      · exact LinearMap.toMatrix'_toLin' A
      · change MatrixCoordinates.mapEquiv k s
          ((LinearMap.fst F2 (Alphabet s) (Vector d)).comp
            (((MatrixCoordinates.mapEquiv k s).symm M).prod T)) = M
        have hf : (LinearMap.fst F2 (Alphabet s) (Vector d)).comp
            (((MatrixCoordinates.mapEquiv k s).symm M).prod T) =
              (MatrixCoordinates.mapEquiv k s).symm M := by
          apply LinearMap.ext
          intro x
          rfl
        rw [hf, LinearEquiv.apply_symm_apply]

def sliceEvent (S : Source) (k s d r : ℕ)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (p : Sample S k s d r) : Bool :=
  decide ((RowErasureMatrix.family s (1 + 2 * k) r).selectedEvent
    (ActualGoodRows.table S k s d labeling p.1.1 p.1.2) α p.2.1 p.2.2)

end
end DFVSGames.Decoder.ActualEvents

namespace DFVSGames.Inverse.RowErasureDescriptions

open DFVSGames.Inverse.Shortcode

@[simp] theorem Description.withTarget_toSlice {ell m r : ℕ}
    (d : Description ell m r) (z : Vector m) (u : Vector ell) :
    (d.withTarget z u).toSlice = d.toSlice := rfl

@[simp] theorem Description.withTarget_coefficient {ell m r : ℕ}
    (d : Description ell m r) (z : Vector m) (u : Vector ell) :
    (d.withTarget z u).coefficient = z := rfl

@[simp] theorem Description.withTarget_intercept {ell m r : ℕ}
    (d : Description ell m r) (z : Vector m) (u : Vector ell) :
    (d.withTarget z u).intercept = u := rfl

end DFVSGames.Inverse.RowErasureDescriptions

namespace DFVSGames.Inverse.RowErasureMatrix

open DFVSGames.Inverse.Shortcode
open DFVSGames.Inverse.RowErasure
open DFVSGames.Inverse.RowErasureDescriptions

noncomputable section

variable {ell m r : ℕ}

theorem exists_normalizedChosenDescription
    (f : Mat ell m → Vector ell) (α : ℝ) (A : RowMap ell r) (S : Mat r m)
    (hgood : (family ell m r).GoodAdvice f α A S)
    (e : Vector m →ₗ[F2] F2)
    (hfold : ∀ (h : Vector ell) M,
      f (M + rankOne h (functionalRow e)) = f M + h)
    (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (ell - r) < α / 8) :
    let d₀ := (family ell m r).chosenDescription f α A S hgood
    ∃ d : Description ell m r,
      (family ell m r).rowMap d = A ∧
      (family ell m r).rowValue d = S ∧
      ((family ell m r).points d).Nonempty ∧
      α / 2 ≤ (family ell m r).agreement f d ∧
      e d.coefficient = 1 ∧
      d.toSlice = d₀.toSlice ∧
      (family ell m r).agreement f d = (family ell m r).agreement f d₀ ∧
      ∀ M, M ∈ (family ell m r).points d₀ →
        (family ell m r).target d M = (family ell m r).target d₀ M := by
  classical
  let d₀ := (family ell m r).chosenDescription f α A S hgood
  obtain ⟨hrow, hvalue, hnonempty, hagree⟩ :=
    (family ell m r).chosenDescription_spec f α A S hgood
  obtain ⟨M₀, hM₀⟩ := hnonempty
  have hcontains : d₀.toSlice.Contains M₀ := by
    exact (Finset.mem_filter.mp hM₀).2
  have hagree' : α / 2 ≤ d₀.toSlice.affineAgreement f d₀.coefficient d₀.intercept := by
    exact (family_agreement d₀ f) ▸ hagree
  obtain ⟨z, u, hfirst, heq, htarget⟩ :=
    d₀.toSlice.first_bit_normalization M₀ hcontains e f d₀.coefficient d₀.intercept
      (fun h M => hfold h M) α hα hagree' hsmall
  have heq' : (family ell m r).agreement f (d₀.withTarget z u) =
      (family ell m r).agreement f d₀ := by
    rw [family_agreement, family_agreement]
    exact heq
  refine ⟨d₀.withTarget z u, hrow, hvalue, ⟨M₀, hM₀⟩, ?_, hfirst, rfl, heq', ?_⟩
  · exact heq'.symm ▸ hagree
  · intro M hM
    exact htarget M (Finset.mem_filter.mp hM).2

def normalizedChosenDescription
    (f : Mat ell m → Vector ell) (α : ℝ) (A : RowMap ell r) (S : Mat r m)
    (hgood : (family ell m r).GoodAdvice f α A S)
    (e : Vector m →ₗ[F2] F2)
    (hfold : ∀ (h : Vector ell) M,
      f (M + rankOne h (functionalRow e)) = f M + h)
    (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (ell - r) < α / 8) :
    Description ell m r :=
  Classical.choose (exists_normalizedChosenDescription f α A S hgood e hfold hα hsmall)

theorem normalizedChosenDescription_spec
    (f : Mat ell m → Vector ell) (α : ℝ) (A : RowMap ell r) (S : Mat r m)
    (hgood : (family ell m r).GoodAdvice f α A S)
    (e : Vector m →ₗ[F2] F2)
    (hfold : ∀ (h : Vector ell) M,
      f (M + rankOne h (functionalRow e)) = f M + h)
    (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (ell - r) < α / 8) :
    let d₀ := (family ell m r).chosenDescription f α A S hgood
    let d := normalizedChosenDescription f α A S hgood e hfold hα hsmall
    (family ell m r).rowMap d = A ∧
      (family ell m r).rowValue d = S ∧
      ((family ell m r).points d).Nonempty ∧
      α / 2 ≤ (family ell m r).agreement f d ∧
      e d.coefficient = 1 ∧
      d.toSlice = d₀.toSlice ∧
      (family ell m r).agreement f d = (family ell m r).agreement f d₀ ∧
      ∀ M, M ∈ (family ell m r).points d₀ →
        (family ell m r).target d M = (family ell m r).target d₀ M :=
  Classical.choose_spec
    (exists_normalizedChosenDescription f α A S hgood e hfold hα hsmall)

end
end DFVSGames.Inverse.RowErasureMatrix

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_SelectedPolicies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace DFVSGames.Decoder.SelectedPolicies

open DFVSGames.Integration.BinaryLinear DFVSGames.Reduction
open DFVSGames.Inverse
open ActualSource VisiblePolicies MatrixCoordinates
open scoped BigOperators Classical

attribute [local instance] Classical.propDecidable

variable {k s d r : ℕ}

def matrixTable (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (occ : ActualGame.Question S k)
    (T : ActualHomogeneous.E k →ₗ[F2] Vector d)
    (M : Shortcode.Mat s (1 + 2 * k)) : Alphabet s :=
  TableKeysGame.unfolded S k s d labeling
    (occ, ((mapEquiv k s).symm M).prod T)

def fullTable (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (q : LeftInput S k s d (Vector r)) : Shortcode.Mat s (1 + 2 * k) → Alphabet s :=
  matrixTable S labeling q.occurrences q.complement

theorem matrixTable_fold (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (occ : ActualGame.Question S k)
    (T : ActualHomogeneous.E k →ₗ[F2] Vector d)
    (h : Alphabet s) (M : Shortcode.Mat s (1 + 2 * k)) :
    matrixTable S labeling occ T
        (M + Shortcode.rankOne h (Shortcode.functionalRow (coordinateTau k))) =
      matrixTable S labeling occ T M + h := by
  unfold matrixTable
  rw [mapEquiv_symm_firstBit_shift]
  have hprod : (((mapEquiv k s).symm M + ActualHomogeneous.tau.smulRight h).prod T) =
      ((mapEquiv k s).symm M).prod T +
        ActualHomogeneous.tau.smulRight (h, (0 : Vector d)) := by
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · rfl
    · simp
  rw [hprod]
  exact TableKeysGame.unfolded_equivariant S k s d labeling
    (occ, ((mapEquiv k s).symm M).prod T) h

def GoodAdvice (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (q : LeftInput S k s d (Vector r)) : Prop :=
  (RowErasureMatrix.family s (1 + 2 * k) r).GoodAdvice (fullTable S labeling q) α
    (LinearMap.toMatrix' q.rowMap) (mapEquiv k r q.rows)

def normalizedDescription (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (q : LeftInput S k s d (Vector r)) (hgood : GoodAdvice S labeling α q) :
    RowErasureDescriptions.Description s (1 + 2 * k) r :=
  RowErasureMatrix.normalizedChosenDescription (fullTable S labeling q) α
    (LinearMap.toMatrix' q.rowMap) (mapEquiv k r q.rows) hgood (coordinateTau k)
    (matrixTable_fold S labeling q.occurrences q.complement) hα hsmall

theorem normalizedDescription_spec (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (q : LeftInput S k s d (Vector r)) (hgood : GoodAdvice S labeling α q) :
    let F := RowErasureMatrix.family s (1 + 2 * k) r
    let D := normalizedDescription S labeling α hα hsmall q hgood
    let D₀ := F.chosenDescription (fullTable S labeling q) α
      (LinearMap.toMatrix' q.rowMap) (mapEquiv k r q.rows) hgood
    F.rowMap D = LinearMap.toMatrix' q.rowMap ∧
      F.rowValue D = mapEquiv k r q.rows ∧
      (F.points D).Nonempty ∧
      α / 2 ≤ F.agreement (fullTable S labeling q) D ∧
      coordinateTau k D.coefficient = 1 ∧
      D.toSlice = D₀.toSlice ∧
      F.agreement (fullTable S labeling q) D = F.agreement (fullTable S labeling q) D₀ ∧
      ∀ M, M ∈ F.points D₀ → F.target D M = F.target D₀ M :=
  RowErasureMatrix.normalizedChosenDescription_spec (fullTable S labeling q) α
    (LinearMap.toMatrix' q.rowMap) (mapEquiv k r q.rows) hgood (coordinateTau k)
    (matrixTable_fold S labeling q.occurrences q.complement) hα hsmall

def normalizedResponse (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (q : LeftInput S k s d (Vector r)) (hgood : GoodAdvice S labeling α q) :
    ResponseWitness k where
  columns := (normalizedDescription S labeling α hα hsmall q hgood).toSlice.columnSpan.map
    (domainCoordinates k).symm.toLinearMap
  coefficient := (domainCoordinates k).symm
    (normalizedDescription S labeling α hα hsmall q hgood).coefficient
  firstBit := (normalizedDescription_spec S labeling α hα hsmall q hgood).2.2.2.2.1

end DFVSGames.Decoder.SelectedPolicies
end

namespace DFVSGames.Decoder.ActualSeedEvents

open Integration.BinaryLinear Reduction ActualSource Foundations.Games
open scoped BigOperators Classical

noncomputable section
attribute [local instance] Fintype.ofFinite

local instance homFintype_r589c63_4 {D F : Type*}
    [AddCommGroup D] [Module F2 D] [AddCommGroup F] [Module F2 F]
    [Fintype D] [Fintype F] : Fintype (D →ₗ[F2] F) :=
  Fintype.ofInjective (fun M : D →ₗ[F2] F => (M : D → F)) DFunLike.coe_injective
abbrev Seed (S : Source) (k s d r : ℕ) :=
  AdviceLaw.FullSeed k (Fin S.occurrences) (Alphabet s) (Vector d) (Vector r)

def draw {S : Source} {k s d r : ℕ} (x : Seed S k s d r) :=
  AdviceLaw.seedToActualDraw x.1.1 x.1.2 x.2

def pad (S : Source) (k s d r : ℕ) (x : Seed S k s d r) : ActualEvents.Sample S k s d r :=
  ActualEvents.fullTableEquiv S k s d r
    (AdviceLaw.fullSeedPad (fun i => toBit (ActualGame.rhs S i)) x)

def slice (S : Source) (k s d r : ℕ)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s)) (α : ℝ) :
    Seed S k s d r → Bool :=
  fun x => ActualEvents.sliceEvent S k s d r labeling α (pad S k s d r x)

theorem slice_eq_selectedEvent (S : Source) (k s d r : ℕ)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s)) (α : ℝ)
    (x : Seed S k s d r) :
    slice S k s d r labeling α x = decide
      ((Inverse.RowErasureMatrix.family s (1 + 2 * k) r).selectedEvent
        (SelectedPolicies.fullTable S labeling
          (AdviceExperiment.leftObservation (ActualGame.rhs S) (draw x))) α
        (LinearMap.toMatrix' (draw x).rowMap)
        (MatrixCoordinates.mapEquiv k s (AdviceExperiment.paddedMatrix (ActualGame.rhs S) (draw x)))) :=
  rfl

end
end DFVSGames.Decoder.ActualSeedEvents

noncomputable section

namespace DFVSGames.Decoder.SelectedDecoding

open DFVSGames.Integration.BinaryLinear DFVSGames.Reduction DFVSGames.Soundness
open DFVSGames.Inverse
open ActualSource VisiblePolicies SelectedPolicies MatrixCoordinates
open scoped BigOperators Classical

attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

variable {k s d r : ℕ}

local instance homFintype_r589c63_5 {D F : Type*}
    [AddCommGroup D] [Module F2 D] [AddCommGroup F] [Module F2 F]
    [Fintype D] [Fintype F] : Fintype (D →ₗ[F2] F) :=
  Fintype.ofInjective (fun M : D →ₗ[F2] F => (M : D → F)) DFunLike.coe_injective
theorem selectedEvent_iff_normalized (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (q : LeftInput S k s d (Vector r)) (hgood : GoodAdvice S labeling α q)
    (M : Shortcode.Mat s (1 + 2 * k))
    (hrow : RowErasureMatrix.rowAdvice (LinearMap.toMatrix' q.rowMap) M =
      mapEquiv k r q.rows) :
    (RowErasureMatrix.family s (1 + 2 * k) r).selectedEvent
        (fullTable S labeling q) α (LinearMap.toMatrix' q.rowMap) M ↔
      M ∈ (RowErasureMatrix.family s (1 + 2 * k) r).points
        (normalizedDescription S labeling α hα hsmall q hgood) := by
  have he := (RowErasureMatrix.family s (1 + 2 * k) r).selectedEvent_iff_of_advice
    (fullTable S labeling q) α (LinearMap.toMatrix' q.rowMap)
    (mapEquiv k r q.rows) hgood M hrow
  obtain ⟨_, _, _, _, _, hslice, _, _⟩ :=
    normalizedDescription_spec S labeling α hα hsmall q hgood
  rw [show (RowErasureMatrix.family s (1 + 2 * k) r).points
      (normalizedDescription S labeling α hα hsmall q hgood) =
      (RowErasureMatrix.family s (1 + 2 * k) r).points
        ((RowErasureMatrix.family s (1 + 2 * k) r).chosenDescription
          (fullTable S labeling q) α (LinearMap.toMatrix' q.rowMap)
          (mapEquiv k r q.rows) hgood) from congrArg Shortcode.Slice.points hslice]
  exact he

end DFVSGames.Decoder.SelectedDecoding
end

noncomputable section

namespace DFVSGames.Decoder.ProjectedColumnSlice

open DFVSGames.Integration.BinaryLinear DFVSGames.Reduction DFVSGames.Soundness
open DFVSGames.Inverse
open ActualSource VisiblePolicies SelectedPolicies MatrixCoordinates
open scoped BigOperators Classical

attribute [local instance] Classical.propDecidable

variable {k s d r : ℕ}

section Algebra

variable {V : Type*} [AddCommGroup V] [Module F2 V]

theorem column_agreement_iff (Q : Submodule F2 (Vector (1 + 2 * k)))
    (π : ActualHomogeneous.E k →ₗ[F2] V) (M Mstar : V →ₗ[F2] Alphabet s) :
    (∀ x ∈ Q, M (π ((domainCoordinates k).symm x)) =
      Mstar (π ((domainCoordinates k).symm x))) ↔
      ∀ v ∈ (Q.map (domainCoordinates k).symm.toLinearMap).map π, M v = Mstar v := by
  constructor
  · intro h v hv
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hv
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hz
    exact h x hx
  · intro h x hx
    apply h
    exact Submodule.mem_map.mpr ⟨(domainCoordinates k).symm x,
      Submodule.mem_map.mpr ⟨x, hx, rfl⟩, rfl⟩

theorem contains_padded_iff
    (D : RowErasureDescriptions.Description s (1 + 2 * k) r)
    (A : Alphabet s →ₗ[F2] Vector r)
    (hDrow : (RowErasureMatrix.family s (1 + 2 * k) r).rowMap D = LinearMap.toMatrix' A)
    (π : ActualHomogeneous.E k →ₗ[F2] V) (Mstar : V →ₗ[F2] Alphabet s)
    (hstar : mapEquiv k s (Mstar.comp π) ∈ D.toSlice.points)
    (M : V →ₗ[F2] Alphabet s) (hrow : A.comp M = A.comp Mstar) :
    mapEquiv k s (M.comp π) ∈ D.toSlice.points ↔
      ∀ v ∈ (D.toSlice.columnSpan.map (domainCoordinates k).symm.toLinearMap).map π,
        M v = Mstar v := by
  have hr : D.toSlice.rowMap = A := by
    change Matrix.toLin' D.1 = A
    change D.1 = LinearMap.toMatrix' A at hDrow
    rw [hDrow, Matrix.toLin'_toMatrix']
  have hc (N : V →ₗ[F2] Alphabet s) :
      Matrix.toLin' (mapEquiv k s (N.comp π)) =
        (N.comp π).comp (domainCoordinates k).symm.toLinearMap := by
    rw [mapEquiv_apply, Matrix.toLin'_toMatrix']
  have hs : D.toSlice.Contains (mapEquiv k s (Mstar.comp π)) :=
    (Finset.mem_filter.mp hstar).2
  have he := D.toSlice.contains_iff_inSlice (mapEquiv k s (Mstar.comp π)) hs
    (mapEquiv k s (M.comp π))
  rw [AffineWitness.InSlice, hr, hc, hc] at he
  have hrows : A.comp ((M.comp π).comp (domainCoordinates k).symm.toLinearMap) =
      A.comp ((Mstar.comp π).comp (domainCoordinates k).symm.toLinearMap) := by
    apply LinearMap.ext
    intro x
    exact LinearMap.congr_fun hrow (π ((domainCoordinates k).symm x))
  constructor
  · intro h
    have hh := he.mp (Finset.mem_filter.mp h).2
    exact (column_agreement_iff D.toSlice.columnSpan π M Mstar).mp hh.2
  · intro h
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, he.mpr ⟨hrows,
      (column_agreement_iff D.toSlice.columnSpan π M Mstar).mpr h⟩⟩

end Algebra

end DFVSGames.Decoder.ProjectedColumnSlice
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_VisibleTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Decoder.ActualConditionalLaw

open Integration.BinaryLinear Reduction ActualSource Foundations.Games
open scoped BigOperators Classical

noncomputable section
attribute [local instance] Fintype.ofFinite

local instance homFintype {D F : Type*}
    [AddCommGroup D] [Module F2 D] [AddCommGroup F] [Module F2 F]
    [Fintype D] [Fintype F] : Fintype (D →ₗ[F2] F) :=
  Fintype.ofInjective (fun M : D →ₗ[F2] F => (M : D → F)) DFunLike.coe_injective

end
end DFVSGames.Decoder.ActualConditionalLaw

noncomputable section

namespace DFVSGames.Decoder.SelectedFiberLaw

open DFVSGames.Integration.BinaryLinear DFVSGames.Reduction DFVSGames.Soundness
open DFVSGames.Inverse DFVSGames.Foundations.Games
open ActualSource VisiblePolicies SelectedPolicies MatrixCoordinates ActualSeedEvents
open scoped BigOperators Classical

attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

variable {k s d r : ℕ}

local instance homFintype_r589c63_6 {D F : Type*}
    [AddCommGroup D] [Module F2 D] [AddCommGroup F] [Module F2 F]
    [Fintype D] [Fintype F] : Fintype (D →ₗ[F2] F) :=
  Fintype.ofInjective (fun M : D →ₗ[F2] F => (M : D → F)) DFunLike.coe_injective
def datumLeft (S : Source) (data : Datum S k s d r) : LeftInput S k s d (Vector r) :=
  AdviceExperiment.leftObservation (ActualGame.rhs S) (AdviceLaw.completeDraw data 0)

def datumMatrix (S : Source) (data : Datum S k s d r) (N : AdviceLaw.PrivateMap data) :=
  (AdviceLaw.completeDraw data N).hiddenMatrix

def datumProjection (S : Source) (data : Datum S k s d r) :=
  AdviceExperiment.projection (ActualGame.rhs S) (AdviceLaw.completeDraw data 0)

theorem datumLeft_eq (S : Source) (data : Datum S k s d r) (N : AdviceLaw.PrivateMap data) :
    AdviceExperiment.leftObservation (ActualGame.rhs S) (AdviceLaw.completeDraw data N) =
      datumLeft S data := by
  unfold datumLeft
  rw [AdviceLaw.completeDraw_left, AdviceLaw.completeDraw_left]

theorem datumMatrix_rows (S : Source) (data : Datum S k s d r) (N : AdviceLaw.PrivateMap data) :
    data.1.2.comp (datumMatrix S data N) = data.2.2.2.val :=
  AdviceLaw.completeDraw_rows data N

theorem datumMatrix_rowAdvice (S : Source) (data : Datum S k s d r)
    (N : AdviceLaw.PrivateMap data) :
    RowErasureMatrix.rowAdvice (LinearMap.toMatrix' data.1.2)
        (mapEquiv k s ((datumMatrix S data N).comp (datumProjection S data))) =
      mapEquiv k r (datumLeft S data).rows := by
  rw [← mapEquiv_rowAdvice]
  change mapEquiv k r ((data.1.2.comp (datumMatrix S data N)).comp (datumProjection S data)) =
    mapEquiv k r ((data.1.2.comp (datumMatrix S data 0)).comp (datumProjection S data))
  rw [datumMatrix_rows, datumMatrix_rows] ; rfl

theorem slice_assemble_iff (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (data : Datum S k s d r) (hgood : GoodAdvice S labeling α (datumLeft S data))
    (N : AdviceLaw.PrivateMap data) :
    slice S k s d r labeling α (AdviceLaw.completeAssemble data N) = true ↔
      mapEquiv k s ((datumMatrix S data N).comp (datumProjection S data)) ∈
        (normalizedDescription S labeling α hα hsmall (datumLeft S data) hgood).toSlice.points := by
  rw [slice_eq_selectedEvent]
  change decide ((RowErasureMatrix.family s (1 + 2 * k) r).selectedEvent
      (fullTable S labeling (AdviceExperiment.leftObservation (ActualGame.rhs S)
        (AdviceLaw.completeDraw data N))) α (LinearMap.toMatrix' data.1.2)
      (mapEquiv k s ((datumMatrix S data N).comp (datumProjection S data)))) = true ↔ _
  rw [datumLeft_eq, decide_eq_true_eq]
  exact SelectedDecoding.selectedEvent_iff_normalized S labeling α hα hsmall
    (datumLeft S data) hgood _ (datumMatrix_rowAdvice S data N)

def selectedPrivateEquiv (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (data : Datum S k s d r) (hgood : GoodAdvice S labeling α (datumLeft S data))
    (Nstar : AdviceLaw.PrivateMap data)
    (hstar : slice S k s d r labeling α (AdviceLaw.completeAssemble data Nstar) = true) :
    {N : AdviceLaw.PrivateMap data //
      slice S k s d r labeling α (AdviceLaw.completeAssemble data N) = true} ≃
      RowErasureSliceQuotient.AffineSlice data.1.2
        ((normalizedResponse S labeling α hα hsmall (datumLeft S data) hgood).columns.map
          (datumProjection S data)) (datumMatrix S data Nstar) := by
  let D := normalizedDescription S labeling α hα hsmall (datumLeft S data) hgood
  let e := AdviceFibers.rowFiberEquiv data.1.2 data.2.2.2.val
    (AdviceFibers.observedBase data.1.2 data.2.2.2)
    (AdviceFibers.observedBase_property data.1.2 data.2.2.2)
  have hs : mapEquiv k s ((datumMatrix S data Nstar).comp (datumProjection S data)) ∈ D.toSlice.points :=
    (slice_assemble_iff S labeling α hα hsmall data hgood Nstar).mp hstar
  have hrow (N : AdviceLaw.PrivateMap data) :
      data.1.2.comp (datumMatrix S data N) = data.1.2.comp (datumMatrix S data Nstar) := by
    rw [datumMatrix_rows, datumMatrix_rows]
  let lift := fun M : RowErasureSliceQuotient.AffineSlice data.1.2
      ((normalizedResponse S labeling α hα hsmall (datumLeft S data) hgood).columns.map
        (datumProjection S data)) (datumMatrix S data Nstar) =>
    e.symm ⟨M.val, M.property.1.trans (datumMatrix_rows S data Nstar)⟩
  have hlift (M) : datumMatrix S data (lift M) = M.val :=
    congrArg Subtype.val (e.apply_symm_apply ⟨M.val, M.property.1.trans (datumMatrix_rows S data Nstar)⟩)
  refine {
    toFun := fun N => ⟨datumMatrix S data N.val, hrow N.val, ?_⟩
    invFun := fun M => ⟨lift M, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · exact (ProjectedColumnSlice.contains_padded_iff D data.1.2
      (normalizedDescription_spec S labeling α hα hsmall (datumLeft S data) hgood).1
      (datumProjection S data) (datumMatrix S data Nstar) hs
      (datumMatrix S data N.val) (hrow N.val)).mp
        ((slice_assemble_iff S labeling α hα hsmall data hgood N.val).mp N.property)
  · apply (slice_assemble_iff S labeling α hα hsmall data hgood (lift M)).mpr
    rw [hlift]
    exact (ProjectedColumnSlice.contains_padded_iff D data.1.2
      (normalizedDescription_spec S labeling α hα hsmall (datumLeft S data) hgood).1
      (datumProjection S data) (datumMatrix S data Nstar) hs M.val M.property.1).mpr M.property.2
  · intro N
    apply Subtype.ext
    exact e.symm_apply_apply N.val
  · intro M
    apply Subtype.ext
    exact hlift M

@[simp] theorem selectedPrivateEquiv_val (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (data : Datum S k s d r) (hgood : GoodAdvice S labeling α (datumLeft S data))
    (Nstar : AdviceLaw.PrivateMap data)
    (hstar : slice S k s d r labeling α (AdviceLaw.completeAssemble data Nstar) = true)
    (N : {N : AdviceLaw.PrivateMap data //
      slice S k s d r labeling α (AdviceLaw.completeAssemble data N) = true}) :
    (selectedPrivateEquiv S labeling α hα hsmall data hgood Nstar hstar N).val =
      datumMatrix S data N.val := rfl

end DFVSGames.Decoder.SelectedFiberLaw
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_CoordinateTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Appendix.FullCompression

open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Appendix.CoordinateTransport
open Module

noncomputable section

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]

def compression (X Y : E →ₗ[F2] F) : X.ker →ₗ[F2] (F ⧸ X.range) :=
  X.range.mkQ.comp (Y.comp X.ker.subtype)

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] in
@[simp] theorem compression_apply (X Y : E →ₗ[F2] F) (k : X.ker) :
    compression X Y k = X.range.mkQ (Y k) := rfl

def Fiber (X : E →ₗ[F2] F) (Z : X.ker →ₗ[F2] (F ⧸ X.range)) :=
  {Y : E →ₗ[F2] F // finrank F2 Y.range =
      finrank F2 X.range + finrank F2 (Y - X).range ∧ compression X Y = Z}

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] in
theorem fiber_condition_iff (X Y : E →ₗ[F2] F)
    (Z : X.ker →ₗ[F2] (F ⧸ X.range))
    (P : Submodule F2 E) (hP : IsCompl X.ker P)
    (C : Submodule F2 F) (hC : IsCompl X.range C) :
    (finrank F2 Y.range = finrank F2 X.range + finrank F2 (Y - X).range ∧
      compression X Y = Z) ↔
    (finrank F2 (toBlocks X P hP C hC Y).range = finrank F2 X.range +
      finrank F2 (toBlocks X P hP C hC Y - CompressionCount.base X.range X.ker C).range ∧
      CompressionCount.compress (toBlocks X P hP C hC Y) =
        (X.range.quotientEquivOfIsCompl C hC).toLinearMap.comp Z) := by
  have hy := finrank_toBlocks X Y P hP C hC
  have hd := finrank_toBlocks X (Y - X) P hP C hC
  rw [map_sub, toBlocks_base] at hd
  change finrank F2 (toBlocks X P hP C hC Y - CompressionCount.base X.range X.ker C).range =
    finrank F2 (Y - X).range at hd
  rw [hy, hd]
  refine and_congr_right (fun _ => ?_)
  constructor
  · intro hz
    apply LinearMap.ext
    intro k
    change (toBlocks X P hP C hC Y (0, k)).2 =
      X.range.quotientEquivOfIsCompl C hC (Z k)
    rw [compressed_toBlocks]
    exact congrArg (X.range.quotientEquivOfIsCompl C hC)
      (DFunLike.congr_fun hz k)
  · intro hz
    apply LinearMap.ext
    intro k
    apply (X.range.quotientEquivOfIsCompl C hC).injective
    have h := DFunLike.congr_fun hz k
    change (toBlocks X P hP C hC Y (0, k)).2 =
      X.range.quotientEquivOfIsCompl C hC (Z k) at h
    rw [compressed_toBlocks] at h
    exact h

def fiberEquiv (X : E →ₗ[F2] F) (Z : X.ker →ₗ[F2] (F ⧸ X.range))
    (P : Submodule F2 E) (hP : IsCompl X.ker P)
    (C : Submodule F2 F) (hC : IsCompl X.range C) :
    Fiber X Z ≃ CompressionCount.Fiber (U := X.range)
      ((X.range.quotientEquivOfIsCompl C hC).toLinearMap.comp Z) :=
  (toBlocks X P hP C hC).toEquiv.subtypeEquiv
    (fun Y => fiber_condition_iff X Y Z P hP C hC)

end

end DFVSGames.Appendix.FullCompression

namespace DFVSGames.Appendix.SubspaceCounting

open Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Module.Finite K V]

variable {U : Type*} [AddCommGroup U] [Module K U] [Module.Finite K U]

omit [Module.Finite K V] [Module.Finite K U] in
@[simp] theorem quotientImageMap_mk (Y X : U →ₗ[K] V)
    (hker : LinearMap.ker Y ≤ LinearMap.ker X)
    (himage : LinearMap.range X ≤ LinearMap.range Y) (u : U) :
    (quotientImageMap Y X hker himage ((LinearMap.ker Y).mkQ u) : V) = X u := rfl

end DFVSGames.Appendix.SubspaceCounting

noncomputable section
namespace DFVSGames.Appendix.WeightedFourthMoment

open Module
open scoped BigOperators
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Appendix.RankAdditivity (RankBelow)
attribute [local instance] Classical.propDecidable

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)]

abbrev rank (X : E →ₗ[F2] F) : ℕ := finrank F2 X.range

@[instance_reducible] def vectorFintype (V : Type*) [AddCommGroup V] [Module F2 V]
    [FiniteDimensional F2 V] : Fintype V :=
  Fintype.ofEquiv (Fin (finrank F2 V) → F2) (Module.finBasis F2 V).equivFun.symm.toEquiv

@[instance_reducible] def compressedFintype (X : E →ₗ[F2] F) : Fintype (X.ker →ₗ[F2] (F ⧸ X.range)) := by
  classical
  letI := vectorFintype X.ker
  letI := vectorFintype (F ⧸ X.range)
  exact Fintype.ofInjective DFunLike.coe DFunLike.coe_injective

def energy (a : (E →ₗ[F2] F) → ℝ) (X : E →ₗ[F2] F) : ℝ := by
  classical
  letI := compressedFintype X
  exact ∑ Z, (∑ Y, if RankBelow X Y ∧ FullCompression.compression X Y = Z
    then a Y else 0)^2

end DFVSGames.Appendix.WeightedFourthMoment
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_Derivatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace DFVSGames.Appendix.Derivatives
open scoped BigOperators
open DFVSGames.Fourier.MatrixCharacters DFVSGames.Fourier.MatrixFourier
attribute [local instance] Classical.propDecidable

variable {E F : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

def mapDerivative (X : F →ₗ[F2] E) (f : (E →ₗ[F2] F) → ℝ) :
    DFVSGames.Fourier.MatrixRestrictions.Parameter X.range X.ker → ℝ :=
  DFVSGames.Fourier.MatrixRestrictions.restrict (rankProjector X f) X.range X.ker 0

end DFVSGames.Appendix.Derivatives
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_A4IndexCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Fourier.MatrixFourier
open DFVSGames.Appendix.Derivatives

namespace DFVSGames.Appendix.OperatorPartitions

attribute [local instance] Classical.propDecidable

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

variable [Finite E] [Finite F]

open DFVSGames.Appendix.LinearIdentities
open DFVSGames.Appendix.RankAdditivity

abbrev A4GeometricIndex (A : Submodule F2 E) (B : Submodule F2 F) :=
  A4IndexCount.Index A B

def a4Mask (A : Submodule F2 E) (B : Submodule F2 F)
    (i : A4GeometricIndex A B) (Y : F →ₗ[F2] E) : Prop :=
  Hybrid Y i.val.1 i.val.2.1 ∧
    RankBelow i.val.2.2 (compress Y i.val.1 i.val.2.1)

def A5Geometry (X : F →ₗ[F2] E) (A : Submodule F2 E) (B : Submodule F2 F)
    (p : Submodule F2 E × Submodule F2 F) : Prop :=
  Disjoint p.1 X.range ∧ p.1 ⊔ X.range = A ∧
    p.2 ⊔ X.ker = ⊤ ∧ p.2 ⊓ X.ker = B

abbrev A5GeometricIndex (X : F →ₗ[F2] E)
    (A : Submodule F2 E) (B : Submodule F2 F) :=
  {p : Submodule F2 E × Submodule F2 F // A5Geometry X A B p}

def a5Mask (X : F →ₗ[F2] E) (A : Submodule F2 E) (B : Submodule F2 F)
    (i : A5GeometricIndex X A B) (Y : F →ₗ[F2] E) : Prop :=
  Hybrid Y i.val.1 i.val.2 ∧
    RankBelow (compress X i.val.1 i.val.2) (compress Y i.val.1 i.val.2)

def a5OuterMask (X : F →ₗ[F2] E) (A : Submodule F2 E)
    (B : Submodule F2 F) (Y : F →ₗ[F2] E) : Prop :=
  RankBelow X Y ∧ Hybrid (compress Y X.range X.ker)
    (A.map X.range.mkQ) (B.comap X.ker.subtype)

end DFVSGames.Appendix.OperatorPartitions
end

noncomputable section

namespace DFVSGames.Appendix.RestrictionTransport

open scoped BigOperators
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Fourier.MatrixRestrictions

section Nested

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]

def nestedEmbedding (A : Submodule F2 E) (B : Submodule F2 F)
    (C : Submodule F2 (E ⧸ A)) (D : Submodule F2 B) :
    Parameter C D →ₗ[F2] (E →ₗ[F2] F) :=
  (embedding A B).comp (embedding C D)

end Nested

end DFVSGames.Appendix.RestrictionTransport

end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_NaturalTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Fourier
open DFVSGames.Appendix.Derivatives
open DFVSGames.Appendix.OperatorPartitions
open DFVSGames.Appendix.LinearIdentities
open DFVSGames.Appendix.RankAdditivity

namespace DFVSGames.Appendix.OperatorNorm

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Finite E] [Finite F]

local instance quotientFinite (A : Submodule F2 E) : Finite (E ⧸ A) :=
  Finite.of_surjective A.mkQ A.mkQ_surjective

local instance compressedDualFintype (A : Submodule F2 E) (B : Submodule F2 F) :
    Fintype (B →ₗ[F2] (E ⧸ A)) := by
  classical
  letI : Fintype B := Fintype.ofFinite _
  letI : Fintype (E ⧸ A) := Fintype.ofFinite _
  exact Fintype.ofInjective (fun L : B →ₗ[F2] (E ⧸ A) => (L : B → E ⧸ A))
    DFunLike.coe_injective

end DFVSGames.Appendix.OperatorNorm
end

noncomputable section
namespace DFVSGames.Appendix.NaturalTransport
open scoped BigOperators
open DFVSGames.Fourier.MatrixCharacters DFVSGames.Fourier.MatrixFourier
open DFVSGames.Fourier.MatrixRestrictions
open DFVSGames.Appendix.Derivatives DFVSGames.Appendix.RankAdditivity
attribute [local instance] Classical.propDecidable

attribute [local instance] OAI.DFVSGames.Appendix.NaturalTransport.naturalTransportQuotientFinite
local instance naturalTransportCompressedDualFintype
    {U V : Type*} [AddCommGroup U] [Module F2 U]
    [AddCommGroup V] [Module F2 V] [Finite U] [Finite V]
    (A : Submodule F2 U) (B : Submodule F2 V) : Fintype (B →ₗ[F2] (U ⧸ A)) :=
  OperatorNorm.compressedDualFintype A B

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Finite E] [Finite F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

def parameterFactor (A : Submodule F2 E) (B : Submodule F2 F)
    (C : Submodule F2 (E ⧸ A)) (D : Submodule F2 B) :
    Parameter C D ≃ₗ[F2] Parameter (C.comap A.mkQ) (D.map B.subtype) :=
  LinearEquiv.arrowCongr (quotientFactor A C).symm (outputFactor B D)

end DFVSGames.Appendix.NaturalTransport
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Probability_KMSFourthMomentZoomTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace DFVSGames.Inverse.KMSAnalyticHybridEnergy

open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Fourier.MatrixCharacters (linearTraceCharacter)
open DFVSGames.Fourier.MatrixFourier
open DFVSGames.Appendix DFVSGames.Appendix.Derivatives
open KMSAnalytic KMSFourthMoment

local instance (priority := 2000) classicalSurjective_r589c63_1 {X Y : Type*} :
    DecidablePred (Function.Surjective : (X → Y) → Prop) :=
  fun g => Classical.propDecidable (Function.Surjective g)
local instance mapFintype {V W : Type*}
    [AddCommGroup V] [Module F2 V] [AddCommGroup W] [Module F2 W]
    [Fintype V] [Fintype W] : Fintype (V →ₗ[F2] W) :=
  Fintype.ofInjective (fun L : V →ₗ[F2] W => (L : V → W)) DFunLike.coe_injective

end DFVSGames.Inverse.KMSAnalyticHybridEnergy

end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_KMSAnalyticHyperplaneExtensions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Fourier.MatrixFourier

variable {E B : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup B] [Module F2 B]

def hyperplaneExtend (z : B →ₗ[F2] E) (v : E) : (B × F2) →ₗ[F2] E :=
  z.coprod (LinearMap.toSpanSingleton F2 E v)

@[simp] theorem hyperplaneExtend_apply (z : B →ₗ[F2] E) (v : E) (b : B) (c : F2) :
    hyperplaneExtend z v (b, c) = z b + c • v := rfl

@[simp] theorem hyperplaneExtend_comp_inl (z : B →ₗ[F2] E) (v : E) :
    (hyperplaneExtend z v).comp (LinearMap.inl F2 B F2) = z :=
  LinearMap.coprod_inl _ _

@[simp] theorem hyperplaneExtend_new_coordinate (z : B →ₗ[F2] E) (v : E) :
    hyperplaneExtend z v (0, 1) = v := by simp

end
end DFVSGames.Inverse.KMSAnalytic

namespace DFVSGames.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear (F2)

variable {E B J : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup B] [Module F2 B]
  [AddCommGroup J] [Module F2 J]

def leftEmbedding (ι : (J × F2) →ₗ[F2] E) : J →ₗ[F2] E :=
  ι.comp (LinearMap.inl F2 J F2)

theorem leftEmbedding_injective (ι : (J × F2) →ₗ[F2] E)
    (hι : Function.Injective ι) : Function.Injective (leftEmbedding ι) := by
  intro x y h
  have hxy : (x, (0 : F2)) = (y, 0) := hι h
  exact congrArg Prod.fst hxy

theorem range_left_comp_of_surjective (ι : (J × F2) →ₗ[F2] E)
    (z : B →ₗ[F2] J) (hz : Function.Surjective z) :
    ((leftEmbedding ι).comp z).range = (leftEmbedding ι).range := by
  ext v
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨z b, rfl⟩
  · rintro ⟨j, rfl⟩
    obtain ⟨b, rfl⟩ := hz j
    exact ⟨b, rfl⟩

def liftedRangeEquiv (ι : (J × F2) →ₗ[F2] E) (hι : Function.Injective ι)
    (z : B →ₗ[F2] J) (hz : Function.Surjective z) :
    J ≃ ((leftEmbedding ι).comp z).range :=
  Equiv.ofBijective
    (fun j => ⟨leftEmbedding ι j, by
      rw [range_left_comp_of_surjective ι z hz]
      exact ⟨j, rfl⟩⟩)
    ⟨by
      intro x y h
      exact leftEmbedding_injective ι hι (congrArg Subtype.val h),
      by
      rintro ⟨v, b, rfl⟩
      exact ⟨z b, rfl⟩⟩

@[simp] theorem liftedRangeEquiv_val (ι : (J × F2) →ₗ[F2] E)
    (hι : Function.Injective ι) (z : B →ₗ[F2] J) (hz : Function.Surjective z) (j : J) :
    (liftedRangeEquiv ι hι z hz j).val = leftEmbedding ι j := rfl

end
end DFVSGames.Inverse.KMSAnalytic

namespace DFVSGames.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Fourier.MatrixFourier

variable {B J K E : Type*}
  [AddCommGroup B] [Module F2 B] [AddCommGroup J] [Module F2 J]
  [AddCommGroup K] [Module F2 K] [AddCommGroup E] [Module F2 E]

def blockFrequency (z : B →ₗ[F2] J) (w : J) : (B × F2) →ₗ[F2] (J × F2) :=
  (hyperplaneExtend z w).prod (LinearMap.snd F2 B F2)

@[simp] theorem blockFrequency_apply (z : B →ₗ[F2] J) (w : J) (b : B) (c : F2) :
    blockFrequency z w (b, c) = (z b + c • w, c) := rfl

def blockOld (T : (B × F2) →ₗ[F2] (J × F2)) : B →ₗ[F2] J :=
  ((LinearMap.fst F2 J F2).comp T).comp (LinearMap.inl F2 B F2)

def blockNew (T : (B × F2) →ₗ[F2] (J × F2)) : J := (T (0, 1)).1

@[simp] theorem blockOld_blockFrequency (z : B →ₗ[F2] J) (w : J) :
    blockOld (blockFrequency z w) = z := by
  ext b
  simp [blockOld]

@[simp] theorem blockNew_blockFrequency (z : B →ₗ[F2] J) (w : J) :
    blockNew (blockFrequency z w) = w := by simp [blockNew]

end
end DFVSGames.Inverse.KMSAnalytic

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_KMSAnalyticSmallTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Fourier.MatrixCharacters
  (linearTraceCharacter linearTraceCharacter_apply linearTracePair)

variable {E F I I' J : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [AddCommGroup I] [Module F2 I] [AddCommGroup I'] [Module F2 I']
  [AddCommGroup J] [Module F2 J]

def smallFrequencyEquiv (e : I ≃ₗ[F2] I') : (F →ₗ[F2] I) ≃ (F →ₗ[F2] I') where
  toFun T := e.toLinearMap.comp T
  invFun T := e.symm.toLinearMap.comp T
  left_inv T := by ext x; simp
  right_inv T := by ext x; simp

@[simp] theorem smallFrequencyEquiv_apply (e : I ≃ₗ[F2] I') (T : F →ₗ[F2] I) :
    smallFrequencyEquiv e T = e.toLinearMap.comp T := rfl

end
end DFVSGames.Inverse.KMSAnalytic

namespace DFVSGames.Inverse.KMSPointComplement

noncomputable section
open DFVSGames.Integration.BinaryLinear (F2)

variable {E I : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup I] [Module F2 I]

def pointEquivOfIsCompl (U : Submodule F2 E) (v : E) (hv : v ≠ 0)
    (hc : IsCompl U (Submodule.span F2 {v})) : (U × F2) ≃ₗ[F2] E :=
  ((LinearEquiv.refl F2 U).prodCongr
    (LinearEquiv.toSpanNonzeroSingleton F2 E v hv)).trans
      (Submodule.prodEquivOfIsCompl U (Submodule.span F2 {v}) hc)

@[simp] theorem pointEquivOfIsCompl_apply (U : Submodule F2 E) (v : E) (hv : v ≠ 0)
    (hc : IsCompl U (Submodule.span F2 {v})) (x : U) (c : F2) :
    pointEquivOfIsCompl U v hv hc (x, c) = (x : E) + c • v := rfl

end
end DFVSGames.Inverse.KMSPointComplement

namespace DFVSGames.Inverse.KMSFourthMoment
noncomputable section
open scoped BigOperators Classical
open DFVSGames.Fourier.MatrixCharacters
open DFVSGames.Fourier.MatrixFourier
open DFVSGames.Inverse.KMSAnalytic

variable {A I : Type*} [AddCommGroup A] [Module F2 A]
  [AddCommGroup I] [Module F2 I] [Subsingleton A]

@[simp] theorem zeroFixedEquiv_apply (x : I) :
    zeroFixedEquiv (A := A) x = (0, x) := rfl

@[simp] theorem zeroFixedEquiv_symm_apply (a : A) (x : I) :
    (zeroFixedEquiv (A := A) (I := I)).symm (a, x) = x := rfl

end
end DFVSGames.Inverse.KMSFourthMoment

namespace DFVSGames.Inverse.KMSFourthMoment
noncomputable section
open scoped BigOperators Classical
open DFVSGames.Fourier.MatrixCharacters
open DFVSGames.Inverse.KMSAnalytic

universe u v

local instance mapFintype {V : Type*} {W : Type*}
    [AddCommGroup V] [Module F2 V] [AddCommGroup W] [Module F2 W]
    [Fintype V] [Fintype W] : Fintype (V →ₗ[F2] W) :=
  Fintype.ofInjective (fun L : V →ₗ[F2] W => (L : V → W)) DFunLike.coe_injective

end
end DFVSGames.Inverse.KMSFourthMoment

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_KMSAnalyticCodomainTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Fourier.MatrixFourier

variable {E F F' I J : Type*}
  [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F] [AddCommGroup F'] [Module F2 F']
  [AddCommGroup I] [Module F2 I] [AddCommGroup J] [Module F2 J]

def codomainFrequencyEquiv (e : F ≃ₗ[F2] F') : (F →ₗ[F2] I) ≃ (F' →ₗ[F2] I) where
  toFun T := T.comp e.symm.toLinearMap
  invFun T := T.comp e.toLinearMap
  left_inv T := by ext x; simp
  right_inv T := by ext x; simp

@[simp] theorem codomainFrequencyEquiv_apply (e : F ≃ₗ[F2] F') (T : F →ₗ[F2] I) :
    codomainFrequencyEquiv e T = T.comp e.symm.toLinearMap := rfl

@[simp] theorem codomainFrequency_cancel (e : F ≃ₗ[F2] F') (T : F →ₗ[F2] I) :
    (T.comp e.symm.toLinearMap).comp e.toLinearMap = T := by ext x; simp

end
end DFVSGames.Inverse.KMSAnalytic

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_KMSAnalyticHybridEnergyMixed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Inverse.KMSAnalyticHybridEnergy

noncomputable section
open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Inverse.KMSAnalytic
open DFVSGames.Inverse.KMSFourthMoment

universe u v w

@[instance_reducible]
def mixedMapFintype {V W : Type*}
    [AddCommGroup V] [Module F2 V] [AddCommGroup W] [Module F2 W]
    [Fintype V] [Fintype W] : Fintype (V →ₗ[F2] W) :=
  Fintype.ofInjective (fun L : V →ₗ[F2] W => (L : V → W)) DFunLike.coe_injective

attribute [local instance] mixedMapFintype

end
end DFVSGames.Inverse.KMSAnalyticHybridEnergy

noncomputable section

namespace DFVSGames.Appendix.LevelInequality

open scoped BigOperators
open DFVSGames.Fourier.MatrixCharacters DFVSGames.Fourier.MatrixFourier

variable {E F : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

def frequencyRank (S : F →ₗ[F2] E) : ℕ := Module.finrank F2 (LinearMap.range S)

end DFVSGames.Appendix.LevelInequality
end

noncomputable section
namespace DFVSGames.Appendix.DerivativeDegree

open scoped BigOperators
open DFVSGames.Fourier.MatrixCharacters DFVSGames.Fourier.MatrixFourier
open DFVSGames.Fourier.MatrixRestrictions
open DFVSGames.Appendix.Derivatives
open DFVSGames.Appendix.LevelInequality (frequencyRank)
attribute [local instance] Classical.propDecidable

variable {E F : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

def DegreeAtMost (d : ℕ) (f : (E →ₗ[F2] F) → ℝ) : Prop :=
  ∀ Y, d < frequencyRank Y → linearCoeff f Y = 0

variable [Finite E] [Finite F]

local instance quotientFinite (A : Submodule F2 E) : Finite (E ⧸ A) :=
  Finite.of_surjective A.mkQ A.mkQ_surjective

local instance compressedDualFintype (A : Submodule F2 E) (B : Submodule F2 F) :
    Fintype (B →ₗ[F2] (E ⧸ A)) := by
  classical
  letI : Fintype B := Fintype.ofFinite _
  letI : Fintype (E ⧸ A) := Fintype.ofFinite _
  exact Fintype.ofInjective (fun L : B →ₗ[F2] (E ⧸ A) => (L : B → E ⧸ A))
    DFunLike.coe_injective

end DFVSGames.Appendix.DerivativeDegree
end

noncomputable section

namespace DFVSGames.Appendix.A5IndexCount

open DFVSGames.Integration.BinaryLinear (F2)

variable {V W : Type*}
  [AddCommGroup V] [Module F2 V] [AddCommGroup W] [Module F2 W]

def insideEquiv (A I : Submodule F2 V) (hIA : I ≤ A) :
    (I.comap A.subtype) ≃ₗ[F2] I where
  toFun i := ⟨i.val.val, i.property⟩
  invFun i := ⟨⟨i.val, hIA i.property⟩, i.property⟩
  left_inv _i := Subtype.ext (Subtype.ext rfl)
  right_inv _i := Subtype.ext rfl
  map_add' _i _j := Subtype.ext rfl
  map_smul' _c _i := Subtype.ext rfl

theorem internal_isCompl (A I A0 : Submodule F2 V) (hIA : I ≤ A)
    (hd : Disjoint A0 I) (hj : A0 ⊔ I = A) :
    IsCompl (I.comap A.subtype) (A0.comap A.subtype) := by
  have hA0 : A0 ≤ A := le_sup_left.trans hj.le
  refine ⟨Submodule.disjoint_def.mpr ?_, codisjoint_iff.mpr ?_⟩
  · intro a hi h0
    exact Subtype.ext (Submodule.disjoint_def.mp hd a.val h0 hi)
  · apply eq_top_iff.mpr
    intro a _
    have ha : a.val ∈ A0 ⊔ I := by rw [hj]; exact a.property
    rcases Submodule.mem_sup.mp ha with ⟨v, hv, i, hi, hvi⟩
    refine Submodule.mem_sup.mpr ⟨⟨i, hIA hi⟩, hi, ⟨v, hA0 hv⟩, hv, ?_⟩
    apply Subtype.ext
    change i + v = a.val
    rw [add_comm]
    exact hvi

def projectionA0 (A I A0 : Submodule F2 V) (hIA : I ≤ A)
    (hd : Disjoint A0 I) (hj : A0 ⊔ I = A) : A →ₗ[F2] I :=
  (insideEquiv A I hIA).toLinearMap.comp
    (((I.comap A.subtype).isComplEquivProj
      ⟨A0.comap A.subtype, internal_isCompl A I A0 hIA hd hj⟩).val)

def fullRange {U L : Type*} [AddCommGroup U] [Module F2 U]
    [AddCommGroup L] [Module F2 L] (S : U →ₗ[F2] L) (hS : S.range = ⊤) :
    L →ₗ[F2] S.range :=
  (LinearMap.id : L →ₗ[F2] L).codRestrict S.range (fun x => by rw [hS]; trivial)

theorem quotientRestriction_surjective (J B0 : Submodule F2 W) (hc : B0 ⊔ J = ⊤) :
    Function.Surjective (A4IndexCount.quotientRestriction J B0) := by
  intro z
  obtain ⟨w, rfl⟩ := J.mkQ_surjective z
  have hw : w ∈ B0 ⊔ J := by rw [hc]; trivial
  rcases Submodule.mem_sup.mp hw with ⟨b, hb, j, hj, hbj⟩
  refine ⟨⟨b, hb⟩, ?_⟩
  change J.mkQ b = J.mkQ w
  have hz : J.mkQ j = 0 := (Submodule.Quotient.mk_eq_zero J).mpr hj
  rw [← hbj, map_add, hz, add_zero]

theorem quotientRestriction_same_kernel (B J B0 : Submodule F2 W)
    (hm : B0 ⊓ J = B) :
    (A4IndexCount.quotientRestriction J B0).ker =
      (A4IndexCount.quotientRestriction B B0).ker := by
  rw [A4IndexCount.ker_quotientRestriction, A4IndexCount.ker_quotientRestriction]
  ext b
  change (b : W) ∈ J ↔ (b : W) ∈ B
  constructor
  · intro hj
    have hb : (b : W) ∈ B0 ⊓ J := ⟨b.property, hj⟩
    rwa [hm] at hb
  · intro hb
    exact (hm.symm.le.trans inf_le_right) hb

def sectionB0 (B J B0 : Submodule F2 W)
    (hc : B0 ⊔ J = ⊤) (hm : B0 ⊓ J = B) : (W ⧸ J) →ₗ[F2] (W ⧸ B) :=
  (A4IndexCount.factorViaRange (A4IndexCount.quotientRestriction J B0)
    (A4IndexCount.quotientRestriction B B0)
    (quotientRestriction_same_kernel B J B0 hm).le).comp
      (fullRange (A4IndexCount.quotientRestriction J B0)
        (LinearMap.range_eq_top.mpr (quotientRestriction_surjective J B0 hc)))

def encode (X : W →ₗ[F2] V) (A : Submodule F2 V) (B : Submodule F2 W)
    (hIA : X.range ≤ A) (p : OperatorPartitions.A5GeometricIndex X A B) :
    (A →ₗ[F2] X.range) × ((W ⧸ X.ker) →ₗ[F2] (W ⧸ B)) :=
  (projectionA0 A X.range p.val.1 hIA p.property.1 p.property.2.1,
    sectionB0 B X.ker p.val.2 p.property.2.2.1 p.property.2.2.2)

end DFVSGames.Appendix.A5IndexCount
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_A5Scalar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace DFVSGames.Appendix.A5Passage

open scoped BigOperators
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Appendix.Derivatives
attribute [local instance] Classical.propDecidable
attribute [local instance] OperatorNorm.quotientFinite OperatorNorm.compressedDualFintype

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]

abbrev OuterIndex (X : F →ₗ[F2] E) (e : Nat) :=
  HybridIndex (E := E ⧸ X.range) (F := X.ker) e

def LiftedA (X : F →ₗ[F2] E) {e : Nat} (s : OuterIndex X e) : Submodule F2 E :=
  s.val.1.comap X.range.mkQ

def LiftedB (X : F →ₗ[F2] E) {e : Nat} (s : OuterIndex X e) : Submodule F2 F :=
  s.val.2.map X.ker.subtype

abbrev Pair (X : F →ₗ[F2] E) {e : Nat} (s : OuterIndex X e) :=
  OperatorPartitions.A5GeometricIndex X (LiftedA X s) (LiftedB X s)

abbrev Passage (X : F →ₗ[F2] E) (e : Nat) :=
  Σ s : OuterIndex X e, Pair X s

def forget (X : F →ₗ[F2] E) (e : Nat) (q : Passage X e) :
    Submodule F2 E × Submodule F2 F := q.2.val

@[simp] theorem forget_val (X : F →ₗ[F2] E) (e : Nat) (q : Passage X e) :
    forget X e q = q.2.val := rfl

variable [Finite E] [Finite F]

instance pairFintype (X : F →ₗ[F2] E) {e : Nat} (s : OuterIndex X e) :
    Fintype (Pair X s) := by
  letI : Finite (Submodule F2 E) :=
    Finite.of_injective (fun A : Submodule F2 E => (A : Set E)) SetLike.coe_injective
  letI : Finite (Submodule F2 F) :=
    Finite.of_injective (fun B : Submodule F2 F => (B : Set F)) SetLike.coe_injective
  exact Fintype.ofFinite _

variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

def descendantSum (A : Submodule F2 E) (B : Submodule F2 F)
    (X : B →ₗ[F2] (E ⧸ A)) (e : Nat) (f : (E →ₗ[F2] F) → ℝ) : ℝ :=
  ∑ q : Passage X e,
    𝔼 U, (𝔼 N, mapDerivative
      (NaturalTransport.dualFactor A B q.2.val.1 q.2.val.2
        (LinearIdentities.compress X q.2.val.1 q.2.val.2))
      (hybridDerivative (q.2.val.1.comap A.mkQ) (q.2.val.2.map B.subtype) U f) N ^ 2) ^ 2

end DFVSGames.Appendix.A5Passage
end

namespace DFVSGames.Appendix.SubspaceExtensions
open scoped BigOperators
open LinearMap Submodule
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

@[simp] theorem hKernel_horizontal (B : Submodule K V) : hKernel (horizontal B) = B := by
  ext x
  change (x ∈ B ∧ (0:K) = 0) ↔ x ∈ B
  simp

@[simp] theorem hKernel_extension (B : Submodule K V) (q : V ⧸ B) : hKernel (extension B q) = B := by
  ext x
  change (x,0) ∈ extension B q ↔ x ∈ B
  rw [extension_mem, zero_smul]
  change (x ∈ LinearMap.ker B.mkQ) ↔ x ∈ B
  rw [Submodule.ker_mkQ]

theorem exists_one_extension (B : Submodule K V) (q : V ⧸ B) : ∃ v, (v,1) ∈ extension B q := by
  obtain ⟨v,hv⟩ := B.mkQ_surjective q
  exact ⟨v, (extension_mem B q v 1).mpr (by simpa only [one_smul] using hv)⟩

theorem eq_extension_of_one_mem (S : Submodule K (V × K)) (v : V)
    (hv : (v,1) ∈ S) : S = extension (hKernel S) ((hKernel S).mkQ v) := by
  ext p
  rcases p with ⟨x,t⟩
  rw [extension_mem, mkQ_eq_smul_iff]
  change (x,t) ∈ S ↔ (x-t•v,0) ∈ S
  have hz : (x-t•v,0) = (x,t)-t•(v,1) := by ext <;> simp
  rw [hz]
  constructor
  · intro hx; exact S.sub_mem hx (S.smul_mem t hv)
  · intro hx
    have h := S.add_mem hx (S.smul_mem t hv)
    simpa only [sub_add_cancel] using h

theorem eq_horizontal_of_no_one (S : Submodule K (V × K))
    (hn : ¬ ∃ v, (v,1) ∈ S) : S = horizontal (hKernel S) := by
  have last_zero : ∀ x t, (x,t) ∈ S → t = 0 := by
    intro x t hxt
    by_contra ht
    have h := S.smul_mem t⁻¹ hxt
    have h' : (t⁻¹ • x,1) ∈ S := by simpa [smul_eq_mul, ht] using h
    exact hn ⟨_,h'⟩
  ext p
  rcases p with ⟨x,t⟩
  change (x,t) ∈ S ↔ (x ∈ hKernel S ∧ t = 0)
  constructor
  · intro hp
    have ht := last_zero x t hp
    subst t
    exact ⟨hp,rfl⟩
  · rintro ⟨hx,rfl⟩
    exact hx

theorem horizontal_ne_extension (A B : Submodule K V) (q : V ⧸ B) : horizontal A ≠ extension B q := by
  intro h
  obtain ⟨v,hv⟩ := exists_one_extension B q
  have hv' : (v,1) ∈ horizontal A := h.symm ▸ hv
  change v ∈ A ∧ (1:K) = 0 at hv'
  exact one_ne_zero hv'.2

theorem extension_injective (B : Submodule K V) : Function.Injective (extension B) := by
  intro q r h
  obtain ⟨v,hv⟩ := B.mkQ_surjective q
  have hp : (v,1) ∈ extension B q := (extension_mem B q v 1).mpr (by simpa using hv)
  have hp' : (v,1) ∈ extension B r := h ▸ hp
  have hr := (extension_mem B r v 1).mp hp'
  simpa only [one_smul, hv] using hr

def encode : (Submodule K V) ⊕ (Σ B : Submodule K V, V ⧸ B) → Submodule K (V × K)
  | .inl B => horizontal B
  | .inr ⟨B,q⟩ => extension B q

theorem encode_injective : Function.Injective (encode (K:=K) (V:=V)) := by
  intro a b h
  cases a with
  | inl A =>
    cases b with
    | inl B =>
      have hAB : A = B := by simpa only [encode,hKernel_horizontal] using congrArg hKernel h
      subst B
      rfl
    | inr b =>
      rcases b with ⟨B,q⟩
      exact False.elim (horizontal_ne_extension A B q h)
  | inr a =>
    rcases a with ⟨A,q⟩
    cases b with
    | inl B => exact False.elim (horizontal_ne_extension B A q h.symm)
    | inr b =>
      rcases b with ⟨B,r⟩
      have hAB : A = B := by simpa only [encode,hKernel_extension] using congrArg hKernel h
      cases hAB
      have hqr : q = r := extension_injective A h
      cases hqr
      rfl

theorem encode_surjective : Function.Surjective (encode (K:=K) (V:=V)) := by
  intro S
  by_cases h : ∃ v, (v,1) ∈ S
  · obtain ⟨v,hv⟩ := h
    exact ⟨.inr ⟨hKernel S,(hKernel S).mkQ v⟩, (eq_extension_of_one_mem S v hv).symm⟩
  · exact ⟨.inl (hKernel S), (eq_horizontal_of_no_one S h).symm⟩

def splitEquiv : Submodule K (V × K) ≃ (Submodule K V) ⊕ (Σ B : Submodule K V, V ⧸ B) :=
  (Equiv.ofBijective encode ⟨encode_injective,encode_surjective⟩).symm

def horizontalEquiv (B : Submodule K V) : B ≃ₗ[K] horizontal B where
  toFun b := ⟨((b:V),0),⟨b.property,rfl⟩⟩
  invFun p := ⟨p.val.1,p.property.1⟩
  left_inv b := by apply Subtype.ext; rfl
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · have hp : p.val.2 = 0 := p.property.2
      exact hp.symm
  map_add' a b := by apply Subtype.ext; simp
  map_smul' c b := by apply Subtype.ext; simp

def extensionEquiv (B : Submodule K V) (q : V ⧸ B) (v : V) (hv : B.mkQ v = q) :
    (B × K) ≃ₗ[K] extension B q where
  toFun p := ⟨((p.1:V)+p.2•v,p.2), by
    apply (extension_mem B q _ _).mpr
    have hb : B.mkQ (p.1:V) = 0 := by
      apply LinearMap.mem_ker.mp
      rw [Submodule.ker_mkQ]
      exact p.1.property
    simp only [map_add,map_smul,hb,hv,zero_add]⟩
  invFun p := (⟨p.val.1-p.val.2•v, by
    apply (mkQ_eq_smul_iff B _ v _).mp
    rw [hv]
    exact (extension_mem B q _ _).mp p.property⟩,p.val.2)
  left_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      change ((p.1:V)+p.2•v)-p.2•v = (p.1:V)
      exact add_sub_cancel_right _ _
    · rfl
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · change (p.val.1-p.val.2•v)+p.val.2•v = p.val.1
      exact sub_add_cancel _ _
    · rfl
  map_add' p r := by
    apply Subtype.ext
    apply Prod.ext
    · change ((p.1:V)+(r.1:V))+(p.2+r.2)•v =
        ((p.1:V)+p.2•v)+((r.1:V)+r.2•v)
      rw [add_smul]
      abel
    · rfl
  map_smul' c p := by
    apply Subtype.ext
    apply Prod.ext
    · change c•(p.1:V)+(c*p.2)•v = c•((p.1:V)+p.2•v)
      rw [smul_add,mul_smul]
    · rfl

variable {W : Type*} [AddCommGroup W] [Module K W]

theorem map_inverse (e : V ≃ₗ[K] W) (B : Submodule K V) :
    (B.map e.toLinearMap).map e.symm.toLinearMap = B := by
  have hc : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id := by ext x; simp
  rw [← Submodule.map_comp,hc,Submodule.map_id]

def subspaceEquiv (e : V ≃ₗ[K] W) : Submodule K V ≃ Submodule K W where
  toFun B := B.map e.toLinearMap
  invFun C := C.map e.symm.toLinearMap
  left_inv := map_inverse e
  right_inv := map_inverse e.symm

def subspaceMapEquiv (e : V ≃ₗ[K] W) (B : Submodule K V) : B ≃ₗ[K] B.map e.toLinearMap where
  toFun b := ⟨e b,Submodule.mem_map.mpr ⟨b,b.property,rfl⟩⟩
  invFun c := ⟨e.symm c,by
    rcases Submodule.mem_map.mp c.property with ⟨b,hb,hbc⟩

    rw [← hbc]
    simpa using hb⟩
  left_inv b := by apply Subtype.ext; simp
  right_inv c := by apply Subtype.ext; simp
  map_add' a b := by apply Subtype.ext; simp
  map_smul' c b := by apply Subtype.ext; simp

def coordinateSplit (n : Nat) :
    (Fin (n+1) → K) ≃ₗ[K] ((Fin n → K) × K) where
  toFun f := (fun i => f i.castSucc, f (Fin.last n))
  invFun p := Fin.lastCases p.2 p.1
  left_inv f := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  right_inv p := by
    apply Prod.ext
    · funext i; simp
    · simp
  map_add' f g := rfl
  map_smul' c f := rfl

end
end DFVSGames.Appendix.SubspaceExtensions

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_SubmoduleInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace DFVSGames.Appendix.A13Index

open Module
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Fourier.MatrixRestrictions (order)

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]

abbrev Triple := LinearIdentities.A4Index (K := F2) (W := F) (V := E)

def weakA (q : Triple (E := E) (F := F)) : Submodule F2 E :=
  q.2.2.range.comap q.1.mkQ

def weakB (q : Triple (E := E) (F := F)) : Submodule F2 F :=
  q.2.2.ker.map q.2.1.subtype

theorem recover_weakA {A : Submodule F2 E} {B : Submodule F2 F}
    (p : A4IndexCount.Index A B) : weakA p.val = A := by
  rcases p with ⟨⟨A0, B0, X⟩, hA, hB, hK, hR⟩
  change X.range.comap A0.mkQ = A
  rw [hR]
  ext a
  change A0.mkQ a ∈ A.map A0.mkQ ↔ a ∈ A
  constructor
  · intro ha
    rcases Submodule.mem_map.mp ha with ⟨v, hv, he⟩
    have hm : a - v ∈ A0 := by
      apply (Submodule.Quotient.mk_eq_zero A0).mp
      change A0.mkQ (a - v) = 0
      rw [map_sub, he, sub_self]
    simpa only [sub_add_cancel] using A.add_mem (hA hm) hv
  · intro ha
    exact Submodule.mem_map.mpr ⟨a, ha, rfl⟩

theorem recover_weakB {A : Submodule F2 E} {B : Submodule F2 F}
    (p : A4IndexCount.Index A B) : weakB p.val = B := by
  rcases p with ⟨⟨A0, B0, X⟩, hA, hB, hK, hR⟩
  change X.ker.map B0.subtype = B
  rw [hK]
  ext b
  constructor
  · intro hb
    rcases Submodule.mem_map.mp hb with ⟨v, hv, rfl⟩
    exact hv
  · intro hb
    exact Submodule.mem_map.mpr ⟨⟨b, hB hb⟩, hb, rfl⟩

theorem canonicalValid (q : Triple (E := E) (F := F)) :
    A4IndexCount.Valid (weakA q) (weakB q) q := by
  rcases q with ⟨A0, B0, X⟩
  change A0 ≤ X.range.comap A0.mkQ ∧ X.ker.map B0.subtype ≤ B0 ∧
    X.ker = (X.ker.map B0.subtype).comap B0.subtype ∧
    X.range = (X.range.comap A0.mkQ).map A0.mkQ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ha
    change A0.mkQ a ∈ X.range
    have hz : A0.mkQ a = 0 := (Submodule.Quotient.mk_eq_zero A0).mpr ha
    rw [hz]
    exact X.range.zero_mem
  · intro b hb
    rcases Submodule.mem_map.mp hb with ⟨v, hv, rfl⟩
    exact v.property
  · ext b
    constructor
    · intro hb
      exact Submodule.mem_map.mpr ⟨b, hb, rfl⟩
    · intro hb
      change (b : F) ∈ X.ker.map B0.subtype at hb
      rcases Submodule.mem_map.mp hb with ⟨v, hv, he⟩
      have h : v = b := Subtype.ext he
      simpa only [h] using hv
  · ext z
    constructor
    · intro hz
      obtain ⟨v, rfl⟩ := A0.mkQ_surjective z
      exact Submodule.mem_map.mpr ⟨v, hz, rfl⟩
    · intro hz
      rcases Submodule.mem_map.mp hz with ⟨v, hv, rfl⟩
      exact hv

variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]

omit [FiniteDimensional F2 F] in
theorem dim_weakA {A : Submodule F2 E} {B : Submodule F2 F}
    (p : A4IndexCount.Index A B) :
    finrank F2 A = finrank F2 p.val.1 + finrank F2 p.val.2.2.range := by
  rcases p with ⟨⟨A0, B0, X⟩, hA, hB, hK, hR⟩
  change finrank F2 A = finrank F2 A0 + finrank F2 X.range
  let Q := A4IndexCount.quotientRestriction A0 A
  have hQR : Q.range = X.range := by
    rw [hR]
    ext z
    constructor
    · rintro ⟨a, rfl⟩
      exact Submodule.mem_map.mpr ⟨a.val, a.property, rfl⟩
    · intro hz
      rcases Submodule.mem_map.mp hz with ⟨a, ha, he⟩
      exact ⟨⟨a, ha⟩, he⟩
  have hQK : finrank F2 Q.ker = finrank F2 A0 := by
    rw [A4IndexCount.ker_quotientRestriction]
    exact (SubmoduleInterval.lowerIntervalSpaceEquiv A ⟨A0, hA⟩).finrank_eq.symm
  have h := Q.finrank_range_add_finrank_ker
  rw [hQR, hQK] at h
  omega

omit [FiniteDimensional F2 E] in
theorem codim_weakB {A : Submodule F2 E} {B : Submodule F2 F}
    (p : A4IndexCount.Index A B) :
    finrank F2 (F ⧸ B) =
      finrank F2 (F ⧸ p.val.2.1) + finrank F2 p.val.2.2.range := by
  rcases p with ⟨⟨A0, B0, X⟩, hA, hB, hK, hR⟩
  change finrank F2 (F ⧸ B) = finrank F2 (F ⧸ B0) + finrank F2 X.range
  have hKB : finrank F2 X.ker = finrank F2 B := by
    rw [hK]
    exact (SubmoduleInterval.lowerIntervalSpaceEquiv B0 ⟨B, hB⟩).finrank_eq.symm
  have h := X.finrank_range_add_finrank_ker
  rw [hKB] at h
  have hBdim := B.finrank_quotient_add_finrank
  have hB0dim := B0.finrank_quotient_add_finrank
  omega

def size (q : Triple (E := E) (F := F)) : Nat :=
  order q.1 q.2.1 + finrank F2 q.2.2.range

theorem weak_order {A : Submodule F2 E} {B : Submodule F2 F}
    (p : A4IndexCount.Index A B) :
    order A B = order p.val.1 p.val.2.1 + 2 * finrank F2 p.val.2.2.range := by
  have ha := dim_weakA p
  have hb := codim_weakB p
  dsimp only [order]
  omega

theorem order_eq_zero_iff (A : Submodule F2 E) (B : Submodule F2 F) :
    order A B = 0 ↔ A = ⊥ ∧ B = ⊤ := by
  constructor
  · intro h
    change finrank F2 A + finrank F2 (F ⧸ B) = 0 at h
    have ha : finrank F2 A = 0 := by omega
    have hb : finrank F2 (F ⧸ B) = 0 := by omega
    refine ⟨Submodule.finrank_eq_zero.mp ha, ?_⟩
    apply Submodule.eq_top_iff_finrank_eq.mpr
    have hq := B.finrank_quotient_add_finrank
    omega
  · rintro ⟨rfl, rfl⟩
    simpa [order] using
      (Module.finrank_eq_zero_of_subsingleton F2 (F ⧸ (⊤ : Submodule F2 F)))

theorem valid_positive_iff {A : Submodule F2 E} {B : Submodule F2 F}
    (p : A4IndexCount.Index A B) :
    (A, B) ≠ (⊥, ⊤) ↔ 0 < size p.val := by
  have h := weak_order p
  constructor
  · intro hp
    by_contra ht
    have hz : order A B = 0 := by
      dsimp only [size] at ht
      omega
    rcases (order_eq_zero_iff A B).mp hz with ⟨hA, hB⟩
    exact hp (Prod.ext hA hB)
  · intro ht hp
    have hAB : A = ⊥ ∧ B = ⊤ := Prod.mk.inj hp
    have hz := (order_eq_zero_iff A B).mpr hAB
    dsimp only [size] at ht
    omega

abbrev WeakPositive :=
  {p : Submodule F2 E × Submodule F2 F // p ≠ (⊥, ⊤)}

abbrev PositiveWitness :=
  Σ p : WeakPositive (E := E) (F := F), A4IndexCount.Index p.val.1 p.val.2

abbrev PositiveTriple := {q : Triple (E := E) (F := F) // 0 < size q}

abbrev BoundedPositiveTriple (d : Nat) :=
  {q : Triple (E := E) (F := F) // 0 < size q ∧ size q ≤ d}

def positiveMap (p : PositiveWitness (E := E) (F := F)) :
    PositiveTriple (E := E) (F := F) :=
  ⟨p.2.val, (valid_positive_iff p.2).mp p.1.property⟩

theorem positiveMap_injective :
    Function.Injective (positiveMap (E := E) (F := F)) := by
  rintro ⟨⟨⟨A, B⟩, hp⟩, p⟩ ⟨⟨⟨A', B'⟩, hp'⟩, p'⟩ he
  have hraw : p.val = p'.val := congrArg Subtype.val he
  have hA : A = A' := by
    calc
      A = weakA p.val := (recover_weakA p).symm
      _ = weakA p'.val := congrArg weakA hraw
      _ = A' := recover_weakA p'
  have hB : B = B' := by
    calc
      B = weakB p.val := (recover_weakB p).symm
      _ = weakB p'.val := congrArg weakB hraw
      _ = B' := recover_weakB p'
  cases hA
  cases hB
  have hpp : p = p' := Subtype.ext hraw
  cases hpp
  rfl

def positiveInverse (q : PositiveTriple (E := E) (F := F)) :
    PositiveWitness (E := E) (F := F) :=
  ⟨⟨(weakA q.val, weakB q.val),
      (valid_positive_iff ⟨q.val, canonicalValid q.val⟩).mpr q.property⟩,
    ⟨q.val, canonicalValid q.val⟩⟩

def positiveEquiv : PositiveWitness (E := E) (F := F) ≃
    PositiveTriple (E := E) (F := F) :=
  Equiv.ofBijective positiveMap ⟨positiveMap_injective, by
    intro q
    refine ⟨positiveInverse q, ?_⟩
    exact Subtype.ext rfl⟩

@[simp] theorem positiveMap_val (p : PositiveWitness (E := E) (F := F)) :
    (positiveMap p).val = p.2.val := rfl

@[simp] theorem positiveEquiv_val (p : PositiveWitness (E := E) (F := F)) :
    (positiveEquiv p).val = p.2.val := rfl

@[instance_reducible]
def tripleFintype [Finite E] [Finite F] :
    Fintype (Triple (E := E) (F := F)) := by
  classical
  letI : Fintype (Submodule F2 E) := SubspaceExtensions.subspaceFintype
  letI : Fintype (Submodule F2 F) := SubspaceExtensions.subspaceFintype
  letI (A : Submodule F2 E) : Finite (E ⧸ A) :=
    Finite.of_surjective A.mkQ A.mkQ_surjective
  letI (A : Submodule F2 E) (B : Submodule F2 F) :
      Fintype (B →ₗ[F2] (E ⧸ A)) := by
    letI : Fintype B := Fintype.ofFinite _
    letI : Fintype (E ⧸ A) := Fintype.ofFinite _
    exact Fintype.ofInjective (fun L : B →ₗ[F2] (E ⧸ A) =>
      (L : B → E ⧸ A)) DFunLike.coe_injective
  exact inferInstance

@[instance_reducible]
def weakPositiveFintype [Finite E] [Finite F] :
    Fintype (WeakPositive (E := E) (F := F)) := by
  classical
  letI : Fintype (Submodule F2 E) := SubspaceExtensions.subspaceFintype
  letI : Fintype (Submodule F2 F) := SubspaceExtensions.subspaceFintype
  exact inferInstance

@[instance_reducible]
def geometricIndexFintype [Finite E] [Finite F]
    (A : Submodule F2 E) (B : Submodule F2 F) :
    Fintype (A4IndexCount.Index A B) := by
  classical
  letI := tripleFintype (E := E) (F := F)
  exact inferInstance

@[instance_reducible]
def positiveWitnessFintype [Finite E] [Finite F] :
    Fintype (PositiveWitness (E := E) (F := F)) := by
  classical
  letI := weakPositiveFintype (E := E) (F := F)
  letI (A : Submodule F2 E) (B : Submodule F2 F) := geometricIndexFintype A B
  exact inferInstance

@[instance_reducible]
def positiveTripleFintype [Finite E] [Finite F] :
    Fintype (PositiveTriple (E := E) (F := F)) := by
  classical
  letI := tripleFintype (E := E) (F := F)
  exact inferInstance

@[instance_reducible]
def boundedPositiveTripleFintype [Finite E] [Finite F] (d : Nat) :
    Fintype (BoundedPositiveTriple (E := E) (F := F) d) := by
  classical
  letI := tripleFintype (E := E) (F := F)
  exact inferInstance

end DFVSGames.Appendix.A13Index
end

namespace DFVSGames.Appendix.TotalPredecessorCount
open Module
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Appendix.RankAdditivity
variable {E F : Type*} [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]

noncomputable def predecessorEnd (Y : E →ₗ[F2] F)
    (R : {R : E →ₗ[F2] F // RankBelow R Y}) : Y.range →ₗ[F2] Y.range :=
  let R' : E →ₗ[F2] Y.range := R.val.codRestrict Y.range
    (fun x => range_le_of_rankBelow R.val Y R.property ⟨x,rfl⟩)
  let hker : Y.ker ≤ R'.ker := by
    intro x hx
    exact Subtype.ext (ker_le_of_rankBelow R.val Y R.property hx)
  (Y.ker.liftQ R' hker).comp Y.quotKerEquivRange.symm.toLinearMap

end DFVSGames.Appendix.TotalPredecessorCount

noncomputable section
namespace DFVSGames.Appendix.F1Energy
open scoped BigOperators
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Appendix.RankAdditivity
variable {E F : Type*} [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
local notation "G" => (E →ₗ[F2] F)
attribute [local instance] Classical.propDecidable

def rank (Y : G) : ℕ := Module.finrank F2 Y.range

def Good (X Y : G) : Prop :=
  ∃ R : G, RankBelow R X ∧ RankBelow R Y ∧ RankBelow (X + R) (X + Y)

abbrev BoundedSplit (d : ℕ) (X : G) :=
  {R : G // RankBelow R X ∧ rank R ≤ d ∧ rank (X + R) ≤ d}

theorem add_self_cancel (X R : G) : (X + R) + R = X := by
  rw [add_assoc, DegreeCover.binary_add_self, add_zero]

def translate (R : G) : G ≃ G where
  toFun X := X + R
  invFun X := X + R
  left_inv X := add_self_cancel X R
  right_inv X := add_self_cancel X R

variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]

variable [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)]

def predecessorCoefficient (a : G → ℝ) (R C : G) : ℝ :=
  if RankBelow R (R+C) then |a (R+C)| else 0

def gram (a : G → ℝ) (R S : G) : ℝ :=
  ∑ C, predecessorCoefficient a R C * predecessorCoefficient a S C

def predecessorEnergy (a : G → ℝ) : ℝ :=
  ∑ R, ∑ C, predecessorCoefficient a R C ^ 2

def goodConvolution (a : G → ℝ) (X : G) : ℝ :=
  ∑ Y, if Good X Y then |a Y| * |a (X+Y)| else 0

open DFVSGames.Fourier.MatrixFourier

end DFVSGames.Appendix.F1Energy
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_UpperMobius
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace DFVSGames.Appendix.UpperMobius
open scoped BigOperators
open DFVSGames.Integration.BinaryLinear
attribute [local instance] Classical.propDecidable
variable {W : Type*} [AddCommGroup W] [Module F2 W]
  [FiniteDimensional F2 W] [Finite W]

local instance quotientFinite (K : Submodule F2 W) : Finite (W ⧸ K) :=
  Finite.of_surjective K.mkQ K.mkQ_surjective

local instance dualFinite {V : Type*} [AddCommGroup V] [Module F2 V] [Finite V] :
    Finite (Module.Dual F2 V) :=
  Finite.of_injective (fun f : Module.Dual F2 V => (f : V → F2)) DFunLike.coe_injective

local instance submoduleFinite {V : Type*} [AddCommGroup V] [Module F2 V] [Finite V] :
    Finite (Submodule F2 V) :=
  Finite.of_injective (fun S : Submodule F2 V => (S : Set V)) SetLike.coe_injective

noncomputable def upperQuotientEquiv (K : Submodule F2 W) :
    {B : Submodule F2 W // K ≤ B} ≃ Submodule F2 (W ⧸ K) :=
  (Submodule.comapMkQRelIso K).symm.toEquiv

noncomputable def dualSubspaceEquiv (V : Type*) [AddCommGroup V]
    [Module F2 V] [FiniteDimensional F2 V] :
    Submodule F2 V ≃ Submodule F2 (Module.Dual F2 V) :=
  (Subspace.orderIsoFiniteDimensional (K := F2) (V := V)).toEquiv

noncomputable def upperDualSubspaceEquiv (K : Submodule F2 W) :
    {B : Submodule F2 W // K ≤ B} ≃
      Submodule F2 (Module.Dual F2 (W ⧸ K)) :=
  (upperQuotientEquiv K).trans (dualSubspaceEquiv (W ⧸ K))

noncomputable def upperWeightedTotal (K : Submodule F2 W) (w : ℕ → ℤ) : ℤ := by
  classical
  letI := Fintype.ofFinite {B : Submodule F2 W // K ≤ B}
  exact ∑ B : {B : Submodule F2 W // K ≤ B}, w (Module.finrank F2 (W ⧸ B.val))

end DFVSGames.Appendix.UpperMobius
end

noncomputable section
namespace DFVSGames.Appendix.BadConvolution
open scoped BigOperators
open DFVSGames.Integration.BinaryLinear (F2)
open Module (finrank)
attribute [local instance] Classical.propDecidable

variable {W V : Type*} [AddCommGroup W] [Module F2 W]
  [AddCommGroup V] [Module F2 V]

def Incidence (A : Submodule F2 V) (B : Submodule F2 W) (Y : W →ₗ[F2] V) : Prop :=
  A ≤ Y.range ∧ Y.ker ≤ B

def Bad (X Y : W →ₗ[F2] V) : Prop :=
  (X.range ⊓ Y.range) ⊓ (X+Y).range ≠ ⊥ ∨
    (X.ker ⊔ Y.ker) ⊔ (X+Y).ker ≠ ⊤

def filteredCoefficient (A : Submodule F2 V) (B : Submodule F2 W)
    (a : (W →ₗ[F2] V) → ℝ) (Y : W →ₗ[F2] V) : ℝ :=
  if Incidence A B Y then a Y else 0

def pairDimension (p : Submodule F2 V × Submodule F2 W) : ℕ :=
  finrank F2 p.1 + finrank F2 (W ⧸ p.2)

def pairWeight (p : Submodule F2 V × Submodule F2 W) : ℝ :=
  mobius (finrank F2 p.1) * mobius (finrank F2 (W ⧸ p.2))

def signedWeight (p : Submodule F2 V × Submodule F2 W) : ℝ :=
  if p = (⊥,⊤) then 0 else -pairWeight p

section FiniteSums
variable [Fintype (W →ₗ[F2] V)]

def pieceConvolution (A : Submodule F2 V) (B : Submodule F2 W)
    (a : (W →ₗ[F2] V) → ℝ) (X : W →ₗ[F2] V) : ℝ :=
  ∑ Y, filteredCoefficient A B a Y * filteredCoefficient A B a (X+Y)

def badConvolution (a : (W →ₗ[F2] V) → ℝ) (X : W →ₗ[F2] V) : ℝ :=
  ∑ Y, if Bad X Y then a Y * a (X+Y) else 0
end FiniteSums

end DFVSGames.Appendix.BadConvolution
end

noncomputable section
namespace DFVSGames.Appendix.A1Reduction
open scoped BigOperators
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Fourier.MatrixFourier
open DFVSGames.Appendix.Derivatives
attribute [local instance] Classical.propDecidable

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype (Submodule F2 E)] [Fintype (Submodule F2 F)]

def weakFourthSum (d : ℕ) (f : (E →ₗ[F2] F) → ℝ) : ℝ :=
  ∑ p : Submodule F2 E × Submodule F2 F,
    if p ≠ (⊥, ⊤) then
      (2:ℝ)^(7*d*(Module.finrank F2 p.1 + Module.finrank F2 (F ⧸ p.2))) *
        (𝔼 M, spectralProjector (fun Y => p.1 ≤ Y.range ∧ Y.ker ≤ p.2) f M^4)
    else 0

end DFVSGames.Appendix.A1Reduction
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Probability_A13Reduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Fourier
open DFVSGames.Appendix.Derivatives
open DFVSGames.Appendix.OperatorPartitions
open DFVSGames.Appendix.LinearIdentities

namespace DFVSGames.Appendix.A13Reduction

attribute [local instance] Classical.propDecidable

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Finite E] [Finite F]

attribute [local instance] OperatorNorm.quotientFinite OperatorNorm.compressedDualFintype

def tripleMoment (p : A4Index (K := F2) (W := F) (V := E))
    (f : (E →ₗ[F2] F) → ℝ) : ℝ :=
  𝔼 T, 𝔼 N, mapDerivative p.2.2 (hybridDerivative p.1 p.2.1 T f) N ^ 4

def tripleTerm (d : ℕ) (p : A13Index.Triple (E := E) (F := F))
    (f : (E →ₗ[F2] F) → ℝ) : ℝ :=
  (2 : ℝ) ^ (24 * d * A13Index.size p) * tripleMoment p f

variable [Fintype (Submodule F2 E)] [Fintype (Submodule F2 F)]

def positiveTripleSum (d : ℕ) (f : (E →ₗ[F2] F) → ℝ) : ℝ :=
  ∑ p : A13Index.PositiveTriple (E := E) (F := F), tripleTerm d p.val f

def boundedPositiveTripleSum (d : ℕ) (f : (E →ₗ[F2] F) → ℝ) : ℝ :=
  ∑ p : A13Index.BoundedPositiveTriple (E := E) (F := F) d, tripleTerm d p.val f

end DFVSGames.Appendix.A13Reduction
end

namespace DFVSGames.Appendix.DerivativeInduction

open DFVSGames.Integration.BinaryLinear
open LinearMap

variable {B U A C : Type*}
variable [AddCommGroup B] [Module F2 B] [AddCommGroup U] [Module F2 U]
variable [AddCommGroup A] [Module F2 A] [AddCommGroup C] [Module F2 C]

def IsAntecedent (Z : B →ₗ[F2] C) (X : (B × U) →ₗ[F2] (A × C)) : Prop :=
  (∀ b, (X (b, 0)).2 = Z b) ∧
  Disjoint X.range (LinearMap.inl F2 A C).range ∧
  (LinearMap.inl F2 B U).range ⊔ X.ker = ⊤

abbrev Antecedent (Z : B →ₗ[F2] C) :=
  { X : (B × U) →ₗ[F2] (A × C) // IsAntecedent Z X }

theorem antecedent_image_from_left (Z : B →ₗ[F2] C)
    (X : (B × U) →ₗ[F2] (A × C)) (hX : IsAntecedent Z X) (p : B × U) :
    ∃ b : B, X p = X (b, 0) := by
  have hp : p ∈ (LinearMap.inl F2 B U).range ⊔ X.ker := by
    rw [hX.2.2]
    trivial
  obtain ⟨q, hq, r, hr, he⟩ := Submodule.mem_sup.mp hp
  obtain ⟨b, rfl⟩ := hq
  refine ⟨b, ?_⟩
  rw [← he, map_add]
  have hz : X r = 0 := hr
  simp only [hz, add_zero, LinearMap.inl_apply]

theorem antecedent_bottom_mem_range (Z : B →ₗ[F2] C)
    (X : (B × U) →ₗ[F2] (A × C)) (hX : IsAntecedent Z X) (p : B × U) :
    (X p).2 ∈ Z.range := by
  obtain ⟨b, hb⟩ := antecedent_image_from_left Z X hX p
  exact ⟨b, (hX.1 b).symm.trans (congrArg Prod.snd hb).symm⟩

theorem antecedent_vertical_zero (Z : B →ₗ[F2] C)
    (X : (B × U) →ₗ[F2] (A × C)) (hX : IsAntecedent Z X)
    (p : B × U) (hp : (X p).2 = 0) : X p = 0 := by
  apply Submodule.disjoint_def.mp hX.2.1 (X p) (LinearMap.mem_range_self X p)
  exact ⟨(X p).1, Prod.ext rfl hp.symm⟩

theorem antecedent_kernel_le_inline_DerivativeInduction (Z : B →ₗ[F2] C)
    (X : (B × U) →ₗ[F2] (A × C)) (hX : IsAntecedent Z X) :
    Z.ker ≤ ((LinearMap.fst F2 A C).comp (X.comp (LinearMap.inl F2 B U))).ker := by
  intro b hb
  have hz : Z b = 0 := hb
  have hx := antecedent_vertical_zero Z X hX (b, 0) ((hX.1 b).trans hz)
  exact congrArg Prod.fst hx

noncomputable def graphParameter (Z : B →ₗ[F2] C)
    (X : Antecedent (U := U) (A := A) Z) : Z.range →ₗ[F2] A :=
  (Z.ker.liftQ ((LinearMap.fst F2 A C).comp
    (X.val.comp (LinearMap.inl F2 B U))) (antecedent_kernel_le_inline_DerivativeInduction Z X.val X.property)).comp
    Z.quotKerEquivRange.symm.toLinearMap

theorem graphParameter_apply (Z : B →ₗ[F2] C)
    (X : Antecedent (U := U) (A := A) Z) (b : B) :
    graphParameter Z X (Z.rangeRestrict b) = (X.val (b, 0)).1 := by
  rw [show Z.rangeRestrict b = ⟨Z b, LinearMap.mem_range_self Z b⟩ from rfl]
  simp [graphParameter, LinearMap.quotKerEquivRange_symm_apply_image]

noncomputable def complementParameter (Z : B →ₗ[F2] C)
    (X : Antecedent (U := U) (A := A) Z) : U →ₗ[F2] Z.range :=
  ((LinearMap.snd F2 A C).comp (X.val.comp (LinearMap.inr F2 B U))).codRestrict
    Z.range (fun u => antecedent_bottom_mem_range Z X.val X.property (0, u))

@[simp] theorem complementParameter_val (Z : B →ₗ[F2] C)
    (X : Antecedent (U := U) (A := A) Z) (u : U) :
    (complementParameter Z X u : C) = (X.val (0, u)).2 := rfl

def lift (Z : B →ₗ[F2] C) (F : Z.range →ₗ[F2] A) (H : U →ₗ[F2] Z.range) :
    (B × U) →ₗ[F2] (A × C) :=
  (F.comp (Z.rangeRestrict.coprod H)).prod
    (Z.range.subtype.comp (Z.rangeRestrict.coprod H))

@[simp] theorem lift_apply (Z : B →ₗ[F2] C)
    (F : Z.range →ₗ[F2] A) (H : U →ₗ[F2] Z.range) (p : B × U) :
    lift Z F H p = (F (Z.rangeRestrict p.1 + H p.2),
      ((Z.rangeRestrict p.1 + H p.2 : Z.range) : C)) := rfl

theorem lift_isAntecedent (Z : B →ₗ[F2] C)
    (F : Z.range →ₗ[F2] A) (H : U →ₗ[F2] Z.range) :
    IsAntecedent Z (lift Z F H) := by
  refine ⟨?_, ?_, ?_⟩
  · intro b
    simp
  · apply Submodule.disjoint_def.mpr
    intro v hv hw
    obtain ⟨p, rfl⟩ := hv
    obtain ⟨a, ha⟩ := hw
    have hz : Z.rangeRestrict p.1 + H p.2 = 0 := by
      apply Subtype.ext
      exact (congrArg Prod.snd ha).symm
    simp [hz]
  · apply top_unique
    intro p _
    obtain ⟨b, hb⟩ := Z.surjective_rangeRestrict (Z.rangeRestrict p.1 + H p.2)
    have he : lift Z F H p = lift Z F H (b, 0) := by
      simp [hb]
    apply Submodule.mem_sup.mpr
    refine ⟨(b, 0), ⟨b, rfl⟩, p - (b, 0), ?_, ?_⟩
    · change lift Z F H (p - (b, 0)) = 0
      rw [map_sub, he, sub_self]
    · simpa only [← add_sub_assoc] using add_sub_cancel_left (b, 0) p

def intoAntecedent (Z : B →ₗ[F2] C)
    (p : (Z.range →ₗ[F2] A) × (U →ₗ[F2] Z.range)) :
    Antecedent (U := U) (A := A) Z :=
  ⟨lift Z p.1 p.2, lift_isAntecedent Z p.1 p.2⟩

theorem graphParameter_lift (Z : B →ₗ[F2] C)
    (F : Z.range →ₗ[F2] A) (H : U →ₗ[F2] Z.range) :
    graphParameter Z (intoAntecedent Z (F, H)) = F := by
  ext c
  obtain ⟨b, rfl⟩ := Z.surjective_rangeRestrict c
  rw [graphParameter_apply]
  simp [intoAntecedent]

theorem complementParameter_lift (Z : B →ₗ[F2] C)
    (F : Z.range →ₗ[F2] A) (H : U →ₗ[F2] Z.range) :
    complementParameter Z (intoAntecedent Z (F, H)) = H := by
  ext u
  simp [intoAntecedent]

theorem lift_parameters (Z : B →ₗ[F2] C)
    (X : Antecedent (U := U) (A := A) Z) :
    lift Z (graphParameter Z X) (complementParameter Z X) = X.val := by
  apply LinearMap.ext
  intro p
  have hb : (Z.rangeRestrict p.1 + complementParameter Z X p.2 : C) = (X.val p).2 := by
    have hp : p = (p.1, 0) + (0, p.2) := by simp
    conv_rhs => rw [hp, map_add]
    simp [X.property.1]
  obtain ⟨b, he⟩ := antecedent_image_from_left Z X.val X.property p
  have hr : Z.rangeRestrict p.1 + complementParameter Z X p.2 = Z.rangeRestrict b := by
    apply Subtype.ext
    exact hb.trans ((congrArg Prod.snd he).trans (X.property.1 b))
  apply Prod.ext
  · change graphParameter Z X (Z.rangeRestrict p.1 + complementParameter Z X p.2) = _
    rw [hr, graphParameter_apply]
    exact (congrArg Prod.fst he).symm
  · exact hb

noncomputable def antecedentEquiv (Z : B →ₗ[F2] C) :
    Antecedent (U := U) (A := A) Z ≃
      (Z.range →ₗ[F2] A) × (U →ₗ[F2] Z.range) where
  toFun X := (graphParameter Z X, complementParameter Z X)
  invFun := intoAntecedent Z
  left_inv X := Subtype.ext (lift_parameters Z X)
  right_inv p := Prod.ext (graphParameter_lift Z p.1 p.2)
    (complementParameter_lift Z p.1 p.2)

theorem isAntecedent_iff_pointwise (Z : B →ₗ[F2] C)
    (X : (B × U) →ₗ[F2] (A × C)) :
    IsAntecedent Z X ↔
      (∀ b, (X (b, 0)).2 = Z b) ∧
      (∀ p, (X p).2 = 0 → X p = 0) ∧
      (∀ p, ∃ b, X p = X (b, 0)) := by
  constructor
  · intro h
    exact ⟨h.1, antecedent_vertical_zero Z X h, antecedent_image_from_left Z X h⟩
  · rintro ⟨hc, hv, hs⟩
    refine ⟨hc, Submodule.disjoint_def.mpr ?_, top_unique ?_⟩
    · rintro v ⟨p, rfl⟩ ⟨a, ha⟩
      exact hv p (congrArg Prod.snd ha).symm
    · intro p _
      obtain ⟨b, hb⟩ := hs p
      apply Submodule.mem_sup.mpr
      refine ⟨(b, 0), ⟨b, rfl⟩, p - (b, 0), ?_, ?_⟩
      · change X (p - (b, 0)) = 0
        rw [map_sub, hb, sub_self]
      · simpa only [← add_sub_assoc] using add_sub_cancel_left (b, 0) p

variable {W V : Type*} [AddCommGroup W] [Module F2 W]
  [AddCommGroup V] [Module F2 V]

theorem disjoint_range_iff_zero (X : W →ₗ[F2] V) (Q : Submodule F2 V) :
    Disjoint X.range Q ↔ ∀ w, X w ∈ Q → X w = 0 := by
  constructor
  · intro h w hw
    exact Submodule.disjoint_def.mp h (X w) (LinearMap.mem_range_self X w) hw
  · intro h
    apply Submodule.disjoint_def.mpr
    rintro v ⟨w, rfl⟩ hw
    exact h w hw

theorem sup_kernel_iff_image (X : W →ₗ[F2] V) (P : Submodule F2 W) :
    P ⊔ X.ker = ⊤ ↔ ∀ w, ∃ p : P, X w = X p := by
  constructor
  · intro h w
    have hw : w ∈ P ⊔ X.ker := by rw [h]; trivial
    obtain ⟨p, hp, r, hr, he⟩ := Submodule.mem_sup.mp hw
    refine ⟨⟨p, hp⟩, ?_⟩
    rw [← he, map_add]
    have hz : X r = 0 := hr
    simp [hz]
  · intro h
    apply top_unique
    intro w _
    obtain ⟨p, hp⟩ := h w
    apply Submodule.mem_sup.mpr
    refine ⟨p, p.property, w - p, ?_, ?_⟩
    · change X (w - p) = 0
      rw [map_sub, hp, sub_self]
    · simpa only [← add_sub_assoc] using add_sub_cancel_left (p : W) w

def IsSubspaceAntecedent (P : Submodule F2 W) (Q D : Submodule F2 V)
    (hQ : IsCompl Q D) (Z : P →ₗ[F2] D) (X : W →ₗ[F2] V) : Prop :=
  (∀ p : P, D.projectionOnto Q hQ.symm (X p) = Z p) ∧
  Disjoint X.range Q ∧ P ⊔ X.ker = ⊤

abbrev SubspaceAntecedent (P : Submodule F2 W) (Q D : Submodule F2 V)
    (hQ : IsCompl Q D) (Z : P →ₗ[F2] D) :=
  { X : W →ₗ[F2] V // IsSubspaceAntecedent P Q D hQ Z X }

noncomputable def coordinateEquiv (P E : Submodule F2 W) (Q D : Submodule F2 V)
    (hP : IsCompl P E) (hQ : IsCompl Q D) :
    (W →ₗ[F2] V) ≃ₗ[F2] ((P × E) →ₗ[F2] (Q × D)) :=
  LinearEquiv.arrowCongr (P.prodEquivOfIsCompl E hP).symm
    (Q.prodEquivOfIsCompl D hQ).symm

@[simp] theorem coordinateEquiv_apply (P E : Submodule F2 W)
    (Q D : Submodule F2 V) (hP : IsCompl P E) (hQ : IsCompl Q D)
    (X : W →ₗ[F2] V) (p : P × E) :
    coordinateEquiv P E Q D hP hQ X p =
      (Q.prodEquivOfIsCompl D hQ).symm (X ((p.1 : W) + p.2)) := rfl

theorem coordinate_antecedent_iff (P E : Submodule F2 W)
    (Q D : Submodule F2 V) (hP : IsCompl P E) (hQ : IsCompl Q D)
    (Z : P →ₗ[F2] D) (X : W →ₗ[F2] V) :
    IsAntecedent Z (coordinateEquiv P E Q D hP hQ X) ↔
      IsSubspaceAntecedent P Q D hQ Z X := by
  rw [isAntecedent_iff_pointwise]
  unfold IsSubspaceAntecedent
  rw [disjoint_range_iff_zero, sup_kernel_iff_image]
  constructor
  · rintro ⟨hc, hv, hs⟩
    refine ⟨?_, ?_, ?_⟩
    · intro p
      simpa using hc p
    · intro w hw
      let p := (P.prodEquivOfIsCompl E hP).symm w
      have hp : (p.1 : W) + p.2 = w :=
        (P.prodEquivOfIsCompl E hP).apply_symm_apply w
      have hz : (coordinateEquiv P E Q D hP hQ X p).2 = 0 := by
        rw [coordinateEquiv_apply, hp]
        exact (Submodule.prodEquivOfIsCompl_symm_apply_snd_eq_zero Q D hQ).mpr hw
      have hh := congrArg (Q.prodEquivOfIsCompl D hQ) (hv p hz)
      simpa only [coordinateEquiv_apply, hp, LinearEquiv.apply_symm_apply, map_zero] using hh
    · intro w
      let p := (P.prodEquivOfIsCompl E hP).symm w
      have hp : (p.1 : W) + p.2 = w :=
        (P.prodEquivOfIsCompl E hP).apply_symm_apply w
      obtain ⟨b, hb⟩ := hs p
      refine ⟨b, ?_⟩
      have hh := congrArg (Q.prodEquivOfIsCompl D hQ) hb
      simpa only [coordinateEquiv_apply, hp, Submodule.coe_zero, add_zero,
        LinearEquiv.apply_symm_apply] using hh
  · rintro ⟨hc, hv, hs⟩
    refine ⟨?_, ?_, ?_⟩
    · intro p
      simpa using hc p
    · intro p hp
      have hm : X ((p.1 : W) + p.2) ∈ Q :=
        (Submodule.prodEquivOfIsCompl_symm_apply_snd_eq_zero Q D hQ).mp hp
      have hz := hv ((p.1 : W) + p.2) hm
      simp [hz]
    · intro p
      obtain ⟨b, hb⟩ := hs ((p.1 : W) + p.2)
      refine ⟨b, ?_⟩
      simpa only [coordinateEquiv_apply, Submodule.coe_zero, add_zero] using
        congrArg (Q.prodEquivOfIsCompl D hQ).symm hb

noncomputable def subspaceAntecedentEquiv (P E : Submodule F2 W)
    (Q D : Submodule F2 V) (hP : IsCompl P E) (hQ : IsCompl Q D)
    (Z : P →ₗ[F2] D) :
    SubspaceAntecedent P Q D hQ Z ≃
      (Z.range →ₗ[F2] Q) × (E →ₗ[F2] Z.range) :=
  (Equiv.subtypeEquiv (coordinateEquiv P E Q D hP hQ).toEquiv
    (fun X => (coordinate_antecedent_iff P E Q D hP hQ Z X).symm)).trans
    (antecedentEquiv Z)

end DFVSGames.Appendix.DerivativeInduction

namespace DFVSGames.Appendix.AntecedentCount

open DFVSGames.Integration.BinaryLinear
open LinearIdentities
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

variable {W V : Type*} [AddCommGroup W] [Module F2 W]
  [AddCommGroup V] [Module F2 V]

def IsAntecedent (P : Submodule F2 W) (Q : Submodule F2 V)
    (Y : P →ₗ[F2] (V ⧸ Q)) (X : W →ₗ[F2] V) : Prop :=
  compress X Q P = Y ∧ Disjoint X.range Q ∧ P ⊔ X.ker = ⊤

abbrev Antecedent (P : Submodule F2 W) (Q : Submodule F2 V)
    (Y : P →ₗ[F2] (V ⧸ Q)) :=
  {X : W →ₗ[F2] V // IsAntecedent P Q Y X}

theorem isAntecedent_iff_subspace (P : Submodule F2 W)
    (Q D : Submodule F2 V) (hQ : IsCompl Q D)
    (Y : P →ₗ[F2] (V ⧸ Q)) (X : W →ₗ[F2] V) :
    IsAntecedent P Q Y X ↔
      DerivativeInduction.IsSubspaceAntecedent P Q D hQ
        ((Q.quotientEquivOfIsCompl D hQ).toLinearMap.comp Y) X := by
  constructor
  · rintro ⟨hXY, hd, hk⟩
    refine ⟨?_, hd, hk⟩
    intro p
    have h := LinearMap.congr_fun hXY p
    exact congrArg (Q.quotientEquivOfIsCompl D hQ) h
  · rintro ⟨hXY, hd, hk⟩
    refine ⟨?_, hd, hk⟩
    ext p
    apply (Q.quotientEquivOfIsCompl D hQ).injective
    exact hXY p

def subspaceEquiv (P : Submodule F2 W) (Q D : Submodule F2 V)
    (hQ : IsCompl Q D) (Y : P →ₗ[F2] (V ⧸ Q)) :
    Antecedent P Q Y ≃ DerivativeInduction.SubspaceAntecedent P Q D hQ
      ((Q.quotientEquivOfIsCompl D hQ).toLinearMap.comp Y) where
  toFun X := ⟨X.val, (isAntecedent_iff_subspace P Q D hQ Y X.val).mp X.property⟩
  invFun X := ⟨X.val, (isAntecedent_iff_subspace P Q D hQ Y X.val).mpr X.property⟩
  left_inv _X := rfl
  right_inv _X := rfl

end

end DFVSGames.Appendix.AntecedentCount

namespace DFVSGames.Appendix.A5ReverseIndex

open DFVSGames.Integration.BinaryLinear
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V W : Type*} [AddCommGroup V] [Module F2 V]
  [AddCommGroup W] [Module F2 W]

abbrev EarlierA (A' : Submodule F2 V) (i : ℕ) :=
  {A : Submodule F2 V // A ≤ A' ∧ Module.finrank F2 A = i}

abbrev EarlierB (B' : Submodule F2 W) (j : ℕ) :=
  {B : Submodule F2 W // B' ≤ B ∧ Module.finrank F2 (W ⧸ B) = j}

def frequencyEquiv (A A' : Submodule F2 V) (B' B : Submodule F2 W)
    (hA : A ≤ A') (hB : B' ≤ B) :
    (B' →ₗ[F2] (V ⧸ A')) ≃ₗ[F2]
      ((B'.comap B.subtype) →ₗ[F2] ((V ⧸ A) ⧸ A'.map A.mkQ)) :=
  LinearEquiv.arrowCongr
    (SubmoduleInterval.lowerIntervalSpaceEquiv B ⟨B', hB⟩)
    (Submodule.quotientQuotientEquivQuotient A A' hA).symm

def relativeFrequency (A A' : Submodule F2 V) (B' B : Submodule F2 W)
    (hA : A ≤ A') (hB : B' ≤ B) (Y : B' →ₗ[F2] (V ⧸ A')) :=
  frequencyEquiv A A' B' B hA hB Y

abbrev Ancestor (A' : Submodule F2 V) (B' : Submodule F2 W)
    (Y : B' →ₗ[F2] (V ⧸ A')) (i j : ℕ) :=
  Σ A : EarlierA A' i, Σ B : EarlierB B' j,
    AntecedentCount.Antecedent (B'.comap B.val.subtype) (A'.map A.val.mkQ)
      (relativeFrequency A.val A' B' B.val A.property.1 B.property.1 Y)

end

end DFVSGames.Appendix.A5ReverseIndex

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_A5ForwardIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace DFVSGames.Appendix.A5FrequencyTransport

open DFVSGames.Integration.BinaryLinear
open DFVSGames.Appendix.LinearIdentities
open DFVSGames.Appendix.NaturalTransport

variable {V W : Type*} [AddCommGroup V] [Module F2 V]
  [AddCommGroup W] [Module F2 W]

theorem quotient_relativeFrequency_apply
    (A A' : Submodule F2 V) (B' B : Submodule F2 W)
    (hA : A ≤ A') (hB : B' ≤ B)
    (Y : B' →ₗ[F2] (V ⧸ A')) (b : B'.comap B.subtype) :
    Submodule.quotientQuotientEquivQuotient A A' hA
      (A5ReverseIndex.relativeFrequency A A' B' B hA hB Y b) =
    Y ((SubmoduleInterval.lowerIntervalSpaceEquiv B ⟨B', hB⟩).symm b) := by
  change Submodule.quotientQuotientEquivQuotient A A' hA
      ((Submodule.quotientQuotientEquivQuotient A A' hA).symm
        (Y ((SubmoduleInterval.lowerIntervalSpaceEquiv B ⟨B', hB⟩).symm b))) = _
  exact (Submodule.quotientQuotientEquivQuotient A A' hA).apply_symm_apply _

theorem quotient_compress_apply
    (A A' : Submodule F2 V) (B' B : Submodule F2 W)
    (hA : A ≤ A') (X : B →ₗ[F2] (V ⧸ A)) (b : B'.comap B.subtype) :
    Submodule.quotientQuotientEquivQuotient A A' hA
      (compress X (A'.map A.mkQ) (B'.comap B.subtype) b) =
    Submodule.mapQ A A' LinearMap.id hA (X b.val) := rfl

theorem compression_eq_relativeFrequency_of_pointwise
    (A A' : Submodule F2 V) (B' B : Submodule F2 W)
    (hA : A ≤ A') (hB : B' ≤ B)
    (X : B →ₗ[F2] (V ⧸ A)) (Y : B' →ₗ[F2] (V ⧸ A'))
    (hY : ∀ b : B', Submodule.mapQ A A' LinearMap.id hA
      (X ⟨b.val, hB b.property⟩) = Y b) :
    compress X (A'.map A.mkQ) (B'.comap B.subtype) =
      A5ReverseIndex.relativeFrequency A A' B' B hA hB Y := by
  ext b
  apply (Submodule.quotientQuotientEquivQuotient A A' hA).injective
  rw [quotient_compress_apply, quotient_relativeFrequency_apply]
  exact hY ((SubmoduleInterval.lowerIntervalSpaceEquiv B ⟨B', hB⟩).symm b)

variable [FiniteDimensional F2 V] [FiniteDimensional F2 W]
  [Finite V] [Finite W]

omit [FiniteDimensional F2 V] [Finite V] in
theorem quotientFactor_mapQ
    (A : Submodule F2 V) (C : Submodule F2 (V ⧸ A))
    (hA : A ≤ C.comap A.mkQ) (u : V ⧸ A) :
    quotientFactor A C
      (Submodule.mapQ A (C.comap A.mkQ) LinearMap.id hA u) = C.mkQ u := by
  obtain ⟨x, rfl⟩ := A.mkQ_surjective u
  change quotientFactor A C ((C.comap A.mkQ).mkQ x) = C.mkQ (A.mkQ x)
  exact quotientFactor_mkQ A C x

omit [FiniteDimensional F2 V] [FiniteDimensional F2 W] [Finite V] [Finite W] in
theorem dualFactor_quotient
    (A : Submodule F2 V) (B : Submodule F2 W)
    (C : Submodule F2 (V ⧸ A)) (D : Submodule F2 B)
    (Z : D →ₗ[F2] ((V ⧸ A) ⧸ C)) (b : D.map B.subtype) :
    quotientFactor A C (dualFactor A B C D Z b) =
      Z ((outputFactor B D).symm b) := by
  change quotientFactor A C ((quotientFactor A C).symm
    (Z ((outputFactor B D).symm b))) = _
  exact (quotientFactor A C).apply_symm_apply _

omit [FiniteDimensional F2 W] [Finite W] in
theorem outputFactor_symm_as_inclusion
    (B : Submodule F2 W) (D : Submodule F2 B)
    (hB : D.map B.subtype ≤ B) (b : D.map B.subtype) :
    (((outputFactor B D).symm b : D) : B) = ⟨b.val, hB b.property⟩ := by
  apply Subtype.ext
  have hh := outputFactor_val B D ((outputFactor B D).symm b)
  rw [LinearEquiv.apply_symm_apply] at hh
  exact hh.symm

omit [FiniteDimensional F2 V] [FiniteDimensional F2 W] [Finite V] [Finite W] in
theorem compression_eq_relativeFrequency_dualFactor
    (A : Submodule F2 V) (B : Submodule F2 W)
    (C : Submodule F2 (V ⧸ A)) (D : Submodule F2 B)
    (hA : A ≤ C.comap A.mkQ) (hB : D.map B.subtype ≤ B)
    (X : B →ₗ[F2] (V ⧸ A)) :
    compress X ((C.comap A.mkQ).map A.mkQ) ((D.map B.subtype).comap B.subtype) =
      A5ReverseIndex.relativeFrequency A (C.comap A.mkQ) (D.map B.subtype) B hA hB
        (dualFactor A B C D (compress X C D)) := by
  apply compression_eq_relativeFrequency_of_pointwise
  intro b
  apply (quotientFactor A C).injective
  rw [quotientFactor_mapQ, dualFactor_quotient]
  change C.mkQ (X ⟨b.val, hB b.property⟩) =
    C.mkQ (X (((outputFactor B D).symm b : D) : B))
  rw [outputFactor_symm_as_inclusion B D hB b]

omit [FiniteDimensional F2 V] [FiniteDimensional F2 W] [Finite V] [Finite W] in
theorem isAntecedent_relativeFrequency_dualFactor
    (A : Submodule F2 V) (B : Submodule F2 W)
    (C : Submodule F2 (V ⧸ A)) (D : Submodule F2 B)
    (hA : A ≤ C.comap A.mkQ) (hB : D.map B.subtype ≤ B)
    (X : B →ₗ[F2] (V ⧸ A))
    (hdis : Disjoint X.range C) (hcover : D ⊔ X.ker = ⊤) :
    AntecedentCount.IsAntecedent ((D.map B.subtype).comap B.subtype)
      ((C.comap A.mkQ).map A.mkQ)
      (A5ReverseIndex.relativeFrequency A (C.comap A.mkQ) (D.map B.subtype) B hA hB
        (dualFactor A B C D (compress X C D))) X := by
  refine ⟨compression_eq_relativeFrequency_dualFactor A B C D hA hB X, ?_, ?_⟩
  · rw [Submodule.map_comap_eq_of_surjective A.mkQ_surjective C]
    exact hdis
  · rw [Submodule.comap_map_eq_of_injective (f := B.subtype) Subtype.val_injective D]
    exact hcover

end DFVSGames.Appendix.A5FrequencyTransport
end

noncomputable section
namespace DFVSGames.Appendix.A5ForwardIndex

open DFVSGames.Integration.BinaryLinear
open DFVSGames.Fourier.MatrixRestrictions (order)
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local instance] OperatorNorm.quotientFinite OperatorNorm.compressedDualFintype

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

abbrev Index (d : ℕ) :=
  Σ r : A13Index.BoundedPositiveTriple (E := E) (F := F) d,
    A5Passage.Passage r.val.2.2 (d - A13Index.size r.val)

def descendant {d : ℕ} (a : Index (E := E) (F := F) d) :
    A13Index.Triple (E := E) (F := F) :=
  ⟨a.2.2.val.1.comap a.1.val.1.mkQ, a.2.2.val.2.map a.1.val.2.1.subtype,
    NaturalTransport.dualFactor a.1.val.1 a.1.val.2.1 a.2.2.val.1 a.2.2.val.2
      (LinearIdentities.compress a.1.val.2.2 a.2.2.val.1 a.2.2.val.2)⟩

def sourceI {d : ℕ} (a : Index (E := E) (F := F) d) : ℕ :=
  Module.finrank F2 a.1.val.1

def sourceJ {d : ℕ} (a : Index (E := E) (F := F) d) : ℕ :=
  Module.finrank F2 (F ⧸ a.1.val.2.1)

def targetRank (r : A13Index.Triple (E := E) (F := F)) : ℕ :=
  Module.finrank F2 r.2.2.range

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem earlierA_le {d : ℕ} (a : Index (E := E) (F := F) d) :
    a.1.val.1 ≤ (descendant a).1 := by
  intro x hx
  change a.1.val.1.mkQ x ∈ a.2.2.val.1
  rw [show a.1.val.1.mkQ x = 0 from (Submodule.Quotient.mk_eq_zero _).mpr hx]
  exact a.2.2.val.1.zero_mem

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem earlierB_le {d : ℕ} (a : Index (E := E) (F := F) d) :
    (descendant a).2.1 ≤ a.1.val.2.1 := by
  rintro x ⟨b, hb, rfl⟩
  exact b.property

abbrev Fiber (d : ℕ) (r : A13Index.Triple (E := E) (F := F)) (i j : ℕ) :=
  {a : Index (E := E) (F := F) d //
    descendant a = r ∧ sourceI a = i ∧ sourceJ a = j}

def encode (d : ℕ) (r : A13Index.Triple (E := E) (F := F)) (i j : ℕ)
    (a : Fiber d r i j) : A5ReverseIndex.Ancestor r.1 r.2.1 r.2.2 i j := by
  rcases a with ⟨a, hr, hi, hj⟩
  cases hr
  refine ⟨⟨a.1.val.1, earlierA_le a, hi⟩,
    ⟨a.1.val.2.1, earlierB_le a, hj⟩, ⟨a.1.val.2.2, ?_⟩⟩
  exact A5FrequencyTransport.isAntecedent_relativeFrequency_dualFactor
    a.1.val.1 a.1.val.2.1 a.2.2.val.1 a.2.2.val.2
    (earlierA_le a) (earlierB_le a) a.1.val.2.2
    a.2.2.property.1.symm a.2.2.property.2.2.1

def earlierTriple {A' : Submodule F2 E} {B' : Submodule F2 F}
    {Y : B' →ₗ[F2] (E ⧸ A')} {i j : ℕ}
    (a : A5ReverseIndex.Ancestor A' B' Y i j) : A13Index.Triple (E := E) (F := F) :=
  ⟨a.1.val, a.2.1.val, a.2.2.val⟩

local instance indexFintype (d : ℕ) : Fintype (Index (E := E) (F := F) d) := by
  letI := A13Index.boundedPositiveTripleFintype (E := E) (F := F) d
  exact inferInstance

end DFVSGames.Appendix.A5ForwardIndex
end

noncomputable section
namespace DFVSGames.Appendix.A5ReverseSum

open scoped BigOperators
open DFVSGames.Integration.BinaryLinear
open DFVSGames.Fourier.MatrixRestrictions (order)
open Derivatives
open A5ForwardIndex

attribute [local instance] Classical.propDecidable
attribute [local instance] OperatorNorm.quotientFinite OperatorNorm.compressedDualFintype
attribute [local instance] SubspaceExtensions.subspaceFintype

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

def actualMoment (f : (E →ₗ[F2] F) → ℝ)
    (r : A13Index.Triple (E := E) (F := F)) : ℝ :=
  𝔼 T, (𝔼 N, mapDerivative r.2.2 (hybridDerivative r.1 r.2.1 T f) N ^ 2) ^ 2

def targetWeight (d : ℕ) (f : (E →ₗ[F2] F) → ℝ)
    (r : A13Index.Triple (E := E) (F := F)) : ℝ :=
  if order r.1 r.2.1 ≤ d then actualMoment f r else 0

end DFVSGames.Appendix.A5ReverseSum
end

noncomputable section
namespace DFVSGames.Appendix.A5Induction

open scoped BigOperators
open DFVSGames.Fourier.MatrixCharacters DFVSGames.Fourier.MatrixFourier
open DFVSGames.Fourier.MatrixRestrictions
open DFVSGames.Appendix.Derivatives DFVSGames.Appendix.DerivativeDegree
open DFVSGames.Appendix.LevelInequality (frequencyRank)
attribute [local instance] Classical.propDecidable
attribute [local instance] OperatorNorm.quotientFinite OperatorNorm.compressedDualFintype
attribute [local instance] SubspaceExtensions.subspaceFintype

universe u v

def BoundAtDegree (d : ℕ) : Prop :=
  ∀ {E : Type u} {F : Type v}
    [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
    [FiniteDimensional F2 E] [FiniteDimensional F2 F]
    [Finite E] [Finite F]
    [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
    (f : (E →ₗ[F2] F) → ℝ),
    DegreeAtMost d f →
      (𝔼 M, f M ^ 4) ≤ (2 : ℝ) ^ (100 * d * d) * hybridMomentSum d f

variable {E : Type u} {F : Type v}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
variable [Finite E] [Finite F]
variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

def dampedMapMoment (d : ℕ) (f : (E →ₗ[F2] F) → ℝ) : ℝ :=
  ∑ X : F →ₗ[F2] E,
    (1 / 2 : ℝ) ^ (31 * d * (frequencyRank X + 1) + 4 * d * frequencyRank X) *
      (𝔼 N, mapDerivative X f N ^ 2) ^ 2

def dampedHybridMoment (d : ℕ) (f : (E →ₗ[F2] F) → ℝ) : ℝ :=
  ∑ s : HybridIndex (E := E) (F := F) d,
    𝔼 T, dampedMapMoment d (hybridDerivative s.val.1 s.val.2 T f)

def postA5Sum (X : F →ₗ[F2] E) (e : ℕ) (f : (E →ₗ[F2] F) → ℝ) : ℝ :=
  ∑ q : A5Passage.Passage X e, 𝔼 S : Parameter X.range X.ker,
    (𝔼 N, mapDerivative (LinearIdentities.compress X q.2.val.1 q.2.val.2)
      (hybridDerivative q.2.val.1 q.2.val.2 (embed X.range X.ker S) f) N ^ 2)^2

end DFVSGames.Appendix.A5Induction
end

end OAI
end


