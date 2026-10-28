-- Prove2me | Definitions.Def_OAIQ082C025
-- name    : OAIQ082C025
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T14:35:04.759589+00:00
-- url     : https://prove2.me/theorems/df193cca-5acd-4566-9b33-b6ed1e39b574
-- title:
--   Definitions bundle OAIQ082C025 of the split of OpenAI, Additive hardness and unbounded configuration gaps in bin packing (result family 118)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.BinPackingGap.main_results`, carved from OpenAI's openai/math development (OpenAI, *Additive hardness and unbounded configuration gaps in bin packing (result family 118)*, OpenAI Math Release, September 24, 2026, result family 118, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 253 declarations of OpenAI's Lean: 104 definitions and 149 theorems. The definitions and types are `OAI.BinPackingGap.GraphPackingGlobalLoop.aggregateWidth`, `OAI.BinPackingGap.GraphPackingGlobalLoop.bodyBudget`, `OAI.BinPackingGap.GraphPackingGlobalLoop.edgeWord`, `OAI.BinPackingGap.GraphPackingGlobalLoop.stream`, `OAI.BinPackingGap.GraphPackingGlobalPhases.globalCount`, `OAI.BinPackingGap.GraphPackingGlobalPhases.globalsBudget`, `OAI.BinPackingGap.GraphPackingGlobalPhases.globalsInput`, `OAI.BinPackingGap.GraphPackingGlobalPhases.globalsWord`, `OAI.BinPackingGap.GraphPackingGlobalPhases.resetBudget`, `OAI.BinPackingGap.GraphPackingGlobalPhases.unitInput`, `OAI.BinPackingGap.GraphPackingGlobalPhases.unitPools`, `OAI.BinPackingGap.GraphPackingGlobalSemantics.flagOutput`, `OAI.BinPackingGap.GraphPackingGlobalSemantics.globalOutput`, `OAI.BinPackingGap.GraphPackingJobs.cleanupPhases`, `OAI.BinPackingGap.GraphPackingJobs.cleanupWidthTimePolynomial`, `OAI.BinPackingGap.GraphPackingJobs.emitted`, `OAI.BinPackingGap.GraphPackingJobs.finalBase`, `OAI.BinPackingGap.GraphPackingJobs.finalTapes`, `OAI.BinPackingGap.GraphPackingJobs.prefixPhases`, `OAI.BinPackingGap.GraphPackingJobs.repeatFinalInputs`, `OAI.BinPackingGap.GraphPackingJobs.repeatLoopPolynomial`, `OAI.BinPackingGap.GraphPackingJobs.repeatPhases`, `OAI.BinPackingGap.GraphPackingJobs.repeatSetPolynomial`, `OAI.BinPackingGap.GraphPackingJobs.repeatWidthPolynomial`, `OAI.BinPackingGap.GraphPackingJobs.resetInputs`, `OAI.BinPackingGap.GraphPackingJobs.setupPhases`, `OAI.BinPackingGap.GraphPackingJobs.setupSetPolynomial`, `OAI.BinPackingGap.GraphPackingJobs.setupTapes`, `OAI.BinPackingGap.GraphPackingJobs.setupValues`, `OAI.BinPackingGap.GraphPackingPreparation.edgeTapes`, `OAI.BinPackingGap.GraphPackingPreparation.factorValues`, `OAI.BinPackingGap.GraphPackingPreparation.fieldTapes`, `OAI.BinPackingGap.GraphPackingPreparation.finalValues`, `OAI.BinPackingGap.GraphPackingPreparation.firstPowerValues`, `OAI.BinPackingGap.GraphPackingPreparation.parsePhases`, `OAI.BinPackingGap.GraphPackingPreparation.parsePolynomial`, `OAI.BinPackingGap.GraphPackingPreparation.powerBudget`, `OAI.BinPackingGap.GraphPackingPreparation.powerPhases`, `OAI.BinPackingGap.GraphPackingPreparation.secondPowerValues`, `OAI.BinPackingGap.GraphPackingPreparation.vertexTapes` and 64 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `BinPacking_Arithmetic_PackingRegisterUpdate`, `BinPacking_Hardness_LiteralSlotGraphComputation`, `BinPacking_Hardness_LiteralSlotGraphEnumeration`, `BinPacking_Machines_GraphPackingGlobalExecution`, `BinPacking_Machines_GraphPackingJobCleanup`, `BinPacking_Machines_GraphPackingJobEdge`, `BinPacking_Machines_GraphPackingJobList`, `BinPacking_Machines_GraphPackingMachine`, `BinPacking_Machines_GraphPackingPreparation`, `BinPacking_Machines_GraphPackingPreparationFinish`, `BinPacking_Machines_GraphPackingStockStreams`, `BinPacking_Machines_GraphPackingVerticesBound`, `BinPacking_Machines_PackingCountedProgram`, `BinPacking_Machines_PackingJobLoop`, `BinPacking_Machines_PackingPowerProgram`, `BinPacking_Machines_PackingSetupGraph`, `BinPacking_Machines_PackingVertexUpdate`, `BinPacking_Packing_PackingAssignments`, `BinPacking_Packing_PackingGapDefinitions`, `BinPacking_Results_OptimalSearch`, `BinPacking_Search_ApproximationImpliesP`, `BinPacking_Search_ExtensionVerifier`, `BinPacking_Search_SearchFinalizeMachine`, `BinPacking_Search_SearchInitialItemsMachine`, `BinPacking_Search_SearchInitializeEncoding`, `BinPacking_Search_SearchPrepareMachine`, `BinPacking_Search_SearchStageMachines`, `BinPacking_Search_SearchUpdateMachine`.
--
--   **Imports.** It imports the published bundle `Def_BinPackingGap`; the bundles `OAIQ082C017`, `OAIQ082C020`, `OAIQ082C021` and `OAIQ082C022` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ082C027` and `OAIQ082C028`; the proofs of `OAI_BinPackingGap_pEqualsNP_of_absoluteAdditiveAlgorithm` and `OAI.BinPackingGap.pEqualsNP_of_absoluteAdditiveAlgorithm_oaiq082`.
-- source:
--   OpenAI, Additive hardness and unbounded configuration gaps in bin packing (result family 118), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 118; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Additive-hardness-and-unbounded-configuration-gaps-in-bin-packing-September-24-2026/Additive-hardness-and-unbounded-configuration-gaps-in-bin-packing-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Std
import Definitions.Def_BinPackingGap
import Definitions.Def_OAIQ082C017
import Definitions.Def_OAIQ082C020
import Definitions.Def_OAIQ082C021
import Definitions.Def_OAIQ082C022

section
-- module Solutions.OAIQ082_BP.BinPacking_Packing_PackingGapDefinitions
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.Packing.instDecidableEqTableBin _root_.OAI.BinPackingGap.Packing.instFintypeTableBin _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.PairFirstProjection

open Turing BinPackingGames.Foundations.Complexity MachineComposition

theorem finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet computation.tm :=
  MachineCanonicalOutput.computableInPolyTime_finite_alphabet program cleanupTapes
    cleanup_complete CookLevin.pairBits id (fun p => p.1) rawTime rawRun

end BinPackingGap.PairFirstProjection

namespace BinPackingGap

open Turing BinPackingGames.Foundations.Complexity

theorem inP_to_inNP {L : BitLanguage} (hL : InP L) : CookLevin.InNP L := by
  classical
  obtain ⟨decider, computation, finiteAlphabet, correct⟩ := hL
  let combined := MachineSequential.composeBits PairFirstProjection.computation computation
  have combinedFinite : MachineFiniteAlphabet.FiniteAlphabet combined.tm :=
    MachineFiniteAlphabet.composeBits PairFirstProjection.computation computation
      PairFirstProjection.finiteAlphabet finiteAlphabet
  let verifier : CookLevin.NPVerifier := {
    witnessBound := 0
    verify := fun p => decider p.1
    computation := combined
    finiteAlphabet := fun k => by
      letI : Finite (combined.tm.Γ k) := combinedFinite k
      exact Fintype.ofFinite (combined.tm.Γ k) }
  refine ⟨verifier, ?_⟩
  intro x
  change L x ↔ ∃ witness : List Bool,
    witness.length ≤ (0 : Polynomial Nat).eval x.length ∧ decider x = true
  constructor
  · intro hx
    exact ⟨[], by simp, (correct x).mp hx⟩
  · rintro ⟨_, _, accepted⟩
    exact (correct x).mpr accepted

theorem classP_subset_classNP : ClassP ⊆ ClassNP :=
  fun _ h => inP_to_inNP h

theorem pEqualsNP_iff_np_subset_p :
    PEqualsNP ↔ ∀ L : BitLanguage, CookLevin.InNP L → InP L := by
  constructor
  · intro equal L hL
    change L ∈ ClassP
    rw [equal]
    exact hL
  · intro inclusion
    apply Set.Subset.antisymm classP_subset_classNP
    exact fun L hL => inclusion L hL

theorem PEqualsNP.inP (h : PEqualsNP) {L : BitLanguage}
    (hL : CookLevin.InNP L) : InP L :=
  pEqualsNP_iff_np_subset_p.mp h L hL

end BinPackingGap

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_SearchInitializeEncoding
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.Packing.instDecidableEqTableBin _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.SearchSemantics

open ExtensionQuery

theorem step_invariant {D : List Bool → Bool} (hD : DecidesExtension D)
    {r : RawInstance} {hr : r.Valid} {s : State} (hs : Invariant r hr s) :
    Invariant r hr (step D s) := by
  rcases hs with ⟨hitems, hs⟩
  refine ⟨(update_items s (D (query s))).trans hitems, ?_⟩
  cases hp : s.phase with
  | invalid => simp only [hp] at hs
  | done =>
      simpa only [step_done D s hp, hp] using hs
  | find =>
      simp only [hp] at hs
      change FindInvariant r hr s at hs
      have hbinspos := hs.bins_pos
      have hquery : query s =
          BinaryEncoding.extensionBits s.bins r (List.replicate r.length none) := by
        simp [query, hp, hitems, hs.fixed_none]
      by_cases ha : D (query s) = true
      · have he := (hD s.bins r (List.replicate r.length none)).mp
          (by simpa only [hquery] using ha)
        have hopt := (ext_none_opt_iff r hr s.bins).mp he
        have hb : s.bins = opt (r.toInstance hr) := Nat.le_antisymm hs.bins_le hopt
        have hn : 0 < r.length := lt_of_lt_of_le hs.bins_pos
          (hs.bins_le.trans (opt_le_n (r.toInstance hr)))
        simp only [step, update, hp, ha, ↓reduceIte]
        refine ⟨hb, hs.bins_pos, hn, hs.bins_pos, ?_, ?_, ?_, ?_⟩
        · simp [hs.fixed_none]
        · simpa [hs.fixed_none] using prefix_none r.length
        · simpa [hs.fixed_none] using he
        · intro j hj
          change j < 0 at hj
          omega
      · have hno : ¬ Ext s.bins r (List.replicate r.length none) := by
          intro he
          exact ha (by simpa only [hquery] using
            (hD s.bins r (List.replicate r.length none)).mpr he)
        have hb : s.bins + 1 ≤ opt (r.toInstance hr) := by
          have := mt (ext_none_opt_iff r hr s.bins).mpr hno
          omega
        simp only [step, update, hp, ha, Bool.false_eq_true, ↓reduceIte]
        exact ⟨by dsimp; omega, hb, hs.item_zero, hs.label_zero, hs.fixed_none⟩
  | fill =>
      simp only [hp] at hs
      change FillInvariant r hr s at hs
      have hitem := hs.item_lt
      have hlength := hs.fixed_length
      have hquery : query s = BinaryEncoding.extensionBits s.bins r
          (s.fixed.set s.item (some s.label)) := by simp [query, hp, hitems]
      by_cases ha : D (query s) = true
      · have he := (hD s.bins r (s.fixed.set s.item (some s.label))).mp
          (by simpa only [hquery] using ha)
        have hpref := prefix_set hs.prefix
          (show s.item < s.fixed.length by omega) s.label
        by_cases hlast : s.item + 1 = r.length
        · simp only [step, update, hp, ha, hitems, hlast, ↓reduceIte]
          exact ⟨hs.bins_eq, rfl, rfl, by simpa using hs.fixed_length,
            by simpa [hlast] using hpref, he⟩
        · simp only [step, update, hp, ha, hitems, hlast, ↓reduceIte]
          refine ⟨hs.bins_eq, hs.bins_pos, by dsimp; omega, hs.bins_pos,
            by simpa using hs.fixed_length, hpref, he, ?_⟩
          intro j hj
          change j < 0 at hj
          omega
      · have hno : ¬ Ext s.bins r (s.fixed.set s.item (some s.label)) := by
          intro he
          exact ha (by simpa only [hquery] using
            (hD s.bins r (s.fixed.set s.item (some s.label))).mpr he)
        obtain ⟨q, hqb, hqe⟩ := ext_next_exists hs.extends
          (show s.item < s.fixed.length by omega)
        have hlq : s.label ≤ q := by
          by_contra h
          exact hs.rejected q (by omega) hqe
        have hneq : q ≠ s.label := by
          intro h
          exact hno (h ▸ hqe)
        have hlabel : s.label + 1 < s.bins := by omega
        simp only [step, update, hp, ha, Bool.false_eq_true, ↓reduceIte]
        refine ⟨hs.bins_eq, hs.bins_pos, hs.item_lt, hlabel, hs.fixed_length,
          hs.prefix, hs.extends, ?_⟩
        intro j hj he
        change j < s.label + 1 at hj
        by_cases hjl : j < s.label
        · exact hs.rejected j hjl he
        · have hje : j = s.label := by omega
          exact hno (hje ▸ he)

theorem run_finishes {D : List Bool → Bool} (hD : DecidesExtension D)
    {r : RawInstance} {hr : r.Valid} {s : State} (hs : Invariant r hr s)
    (t : Nat) (ht : rank s ≤ t) :
    (run D t s).phase = .done ∧ Invariant r hr (run D t s) := by
  induction t generalizing s with
  | zero =>
      have hd : s.phase = .done := by
        by_contra hd
        have := rank_pos hs hd
        omega
      exact ⟨hd, hs⟩
  | succ t ih =>
      by_cases hd : s.phase = .done
      · simpa only [run_done D s hd (t + 1)] using And.intro hd hs
      · have hnext := step_invariant hD hs
        have hlt := rank_step_lt (D := D) hs hd
        have hdone := ih hnext (by omega)
        simpa only [run] using hdone

theorem search_optimal {D : List Bool → Bool} (hD : DecidesExtension D)
    (r : RawInstance) (hr : r.Valid) :
    ∃ p : RawPacking, search D r true = some p ∧
      p.Feasible r ∧ p.bins = opt (r.toInstance hr) := by
  let s := run D (fuel r) (initial r true)
  have hfinal := run_finishes hD (initial_invariant r hr) (fuel r) (rank_initial_le r)
  have hd : s.phase = .done := hfinal.1
  have hinv : DoneInvariant r hr s := by
    have hi := hfinal.2.2
    simpa only [show run D (fuel r) (initial r true) = s from rfl, hd] using hi
  refine ⟨⟨s.bins, labels s.fixed⟩, ?_, ?_, hinv.bins_eq⟩
  · change output s = some _
    simp [output, hd]
  · exact ext_complete hinv.extends (by simpa [hinv.fixed_length] using hinv.prefix)

end BinPackingGap.SearchSemantics

namespace BinPackingGap.SearchMachineComposition

open Turing BinPackingGames.Foundations.Complexity
open SearchSemantics SearchEncoding

theorem algorithm_optimal {D : List Bool → Bool} (correct : DecidesExtension D)
    (items : RawInstance) (valid : items.Valid) :
    ∃ packing : RawPacking,
      algorithm D (BinaryEncoding.rawInstanceBits items) = some packing ∧
      packing.Feasible items ∧ packing.bins = opt (items.toInstance valid) := by
  have accepted : ExtensionCertificate.validItems items = true :=
    (ExtensionCertificate.validItems_eq_true_iff items).mpr valid
  simpa only [algorithm_encoded, accepted] using search_optimal correct items valid

noncomputable def loopComputation (stages : Stages) (D : List Bool → Bool)
    (decision : TM2ComputableInPolyTime (id : List Bool → List Bool)
      (fun answer => [answer]) D) :
    TM2ComputableInPolyTime (MachineBoundedIteration.inputBits stateBits) stateBits
      (MachineBoundedIteration.iterate (step D)) :=
  MachineBoundedIteration.computation stateBits (step D)
    (bodyComputation stages D decision) growthPolynomial (growthBound D)

theorem loopComputation_finiteAlphabet (stages : Stages) (D : List Bool → Bool)
    (decision : TM2ComputableInPolyTime (id : List Bool → List Bool)
      (fun answer => [answer]) D)
    (finite : MachineFiniteAlphabet.FiniteAlphabet decision.tm) :
    MachineFiniteAlphabet.FiniteAlphabet (loopComputation stages D decision).tm :=
  MachineBoundedIteration.computation_finiteAlphabet stateBits (step D)
    (bodyComputation stages D decision) growthPolynomial (growthBound D)
    (bodyComputation_finiteAlphabet stages D decision finite)

noncomputable def computation (stages : Stages) (D : List Bool → Bool)
    (decision : TM2ComputableInPolyTime (id : List Bool → List Bool)
      (fun answer => [answer]) D) :
    TM2ComputableInPolyTime (id : List Bool → List Bool)
      BinaryEncoding.packingResultBits (algorithm D) :=
  MachineSequential.composeBits (f := «initialize_»)
    (g := fun p => output (MachineBoundedIteration.iterate (step D) p))
    stages.initializeComputation
    (MachineSequential.composeBits (f := MachineBoundedIteration.iterate (step D))
      (g := output) (loopComputation stages D decision) stages.finalizeComputation)

theorem computation_finiteAlphabet (stages : Stages) (D : List Bool → Bool)
    (decision : TM2ComputableInPolyTime (id : List Bool → List Bool)
      (fun answer => [answer]) D)
    (finite : MachineFiniteAlphabet.FiniteAlphabet decision.tm) :
    MachineFiniteAlphabet.FiniteAlphabet (computation stages D decision).tm := by
  exact MachineFiniteAlphabet.composeBits stages.initializeComputation _
    stages.initializeFinite (MachineFiniteAlphabet.composeBits _ stages.finalizeComputation
      (loopComputation_finiteAlphabet stages D decision finite) stages.finalizeFinite)

end BinPackingGap.SearchMachineComposition

namespace BinPackingGap.SearchOptimalConstruction

open Turing BinPackingGames.Foundations.Complexity

noncomputable def ofDecision (stages : SearchMachineComposition.Stages)
    (D : List Bool → Bool)
    (decision : TM2ComputableInPolyTime (id : List Bool → List Bool)
      (fun answer => [answer]) D)
    (finite : MachineFiniteAlphabet.FiniteAlphabet decision.tm)
    (correct : SearchSemantics.DecidesExtension D) : AbsoluteAdditiveAlgorithm 0 where
  run := SearchMachineComposition.algorithm D
  computation := SearchMachineComposition.computation stages D decision
  finiteAlphabet := SearchMachineComposition.computation_finiteAlphabet
    stages D decision finite
  guarantee items valid := by
    obtain ⟨packing, returned, feasible, optimal⟩ :=
      SearchMachineComposition.algorithm_optimal correct items valid
    exact ⟨packing, returned, feasible, by simp [optimal]⟩

end BinPackingGap.SearchOptimalConstruction

namespace BinPackingGap.SearchInitializeEncoding

open BinPackingGames.Foundations.Complexity

def classify (input : List Bool) : Data :=
  match BinaryEncoding.decodeRawInstance input with
  | none => ([], false)
  | some items => (items, ExtensionCertificate.validItems items)

def dataBits (data : Data) : List Bool :=
  data.2 :: (encodeWord data.1.length ++ BinaryEncoding.rawInstanceBits data.1)

def emit (data : Data) : Nat × SearchSemantics.State :=
  (if data.2 then SearchSemantics.fuel data.1 else 0,
    SearchSemantics.initial data.1 data.2)

theorem emit_classify (input : List Bool) :
    emit (classify input) = SearchMachineComposition.initialize_ input := by
  unfold classify SearchMachineComposition.initialize_
  cases BinaryEncoding.decodeRawInstance input <;> rfl

end BinPackingGap.SearchInitializeEncoding

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_SearchInitialItemsMachine
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.Packing.instDecidableEqTableBin _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.SearchInitialItemsMachine

open Turing BinPackingGames.Foundations.Complexity MachineComposition
open SearchInitializeEncoding
open BinPackingGames.Reduction.MachineTransfer

def itemsInTime (items : RawInstance) (valid : Bool) (raw : List Bool) (count : Nat) :
    StateTransition.EvalsToInTime machine.step
      (cfg (some (.control .marker)) valid
        (tapes raw (BinaryEncoding.rawInstanceBits items) [] [] [] (encodeWord count)))
      (some (cfg (some (.control .countOut))
        (valid && ExtensionCertificate.validItems items)
        (tapes raw [] [] [] [] (encodeWord (count + items.length)))))
      (loopTime items) := by
  induction items generalizing valid count with
  | nil =>
      simpa [loopTime, ExtensionCertificate.validItems,
        BinaryEncoding.rawInstanceBits, BinaryEncoding.listBits] using
        oneStep (markerStep valid false raw [] (encodeWord count))
  | cons item items ih =>
      rcases item with ⟨a, d⟩
      have marker := oneStep (markerStep valid true raw
        (BinaryEncoding.natBits a ++ BinaryEncoding.natBits d ++
          BinaryEncoding.rawInstanceBits items) (encodeWord count))
      have numerator := numeratorInTime valid raw
        (BinaryEncoding.natBits d ++ BinaryEncoding.rawInstanceBits items)
        (encodeWord (count + 1)) a
      have positive := oneStep (positiveStep valid raw
        (BinaryEncoding.natBits d ++ BinaryEncoding.rawInstanceBits items) a.bits
        (encodeWord (count + 1)))
      have nonempty : decide (a.bits ≠ []) = decide (0 < a) := by
        simp only [ne_eq, bits_eq_nil_iff, Nat.pos_iff_ne_zero]
      rw [nonempty] at positive
      have denominator := denominatorInTime (valid && decide (0 < a)) raw
        (BinaryEncoding.rawInstanceBits items) (encodeWord (count + 1)) a d
      have comparison := comparisonInTime (valid && decide (0 < a)) raw
        (BinaryEncoding.rawInstanceBits items) (encodeWord (count + 1)) a d
      have clear := clearInTime (valid && decide (0 < a) && decide (a ≤ d)) raw
        (BinaryEncoding.rawInstanceBits items) a.bits d.bits (encodeWord (count + 1))
      have rest := ih (valid && decide (0 < a) && decide (a ≤ d)) (count + 1)
      have count_succ : true :: encodeWord count = encodeWord (count + 1) := by
        simp [encodeWord, List.replicate_succ]
      rw [count_succ] at marker
      simp only [List.append_assoc] at marker
      have trace := join (join (join (join (join (join marker numerator) positive)
        denominator) comparison) clear) rest
      have bounded : 1 + (2 * a.size + 2) + 1 + (2 * d.size + 2) +
          (BinaryOrderMachine.preservingSteps a.size d.size + 1) +
          (a.bits.length + d.bits.length + 2) + loopTime items ≤
          loopTime ((a, d) :: items) := by
        have h := BinaryOrderMachine.preservingSteps_le a.size d.size
        simp only [loopTime, rowTime, Nat.size_eq_bits_len]
        omega
      simpa only [BinaryEncoding.rawInstanceBits, BinaryEncoding.listBits,
        BinaryEncoding.pairBits, List.length_cons, List.append_assoc,
        validItems_cons, Bool.and_assoc, Nat.add_assoc, Nat.add_comm 1 items.length] using
        enlarge trace bounded

theorem loopTime_le (items : RawInstance) :
    loopTime items ≤ 5 * (BinaryEncoding.rawInstanceBits items).length := by
  induction items with
  | nil => simp [loopTime, BinaryEncoding.rawInstanceBits, BinaryEncoding.listBits]
  | cons item items ih =>
      rcases item with ⟨a, d⟩
      have length : (BinaryEncoding.rawInstanceBits ((a, d) :: items)).length =
          2 * a.size + 2 * d.size + 3 + (BinaryEncoding.rawInstanceBits items).length := by
        simp only [BinaryEncoding.rawInstanceBits, BinaryEncoding.listBits,
          BinaryEncoding.pairBits, List.length_cons, List.length_append,
          BinaryEncoding.natBits_length]
        omega
      rw [length]
      simp only [loopTime, rowTime]
      omega

def encodedInTime (items : RawInstance) :
    TM2OutputsInTime machine (true :: BinaryEncoding.rawInstanceBits items)
      (some (dataBits (items, ExtensionCertificate.validItems items)))
      (16 * ((BinaryEncoding.rawInstanceBits items).length + 2)) := by
  have entry := oneStep (entryStep true (BinaryEncoding.rawInstanceBits items))
  have copy := copyInTime (BinaryEncoding.rawInstanceBits items)
  have seed := oneStep (seedStep (BinaryEncoding.rawInstanceBits items))
  have loop := itemsInTime items true (BinaryEncoding.rawInstanceBits items) 0
  simp only [Bool.true_and, Nat.zero_add] at loop
  have count := countInTime (ExtensionCertificate.validItems items)
    (BinaryEncoding.rawInstanceBits items) items.length
  have finish := oneStep (finishStep (ExtensionCertificate.validItems items)
    (encodeWord items.length ++ BinaryEncoding.rawInstanceBits items))
  have trace := join (join (join (join (join entry copy) seed) loop) count) finish
  have bounded : 1 + 2 * ((BinaryEncoding.rawInstanceBits items).length + 1) + 1 +
      loopTime items + 2 * (items.length + 2) + 1 ≤
      16 * ((BinaryEncoding.rawInstanceBits items).length + 2) := by
    have loopBound := loopTime_le items
    have countBound := item_count_le items
    omega
  change StateTransition.EvalsToInTime machine.step
    (initList machine (true :: BinaryEncoding.rawInstanceBits items))
    (some (haltList machine (dataBits (items, ExtensionCertificate.validItems items)))) _
  rw [initList_eq, haltList_eq]
  exact enlarge trace bounded

def malformedInTime (raw : List Bool) :
    TM2OutputsInTime machine (false :: raw) (some (dataBits ([], false)))
      (16 * (raw.length + 2)) := by
  have entry := oneStep (entryStep false raw)
  have drain := MachineDrain.drainInTime (0 : Tape) (.control .malformedDrain)
    (some (.control .malformedFinish)) program rfl (tapes raw [] [] [] [] [])
    (((true, Ordering.eq), false), none) none
  simp only [update_raw, tapes] at drain
  have finish : machine.step (cfg (some (.control .malformedFinish)) true
      (tapes [] [] [] [] [] [])) =
      some (cfg none true (tapes (dataBits ([], false)) [] [] [] [] [])) := by
    change some (TM2.stepAux (program (.control .malformedFinish)) (clean true)
      (tapes [] [] [] [] [] [])) = _
    simp [program, instruction, cfg, dataBits, encodeWord, BinaryEncoding.rawInstanceBits,
      BinaryEncoding.listBits, TM2.stepAux, update_raw, tapes]
    rfl
  have trace := join (join entry drain) (oneStep finish)
  change StateTransition.EvalsToInTime machine.step
    (initList machine (false :: raw)) (some (haltList machine (dataBits ([], false)))) _
  rw [initList_eq, haltList_eq]
  exact enlarge trace (by omega)

def outputsInTime (input : List Bool) :
    TM2OutputsInTime machine (shapeBits input) (some (dataBits (classify input)))
      (16 * ((shapeBits input).length + 1)) := by
  cases parsed : BinaryEncoding.decodeRawInstance input with
  | none =>
      simpa only [shapeBits, classify, parsed, Option.isSome_none, List.length_cons]
        using malformedInTime input
  | some items =>
      have encoded := BinaryEncoding.decodeRawInstance_sound parsed
      subst input
      simpa only [shapeBits, classify, BinaryEncoding.decodeRawInstance_rawInstanceBits,
        Option.isSome_some, List.length_cons] using encodedInTime items

noncomputable def computation : TM2ComputableInPolyTime shapeBits dataBits classify where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 16 * (Polynomial.X + 1)
  outputsFun input := by
    change TM2OutputsInTime machine ((shapeBits input).map id)
      (some ((dataBits (classify input)).map id))
      ((16 * (Polynomial.X + 1) : Polynomial Nat).eval (shapeBits input).length)
    simpa only [List.map_id_fun, id_eq, Polynomial.eval_mul, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_ofNat, Polynomial.eval_one] using outputsInTime input

theorem finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet computation.tm := by
  intro k
  change Finite Bool
  infer_instance

end BinPackingGap.SearchInitialItemsMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_PackingPowerProgram
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.Packing.instFintypeTableBin _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.PackingPowerProgram

open Turing
open BinPackingGames.Foundations.Complexity
open FiniteTapeProgram

variable {K A : Type} [DecidableEq K]

noncomputable def runInTime (slots : Fin 11 ↪ K) (base : K → List Bool) (a n : Nat)
    (ready : Ready slots base a n) (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step (BinaryPowerMachine.program (A := A) slots))
      ⟨some .initialize_, BinaryAddMachine.clean ambient, base⟩
      (some ⟨none, BinaryAddMachine.clean ambient, resultTapes slots base a n⟩)
      (budget a n) := by
  have run := BinaryPowerMachine.powerInPolynomialTime slots id none
    (BinaryPowerMachine.program (A := A) slots) (fun _ => rfl)
    base a (List.replicate n true) ready.baseWord ready.outputEmpty ready.tallyWord
    ready.workspace ambient
  simpa only [id_eq, List.length_replicate, resultTapes, budget] using run

theorem exec (slots : Fin 11 ↪ K) (base : K → List Bool) (a n : Nat)
    (ready : Ready slots base a n) (ambient : A) :
    ∃ steps ≤ budget a n,
      Exec (code (A := A) slots) ⟨BinaryAddMachine.clean ambient, base⟩ steps
        ⟨BinaryAddMachine.clean ambient, resultTapes slots base a n⟩ := by
  let run := runInTime slots base a n ready ambient
  refine ⟨run.steps, run.steps_le_m, ?_⟩
  refine Exec.routine inferInstance (BinaryPowerMachine.Label.initialize_)
    (BinaryPowerMachine.program slots)
    ⟨BinaryAddMachine.clean ambient, base⟩
    ⟨BinaryAddMachine.clean ambient, resultTapes slots base a n⟩ run.steps ?_
  have trace := run.evals_in_steps
  change (MachineComposition.advance (TM2.step (BinaryPowerMachine.program (A := A) slots)))^[run.steps]
    (some (⟨some BinaryPowerMachine.Label.initialize_, BinaryAddMachine.clean ambient, base⟩ :
      TM2.Cfg (fun _ : K => Bool) BinaryPowerMachine.Label (BinaryAddMachine.State A))) =
    some ⟨none, BinaryAddMachine.clean ambient, resultTapes slots base a n⟩ at trace
  exact trace

end BinPackingGap.PackingPowerProgram

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_PackingCountedProgram
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.Packing.instDecidableEqTableBin _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.GraphPreparationMachine

open Turing
open BinPackingGames.Foundations.Complexity

variable {K Λ A : Type} [DecidableEq K]

theorem preparationTrace (slots : Fin 7 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (P : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State A))
    (atLabels : ∀ l, P (labels l) = instruction slots labels exit l)
    (base : K → List Bool) (input : GraphReductionInput)
    (graphWord : base (slots 0) = graphBits input)
    (scratchEmpty : base (slots 1) = []) (temporaryEmpty : base (slots 2) = [])
    (ambient : A) :
    (MachineComposition.advance (TM2.step P))^[steps input]
      (some ⟨some (labels (.threshold .scan)), GraphFieldMachine.clean ambient, base⟩) =
      some ⟨exit, GraphFieldMachine.clean ambient, preparedTapes slots base input⟩ := by
  have hd (i j : Fin 7) (h : i ≠ j) : slots i ≠ slots j := slots.injective.ne h
  let b₁ := GraphFieldMachine.resultTapes .threshold (fieldSlots slots false) base input
  let b₂ := GraphFieldMachine.resultTapes .endpoints (fieldSlots slots true) b₁ input
  let b₃ := GraphTokenMachine.resultTapes .vertex (tokenSlots slots false) b₂ input
  have g₁ : b₁ (slots 0) = graphBits input := by
    simp [b₁, GraphFieldMachine.resultTapes, hd 0 3 (by decide), graphWord]
  have s₁ : b₁ (slots 1) = [] := by
    simp [b₁, GraphFieldMachine.resultTapes, hd 1 3 (by decide), scratchEmpty]
  have t₁ : b₁ (slots 2) = [] := by
    simp [b₁, GraphFieldMachine.resultTapes, hd 2 3 (by decide), temporaryEmpty]
  have g₂ : b₂ (slots 0) = graphBits input := by
    simp [b₂, GraphFieldMachine.resultTapes, hd 0 4 (by decide), g₁]
  have s₂ : b₂ (slots 1) = [] := by
    simp [b₂, GraphFieldMachine.resultTapes, hd 1 4 (by decide), s₁]
  have g₃ : b₃ (slots 0) = graphBits input := by
    simp [b₃, GraphTokenMachine.resultTapes, hd 0 5 (by decide), g₂]
  have s₃ : b₃ (slots 1) = [] := by
    simp [b₃, GraphTokenMachine.resultTapes, hd 1 5 (by decide), s₂]
  have r₁ := GraphFieldMachine.extractTrace .threshold (fieldSlots slots false)
    (fun l => labels (.threshold l)) (some (labels (.endpoints .scan))) P
    (fun l => atLabels (.threshold l)) base input
    (by simpa using graphWord) (by simpa using scratchEmpty)
    (by simpa using temporaryEmpty) ambient
  have r₂ := GraphFieldMachine.extractTrace .endpoints (fieldSlots slots true)
    (fun l => labels (.endpoints l)) (some (labels (.vertices .scan))) P
    (fun l => atLabels (.endpoints l)) b₁ input
    (by simpa using g₁) (by simpa using s₁) (by simpa using t₁) ambient
  have r₃ := GraphTokenMachine.tokensTrace .vertex (tokenSlots slots false)
    (fun l => labels (.vertices l)) (some (labels (.edges .scan))) P
    (fun l => atLabels (.vertices l)) b₂ input
    (by simpa using g₂) (by simpa using s₂) ambient
  have r₄ := GraphTokenMachine.tokensTrace .edge (tokenSlots slots true)
    (fun l => labels (.edges l)) exit P (fun l => atLabels (.edges l)) b₃ input
    (by simpa using g₃) (by simpa using s₃) ambient
  exact joinTrace (joinTrace (joinTrace r₁ r₂) r₃) r₄

end BinPackingGap.GraphPreparationMachine

namespace BinPackingGap.PackingMachineBlocks

open Turing
open BinPackingGames.Foundations.Complexity
open FiniteTapeProgram

variable {K : Type} [DecidableEq K]

theorem prepareGraph_exec (slots : Fin 7 ↪ K) (start : Data K State)
    (input : GraphReductionInput) (graphWord : start.tapes (slots 0) = graphBits input)
    (scratchEmpty : start.tapes (slots 1) = []) (temporaryEmpty : start.tapes (slots 2) = []) :
    Exec (prepareGraph slots) start (1 + GraphPreparationMachine.steps input)
      ⟨.graph (GraphFieldMachine.clean ()),
        GraphPreparationMachine.preparedTapes slots start.tapes input⟩ := by
  apply invokeExec
  exact GraphPreparationMachine.preparationTrace slots id none
    (GraphPreparationMachine.instruction slots id none) (fun _ => rfl)
    start.tapes input graphWord scratchEmpty temporaryEmpty ()

end BinPackingGap.PackingMachineBlocks

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Arithmetic_PackingRegisterUpdate
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.Packing.instDecidableEqTableBin _root_.OAI.BinPackingGap.Packing.instFintypeTableBin _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.PackingRegisterUpdate

open Turing
open BinPackingGames.Foundations.Complexity
open BinaryRegisterProgram
open FiniteTapeProgram PackingMachineBlocks

theorem commands_ready (kind : Kind) (a b : Nat) : Ready (commands kind) (values a b) := by
  cases kind <;>
    simp [commands, operator, Ready, commandReady, result, destination, value, operands, values]

theorem commands_result (kind : Kind) (a b : Nat) :
    resultOf (commands kind) (values a b) = values a (operation kind a b) := by
  funext r
  cases kind <;> fin_cases r <;>
    simp [commands, operator, resultOf_cons, result, destination, value, operands, values,
      operation]

theorem commands_budget (kind : Kind) (a b : Nat) :
    budget (commands kind) (values a b) =
      cost (operator kind) (values a b) + b.size + 3 * (operation kind a b).size + 4 := by
  cases kind <;>
    simp [commands, operator, budget, MachineFiniteSequence.steps, result, destination,
      value, operands, values, cost, operation] <;> omega

theorem commands_budget_le (kind : Kind) (a b : Nat) :
    budget (commands kind) (values a b) + 1 ≤ 64 * (a.size + b.size + 1) ^ 2 := by
  have hsize := operation_size_le kind a b
  have hw : 1 ≤ a.size + b.size + 1 := by omega
  have hsquare : a.size + b.size + 1 ≤ (a.size + b.size + 1) ^ 2 := by nlinarith
  rw [commands_budget]
  cases kind <;> simp [operator, cost, operands, values, operation] at * <;> nlinarith

variable {K : Type} [DecidableEq K]

theorem exec (slots : (Fin 3 ⊕ Fin 6) ↪ K) (kind : Kind)
    (base : K → List Bool) (a b : Nat) (state : State) :
    ∃ steps ≤ 64 * (a.size + b.size + 1) ^ 2,
      Exec (code slots kind) ⟨state, registerTapes slots base (values a b)⟩ steps
        ⟨.arithmetic (BinaryAddMachine.clean ()),
          registerTapes slots base (values a (operation kind a b))⟩ := by
  have run := BinaryRegisterProgram.programInTime slots (commands kind) base
    (values a b) (commands_ready kind a b) ()
  rw [commands_result] at run
  have run' : StateTransition.EvalsToInTime
      (TM2.step (BinaryRegisterProgram.program (A := Unit) slots (commands kind)))
      ⟨some (main kind), BinaryAddMachine.clean (), registerTapes slots base (values a b)⟩
      (some ⟨none, BinaryAddMachine.clean (),
        registerTapes slots base (values a (operation kind a b))⟩)
      (budget (commands kind) (values a b)) := run
  obtain ⟨n, hn, hrun⟩ := invokeExecInTime arithmeticControl (BinaryAddMachine.clean ())
    (main kind) (BinaryRegisterProgram.program slots (commands kind))
    ⟨state, registerTapes slots base (values a b)⟩ (BinaryAddMachine.clean ())
    (registerTapes slots base (values a (operation kind a b))) _ run'
  exact ⟨n, hn.trans (commands_budget_le kind a b), hrun⟩

end BinPackingGap.PackingRegisterUpdate

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Hardness_LiteralSlotGraphEnumeration
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.Packing.instDecidableEqTableBin _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.LiteralSlotGraphMachine

section

open FiniteTapeProgram BinPackingGames.Foundations.Complexity

theorem vertexBody_exec (base : Tape → List Bool) (a : Control) (register : Option Bool)
    (i : Nat) (hI : base .outerIndex = i.bits) (hU : base .unary = [])
    (hW : base .scratch = []) :
    Exec vertexBody ⟨((a, ()), register), base⟩ (vertexBodyCost i)
      ⟨BooleanTapeCode.clean a,
        Function.update (Function.update base .accumulator
          ((vertexRecord i).reverse ++ base .accumulator)) .outerIndex (i + 1).bits⟩ := by
  let b₁ := Function.update base Tape.accumulator (true :: base .accumulator)
  let b₂ := Function.update b₁ Tape.accumulator
    ((BinPackingCompleteness.BinaryEncoding.frame i.bits).reverse ++ b₁ .accumulator)
  have first : Exec (pushBit .accumulator true) ⟨((a, ()), register), base⟩ 1
      ⟨((a, ()), register), b₁⟩ := Exec.atom _ _
  have emitted := BooleanTapeCode.frame_exec Tape.outerIndex .scratch .accumulator
    (by decide) (by decide) (by decide) b₁ (by simpa [b₁] using hW) a register
  have hi₁ : b₁ .outerIndex = i.bits := by simpa [b₁] using hI
  rw [hi₁] at emitted
  have increased := BooleanTapeCode.increment_exec (n := i) Tape.outerIndex .unary .scratch
    (by decide) (by decide) (by decide) b₂
    (by simpa [b₂, b₁] using hU) (by simpa [b₂, b₁] using hW)
    (by simpa [b₂, b₁] using hI) a none
  have last := Exec.atom (Action.done : Action Tape State)
    (Data.mk (BooleanTapeCode.clean a) (Function.update b₂ .outerIndex (i + 1).bits))
  have run := Exec.seq first (Exec.seq emitted (Exec.seq increased last))
  have bc : 1 + ((3 * i.bits.length + 3) + ((1 + UnaryToBinaryMachine.steps 1 i) + 1)) =
      vertexBodyCost i := by simp [vertexBodyCost]; omega
  simpa [vertexBody, sequence, skip, frame, increment, b₂, b₁, vertexRecord,
    BinaryEncoding.natBits, BinPackingCompleteness.BinaryEncoding.nameBits, bc,
    List.reverse_cons, List.append_assoc, Action.eval] using run

theorem vertices_exec (base : Tape → List Bool) (a : Control) (register : Option Bool)
    (n i : Nat) (hN : base .vertexCount = List.replicate n true)
    (hI : base .outerIndex = i.bits) (hU : base .unary = []) (hW : base .scratch = []) :
    Exec vertices ⟨((a, ()), register), base⟩ (vertexLoopCost n i)
      ⟨BooleanTapeCode.clean a, vertexResult base n i⟩ := by
  induction n generalizing base i register with
  | zero =>
      have run := Exec.loop_false (g := Action.pop Tape.vertexCount saveHead .done)
        (p := fun s : State => s.2.isSome) (a := vertexBody)
        (d := Data.mk ((a, ()), register) base)
        (by simp [Action.eval, saveHead, hN])
      have result : vertexResult base 0 i = Function.update base Tape.vertexCount [] := by
        funext tape
        cases tape <;> simp [vertexResult, vertexRecords, hI]
      simpa [vertices, vertexLoopCost, Action.eval, saveHead, hN,
        BooleanTapeCode.clean, result] using run
  | succ n ih =>
      let b₀ := Function.update base Tape.vertexCount (List.replicate n true)
      let b₁ := Function.update (Function.update b₀ Tape.accumulator
        ((vertexRecord i).reverse ++ b₀ .accumulator)) Tape.outerIndex (i + 1).bits
      have guardEq : (Action.pop Tape.vertexCount saveHead .done).eval
          ⟨((a, ()), register), base⟩ = ⟨((a, ()), some true), b₀⟩ := by
        simp [Action.eval, saveHead, hN, List.replicate_succ, b₀]
      have body := vertexBody_exec b₀ a (some true) i
        (by simpa [b₀] using hI) (by simpa [b₀] using hU) (by simpa [b₀] using hW)
      have tail := ih b₁ none (i + 1)
        (by simp [b₁, b₀]) (by simp [b₁])
        (by simpa [b₁, b₀] using hU) (by simpa [b₁, b₀] using hW)
      have run := Exec.loop_true (g := Action.pop Tape.vertexCount saveHead .done)
        (p := fun s : State => s.2.isSome)
        (d := Data.mk ((a, ()), register) base)
        (by rw [guardEq]; rfl)
        (by simpa only [guardEq, BooleanTapeCode.clean, b₁] using body) tail
      have result : vertexResult b₁ n (i + 1) = vertexResult base (n + 1) i := by
        funext tape
        cases tape <;> simp [vertexResult, vertexRecords, b₁, b₀,
          List.reverse_append, List.append_assoc, Nat.add_comm, Nat.add_left_comm]
      simpa only [vertices, vertexLoopCost, result] using run

theorem emitPair_exec (base : Tape → List Bool) (a : Control) (register : Option Bool)
    (u v : Nat) (hU : base .outerIndex = u.bits) (hV : base .innerIndex = v.bits)
    (hW : base .scratch = []) :
    Exec emitPair ⟨((a, ()), register), base⟩ (pairCost u v)
      ⟨BooleanTapeCode.clean a, Function.update base .accumulator
        ((pairRecord u v).reverse ++ base .accumulator)⟩ := by
  let b₁ := Function.update base Tape.accumulator (true :: base .accumulator)
  let b₂ := Function.update b₁ Tape.accumulator
    ((BinPackingCompleteness.BinaryEncoding.frame u.bits).reverse ++ b₁ .accumulator)
  let b₃ := Function.update b₂ Tape.accumulator
    ((BinPackingCompleteness.BinaryEncoding.frame v.bits).reverse ++ b₂ .accumulator)
  have first : Exec (pushBit .accumulator true) ⟨((a, ()), register), base⟩ 1
      ⟨((a, ()), register), b₁⟩ := Exec.atom _ _
  have left := BooleanTapeCode.frame_exec Tape.outerIndex .scratch .accumulator
    (by decide) (by decide) (by decide) b₁ (by simpa [b₁] using hW) a register
  have hi₁ : b₁ .outerIndex = u.bits := by simpa [b₁] using hU
  rw [hi₁] at left
  have right := BooleanTapeCode.frame_exec Tape.innerIndex .scratch .accumulator
    (by decide) (by decide) (by decide) b₂ (by simpa [b₂, b₁] using hW) a none
  have hi₂ : b₂ .innerIndex = v.bits := by simpa [b₂, b₁] using hV
  rw [hi₂] at right
  have last : Exec skip ⟨BooleanTapeCode.clean a, b₃⟩ 1
      ⟨BooleanTapeCode.clean a, b₃⟩ := Exec.atom .done _
  have run := Exec.seq first (Exec.seq left (Exec.seq right last))
  have cost : 1 + ((3 * u.bits.length + 3) + ((3 * v.bits.length + 3) + 1)) = pairCost u v := by
    simp [pairCost]; omega
  simpa [emitPair, sequence, frame, b₃, b₂, b₁, pairRecord, BinaryEncoding.natBits,
    BinPackingCompleteness.BinaryEncoding.nameBits, cost, List.reverse_cons,
    List.reverse_append, List.append_assoc] using run

theorem innerBody_exec (base : Tape → List Bool) (a : Control) (register : Option Bool)
    (left right : RawLiteral) (u v : Nat) (suffix : List Bool)
    (hS : base .innerSource = literalBits right ++ suffix)
    (hL : base .outerVariable = List.replicate left.1 true)
    (hR : base .innerVariable = []) (hC : base .comparison = [])
    (hU : base .outerIndex = u.bits) (hV : base .innerIndex = v.bits)
    (hW : base .scratch = []) (hN : base .unary = []) :
    Exec innerBody ⟨((a, ()), register), base⟩ (innerBodyCost a left right u v)
      ⟨BooleanTapeCode.clean (bodyControl a left right),
        innerBodyResult base a left right u v suffix⟩ := by
  let signBits := encodeWord (if right.2 then 1 else 0)
  let b₁ := twoTapes base Tape.innerSource Tape.innerVariable
    (signBits ++ suffix) (List.replicate right.1 true)
  let a₁ := {a with innerSign := right.2}
  let b₂ := Function.update b₁ Tape.innerSource suffix
  let b₃ := Function.update b₂ Tape.comparison (List.replicate left.1 true)
  let a₂ := {a₁ with otherHead := none, equal := decide (left.1 = right.1)}
  let b₄ := twoTapes b₃ Tape.comparison Tape.innerVariable [] []
  let b₅ := Function.update b₄ Tape.accumulator (bodyAccumulator base a left right u v)
  let b₆ := Function.update b₅ Tape.innerIndex (v + 1).bits
  have first := readVariable_exec Tape.innerSource .innerVariable (by decide)
    base ((a, ()), register) right.1 (signBits ++ suffix) []
  have startEq : twoTapes base Tape.innerSource Tape.innerVariable
      (encodeWord right.1 ++ (signBits ++ suffix)) [] = base := by
    funext tape
    cases tape <;> simp [twoTapes, hS, hR, literalBits, signBits, List.append_assoc]
  rw [startEq] at first
  simp only [List.append_nil] at first
  have signed := readSign_exec Tape.innerSource (fun a b => {a with innerSign := b}) b₁
    (BooleanTapeCode.clean a) right.2 suffix
  have signStart : Function.update b₁ Tape.innerSource (signBits ++ suffix) = b₁ := by
    simp [b₁, twoTapes]
  change Exec (readSign .innerSource (fun a b => {a with innerSign := b}))
    ⟨BooleanTapeCode.clean a, Function.update b₁ .innerSource (signBits ++ suffix)⟩ 1
    ⟨BooleanTapeCode.clean a₁, b₂⟩ at signed
  rw [signStart] at signed
  have copied := BooleanTapeCode.copy_exec Tape.outerVariable .comparison .scratch
    (by decide) (by decide) (by decide) b₂ (by simpa [b₂, b₁, twoTapes] using hW)
    (BooleanTapeCode.clean a₁)
  have outerWord : b₂ .outerVariable = List.replicate left.1 true := by
    simpa [b₂, b₁, twoTapes] using hL
  have compEmpty : b₂ .comparison = [] := by simpa [b₂, b₁, twoTapes] using hC
  rw [outerWord, compEmpty, List.append_nil, List.length_replicate] at copied
  have compared := compareVariables_exec b₃ a₁ none left.1 right.1
  have compareStart : twoTapes b₃ Tape.comparison Tape.innerVariable
      (List.replicate left.1 true) (List.replicate right.1 true) = b₃ := by
    funext tape
    cases tape <;> simp [b₃, b₂, b₁, twoTapes]
  rw [compareStart] at compared
  have chosen : Exec (.branch isEdge emitPair skip) ⟨BooleanTapeCode.clean a₂, b₄⟩
      (branchCost a left right u v) ⟨BooleanTapeCode.clean a₂, b₅⟩ := by
    have testEq : isEdge (BooleanTapeCode.clean a₂) = decide (bodyEdge a left right) := by
      cases hs : a.outerSign <;> cases hr : right.2 <;>
        simp [isEdge, BooleanTapeCode.clean, a₂, a₁, bodyEdge, hs, hr]
    by_cases edge : bodyEdge a left right
    · have emitted := emitPair_exec b₄ a₂ none u v
        (by simpa [b₄, b₃, b₂, b₁, twoTapes] using hU)
        (by simpa [b₄, b₃, b₂, b₁, twoTapes] using hV)
        (by simpa [b₄, b₃, b₂, b₁, twoTapes] using hW)
      have run := Exec.branch_true (p := isEdge) (b := skip)
        (by change isEdge (BooleanTapeCode.clean a₂) = true; simp [testEq, edge]) emitted
      simpa [b₅, bodyAccumulator, branchCost, edge, b₄, b₃, b₂, b₁, twoTapes,
        BooleanTapeCode.clean] using run
    · have unchanged : b₅ = b₄ := by
        funext tape
        cases tape <;> simp [b₅, bodyAccumulator, edge, b₄, b₃, b₂, b₁, twoTapes]
      have run := Exec.branch_false (p := isEdge) (a := emitPair)
        (by change isEdge (BooleanTapeCode.clean a₂) = false; simp [testEq, edge])
        (Exec.atom (Action.done : Action Tape State) (Data.mk (BooleanTapeCode.clean a₂) b₄))
      simpa [branchCost, edge, unchanged, skip, Action.eval] using run
  have increased := BooleanTapeCode.increment_exec (n := v) Tape.innerIndex .unary .scratch
    (by decide) (by decide) (by decide) b₅
    (by simpa [b₅, b₄, b₃, b₂, b₁, twoTapes] using hN)
    (by simpa [b₅, b₄, b₃, b₂, b₁, twoTapes] using hW)
    (by simpa [b₅, b₄, b₃, b₂, b₁, twoTapes] using hV) a₂ none
  have changed : Exec (changeControl nextRemaining) ⟨BooleanTapeCode.clean a₂, b₆⟩ 1
      ⟨BooleanTapeCode.clean (nextRemaining a₂), b₆⟩ := Exec.atom _ _
  have last : Exec skip ⟨BooleanTapeCode.clean (nextRemaining a₂), b₆⟩ 1
      ⟨BooleanTapeCode.clean (nextRemaining a₂), b₆⟩ := Exec.atom .done _
  have run := Exec.seq first (Exec.seq signed (Exec.seq copied (Exec.seq compared
    (Exec.seq chosen (Exec.seq increased (Exec.seq changed last))))))
  have endEq : b₆ = innerBodyResult base a left right u v suffix := by
    funext tape
    cases tape <;> simp [b₆, b₅, b₄, b₃, b₂, b₁, twoTapes, innerBodyResult, hC, hR]
  simpa only [innerBody, sequence, copy, increment, skip, innerBodyCost,
    bodyControl, a₂, a₁, endEq] using run

theorem innerLoop_exec (base : Tape → List Bool) (a : Control) (register : Option Bool)
    (left : RawLiteral) (u t : Nat) (rest : List RawLiteral)
    (hS : base .innerSource = literalsBits rest)
    (hL : base .outerVariable = List.replicate left.1 true)
    (hR : base .innerVariable = []) (hC : base .comparison = [])
    (hU : base .outerIndex = u.bits) (hV : base .innerIndex = (u + 1 + t).bits)
    (hW : base .scratch = []) (hN : base .unary = [])
    (hA : a.outerSign = left.2) (hT : a.remaining.val = (2 - u % 3) - t) :
    Exec innerLoop ⟨((a, ()), register), base⟩
      (innerLoopCost a left u (u + 1 + t) rest)
      ⟨BooleanTapeCode.clean (rowControl a left rest),
        innerLoopResult base left u (u + 1 + t) rest⟩ := by
  induction rest generalizing base a register t with
  | nil =>
      have run := Exec.loop_false (g := Action.peek Tape.innerSource saveHead .done)
        (p := fun s : State => s.2.isSome) (a := innerBody)
        (d := Data.mk ((a, ()), register) base)
        (by simp [Action.eval, saveHead, hS, literalsBits])
      have result : innerLoopResult base left u (u + 1 + t) [] = base := by
        funext tape
        cases tape <;> simp [innerLoopResult, rowEdges, edgeRecords, hS, literalsBits, hV]
      simpa [innerLoop, innerLoopCost, rowControl, Action.eval, saveHead, hS,
        literalsBits, BooleanTapeCode.clean, result] using run
  | cons right rest ih =>
      let v := u + 1 + t
      let a₁ := bodyControl a left right
      let b₁ := innerBodyResult base a left right u v (literalsBits rest)
      have guardEq : (Action.peek Tape.innerSource saveHead .done).eval
          ⟨((a, ()), register), base⟩ = ⟨((a, ()), (base .innerSource).head?), base⟩ := rfl
      have sourceNonempty : (base .innerSource).head?.isSome = true := by
        rw [hS]
        cases hv : right.1 <;>
          simp [literalsBits, literalBits, encodeWord, hv, List.replicate_succ]
      have body := innerBody_exec base a (base .innerSource).head? left right u v
        (literalsBits rest) (by simpa only [literalsBits_cons] using hS)
        hL hR hC hU hV hW hN
      have indexEq : v + 1 = u + 1 + (t + 1) := by dsimp [v]; omega
      have tail := ih b₁ a₁ none (t + 1)
        (by simp [b₁, innerBodyResult])
        (by simpa [b₁, innerBodyResult] using hL)
        (by simpa [b₁, innerBodyResult] using hR)
        (by simpa [b₁, innerBodyResult] using hC)
        (by simpa [b₁, innerBodyResult] using hU)
        (by simp [b₁, innerBodyResult, indexEq])
        (by simpa [b₁, innerBodyResult] using hW)
        (by simpa [b₁, innerBodyResult] using hN)
        (by simpa [a₁] using hA)
        (by simp only [a₁, bodyControl_remaining, hT]; omega)
      rw [← indexEq] at tail
      have run := Exec.loop_true (g := Action.peek Tape.innerSource saveHead .done)
        (p := fun s : State => s.2.isSome)
        (d := Data.mk ((a, ()), register) base)
        (by simpa only [guardEq] using sourceNonempty)
        (by simpa only [guardEq, BooleanTapeCode.clean, a₁, b₁] using body) tail
      have edgeIff : bodyEdge a left right ↔
          u / 3 = v / 3 ∨ (left.1 = right.1 ∧ left.2 ≠ right.2) := by
        simp only [bodyEdge, hT, hA, remaining_same_clause, v]
      have result : innerLoopResult b₁ left u (v + 1) rest =
          innerLoopResult base left u v (right :: rest) := by
        funext tape
        by_cases edge : bodyEdge a left right
        · have selected := edgeIff.mp edge
          cases tape <;>
            simp [innerLoopResult, b₁, innerBodyResult, rowEdges, edgeRecords,
              bodyAccumulator, edge, selected, List.reverse_append, List.append_assoc,
              Nat.add_assoc, Nat.add_comm]
        · have omitted : ¬(u / 3 = v / 3 ∨ (left.1 = right.1 ∧ left.2 ≠ right.2)) :=
            fun h => edge (edgeIff.mpr h)
          cases tape <;>
            simp [innerLoopResult, b₁, innerBodyResult, rowEdges, edgeRecords,
              bodyAccumulator, edge, omitted, Nat.add_assoc, Nat.add_comm]
      simpa only [innerLoop, innerLoopCost, rowControl, a₁, v, result] using run

theorem outerBody_exec (base : Tape → List Bool) (a : Control) (register : Option Bool)
    (left : RawLiteral) (u : Nat) (rest : List RawLiteral)
    (hS : base .input = literalBits left ++ literalsBits rest)
    (hL : base .outerVariable = []) (hR : base .innerVariable = [])
    (hC : base .comparison = []) (hU : base .outerIndex = u.bits)
    (hV : base .innerIndex = []) (hI : base .innerSource = [])
    (hW : base .scratch = []) (hN : base .unary = []) (hA : a.slot.val = u % 3) :
    Exec outerBody ⟨((a, ()), register), base⟩ (outerBodyCost a left u rest)
      ⟨BooleanTapeCode.clean (outerBodyControl a left rest), outerBodyResult base left u rest⟩ := by
  let signBits := encodeWord (if left.2 then 1 else 0)
  let b₁ := twoTapes base Tape.input Tape.outerVariable
    (signBits ++ literalsBits rest) (List.replicate left.1 true)
  let a₁ := {a with outerSign := left.2}
  let b₂ := Function.update b₁ Tape.input (literalsBits rest)
  let b₃ := Function.update b₂ Tape.innerSource (literalsBits rest)
  let b₄ := Function.update b₃ Tape.innerIndex u.bits
  let b₅ := Function.update b₄ Tape.innerIndex (u + 1).bits
  let a₂ := rowStartControl a left
  let ar := rowControl a₂ left rest
  let b₆ := innerLoopResult b₅ left u (u + 1) rest
  let b₇ := Function.update b₆ Tape.innerIndex []
  let b₈ := Function.update b₇ Tape.outerVariable []
  let b₉ := Function.update b₈ Tape.outerIndex (u + 1).bits
  have first := readVariable_exec Tape.input .outerVariable (by decide) base
    ((a, ()), register) left.1 (signBits ++ literalsBits rest) []
  have startEq : twoTapes base Tape.input Tape.outerVariable
      (encodeWord left.1 ++ (signBits ++ literalsBits rest)) [] = base := by
    funext tape
    cases tape <;> simp [twoTapes, hS, hL, literalBits, signBits, List.append_assoc]
  rw [startEq] at first
  simp only [List.append_nil] at first
  have signed := readSign_exec Tape.input (fun a b => {a with outerSign := b}) b₁
    (BooleanTapeCode.clean a) left.2 (literalsBits rest)
  have signStart : Function.update b₁ Tape.input (signBits ++ literalsBits rest) = b₁ := by
    simp [b₁, twoTapes]
  change Exec (readSign .input (fun a b => {a with outerSign := b}))
    ⟨BooleanTapeCode.clean a, Function.update b₁ .input (signBits ++ literalsBits rest)⟩ 1
    ⟨BooleanTapeCode.clean a₁, b₂⟩ at signed
  rw [signStart] at signed
  have sourceCopy := BooleanTapeCode.copy_exec Tape.input .innerSource .scratch
    (by decide) (by decide) (by decide) b₂ (by simpa [b₂, b₁, twoTapes] using hW)
    (BooleanTapeCode.clean a₁)
  have inputWord : b₂ .input = literalsBits rest := by simp [b₂]
  have sourceEmpty : b₂ .innerSource = [] := by simpa [b₂, b₁, twoTapes] using hI
  rw [inputWord, sourceEmpty, List.append_nil] at sourceCopy
  have indexCopy := BooleanTapeCode.copy_exec Tape.outerIndex .innerIndex .scratch
    (by decide) (by decide) (by decide) b₃ (by simpa [b₃, b₂, b₁, twoTapes] using hW)
    (BooleanTapeCode.clean a₁)
  have indexWord : b₃ .outerIndex = u.bits := by simpa [b₃, b₂, b₁, twoTapes] using hU
  have indexEmpty : b₃ .innerIndex = [] := by simpa [b₃, b₂, b₁, twoTapes] using hV
  rw [indexWord, indexEmpty, List.append_nil] at indexCopy
  have increased := BooleanTapeCode.increment_exec (n := u) Tape.innerIndex .unary .scratch
    (by decide) (by decide) (by decide) b₄
    (by simpa [b₄, b₃, b₂, b₁, twoTapes] using hN)
    (by simpa [b₄, b₃, b₂, b₁, twoTapes] using hW) (by simp [b₄]) a₁ none
  have started : Exec (changeControl startRow) ⟨BooleanTapeCode.clean a₁, b₅⟩ 1
      ⟨BooleanTapeCode.clean a₂, b₅⟩ := Exec.atom _ _
  have row := innerLoop_exec b₅ a₂ none left u 0 rest
    (by simp [b₅, b₄, b₃]) (by simp [b₅, b₄, b₃, b₂, b₁, twoTapes])
    (by simpa [b₅, b₄, b₃, b₂, b₁, twoTapes] using hR)
    (by simpa [b₅, b₄, b₃, b₂, b₁, twoTapes] using hC)
    (by simpa [b₅, b₄, b₃, b₂, b₁, twoTapes] using hU)
    (by simp [b₅])
    (by simpa [b₅, b₄, b₃, b₂, b₁, twoTapes] using hW)
    (by simpa [b₅, b₄, b₃, b₂, b₁, twoTapes] using hN)
    rfl (by simp [a₂, rowStartControl, startRow, hA])
  simp only [Nat.add_zero] at row
  have clearIndex := BooleanTapeCode.drain_exec Tape.innerIndex b₆ (BooleanTapeCode.clean ar)
  have finalIndex : b₆ .innerIndex = (u + 1 + rest.length).bits := by simp [b₆, innerLoopResult]
  rw [finalIndex] at clearIndex
  have clearVariable := BooleanTapeCode.drain_exec Tape.outerVariable b₇ (BooleanTapeCode.clean ar)
  have variableWord : b₇ .outerVariable = List.replicate left.1 true := by
    simp [b₇, b₆, innerLoopResult, b₅, b₄, b₃, b₂, b₁, twoTapes]
  rw [variableWord, List.length_replicate] at clearVariable
  have advanceOuter := BooleanTapeCode.increment_exec (n := u) Tape.outerIndex .unary .scratch
    (by decide) (by decide) (by decide) b₈
    (by simpa [b₈, b₇, b₆, innerLoopResult, b₅, b₄, b₃, b₂, b₁, twoTapes] using hN)
    (by simpa [b₈, b₇, b₆, innerLoopResult, b₅, b₄, b₃, b₂, b₁, twoTapes] using hW)
    (by simpa [b₈, b₇, b₆, innerLoopResult, b₅, b₄, b₃, b₂, b₁, twoTapes] using hU) ar none
  have advanceSlot : Exec (changeControl nextSlot) ⟨BooleanTapeCode.clean ar, b₉⟩ 1
      ⟨BooleanTapeCode.clean (nextSlot ar), b₉⟩ := Exec.atom _ _
  have last : Exec skip ⟨BooleanTapeCode.clean (nextSlot ar), b₉⟩ 1
      ⟨BooleanTapeCode.clean (nextSlot ar), b₉⟩ := Exec.atom .done _
  have run := Exec.seq first (Exec.seq signed (Exec.seq sourceCopy (Exec.seq indexCopy
    (Exec.seq increased (Exec.seq started (Exec.seq row (Exec.seq clearIndex
      (Exec.seq clearVariable (Exec.seq advanceOuter (Exec.seq advanceSlot last))))))))))
  have endEq : b₉ = outerBodyResult base left u rest := by
    funext tape
    cases tape <;>
      simp [b₉, b₈, b₇, b₆, innerLoopResult, b₅, b₄, b₃, b₂, b₁, twoTapes,
        outerBodyResult, hL, hI, hV]
  simpa only [outerBody, sequence, copy, increment, drain, skip, outerBodyCost,
    outerBodyControl, a₂, ar, endEq] using run

theorem outerLoop_exec (base : Tape → List Bool) (a : Control) (register : Option Bool)
    (u : Nat) (literals : List RawLiteral) (hS : base .input = literalsBits literals)
    (hL : base .outerVariable = []) (hR : base .innerVariable = [])
    (hC : base .comparison = []) (hU : base .outerIndex = u.bits)
    (hV : base .innerIndex = []) (hI : base .innerSource = [])
    (hW : base .scratch = []) (hN : base .unary = []) (hA : a.slot.val = u % 3) :
    Exec outerLoop ⟨((a, ()), register), base⟩ (outerLoopCost a u literals)
      ⟨BooleanTapeCode.clean (outerControl a literals), outerLoopResult base u literals⟩ := by
  induction literals generalizing base a register u with
  | nil =>
      have run := Exec.loop_false (g := Action.peek Tape.input saveHead .done)
        (p := fun s : State => s.2.isSome) (a := outerBody)
        (d := Data.mk ((a, ()), register) base)
        (by simp [Action.eval, saveHead, hS, literalsBits])
      have result : outerLoopResult base u [] = base := by
        funext tape
        cases tape <;> simp [outerLoopResult, suffixEdges, edgeRecords, hS, literalsBits, hU]
      simpa [outerLoop, outerLoopCost, outerControl, Action.eval, saveHead, hS,
        literalsBits, BooleanTapeCode.clean, result] using run
  | cons left rest ih =>
      let a₁ := outerBodyControl a left rest
      let b₁ := outerBodyResult base left u rest
      have guardEq : (Action.peek Tape.input saveHead .done).eval
          ⟨((a, ()), register), base⟩ = ⟨((a, ()), (base .input).head?), base⟩ := rfl
      have sourceNonempty : (base .input).head?.isSome = true := by
        rw [hS]
        cases hv : left.1 <;>
          simp [literalsBits, literalBits, encodeWord, hv, List.replicate_succ]
      have body := outerBody_exec base a (base .input).head? left u rest
        (by simpa only [literalsBits_cons] using hS) hL hR hC hU hV hI hW hN hA
      have tail := ih b₁ a₁ none (u + 1)
        (by simp [b₁, outerBodyResult])
        (by simpa [b₁, outerBodyResult] using hL)
        (by simpa [b₁, outerBodyResult] using hR)
        (by simpa [b₁, outerBodyResult] using hC)
        (by simp [b₁, outerBodyResult])
        (by simpa [b₁, outerBodyResult] using hV)
        (by simpa [b₁, outerBodyResult] using hI)
        (by simpa [b₁, outerBodyResult] using hW)
        (by simpa [b₁, outerBodyResult] using hN)
        (by simp [a₁, outerBodyControl_slot, hA, Nat.add_mod])
      have run := Exec.loop_true (g := Action.peek Tape.input saveHead .done)
        (p := fun s : State => s.2.isSome)
        (d := Data.mk ((a, ()), register) base)
        (by simpa only [guardEq] using sourceNonempty)
        (by simpa only [guardEq, BooleanTapeCode.clean, a₁, b₁] using body) tail
      have result : outerLoopResult b₁ (u + 1) rest = outerLoopResult base u (left :: rest) := by
        funext tape
        cases tape <;> simp [outerLoopResult, b₁, outerBodyResult, suffixEdges,
          edgeRecords, List.flatMap_append, List.reverse_append, List.append_assoc,
          Nat.add_comm, Nat.add_left_comm]
      simpa only [outerLoop, outerLoopCost, outerControl, a₁, result] using run

theorem raw_program_exec («variables» clauses : Nat) (literals : List RawLiteral) :
    Exec program
      ⟨initialState, Function.update (fun _ => []) .input (rawInput «variables» clauses literals)⟩
      (rawCost «variables» clauses literals)
      ⟨initialState, Function.update (fun _ => []) .output (rawGraphWord clauses literals)⟩ := by
  let rest := literalsBits literals
  let header := BinaryEncoding.natBits (2 * clauses)
  let verts := vertexRecords 0 (3 * clauses)
  let edges := edgeRecords (suffixEdges 0 literals)
  let acc₁ := header.reverse
  let acc₂ := verts.reverse ++ acc₁
  let acc₃ := false :: acc₂
  let acc₄ := edges.reverse ++ acc₃
  let acc₅ := false :: acc₄
  let ar := outerControl initialControl literals
  have skipped := skipField_exec Tape.input
    (mainTapes (rawInput «variables» clauses literals) [] [] [] [] []) initialState «variables»
    (encodeWord clauses ++ rest) (by simp [mainTapes, rawInput, rest, List.append_assoc])
  simp only [mainTapes_input] at skipped
  have seeded : Exec (pushBit .unary false)
      ⟨(initialState.1, some false), mainTapes (encodeWord clauses ++ rest) [] [] [] [] []⟩ 1
      ⟨(initialState.1, some false), mainTapes (encodeWord clauses ++ rest) [] [] [] [false] []⟩ := by
    simpa [pushBit, Action.eval, mainTapes] using Exec.atom
      (Action.push Tape.unary (fun _ : State => false) .done)
      (Data.mk (initialState.1, some false)
        (mainTapes (encodeWord clauses ++ rest) [] [] [] [] []))
  have counted := countHeader_exec
    (mainTapes (encodeWord clauses ++ rest) [] [] [] [false] [])
    (initialState.1, some false) clauses rest rfl
  have countResultEq : countHeaderResult
      (mainTapes (encodeWord clauses ++ rest) [] [] [] [false] []) clauses rest =
      mainTapes rest [] [] (List.replicate (3 * clauses) true) (encodeWord (2 * clauses)) [] := by
    simp [countHeaderResult, mainTapes, encodeWord]
  rw [countResultEq] at counted
  have reset : Exec (.atom (.load resetHead .done))
      ⟨(initialState.1, some false),
        mainTapes rest [] [] (List.replicate (3 * clauses) true) (encodeWord (2 * clauses)) []⟩ 1
      ⟨initialState,
        mainTapes rest [] [] (List.replicate (3 * clauses) true) (encodeWord (2 * clauses)) []⟩ :=
    Exec.atom _ _
  have converted := BooleanTapeCode.convert_exec Tape.unary .outerIndex .scratch
    (by decide) (by decide) (by decide)
    (mainTapes rest [] [] (List.replicate (3 * clauses) true) [] [])
    initialControl (2 * clauses) 0 []
  simp only [UnaryToBinaryMachine.tapes, List.append_nil, Nat.zero_bits, Nat.zero_add,
    mainTapes_unary, mainTapes_outerIndex, mainTapes_scratch] at converted
  have emitted := BooleanTapeCode.frame_exec Tape.outerIndex .scratch .accumulator
    (by decide) (by decide) (by decide)
    (mainTapes rest [] (2 * clauses).bits (List.replicate (3 * clauses) true) [] [])
    rfl initialControl none
  simp only [mainTapes, List.append_nil, mainTapes_accumulator] at emitted
  have drained := BooleanTapeCode.drain_exec Tape.outerIndex
    (mainTapes rest acc₁ (2 * clauses).bits (List.replicate (3 * clauses) true) [] []) initialState
  simp only [mainTapes, mainTapes_outerIndex] at drained
  have vertexRun := vertices_exec
    (mainTapes rest acc₁ [] (List.replicate (3 * clauses) true) [] [])
    initialControl none (3 * clauses) 0 rfl rfl rfl rfl
  simp only [vertexResult, Nat.zero_add, mainTapes, mainTapes_vertexCount,
    mainTapes_outerIndex, mainTapes_accumulator] at vertexRun
  have vertexEnd : Exec (pushBit .accumulator false)
      ⟨initialState, mainTapes rest acc₂ (3 * clauses).bits [] [] []⟩ 1
      ⟨initialState, mainTapes rest acc₃ (3 * clauses).bits [] [] []⟩ := by
    simpa [pushBit, Action.eval, mainTapes, acc₃] using Exec.atom
      (Action.push Tape.accumulator (fun _ : State => false) .done)
      (Data.mk initialState (mainTapes rest acc₂ (3 * clauses).bits [] [] []))
  have resetIndex := BooleanTapeCode.drain_exec Tape.outerIndex
    (mainTapes rest acc₃ (3 * clauses).bits [] [] []) initialState
  simp only [mainTapes, mainTapes_outerIndex] at resetIndex
  have edgeRun := outerLoop_exec (mainTapes rest acc₃ [] [] [] []) initialControl none
    0 literals rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  simp only [outerLoopResult, Nat.zero_add, mainTapes, mainTapes_input,
    mainTapes_outerIndex, mainTapes_accumulator] at edgeRun
  have edgeEnd : Exec (pushBit .accumulator false)
      ⟨BooleanTapeCode.clean ar, mainTapes [] acc₄ literals.length.bits [] [] []⟩ 1
      ⟨BooleanTapeCode.clean ar, mainTapes [] acc₅ literals.length.bits [] [] []⟩ := by
    simpa [pushBit, Action.eval, mainTapes, acc₅] using Exec.atom
      (Action.push Tape.accumulator (fun _ : State => false) .done)
      (Data.mk (BooleanTapeCode.clean ar) (mainTapes [] acc₄ literals.length.bits [] [] []))
  have cleanIndex := BooleanTapeCode.drain_exec Tape.outerIndex
    (mainTapes [] acc₅ literals.length.bits [] [] []) (BooleanTapeCode.clean ar)
  simp only [mainTapes, mainTapes_outerIndex] at cleanIndex
  have outputRun := BooleanTapeCode.transfer_exec Tape.accumulator .output (by decide)
    (mainTapes [] acc₅ [] [] [] []) (BooleanTapeCode.clean ar)
  simp only [mainTapes, BinPackingGames.Reduction.MachineTransfer.tapesAt,
    mainTapes_accumulator, mainTapes_output, List.append_nil] at outputRun
  have accumulatorEq : acc₅ = (rawGraphWord clauses literals).reverse := by
    simp [acc₅, acc₄, acc₃, acc₂, acc₁, edges, verts, header, rawGraphWord,
      List.reverse_append, List.append_assoc]
  rw [accumulatorEq, List.length_reverse, List.reverse_reverse] at outputRun
  have outputJoined : Exec (BooleanTapeCode.transfer Tape.accumulator .output)
      ⟨((BooleanTapeCode.clean ar).1, none), mainTapes [] acc₅ [] [] [] []⟩
      ((rawGraphWord clauses literals).length + 1)
      ⟨BooleanTapeCode.clean ar, mainTapes [] [] [] [] [] (rawGraphWord clauses literals)⟩ := by
    simpa only [accumulatorEq, BooleanTapeCode.clean] using outputRun
  have cleanControl : Exec (.atom (.load (fun _ => initialState) .done))
      ⟨BooleanTapeCode.clean ar, mainTapes [] [] [] [] [] (rawGraphWord clauses literals)⟩ 1
      ⟨initialState, mainTapes [] [] [] [] [] (rawGraphWord clauses literals)⟩ := Exec.atom _ _
  have last : Exec skip
      ⟨initialState, mainTapes [] [] [] [] [] (rawGraphWord clauses literals)⟩ 1
      ⟨initialState, mainTapes [] [] [] [] [] (rawGraphWord clauses literals)⟩ := Exec.atom .done _
  have run := Exec.seq skipped (Exec.seq seeded (Exec.seq counted (Exec.seq reset
    (Exec.seq converted (Exec.seq emitted (Exec.seq drained (Exec.seq vertexRun
      (Exec.seq vertexEnd (Exec.seq resetIndex (Exec.seq edgeRun (Exec.seq edgeEnd
        (Exec.seq cleanIndex (Exec.seq outputJoined (Exec.seq cleanControl last))))))))))))))
  have initialTapesEq : mainTapes (rawInput «variables» clauses literals) [] [] [] [] [] =
      Function.update (fun _ => []) Tape.input (rawInput «variables» clauses literals) := by
    funext tape; cases tape <;> rfl
  have finalTapesEq : mainTapes [] [] [] [] [] (rawGraphWord clauses literals) =
      Function.update (fun _ => []) Tape.output (rawGraphWord clauses literals) := by
    funext tape; cases tape <;> rfl
  simpa only [program, sequence, skip, frame, drain, transfer, rawCost, phaseCosts,
    List.sum_cons, List.sum_nil, Nat.add_zero, Nat.add_assoc, initialState,
    BooleanTapeCode.clean, BinaryEncoding.natBits, BinPackingCompleteness.BinaryEncoding.nameBits,
    initialTapesEq, finalTapesEq, rest, acc₁, acc₂, acc₃, acc₄, acc₅, ar, header, verts, edges] using run

end

open BinPackingGames.Foundations.Target BinPackingGames.Foundations.Complexity

end BinPackingGap.LiteralSlotGraphMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Hardness_LiteralSlotGraphComputation
attribute [-instance] _root_.OAI.BinPackingCompleteness.PCPSource.clauseCount_neZero _root_.OAI.BinPackingGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.Packing.instDecidableEqTableBin _root_.OAI.BinPackingGap.Packing.instFintypeTableBin _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.LiteralSlotGraphMachine

open Turing FiniteTapeProgram BinPackingGames.Foundations.Target
open BinPackingGames.Foundations.Complexity

def outputsInTime (F : NonemptyFormula) :
    TM2OutputsInTime machine (inputBits F) (some (graphBits (graphInput F)))
      (100 * ((inputBits F).length + 1) ^ 3) := by
  have run := program.outputsInTime Tape.input .output initialState
    (rawInput F.val.variables F.val.clauses.length (formulaLiterals F.val))
    (rawGraphWord F.val.clauses.length (formulaLiterals F.val))
    (rawCost F.val.variables F.val.clauses.length (formulaLiterals F.val))
    (100 * ((formulaBits F.val).length + 1) ^ 3)
    (raw_program_exec F.val.variables F.val.clauses.length (formulaLiterals F.val))
    (rawCost_formula_le F.val)
  simpa only [rawInput_formula, rawGraphWord_graphBits, machine, inputBits] using run

noncomputable def computation :
    TM2ComputableInPolyTime inputBits graphBits graphInput where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.C 100 * (Polynomial.X + Polynomial.C 1) ^ 3
  outputsFun F := by
    change TM2OutputsInTime machine ((inputBits F).map id)
      (some ((graphBits (graphInput F)).map id))
      ((Polynomial.C 100 * (Polynomial.X + Polynomial.C 1) ^ 3 : Polynomial Nat).eval
        (inputBits F).length)
    simp only [List.map_id_fun, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]
    change TM2OutputsInTime machine (inputBits F) (some (graphBits (graphInput F)))
      (100 * ((inputBits F).length + 1) ^ 3)
    exact outputsInTime F

end BinPackingGap.LiteralSlotGraphMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Packing_PackingAssignments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.PackingAssignments

open BinaryRegisterProgram FiniteTapeProgram PackingMachineBlocks

variable {Reg K : Type} [DecidableEq Reg] [DecidableEq K]

theorem exec (slot : (Reg ⊕ Fin 6) ↪ K) (commands : List (Command Reg))
    (base : K → List Bool) (values : Reg → Nat) (ready : Ready commands values)
    (state : State) (width : Nat) (bounded : ∀ r, (values r).size ≤ width) :
    ∃ steps ≤ (runtimePolynomial commands).eval width + 2,
      Exec (code slot commands) ⟨state, registerTapes slot base values⟩ steps
        ⟨.arithmetic (BinaryAddMachine.clean ()),
          registerTapes slot base (resultOf commands values)⟩ := by
  simpa only [code, Nat.add_assoc, Nat.reduceAdd] using PackingArithmeticProgram.exec_in_time
    (BinaryRegisterStructured.code slot commands) _ _ _ state
    (BinaryRegisterStructured.exec_polynomial slot commands base values ready () width bounded)

theorem copy_ready (destination source : Reg) (different : destination ≠ source)
    (values : Reg → Nat) : Ready (copyCommands destination source different) values := by
  simp [copyCommands, Ready, commandReady, result, BinaryRegisterProgram.destination,
    BinaryRegisterProgram.value]

theorem copy_result (destination source : Reg) (different : destination ≠ source)
    (values : Reg → Nat) :
    resultOf (copyCommands destination source different) values =
      Function.update values destination (values source) := by
  simp [copyCommands, resultOf_cons, result, BinaryRegisterProgram.destination,
    BinaryRegisterProgram.value, Ne.symm different]

theorem copy_exec (slot : (Reg ⊕ Fin 6) ↪ K) (destination source : Reg)
    (different : destination ≠ source) (base : K → List Bool) (values : Reg → Nat)
    (state : State) (width : Nat) (bounded : ∀ r, (values r).size ≤ width) :
    ∃ steps ≤ (runtimePolynomial (copyCommands destination source different)).eval width + 2,
      Exec (copy slot destination source different)
        ⟨state, registerTapes slot base values⟩ steps
        ⟨.arithmetic (BinaryAddMachine.clean ()),
          registerTapes slot base (Function.update values destination (values source))⟩ := by
  simpa only [copy, copy_result] using exec slot (copyCommands destination source different)
    base values (copy_ready destination source different values) state width bounded

end BinPackingGap.PackingAssignments

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_PackingVertexUpdate
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.Packing.instDecidableEqTableBin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.PackingLayoutCommands

open NatExpressionCompiler BinaryRegisterProgram FiniteTapeProgram PackingMachineBlocks
open PackingMachineLayout

variable {Descriptor Input Other Extra : Type}
variable [DecidableEq Descriptor] [DecidableEq Input] [DecidableEq Other] [DecidableEq Extra]

def inputFromOtherTime (num : Descriptor → Expr Input) (den : Expr Input)
    (destination : Input) (source : Other) : Polynomial Nat :=
  runtimePolynomial (PackingAssignments.copyCommands (inputs num den destination)
    (others num den source) (input_ne_other num den destination source)) + 2

theorem inputFromOther_exec (num : Descriptor → Expr Input) (den : Expr Input)
    (destination : Input) (source : Other) (base : Tape num den Other Extra → List Bool)
    (input : Input → Nat) (other : Other → Nat) (state : State) (width : Nat)
    (hi : ∀ a, (input a).size ≤ width) (ho : ∀ a, (other a).size ≤ width) :
    ∃ steps ≤ (inputFromOtherTime num den destination source).eval width,
      Exec (inputFromOther num den destination source)
        ⟨state, tapes num den base input other⟩ steps
        ⟨.arithmetic (BinaryAddMachine.clean ()),
          tapes num den base (Function.update input destination (other source)) other⟩ := by
  have run := PackingAssignments.copy_exec (registers (Extra := Extra) num den)
    (inputs num den destination) (others num den source) (input_ne_other num den destination source)
    base (values num den input other) state width (values_width num den input other width hi ho)
  rw [values_others, ← values_update_input] at run
  simpa only [inputFromOther, inputFromOtherTime, Polynomial.eval_add,
    Polynomial.eval_ofNat, tapes] using run

def setOtherTime (num : Descriptor → Expr Input) (den : Expr Input)
    (destination : Other) (constant : Nat) : Polynomial Nat :=
  runtimePolynomial (PackingAssignments.constantCommands
    (others num den destination) constant) + 2

end BinPackingGap.PackingLayoutCommands

namespace BinPackingGap.PackingVertexUpdate

open NatExpressionCompiler BinaryRegisterProgram FiniteTapeProgram

variable {Descriptor Input Other Extra : Type}
variable [DecidableEq Descriptor] [DecidableEq Input]

variable [DecidableEq Other] [DecidableEq Extra]

theorem exec (num : Descriptor → Expr Input) (den : Expr Input)
    (power : Input) (three temporary : Other) (distinct : three ≠ temporary)
    (base : PackingMachineLayout.Tape num den Other Extra → List Bool)
    (input : Input → Nat) (other : Other → Nat)
    (hthree : other three = 3) (htemporary : other temporary = 0)
    (state : PackingMachineBlocks.State) :
    ∃ steps ≤ 64 * ((3 : Nat).size + (input power).size + 1) ^ 2,
      Exec (PackingRegisterUpdate.code
          (updateSlots num den power three temporary distinct) .multiply)
        ⟨state, PackingMachineLayout.tapes num den base input other⟩ steps
        ⟨.arithmetic (BinaryAddMachine.clean ()),
          PackingMachineLayout.tapes num den base
            (Function.update input power (3 * input power)) other⟩ := by
  obtain ⟨steps, hsteps, hrun⟩ := PackingRegisterUpdate.exec
    (updateSlots num den power three temporary distinct) .multiply
    (PackingMachineLayout.tapes num den base input other) 3 (input power) state
  refine ⟨steps, hsteps, ?_⟩
  change Exec (PackingRegisterUpdate.code
      (updateSlots num den power three temporary distinct) .multiply)
    ⟨state, registerTapes (updateSlots num den power three temporary distinct)
      (PackingMachineLayout.tapes num den base input other)
      (PackingRegisterUpdate.values 3 (input power))⟩ steps
    ⟨.arithmetic (BinaryAddMachine.clean ()),
      registerTapes (updateSlots num den power three temporary distinct)
        (PackingMachineLayout.tapes num den base input other)
        (PackingRegisterUpdate.values 3 (3 * input power))⟩ at hrun
  rw [shape num den power three temporary distinct base input other hthree htemporary,
    updated_shape num den power three temporary distinct base input other hthree htemporary] at hrun
  exact hrun

theorem general_exec (num : Descriptor → Expr Input) (den : Expr Input)
    (power : Input) (baseRegister temporary : Other) (distinct : baseRegister ≠ temporary)
    (kind : PackingRegisterUpdate.Kind)
    (base : PackingMachineLayout.Tape num den Other Extra → List Bool)
    (input : Input → Nat) (other : Other → Nat) (htemporary : other temporary = 0)
    (state : PackingMachineBlocks.State) :
    ∃ steps ≤ 64 * ((other baseRegister).size + (input power).size + 1) ^ 2,
      Exec (PackingRegisterUpdate.code
          (updateSlots num den power baseRegister temporary distinct) kind)
        ⟨state, PackingMachineLayout.tapes num den base input other⟩ steps
        ⟨.arithmetic (BinaryAddMachine.clean ()),
          PackingMachineLayout.tapes num den base
            (Function.update input power
              (PackingRegisterUpdate.operation kind (other baseRegister) (input power))) other⟩ := by
  obtain ⟨steps, hsteps, hrun⟩ := PackingRegisterUpdate.exec
    (updateSlots num den power baseRegister temporary distinct) kind
    (PackingMachineLayout.tapes num den base input other)
    (other baseRegister) (input power) state
  refine ⟨steps, hsteps, ?_⟩
  simpa only [general_shape num den power baseRegister temporary distinct base input other htemporary,
    general_updated_shape num den power baseRegister temporary distinct kind base input other
      htemporary] using hrun

end BinPackingGap.PackingVertexUpdate

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_PackingJobLoop
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.PackingDescriptorExpression

open NatExpressionCompiler PackingInventoryDescriptors

theorem chunk_records (D : InventoryData) (label : Option D.Vertex) (edge rep : Nat)
    (descriptors : List (ItemDescriptor D)) :
    PackingChunkMachine.records (numerator D) PackingItemExpression.denominator
      (fun _ => values D label edge rep) descriptors =
      rawRecords (descriptors.map (rawOfDescriptor D label edge rep)) := by
  simp only [PackingChunkMachine.records, rawRecords, List.flatMap_map, record_eq]

theorem rawInstanceBits_eq (items : RawInstance) :
    BinaryEncoding.rawInstanceBits items = rawRecords items ++ [false] := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
      simp only [BinaryEncoding.rawInstanceBits, BinaryEncoding.listBits,
        BinaryEncoding.pairBits, rawRecords, List.flatMap_cons, rawRecord] at *
      rw [ih]
      simp only [List.cons_append, List.append_assoc]

theorem reductionOutputBits_eq (B : Nat) (items : RawInstance) :
    BinaryEncoding.rawReductionOutputBits (B, items) =
      BinaryEncoding.natBits B ++ rawRecords items ++ [false] := by
  rw [BinaryEncoding.rawReductionOutputBits, rawInstanceBits_eq, List.append_assoc]

end BinPackingGap.PackingDescriptorExpression

namespace BinPackingGap.PackingJobBody

open FiniteTapeProgram PackingMachineBlocks BinaryRegisterProgram NatExpressionCompiler
open PackingMachineLayout
open PackingItemBlockMachine (outputTapes)

variable {α δ Other Extra : Type}
variable [DecidableEq α] [DecidableEq δ] [DecidableEq Other] [DecidableEq Extra]

def bodyTimePolynomial (num : δ → Expr α) (den : Expr α) (descriptors : List δ)
    (power : α) (leftPower rightPower : Other) : Polynomial Nat :=
  PackingLayoutCommands.inputFromOtherTime num den power leftPower +
    PackingLayoutCommands.inputFromOtherTime num den power rightPower +
    2 * (PackingChunkMachine.timePolynomial num den descriptors + 1) +
    64 * (Polynomial.X + 2) ^ 2

omit [DecidableEq α] [DecidableEq δ] [DecidableEq Other] in
theorem bodyTimePolynomial_eval (num : δ → Expr α) (den : Expr α)
    (descriptors : List δ) (power : α) (leftPower rightPower : Other) (width : Nat) :
    (bodyTimePolynomial num den descriptors power leftPower rightPower).eval width =
      (PackingLayoutCommands.inputFromOtherTime num den power leftPower).eval width +
        (PackingLayoutCommands.inputFromOtherTime num den power rightPower).eval width +
        2 * ((PackingChunkMachine.timePolynomial num den descriptors).eval width + 1) +
        64 * (width + 2) ^ 2 := by
  simp [bodyTimePolynomial]

end BinPackingGap.PackingJobBody

namespace BinPackingGap.PackingVertexRecords

open NatExpressionCompiler

theorem rawRecords_flatMap {ι : Type} (indices : List ι) (items : ι → RawInstance) :
    PackingDescriptorExpression.rawRecords (indices.flatMap items) =
      indices.flatMap (fun i => PackingDescriptorExpression.rawRecords (items i)) := by
  simp only [PackingDescriptorExpression.rawRecords, List.flatMap_assoc]

theorem stream_eq_vertexStream (D : InventoryData) :
    PackingVertexLoop.stream (PackingDescriptorExpression.numerator D)
        PackingItemExpression.denominator (PackingInventoryDescriptors.vertexDescriptors D)
        (PackingDescriptorExpression.values D none 0 0) .labelPower 0 D.graph.n =
      PackingDescriptorExpression.rawRecords (PackingInventoryDescriptors.vertexStream D) := by
  rw [stream_eq_finRange, PackingInventoryDescriptors.vertexStream, rawRecords_flatMap]
  apply List.flatMap_congr
  intro v _
  simpa only [Nat.zero_add, values_vertexInput] using
    PackingDescriptorExpression.chunk_records D (some v) 0 0
      (PackingInventoryDescriptors.vertexDescriptors D)

end BinPackingGap.PackingVertexRecords

namespace BinPackingGap.PackingJobLoop

open FiniteTapeProgram PackingMachineBlocks BinaryRegisterProgram NatExpressionCompiler
open PackingMachineLayout
open PackingItemBlockMachine (outputTapes)
open PackingCountedProgram (counterTapes guardState)
open PackingJobBody (nextInput pairRecords bodyTimePolynomial)

variable {α δ Other Extra : Type}
variable [DecidableEq α] [DecidableEq δ] [DecidableEq Other] [DecidableEq Extra]

def timePolynomial (num : δ → Expr α) (den : Expr α) (descriptors : List δ)
    (power : α) (leftPower rightPower : Other) : Polynomial Nat :=
  Polynomial.X * (bodyTimePolynomial num den descriptors power leftPower rightPower + 1) + 1

end BinPackingGap.PackingJobLoop

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_PackingSetupGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.PackingSetupMachine

section

open NatExpressionCompiler BinaryRegisterProgram FiniteTapeProgram
open PackingSetupExpression

variable {K A : Type} [DecidableEq K]

def timePolynomial (p : Parameters) : Polynomial Nat :=
  runtimePolynomial (commands p) + Polynomial.C 1

end

open BinaryRegisterProgram FiniteTapeProgram PackingSetupExpression

end BinPackingGap.PackingSetupMachine

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_GraphPackingJobList
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.GraphPackingJobStream

open PackingDescriptorExpression PackingInventoryDescriptors

theorem pairRecords_eq (D : InventoryData) (label : Option D.Vertex)
    (edge : D.Edge) (rep : Nat) :
    PackingJobBody.pairRecords (numerator D) PackingItemExpression.denominator
        (jobDescriptors D) (values D label edge.val rep) .labelPower
        (endpointPower D edge 0) (endpointPower D edge 1) =
      rawRecords (rawPair D edge rep) := by
  have sides : List.finRange 2 = [0, 1] := by decide
  unfold PackingJobBody.pairRecords endpointPower
  rw [values_update_label, values_update_label, chunk_records, chunk_records]
  simp only [rawPair, sides, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, rawRecords, List.flatMap_append]

theorem stream_eq (D : InventoryData) (edge : D.Edge) (count rep : Nat)
    (label : Option D.Vertex) :
    PackingJobLoop.stream (numerator D) PackingItemExpression.denominator
        (jobDescriptors D) (values D label edge.val rep) .labelPower .repetitionOne
        (endpointPower D edge 0) (endpointPower D edge 1) count =
      rawRecords ((List.finRange count).flatMap fun j => rawPair D edge (rep + j.val)) := by
  induction count generalizing rep label with
  | zero => simp [PackingJobLoop.stream, rawRecords]
  | succ count ih =>
      rw [PackingJobLoop.stream_succ, pairRecords_eq, nextInput_values, ih]
      have order : (List.finRange (count + 1)).flatMap
          (fun j => rawPair D edge (rep + j.val)) =
          rawPair D edge rep ++ (List.finRange count).flatMap
            (fun j => rawPair D edge ((rep + 1) + j.val)) := by
        rw [List.finRange_succ, List.flatMap_cons, List.flatMap_map]
        simp only [Fin.val_zero, Nat.add_zero, Fin.val_succ]
        congr 1
        apply congrArg (fun f => (List.finRange count).flatMap f)
        funext j
        congr 1
        omega
      rw [order]
      simp only [rawRecords, List.flatMap_append]

theorem stream_edge_eq (D : InventoryData) (edge : D.Edge) (label : Option D.Vertex) :
    PackingJobLoop.stream (numerator D) PackingItemExpression.denominator
        (jobDescriptors D) (values D label edge.val 1) .labelPower .repetitionOne
        (endpointPower D edge 0) (endpointPower D edge 1) D.R =
      rawRecords ((List.finRange D.R).flatMap fun j =>
        (List.finRange 2).flatMap fun side =>
          (jobDescriptors D).map
            (rawOfDescriptor D (some (D.graph.endpoint edge side)) edge.val (j.val + 1))) := by
  simpa only [rawPair, Nat.add_comm 1] using stream_eq D edge D.R 1 label

theorem stream_edge_instantiate_eq (fixed : InventoryData) (graph : GraphInput)
    (R k : Nat) (edge : graph.Edge) (label : Option graph.Vertex) :
    PackingJobLoop.stream (numerator fixed) PackingItemExpression.denominator
        (jobDescriptors fixed) (values (instantiate fixed graph R k) label edge.val 1)
        .labelPower .repetitionOne
        (endpointPower (instantiate fixed graph R k) edge 0)
        (endpointPower (instantiate fixed graph R k) edge 1) R =
      rawRecords ((List.finRange R).flatMap fun j =>
        (List.finRange 2).flatMap fun side =>
          (jobDescriptors fixed).map (rawOfDescriptor (instantiate fixed graph R k)
            (some (graph.endpoint edge side)) edge.val (j.val + 1))) := by
  have hnum : numerator (instantiate fixed graph R k) = numerator fixed := by
    funext descriptor
    exact numerator_instantiate fixed graph R k descriptor
  have hstream := stream_edge_eq (instantiate fixed graph R k) edge label
  simp only [jobDescriptors_instantiate, hnum] at hstream
  simpa only [instantiate] using hstream

end BinPackingGap.GraphPackingJobStream

namespace BinPackingGap.GraphPackingJobs

section

open GraphPackingRegisters GraphPackingPreparation PackingItemExpression
open PackingDescriptorExpression PackingInventoryDescriptors

variable (fixed : InventoryData) (K : Nat)

def repeatFinalInputs (x : GraphReductionInput) (e : x.graph.Edge) : Variable → Nat :=
  completedInputs fixed K x e.val (x.graph.right e).val

theorem repeatInputs_eq_values (x : GraphReductionInput) (edge : Nat) :
    repeatInputs fixed K x edge = values (inventory fixed K x) none edge 1 := by
  unfold repeatInputs
  rw [inputs_eq_values]
  funext reg
  cases reg <;> simp [PackingDescriptorExpression.values]

theorem loaded_one (x : GraphReductionInput) (left right : Nat) :
    loadedOther fixed K x left right
        (.inl (PackingSetupMachine.output (parameters fixed K) .one)) = 1 := by
  rw [loaded_setup]
  rfl

theorem loaded_repetitions (x : GraphReductionInput) (left right : Nat) :
    loadedOther fixed K x left right
        (.inl (PackingSetupMachine.output (parameters fixed K) .repetitions)) =
      GraphPackingPreparation.repetitions fixed K x := by
  rw [loaded_setup]
  rfl

theorem repeatStream_eq (x : GraphReductionInput) (e : x.graph.Edge) :
    PackingJobLoop.stream (numerator fixed) denominator (jobDescriptors fixed)
        (repeatInputs fixed K x e.val) .labelPower .repetitionOne
        (loadedOther fixed K x (x.graph.left e).val (x.graph.right e).val (.inr .leftPower))
        (loadedOther fixed K x (x.graph.left e).val (x.graph.right e).val (.inr .rightPower))
        (GraphPackingPreparation.repetitions fixed K x) =
      edgeWord fixed K x e := by
  rw [repeatInputs_eq_values, loaded_left, loaded_right]
  simpa only [edgeWord, inventory, GraphPackingJobStream.endpointPower,
    PackingDescriptorExpression.instantiate, GraphInput.endpoint_zero, GraphInput.endpoint_one] using
    GraphPackingJobStream.stream_edge_instantiate_eq fixed x.graph
      (GraphPackingPreparation.repetitions fixed K x) x.k e none

theorem repeatIteration_eq (x : GraphReductionInput) (e : x.graph.Edge) :
    PackingJobLoop.iterationInput (repeatInputs fixed K x e.val) .labelPower .repetitionOne
        (loadedOther fixed K x (x.graph.left e).val (x.graph.right e).val (.inr .rightPower))
        (GraphPackingPreparation.repetitions fixed K x) =
      repeatFinalInputs fixed K x e := by
  have positive : 0 < GraphPackingPreparation.repetitions fixed K x := by
    unfold GraphPackingPreparation.repetitions
    omega
  rw [loaded_right]
  cases hcount : GraphPackingPreparation.repetitions fixed K x with
  | zero => omega
  | succ count =>
      funext reg
      cases reg <;>
        simp [PackingJobLoop.iterationInput, hcount, repeatInputs,
          repeatFinalInputs, completedInputs, Nat.add_comm]

end

open BinaryEncoding PackingDescriptorExpression PackingInventoryDescriptors

theorem edgeFields_finRange (x : GraphReductionInput) :
    edgeFields x (List.finRange x.graph.edges.length) =
      GraphFieldMachine.fieldBits .endpoints x := by
  let encode : (Fin x.graph.n × Fin x.graph.n) → List Bool :=
    fun p => natBits p.1.val ++ natBits p.2.val
  calc
    edgeFields x (List.finRange x.graph.edges.length) =
        listBits encode ((List.finRange x.graph.edges.length).map x.graph.edges.get) := by
      exact (listBits_map encode x.graph.edges.get
        (List.finRange x.graph.edges.length)).symm
    _ = listBits encode x.graph.edges := by rw [List.map_get_finRange]
    _ = GraphFieldMachine.fieldBits .endpoints x := by
      simp only [encode, GraphFieldMachine.fieldBits, GraphFieldMachine.fieldsOutput,
        GraphReductionInput.fields, GraphInput.endpointPairs, listBits_map, pairBits]

theorem edgeWords_finRange (fixed : InventoryData) (K : Nat)
    (x : GraphReductionInput) :
    edgeWords fixed K x (List.finRange x.graph.edges.length) =
      rawRecords (jobStream (inventory fixed K x)) := by
  unfold edgeWords edgeWord
  simp only [jobStream, rawRecords, List.flatMap_assoc,
    inventory, jobDescriptors_instantiate]
  simp only [instantiate]

end BinPackingGap.GraphPackingJobs

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_GraphPackingPreparationFinish
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.PackingEndpointPower

open BinPackingGames.Foundations.Complexity
open BinaryRegisterProgram FiniteTapeProgram PackingMachineBlocks

variable {K : Type} [DecidableEq K]

theorem exec (slots : (Fin 7 ⊕ Fin 6) ↪ K) (tally : K)
    (outside : ∀ q, slots q ≠ tally) (base : K → List Bool) (v : Nat)
    (ready : Ready slots tally base v) (state : State) :
    ∃ steps ≤ timePolynomial.eval v,
      Exec (code slots tally outside) ⟨state, base⟩ steps
        ⟨.arithmetic (BinaryAddMachine.clean ()), resultTapes slots base v⟩ := by
  have hs (a b : Fin 7 ⊕ Fin 6) : slots a = slots b ↔ a = b := slots.injective.eq_iff
  have ht (a : Fin 7 ⊕ Fin 6) : tally ≠ slots a := (outside a).symm
  have tallyOutside : ∀ q, tallySlots slots q ≠ tally := by
    intro q
    cases q with
    | inl r => exact outside (.inl (tallyRegister r))
    | inr j => exact outside (.inr j)
  have tallyRegisters : ∀ r, base (tallySlots slots (.inl r)) =
      (BinaryToTallyMachine.initial v r).bits := by
    intro r
    cases r with
    | source => exact ready.registers 0
    | counter => exact ready.registers 3
    | one => exact ready.registers 4
    | temporary => exact ready.registers 5
  have tallyScratch : ∀ j, base (tallySlots slots (.inr j)) = [] := by
    intro j
    exact ready.scratch j
  let tallied := Function.update base tally (List.replicate v true)
  have convertRun : ∃ steps ≤ BinaryToTallyMachine.runtimeBound v,
      Exec (BinaryToTallyMachine.code (A := Unit) (tallySlots slots) tally)
        ⟨BinaryAddMachine.clean (), base⟩ steps
        ⟨BinaryAddMachine.clean (), tallied⟩ := by
    simpa only [ready.tallyEmpty, List.append_nil] using
      BinaryToTallyMachine.exec_from_tapes (tallySlots slots) tally tallyOutside base v
        tallyRegisters tallyScratch ()
  obtain ⟨ct, hc, converted⟩ := PackingArithmeticProgram.exec_in_time
    (BinaryToTallyMachine.code (tallySlots slots) tally) base tallied _ state convertRun
  have tallied_register (r : Fin 7) : tallied (slots (.inl r)) = (values v 0 r).bits := by
    simp only [tallied, Function.update_of_ne (outside (.inl r)), ready.registers]
  have tallied_scratch (j : Fin 6) : tallied (slots (.inr j)) = [] := by
    simp only [tallied, Function.update_of_ne (outside (.inr j)), ready.scratch]
  have powerSlot (j : Fin 11) : powerSlots slots tally outside j =
      ![slots (.inl 1), slots (.inl 2), slots (.inl 5),
        slots (.inr 0), slots (.inr 1), slots (.inr 2), slots (.inr 3),
        slots (.inr 4), slots (.inr 5), tally, slots (.inl 6)] j := rfl
  have powerReady : PackingPowerProgram.Ready (powerSlots slots tally outside) tallied 3 v := by
    constructor
    · exact tallied_register 1
    · exact tallied_register 2
    · change tallied tally = List.replicate v true
      simp only [tallied, Function.update_self]
    · intro j hj hj9
      rw [powerSlot]
      fin_cases j <;> simp_all [values]
  let powered := PackingPowerProgram.resultTapes (powerSlots slots tally outside) tallied 3 v
  obtain ⟨pt, hp, powerRun⟩ := PackingArithmeticProgram.exec_in_time
    (PackingPowerProgram.code (powerSlots slots tally outside)) tallied powered
    (PackingPowerProgram.budget 3 v) (.arithmetic (BinaryAddMachine.clean ()))
    (PackingPowerProgram.exec (powerSlots slots tally outside) tallied 3 v powerReady ())
  have powered_eq : powered = Function.update base (slots (.inl 2)) (3 ^ v).bits := by
    change Function.update
      (Function.update (Function.update base tally (List.replicate v true)) tally [])
      (slots (.inl 2)) (3 ^ v).bits = _
    rw [Function.update_idem, ← ready.tallyEmpty, Function.update_eq_self]
  have updateRegisters : ∀ r, powered (updateSlots slots (.inl r)) =
      (PackingRegisterUpdate.values 3 (3 ^ v) r).bits := by
    intro r
    rw [powered_eq]
    change Function.update base (slots (.inl 2)) (3 ^ v).bits
      (slots (.inl (![1, 2, 5] r))) = _
    fin_cases r <;> simp [hs, ready.registers, values, PackingRegisterUpdate.values]
  have updateScratch : ∀ j, powered (updateSlots slots (.inr j)) = [] := by
    intro j
    rw [powered_eq]
    simp [hs, ready.scratch]
  have updateFrame : registerTapes (updateSlots slots) powered
      (PackingRegisterUpdate.values 3 (3 ^ v)) = powered :=
    register_frame_eq (updateSlots slots) powered _ updateRegisters updateScratch
  have newValues : PackingRegisterUpdate.values 3
        (PackingRegisterUpdate.operation .multiply 3 (3 ^ v)) =
      Function.update (PackingRegisterUpdate.values 3 (3 ^ v)) 1 (3 * 3 ^ v) := by
    funext r
    fin_cases r <;> simp [PackingRegisterUpdate.values, PackingRegisterUpdate.operation]
  obtain ⟨mt, hm, multiplyRun⟩ := PackingRegisterUpdate.exec (updateSlots slots) .multiply
    powered 3 (3 ^ v) (.arithmetic (BinaryAddMachine.clean ()))
  rw [newValues, ← registerTapes_update, updateFrame] at multiplyRun
  have finalFrame : Function.update powered (updateSlots slots (.inl 1)) (3 * 3 ^ v).bits =
      resultTapes slots base v := by
    rw [powered_eq]
    change Function.update (Function.update base (slots (.inl 2)) (3 ^ v).bits)
      (slots (.inl 2)) (3 * 3 ^ v).bits = _
    simp only [Function.update_idem, resultTapes, Nat.pow_succ, Nat.mul_comm]
  rw [finalFrame] at multiplyRun
  refine ⟨ct + (pt + mt), ?_, Exec.seq converted (Exec.seq powerRun multiplyRun)⟩
  have hct := tally_budget_le v
  have hpt := power_budget v
  have hmt := multiply_budget_le v
  rw [timePolynomial_eval]
  omega

end BinPackingGap.PackingEndpointPower

namespace BinPackingGap.PackingVertexLoop

open FiniteTapeProgram PackingMachineBlocks BinaryRegisterProgram NatExpressionCompiler
open PackingMachineLayout
open PackingItemBlockMachine (outputTapes)
open PackingCountedProgram (counterTapes guardState)

variable {α δ Other Extra : Type}
variable [DecidableEq α] [DecidableEq δ] [DecidableEq Other] [DecidableEq Extra]

def bodyTimePolynomial (num : δ → Expr α) (den : Expr α) (descriptors : List δ) :
    Polynomial Nat :=
  PackingChunkMachine.timePolynomial num den descriptors + 1 +
    64 * (Polynomial.X + 3) ^ 2

omit [DecidableEq α] [DecidableEq δ] in
theorem bodyTimePolynomial_eval (num : δ → Expr α) (den : Expr α)
    (descriptors : List δ) (width : Nat) :
    (bodyTimePolynomial num den descriptors).eval width =
      (PackingChunkMachine.timePolynomial num den descriptors).eval width + 1 +
        64 * (width + 3) ^ 2 := by
  simp [bodyTimePolynomial]

end BinPackingGap.PackingVertexLoop

namespace BinPackingGap.GraphPackingProgram

open FiniteTapeProgram

variable {fixed : InventoryData} {K : Nat}

namespace PhaseRuns

theorem append {first second : List (Program fixed K)} {before middle after n m}
    (left : PhaseRuns first before n middle) (right : PhaseRuns second middle m after) :
    PhaseRuns (first ++ second) before (n + m) after := by
  induction left with
  | nil => simpa only [List.nil_append, Nat.zero_add] using right
  | cons head tail ih =>
      simpa only [List.cons_append, Nat.add_assoc] using PhaseRuns.cons head (ih right)

end PhaseRuns

end BinPackingGap.GraphPackingProgram

namespace BinPackingGap.GraphPackingTapeBlocks

open BinaryRegisterProgram FiniteTapeProgram PackingMachineBlocks
open GraphPackingRegisters PackingRegisterFrame

variable (fixed : InventoryData) (K : Nat)

theorem power_exec (source : CountSource) (destination : PackingItemExpression.Variable)
    (base : Tape fixed K → List Bool) (vals : Register fixed K → Nat)
    (exponent : Nat) (state : State)
    (destinationZero : vals (item fixed K destination) = 0)
    (temporaryZero : vals (work fixed K .temporary) = 0)
    (reverseZero : vals (work fixed K .reverse) = 0)
    (tallyWord : base (.inr .powerCounter) = List.replicate exponent true) :
    ∃ steps ≤ PackingPowerProgram.budget (vals (countRegister fixed K source)) exponent + 1,
      Exec (GraphPackingProgram.power fixed K source destination)
        ⟨state, registerTapes (slots fixed K) base vals⟩ steps
        ⟨.arithmetic (BinaryAddMachine.clean ()),
          registerTapes (slots fixed K) (Function.update base (.inr .powerCounter) [])
            (Function.update vals (item fixed K destination)
              (vals (countRegister fixed K source) ^ exponent))⟩ := by
  have powerSlot (j : Fin 11) : powerSlots fixed K source destination j =
      ![slots fixed K (.inl (countRegister fixed K source)),
        slots fixed K (.inl (item fixed K destination)),
        slots fixed K (.inl (work fixed K .temporary)),
        slots fixed K (.inr 0), slots fixed K (.inr 1), slots fixed K (.inr 2),
        slots fixed K (.inr 3), slots fixed K (.inr 4), slots fixed K (.inr 5),
        .inr .powerCounter, slots fixed K (.inl (work fixed K .reverse))] j := rfl
  have ready : PackingPowerProgram.Ready (powerSlots fixed K source destination)
      (registerTapes (slots fixed K) base vals) (vals (countRegister fixed K source)) exponent := by
    constructor
    · simp [powerSlot]
    · simp [powerSlot, destinationZero]
    · simp [powerSlot, tallyWord]
    · intro j hj hj9
      fin_cases j <;> simp_all
  have after : PackingPowerProgram.resultTapes (powerSlots fixed K source destination)
      (registerTapes (slots fixed K) base vals) (vals (countRegister fixed K source)) exponent =
      registerTapes (slots fixed K) (Function.update base (.inr .powerCounter) [])
        (Function.update vals (item fixed K destination)
          (vals (countRegister fixed K source) ^ exponent)) := by
    change Function.update
      (Function.update (registerTapes (slots fixed K) base vals) (.inr .powerCounter) [])
      (slots fixed K (.inl (item fixed K destination)))
      (vals (countRegister fixed K source) ^ exponent).bits = _
    rw [← external_update (slots fixed K) base vals (.inr .powerCounter)
      (slots_outside fixed K .powerCounter), registerTapes_update]
  obtain ⟨t, ht, actual⟩ := PackingPowerProgram.exec (powerSlots fixed K source destination)
    (registerTapes (slots fixed K) base vals) (vals (countRegister fixed K source)) exponent ready ()
  rw [after] at actual
  exact PackingArithmeticProgram.exec_in_time
    (PackingPowerProgram.code (powerSlots fixed K source destination)) _ _ _ state ⟨t, ht, actual⟩

end BinPackingGap.GraphPackingTapeBlocks

namespace BinPackingGap.GraphPackingPreparation

section

open GraphPackingRegisters BinaryRegisterProgram FiniteTapeProgram PackingMachineBlocks
open GraphPackingProgram PackingRegisterFrame

variable (fixed : InventoryData) (K : Nat)

def firstPowerValues (x : GraphReductionInput) : Register fixed K → Nat :=
  Function.update (setupValues fixed K x) (item fixed K .vertexPower) (3 ^ x.graph.n)

def secondPowerValues (x : GraphReductionInput) : Register fixed K → Nat :=
  Function.update (firstPowerValues fixed K x) (item fixed K .totalPower)
    ((repetitions fixed K x + 1) ^ x.graph.edges.length)

def factorValues (x : GraphReductionInput) : Register fixed K → Nat :=
  Function.update (secondPowerValues fixed K x) (work fixed K .geometryFactor)
    (geometryFactor fixed)

def finalValues (x : GraphReductionInput) : Register fixed K → Nat :=
  Function.update (factorValues fixed K x) (item fixed K .geometry)
    (geometryFactor fixed * (repetitions fixed K x + 1) ^ x.graph.edges.length)

def powerPhases : List (Program fixed K) :=
  [tally fixed K (.input .n) .powerCounter,
    power fixed K (.output .three) .vertexPower,
    tally fixed K (.input .m) .powerCounter,
    power fixed K (.output .base) .totalPower]

def powerBudget (x : GraphReductionInput) : Nat :=
  BinaryToTallyMachine.runtimeBound x.graph.n +
    PackingPowerProgram.budget 3 x.graph.n +
    BinaryToTallyMachine.runtimeBound x.graph.edges.length +
    PackingPowerProgram.budget (repetitions fixed K x + 1) x.graph.edges.length + 4

theorem powers_exec (x : GraphReductionInput) (state : State) :
    ∃ steps ≤ powerBudget fixed K x,
      PhaseRuns (powerPhases fixed K)
        ⟨state, registerTapes (slots fixed K) (baseTapes fixed K x) (setupValues fixed K x)⟩ steps
        ⟨.arithmetic (BinaryAddMachine.clean ()),
          registerTapes (slots fixed K) (baseTapes fixed K x) (secondPowerValues fixed K x)⟩ := by
  let base := baseTapes fixed K x
  let vals := setupValues fixed K x
  let counter (n : Nat) := Function.update base (.inr .powerCounter) (List.replicate n true)
  have clearCounter (n : Nat) : Function.update (counter n) (.inr .powerCounter) [] = base := by
    change Function.update
      (Function.update base (.inr .powerCounter) (List.replicate n true))
      (.inr .powerCounter) [] = base
    rw [Function.update_idem]
    exact Function.update_eq_self_iff.mpr rfl
  obtain ⟨a, ha, arun⟩ := GraphPackingTapeBlocks.tally_exec fixed K (.input .n) .powerCounter
    base vals state rfl rfl rfl
  have arun' : Exec (tally fixed K (.input .n) .powerCounter)
      ⟨state, registerTapes (slots fixed K) base vals⟩ a
      ⟨.arithmetic (BinaryAddMachine.clean ()), registerTapes (slots fixed K)
        (counter x.graph.n) vals⟩ := by
    simpa only [vals, countRegister, setupValues_input, PackingSetupExpression.inputs,
      base, base_powerCounter, List.append_nil, counter] using arun
  obtain ⟨b, hb, brun⟩ := GraphPackingTapeBlocks.power_exec fixed K (.output .three) .vertexPower
    (counter x.graph.n) vals x.graph.n (.arithmetic (BinaryAddMachine.clean ())) rfl rfl rfl
    (by simp [counter])
  have brun' : Exec (power fixed K (.output .three) .vertexPower)
      ⟨.arithmetic (BinaryAddMachine.clean ()), registerTapes (slots fixed K)
        (counter x.graph.n) vals⟩ b
      ⟨.arithmetic (BinaryAddMachine.clean ()), registerTapes (slots fixed K)
        base (firstPowerValues fixed K x)⟩ := by
    simpa only [clearCounter, vals, countRegister, setupValues_output,
      PackingSetupExpression.outputValues, firstPowerValues] using brun
  have unchanged (r : Register fixed K) (hne : r ≠ item fixed K .vertexPower) :
      firstPowerValues fixed K x r = setupValues fixed K x r :=
    Function.update_of_ne hne _ _
  have workZero (w : Work) : firstPowerValues fixed K x (work fixed K w) = 0 := by
    rw [unchanged _ (by
      change (Sum.inl (Sum.inr (Sum.inr w)) : Register fixed K) ≠
        Sum.inl (Sum.inl .vertexPower)
      simp)]
    exact setupValues_work fixed K x w
  obtain ⟨c, hc, crun⟩ := GraphPackingTapeBlocks.tally_exec fixed K (.input .m) .powerCounter
    base (firstPowerValues fixed K x) (.arithmetic (BinaryAddMachine.clean ()))
    (workZero .counter) (workZero .one) (workZero .temporary)
  have inputM : firstPowerValues fixed K x (countRegister fixed K (.input .m)) =
      x.graph.edges.length := by
    rw [unchanged _ (by
      change (Sum.inl (Sum.inr (Sum.inl
        (PackingSetupMachine.input (parameters fixed K) .m))) : Register fixed K) ≠
          Sum.inl (Sum.inl .vertexPower)
      simp)]
    rfl
  have crun' : Exec (tally fixed K (.input .m) .powerCounter)
      ⟨.arithmetic (BinaryAddMachine.clean ()), registerTapes (slots fixed K)
        base (firstPowerValues fixed K x)⟩ c
      ⟨.arithmetic (BinaryAddMachine.clean ()), registerTapes (slots fixed K)
        (counter x.graph.edges.length) (firstPowerValues fixed K x)⟩ := by
    simpa only [inputM, base, base_powerCounter, List.append_nil, counter] using crun
  have totalEmpty : firstPowerValues fixed K x (item fixed K .totalPower) = 0 := by
    rw [unchanged _ (by
      intro h
      have equal := (item fixed K).injective h
      cases equal)]
    exact setupValues_item fixed K x .totalPower
  have baseValue : firstPowerValues fixed K x (countRegister fixed K (.output .base)) =
      repetitions fixed K x + 1 := by
    rw [unchanged _ (by
      change (Sum.inl (Sum.inr (Sum.inl
        (PackingSetupMachine.output (parameters fixed K) .base))) : Register fixed K) ≠
          Sum.inl (Sum.inl .vertexPower)
      simp)]
    rfl
  obtain ⟨d, hd, drun⟩ := GraphPackingTapeBlocks.power_exec fixed K (.output .base) .totalPower
    (counter x.graph.edges.length) (firstPowerValues fixed K x) x.graph.edges.length
    (.arithmetic (BinaryAddMachine.clean ())) totalEmpty (workZero .temporary) (workZero .reverse)
    (by simp [counter])
  have drun' : Exec (power fixed K (.output .base) .totalPower)
      ⟨.arithmetic (BinaryAddMachine.clean ()), registerTapes (slots fixed K)
        (counter x.graph.edges.length) (firstPowerValues fixed K x)⟩ d
      ⟨.arithmetic (BinaryAddMachine.clean ()), registerTapes (slots fixed K)
        base (secondPowerValues fixed K x)⟩ := by
    simpa only [clearCounter, baseValue, secondPowerValues] using drun
  refine ⟨a + (b + (c + d)), ?_, ?_⟩
  · rw [inputM] at hc
    rw [baseValue] at hd
    simp only [vals, countRegister, setupValues_input, PackingSetupExpression.inputs,
      setupValues_output, PackingSetupExpression.outputValues] at ha hb
    unfold powerBudget
    omega
  · exact PhaseRuns.cons arun' (PhaseRuns.cons brun'
      (PhaseRuns.cons crun' (PhaseRuns.single drun')))

end

open GraphPackingRegisters BinaryRegisterProgram FiniteTapeProgram PackingMachineBlocks
open GraphPackingProgram

variable (fixed : InventoryData) (K : Nat)

theorem item_register (v : PackingItemExpression.Variable) :
    item fixed K v = (Sum.inl (Sum.inl v) : Register fixed K) := rfl

theorem work_register (w : Work) :
    work fixed K w = (Sum.inl (Sum.inr (Sum.inr w)) : Register fixed K) := rfl

theorem finalValues_eq (x : GraphReductionInput) :
    finalValues fixed K x = PackingMachineLayout.values (Numerator fixed)
      PackingItemExpression.denominator (preparedInputs fixed K x) (preparedOther fixed K x) := by
  funext r
  rcases r with (a | (r | w)) | node
  · cases a <;> simp [finalValues, factorValues, secondPowerValues, firstPowerValues,
      setupValues, item_register, work_register,
      PackingMachineLayout.values, preparedInputs]
  · simp [finalValues, factorValues, secondPowerValues, firstPowerValues,
      setupValues, item_register, work_register,
      PackingMachineLayout.values, preparedOther, setupOther]
  · cases w <;> simp [finalValues, factorValues, secondPowerValues, firstPowerValues,
      setupValues, item_register, work_register,
      PackingMachineLayout.values, preparedOther, setupOther, preparedWork]
  · simp [finalValues, factorValues, secondPowerValues, firstPowerValues,
      setupValues, item_register, work_register,
      PackingMachineLayout.values]

theorem headerDifferent : work fixed K .header ≠ output fixed K .bins := by
  simp [work, output, setup, PackingMachineLayout.others, PackingSetupMachine.output]

end BinPackingGap.GraphPackingPreparation

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_GraphPackingJobCleanup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.GraphPackingJobs

open FiniteTapeProgram PackingMachineBlocks GraphPackingRegisters
open GraphPackingPreparation PackingItemExpression
open GraphPackingProgram (PhaseRuns)
open PackingMachineLayout (tapes)

variable (fixed : InventoryData) (K : Nat)

def cleanupPhases : List (GraphPackingProgram.Program fixed K) :=
  [GraphPackingProgram.incrementEdge fixed K,
    GraphPackingProgram.setWork fixed K .leftEndpoint 0,
    GraphPackingProgram.setWork fixed K .rightEndpoint 0,
    GraphPackingProgram.setWork fixed K .leftPower 0,
    GraphPackingProgram.setWork fixed K .rightPower 0,
    GraphPackingProgram.setItem fixed K .labelPower 0,
    GraphPackingProgram.setItem fixed K .repetitionOne 0]

def cleanupWidthTimePolynomial : Polynomial Nat :=
  64 * (2 * Polynomial.X + 1) ^ 2 +
    PackingLayoutCommands.setOtherTime (Numerator fixed) denominator
      (Other := Other fixed K) (.inr .leftEndpoint) 0 +
    PackingLayoutCommands.setOtherTime (Numerator fixed) denominator
      (Other := Other fixed K) (.inr .rightEndpoint) 0 +
    PackingLayoutCommands.setOtherTime (Numerator fixed) denominator
      (Other := Other fixed K) (.inr .leftPower) 0 +
    PackingLayoutCommands.setOtherTime (Numerator fixed) denominator
      (Other := Other fixed K) (.inr .rightPower) 0 +
    PackingLayoutCommands.setInputTime (Numerator fixed) denominator
      (Other := Other fixed K) .labelPower 0 +
    PackingLayoutCommands.setInputTime (Numerator fixed) denominator
      (Other := Other fixed K) .repetitionOne 0

end BinPackingGap.GraphPackingJobs

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_GraphPackingJobEdge
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.GraphPackingProgram

open BinPackingGames.Foundations.Complexity
open FiniteTapeProgram PackingMachineBlocks BinaryRegisterProgram
open GraphPackingRegisters PackingRegisterFrame

variable (fixed : InventoryData) (K : Nat)

def endpointResultValues (right : Bool) (vals : Register fixed K → Nat) (v : Nat) :
    Register fixed K → Nat := by
  classical
  exact Function.update
    (Function.update vals (endpointRegisters fixed K right 0) v)
    (endpointRegisters fixed K right 2) (3 ^ (v + 1))

def endpointResultTapes (right : Bool) (base : Tape fixed K → List Bool)
    (vals : Register fixed K → Nat) (v : Nat) (suffix : List Bool) :
    Tape fixed K → List Bool :=
  registerTapes (slots fixed K) (Function.update base (.inr .endpoints) suffix)
    (endpointResultValues fixed K right vals v)

theorem endpoint_frame_extra (base : Tape fixed K → List Bool)
    (vals : Register fixed K → Nat) (e : Extra) :
    registerTapes (slots fixed K) base vals (.inr e) = base (.inr e) := by
  apply registerTapes_other
  rintro ⟨i, hi⟩
  cases hi

theorem endpoint_extra_outside (e : Extra) (i : Register fixed K ⊕ Fin 6) :
    slots fixed K i ≠ Sum.inr e := by
  simp [slots, PackingMachineLayout.registers]

theorem endpoint_exec (right : Bool) (base : Tape fixed K → List Bool)
    (vals : Register fixed K → Nat) (v : Nat) (suffix : List Bool)
    (sourceWord : base (.inr .endpoints) = BinaryEncoding.natBits v ++ suffix)
    (decodeScratch : base (.inr .decodeScratch) = [])
    (powerCounter : base (.inr .powerCounter) = [])
    (initialRegisters : ∀ i : Fin 7,
      vals (endpointRegisters fixed K right i) = PackingEndpointPower.values 0 0 i)
    (state : State) :
    ∃ steps ≤ 2 * v.size + 4 + PackingEndpointPower.timePolynomial.eval v,
      Exec (endpoint fixed K right)
        ⟨state, registerTapes (slots fixed K) base vals⟩ steps
        ⟨.arithmetic (BinaryAddMachine.clean ()),
          endpointResultTapes fixed K right base vals v suffix⟩ := by
  classical
  let start := registerTapes (slots fixed K) base vals
  let afterBase := Function.update base (.inr .endpoints) suffix
  let afterVals := Function.update vals (endpointRegisters fixed K right 0) v
  let decoded := registerTapes (slots fixed K) afterBase afterVals
  have selectedZero : vals (endpointRegisters fixed K right 0) = 0 := by
    simpa [PackingEndpointPower.values] using initialRegisters 0
  have source : start (decoderSlots fixed K right 0) =
      BinaryEncoding.natBits v ++ suffix := by
    change registerTapes (slots fixed K) base vals (.inr .endpoints) = _
    rw [endpoint_frame_extra]
    exact sourceWord
  have scratch : start (decoderSlots fixed K right 1) = [] := by
    change registerTapes (slots fixed K) base vals (.inr .decodeScratch) = []
    rw [endpoint_frame_extra]
    exact decodeScratch
  have destination : start (slots fixed K (.inl (endpointRegisters fixed K right 0))) =
      [] := by
    simp only [start, registerTapes_reg, selectedZero, Nat.zero_bits]
  have decodedFrame :
      PackingFieldDecodeMachine.decodedTapes (decoderSlots fixed K right)
        start v.bits suffix = decoded := by
    change Function.update (Function.update start (.inr .endpoints) suffix)
      (slots fixed K (.inl (endpointRegisters fixed K right 0)))
      (v.bits ++ start (slots fixed K (.inl (endpointRegisters fixed K right 0)))) = _
    rw [destination, List.append_nil]
    change Function.update
      (Function.update (registerTapes (slots fixed K) base vals) (.inr .endpoints) suffix)
      (slots fixed K (.inl (endpointRegisters fixed K right 0))) v.bits = _
    rw [← external_update (slots fixed K) base vals (.inr .endpoints)
      (endpoint_extra_outside fixed K .endpoints) suffix]
    exact registerTapes_update (slots fixed K) afterBase vals
      (endpointRegisters fixed K right 0) v
  have decodedRun := PackingFieldDecodeMachine.decodeNat_exec
    (decoderSlots fixed K right) start () v suffix source scratch
  rw [decodedFrame] at decodedRun
  have first := PackingArithmeticProgram.exec
    (PackingFieldDecodeMachine.code (decoderSlots fixed K right)) start decoded
    (2 * v.size + 2) state decodedRun
  have afterRegisters : ∀ i : Fin 7,
      afterVals (endpointRegisters fixed K right i) = PackingEndpointPower.values v 0 i := by
    intro i
    have hi (a b : Fin 7) : endpointRegisters fixed K right a =
        endpointRegisters fixed K right b ↔ a = b :=
      (endpointRegisters fixed K right).injective.eq_iff
    fin_cases i <;>
      simp [afterVals, hi, initialRegisters, PackingEndpointPower.values]
  have ready : PackingEndpointPower.Ready (endpointSlots fixed K right)
      (.inr .powerCounter) decoded v := by
    constructor
    · intro i
      change registerTapes (slots fixed K) afterBase afterVals
        (slots fixed K (.inl (endpointRegisters fixed K right i))) = _
      rw [registerTapes_reg, afterRegisters]
    · intro j
      change registerTapes (slots fixed K) afterBase afterVals (slots fixed K (.inr j)) = []
      exact registerTapes_scratch (slots fixed K) afterBase afterVals j
    · change registerTapes (slots fixed K) afterBase afterVals (.inr .powerCounter) = []
      rw [endpoint_frame_extra]
      simpa [afterBase] using powerCounter
  obtain ⟨powerSteps, powerBound, second⟩ := PackingEndpointPower.exec
    (endpointSlots fixed K right) (.inr .powerCounter)
    (endpoint_outside fixed K right .powerCounter) decoded v ready
    (.arithmetic (BinaryAddMachine.clean ()))
  have finalFrame : PackingEndpointPower.resultTapes (endpointSlots fixed K right) decoded v =
      endpointResultTapes fixed K right base vals v suffix := by
    change Function.update (registerTapes (slots fixed K) afterBase afterVals)
      (slots fixed K (.inl (endpointRegisters fixed K right 2))) (3 ^ (v + 1)).bits = _
    exact registerTapes_update (slots fixed K) afterBase afterVals
      (endpointRegisters fixed K right 2) (3 ^ (v + 1))
  rw [finalFrame] at second
  have phases := PhaseRuns.cons first (PhaseRuns.single second)
  refine ⟨(1 + (2 * v.size + 2)) + powerSteps + 1, by omega, ?_⟩
  simpa only [endpoint] using phases.toExec

theorem endpoint_exec_polynomial (right : Bool) (base : Tape fixed K → List Bool)
    (vals : Register fixed K → Nat) (v : Nat) (suffix : List Bool)
    (sourceWord : base (.inr .endpoints) = BinaryEncoding.natBits v ++ suffix)
    (decodeScratch : base (.inr .decodeScratch) = [])
    (powerCounter : base (.inr .powerCounter) = [])
    (initialRegisters : ∀ i : Fin 7,
      vals (endpointRegisters fixed K right i) = PackingEndpointPower.values 0 0 i)
    (state : State) :
    ∃ steps ≤ endpointTimePolynomial.eval (v + (BinaryEncoding.natBits v).length),
      Exec (endpoint fixed K right)
        ⟨state, registerTapes (slots fixed K) base vals⟩ steps
        ⟨.arithmetic (BinaryAddMachine.clean ()),
          endpointResultTapes fixed K right base vals v suffix⟩ := by
  obtain ⟨steps, bound, run⟩ := endpoint_exec fixed K right base vals v suffix
    sourceWord decodeScratch powerCounter initialRegisters state
  refine ⟨steps, bound.trans ?_, run⟩
  have monotone := MachineComposition.natPolynomial_eval_mono
    PackingEndpointPower.timePolynomial
    (Nat.le_add_right v (BinaryEncoding.natBits v).length)
  have fieldLength := BinaryEncoding.natBits_length v
  simp only [endpointTimePolynomial, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_C]
  omega

theorem endpoint_layout_exec (right : Bool) (base : Tape fixed K → List Bool)
    (input : PackingItemExpression.Variable → Nat) (other : Other fixed K → Nat)
    (v : Nat) (suffix : List Bool)
    (sourceWord : base (.inr .endpoints) = BinaryEncoding.natBits v ++ suffix)
    (decodeScratch : base (.inr .decodeScratch) = [])
    (powerCounter : base (.inr .powerCounter) = [])
    (initialRegisters : ∀ i : Fin 7,
      PackingMachineLayout.values (Numerator fixed) PackingItemExpression.denominator input other
        (endpointRegisters fixed K right i) = PackingEndpointPower.values 0 0 i)
    (state : State) :
    ∃ steps ≤ endpointTimePolynomial.eval (v + (BinaryEncoding.natBits v).length),
      Exec (endpoint fixed K right)
        ⟨state, PackingMachineLayout.tapes (Numerator fixed)
          PackingItemExpression.denominator base input other⟩ steps
        ⟨.arithmetic (BinaryAddMachine.clean ()),
          PackingMachineLayout.tapes (Numerator fixed) PackingItemExpression.denominator
            (Function.update base (.inr .endpoints) suffix) input
            (Function.update (Function.update other
              (.inr (if right then Work.rightEndpoint else Work.leftEndpoint)) v)
              (.inr (if right then Work.rightPower else Work.leftPower)) (3 ^ (v + 1)))⟩ := by
  classical
  have updates : endpointResultValues fixed K right
      (PackingMachineLayout.values (Numerator fixed) PackingItemExpression.denominator input other) v =
      PackingMachineLayout.values (Numerator fixed) PackingItemExpression.denominator input
        (Function.update (Function.update other
          (.inr (if right then Work.rightEndpoint else Work.leftEndpoint)) v)
          (.inr (if right then Work.rightPower else Work.leftPower)) (3 ^ (v + 1))) := by
    simp only [endpointResultValues, PackingMachineLayout.values_update_other]
    rfl
  obtain ⟨steps, bound, run⟩ := endpoint_exec_polynomial fixed K right base
    (PackingMachineLayout.values (Numerator fixed) PackingItemExpression.denominator input other)
    v suffix sourceWord decodeScratch powerCounter initialRegisters state
  refine ⟨steps, bound, ?_⟩
  unfold endpointResultTapes at run
  rw [updates] at run
  exact run

end BinPackingGap.GraphPackingProgram

namespace BinPackingGap.GraphPackingJobs

section

open FiniteTapeProgram PackingMachineBlocks BinaryRegisterProgram
open GraphPackingRegisters GraphPackingPreparation PackingItemExpression
open GraphPackingProgram (PhaseRuns)
open PackingMachineLayout (tapes values)
open PackingItemBlockMachine (outputTapes)
open PackingCountedProgram (counterTapes guardState)
open BinPackingGames.Foundations.Complexity

variable (fixed : InventoryData) (K : Nat)

def repeatPhases : List (GraphPackingProgram.Program fixed K) :=
  [GraphPackingProgram.setItem fixed K .repetitionOne 1,
    GraphPackingProgram.tally fixed K (.output .repetitions) .repetitionCounter,
    PackingJobLoop.code (Numerator fixed) denominator
      (PackingInventoryDescriptors.jobDescriptors fixed)
      .labelPower .repetitionOne (by decide)
      (.inr Work.leftPower) (.inr Work.rightPower)
      (GraphPackingProgram.otherSetup fixed K .one) (.inr Work.temporary)
      (by simp [GraphPackingProgram.otherSetup]) .reverseOutput .repetitionCounter]

def repeatSetPolynomial : Polynomial Nat :=
  PackingLayoutCommands.setInputTime (Other := Other fixed K)
    (Numerator fixed) denominator .repetitionOne 1

def repeatLoopPolynomial : Polynomial Nat :=
  PackingJobLoop.timePolynomial (Numerator fixed) denominator
    (PackingInventoryDescriptors.jobDescriptors fixed) .labelPower
    (.inr Work.leftPower : Other fixed K) (.inr Work.rightPower)

def repeatWidthPolynomial : Polynomial Nat :=
  repeatSetPolynomial fixed K + 40 * (Polynomial.X + 1) ^ 3 + 1 +
    (repeatLoopPolynomial fixed K).comp (3 * Polynomial.X + 2)

end

section

open FiniteTapeProgram PackingMachineBlocks BinaryRegisterProgram
open GraphPackingRegisters GraphPackingPreparation PackingItemExpression
open GraphPackingProgram (PhaseRuns)
open PackingMachineLayout (tapes values)
open BinPackingGames.Foundations.Complexity

variable (fixed : InventoryData) (K : Nat)

def prefixPhases : List (GraphPackingProgram.Program fixed K) :=
  [.atom (.pop (.inr .endpoints) (fun state _ => state) .done),
    GraphPackingProgram.endpoint fixed K false,
    GraphPackingProgram.endpoint fixed K true]

theorem prepared_endpoint_registers (x : GraphReductionInput)
    (input : Variable → Nat) (right : Bool) :
    ∀ i : Fin 7, values (Numerator fixed) denominator input (preparedOther fixed K x)
      (endpointRegisters fixed K right i) = PackingEndpointPower.values 0 0 i := by
  intro i
  cases right <;> fin_cases i <;> rfl

theorem right_after_left_registers (x : GraphReductionInput)
    (input : Variable → Nat) (left : Nat) :
    ∀ i : Fin 7, values (Numerator fixed) denominator input
      (loadEndpoint fixed K (preparedOther fixed K x) false left)
      (endpointRegisters fixed K true i) = PackingEndpointPower.values 0 0 i := by
  intro i
  fin_cases i <;> rfl

theorem endpoint_measure_le (x : GraphReductionInput) (v : x.graph.Vertex) :
    v.val + (BinaryEncoding.natBits v.val).length ≤ 4 * ((graphBits x).length + 1) := by
  have hv : v.val ≤ (graphBits x).length :=
    (Nat.le_of_lt v.isLt).trans (graph_vertexCount_le_bits x)
  have hs : v.val.size ≤ v.val := nat_size_le_self v.val
  rw [BinaryEncoding.natBits_length]
  omega

theorem prefix_exec (x : GraphReductionInput) (edge : x.graph.Edge)
    (base : Tape fixed K → List Bool) (input : Variable → Nat)
    (suffix : List Bool) (state : State)
    (sourceWord : base (.inr .endpoints) = true ::
      (BinaryEncoding.natBits (x.graph.left edge).val ++
        (BinaryEncoding.natBits (x.graph.right edge).val ++ suffix)))
    (decodeScratch : base (.inr .decodeScratch) = [])
    (powerCounter : base (.inr .powerCounter) = []) :
    ∃ steps ≤ prefixTimePolynomial.eval (graphBits x).length,
      PhaseRuns (prefixPhases fixed K)
        ⟨state, tapes (Numerator fixed) denominator base input (preparedOther fixed K x)⟩ steps
        ⟨.arithmetic (BinaryAddMachine.clean ()),
          tapes (Numerator fixed) denominator (Function.update base (.inr .endpoints) suffix)
            input (loadedOther fixed K x (x.graph.left edge).val (x.graph.right edge).val)⟩ := by
  let remainder := BinaryEncoding.natBits (x.graph.left edge).val ++
    (BinaryEncoding.natBits (x.graph.right edge).val ++ suffix)
  let afterMarker := Function.update base (.inr Extra.endpoints) remainder
  let afterLeft := Function.update base (.inr Extra.endpoints)
    (BinaryEncoding.natBits (x.graph.right edge).val ++ suffix)
  let leftOther := loadEndpoint fixed K (preparedOther fixed K x) false (x.graph.left edge).val
  have markerFrame : Function.update
      (tapes (Numerator fixed) denominator base input (preparedOther fixed K x))
      (.inr Extra.endpoints) remainder =
      tapes (Numerator fixed) denominator afterMarker input (preparedOther fixed K x) := by
    exact (RegisterFrameEmission.external_update (slots fixed K) base
      (values (Numerator fixed) denominator input (preparedOther fixed K x))
      (.inr Extra.endpoints)
      (by intro q; simp [slots, PackingMachineLayout.registers]) remainder).symm
  have markerRun : Exec
      (.atom (.pop (.inr Extra.endpoints) (fun state _ => state) .done))
      ⟨state, tapes (Numerator fixed) denominator base input (preparedOther fixed K x)⟩ 1
      ⟨state, tapes (Numerator fixed) denominator afterMarker input (preparedOther fixed K x)⟩ := by
    have actual := Exec.atom
      (Action.pop (.inr Extra.endpoints) (fun state _ => state) .done)
      ⟨state, tapes (Numerator fixed) denominator base input (preparedOther fixed K x)⟩
    simp only [Action.eval, PackingMachineLayout.tapes_extra, sourceWord,
      List.tail_cons] at actual
    change Exec _ _ 1 ⟨state, Function.update
      (tapes (Numerator fixed) denominator base input (preparedOther fixed K x))
      (.inr Extra.endpoints) remainder⟩ at actual
    rw [markerFrame] at actual
    exact actual
  have leftSource : afterMarker (.inr .endpoints) =
      BinaryEncoding.natBits (x.graph.left edge).val ++
        (BinaryEncoding.natBits (x.graph.right edge).val ++ suffix) := by simp [afterMarker, remainder]
  have leftScratch : afterMarker (.inr .decodeScratch) = [] := by
    simpa [afterMarker] using decodeScratch
  have leftCounter : afterMarker (.inr .powerCounter) = [] := by
    simpa [afterMarker] using powerCounter
  obtain ⟨leftSteps, leftBound, leftRun⟩ := GraphPackingProgram.endpoint_layout_exec fixed K
    false afterMarker input (preparedOther fixed K x) (x.graph.left edge).val
    (BinaryEncoding.natBits (x.graph.right edge).val ++ suffix)
    leftSource leftScratch leftCounter (prepared_endpoint_registers fixed K x input false) state
  have leftRun' : Exec (GraphPackingProgram.endpoint fixed K false)
      ⟨state, tapes (Numerator fixed) denominator afterMarker input (preparedOther fixed K x)⟩
      leftSteps ⟨.arithmetic (BinaryAddMachine.clean ()),
        tapes (Numerator fixed) denominator afterLeft input leftOther⟩ := by
    simpa [afterMarker, afterLeft, leftOther, loadEndpoint, endpointWork, powerWork,
      Function.update_idem] using leftRun
  have rightSource : afterLeft (.inr .endpoints) =
      BinaryEncoding.natBits (x.graph.right edge).val ++ suffix := by simp [afterLeft]
  have rightScratch : afterLeft (.inr .decodeScratch) = [] := by
    simpa [afterLeft] using decodeScratch
  have rightCounter : afterLeft (.inr .powerCounter) = [] := by
    simpa [afterLeft] using powerCounter
  obtain ⟨rightSteps, rightBound, rightRun⟩ := GraphPackingProgram.endpoint_layout_exec fixed K
    true afterLeft input leftOther (x.graph.right edge).val suffix rightSource rightScratch
    rightCounter (right_after_left_registers fixed K x input (x.graph.left edge).val)
    (.arithmetic (BinaryAddMachine.clean ()))
  have rightRun' : Exec (GraphPackingProgram.endpoint fixed K true)
      ⟨.arithmetic (BinaryAddMachine.clean ()),
        tapes (Numerator fixed) denominator afterLeft input leftOther⟩ rightSteps
      ⟨.arithmetic (BinaryAddMachine.clean ()),
        tapes (Numerator fixed) denominator (Function.update base (.inr .endpoints) suffix)
          input (loadedOther fixed K x (x.graph.left edge).val (x.graph.right edge).val)⟩ := by
    simpa [afterLeft, loadedOther, leftOther, loadEndpoint, endpointWork, powerWork,
      Function.update_idem] using rightRun
  have phases : PhaseRuns (prefixPhases fixed K)
      ⟨state, tapes (Numerator fixed) denominator base input (preparedOther fixed K x)⟩
      (1 + (leftSteps + rightSteps))
      ⟨.arithmetic (BinaryAddMachine.clean ()),
        tapes (Numerator fixed) denominator (Function.update base (.inr .endpoints) suffix)
          input (loadedOther fixed K x (x.graph.left edge).val (x.graph.right edge).val)⟩ :=
    .cons markerRun (.cons leftRun' (PhaseRuns.single rightRun'))
  refine ⟨1 + (leftSteps + rightSteps), ?_, phases⟩
  have leftUpper := MachineComposition.natPolynomial_eval_mono
    GraphPackingProgram.endpointTimePolynomial (endpoint_measure_le x (x.graph.left edge))
  have rightUpper := MachineComposition.natPolynomial_eval_mono
    GraphPackingProgram.endpointTimePolynomial (endpoint_measure_le x (x.graph.right edge))
  rw [prefixTimePolynomial_eval]
  omega

end

open FiniteTapeProgram PackingMachineBlocks GraphPackingRegisters
open GraphPackingPreparation PackingItemExpression
open GraphPackingProgram (PhaseRuns)
open PackingMachineLayout (tapes)
open PackingItemBlockMachine (outputTapes)

variable (fixed : InventoryData) (K : Nat)

theorem resultBase_append (base : Tape fixed K → List Bool)
    (firstSuffix finalSuffix firstWord secondWord : List Bool) :
    resultBase fixed K (resultBase fixed K base firstSuffix firstWord) finalSuffix secondWord =
      resultBase fixed K base finalSuffix (firstWord ++ secondWord) := by
  funext tape
  by_cases ho : tape = .inr Extra.reverseOutput
  · subst tape
    simp [resultBase, outputTapes, List.reverse_append, List.append_assoc]
  · by_cases he : tape = .inr Extra.endpoints
    · subst tape
      simp [resultBase, outputTapes]
    · simp [resultBase, outputTapes, ho, he]

theorem resultBase_counter (base : Tape fixed K → List Bool)
    (suffix word : List Bool) (count : Nat) :
    resultBase fixed K (PackingCountedProgram.counterTapes (.inr .edgeCounter) base count)
        suffix word =
      PackingCountedProgram.counterTapes (.inr .edgeCounter)
        (resultBase fixed K base suffix word) count := by
  funext tape
  by_cases hc : tape = .inr Extra.edgeCounter
  · subst tape
    simp [resultBase, outputTapes, PackingCountedProgram.counterTapes]
  · by_cases ho : tape = .inr Extra.reverseOutput
    · subst tape
      simp [resultBase, outputTapes, PackingCountedProgram.counterTapes]
    · by_cases he : tape = .inr Extra.endpoints
      · subst tape
        simp [resultBase, outputTapes, PackingCountedProgram.counterTapes]
      · simp [resultBase, outputTapes, PackingCountedProgram.counterTapes, hc, ho, he]

theorem resultBase_nil (base : Tape fixed K → List Bool)
    (empty : base (.inr .endpoints) = [false]) :
    resultBase fixed K base [false] [] = base := by
  simp only [resultBase, PackingChunkMachine.outputTapes_nil]
  rw [← empty, Function.update_eq_self]

end BinPackingGap.GraphPackingJobs

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_GraphPackingStockStreams
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.GraphPackingStockStreams

open PackingConstantPool PackingInventoryDescriptors PackingDescriptorExpression

theorem repeatRecords_rawRecord (pair : Nat × Nat) (n : Nat) :
    repeatRecords (rawRecord pair) n = rawRecords (List.replicate n pair) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simpa only [repeatRecords, List.replicate_succ, rawRecords, List.flatMap_cons] using
        congrArg (fun word => rawRecord pair ++ word) ih

theorem globalPool_chunk_records (D : InventoryData) (species : GlobalSpecies D.graph) :
    repeatRecords
      (PackingChunkMachine.records (numerator D) PackingItemExpression.denominator
        (fun _ => values D none (globalEdgeIndex D species) 0) [globalDescriptor D species])
      (D.globalStock species) = rawRecords (globalPoolStream D species) := by
  rw [singleton_chunk_records, globalPoolStream_eq_replicate, repeatRecords_rawRecord]

theorem flagPool_chunk_records (D : InventoryData) (species : FlagSpecies) :
    repeatRecords
      (PackingChunkMachine.records (numerator D) PackingItemExpression.denominator
        (fun _ => values D none 0 0) [flagDescriptor D species])
      (D.flagStock species) = rawRecords (flagPoolStream D species) := by
  rw [singleton_chunk_records, flagPoolStream_eq_replicate, repeatRecords_rawRecord]

end BinPackingGap.GraphPackingStockStreams

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_GraphPackingGlobalExecution
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.GraphPackingGlobalLoop

open FiniteTapeProgram PackingMachineBlocks GraphPackingRegisters
open PackingMachineLayout GraphPackingProgram GraphPackingPoolExec
open PackingItemExpression (Variable denominator)
open PackingItemBlockMachine (outputTapes)
open PackingCountedProgram (counterTapes guardState)

variable (fixed : InventoryData) (K : Nat)

theorem edgeInput_update (input : Variable → Nat) (other : Other fixed K → Nat) (edge : Nat) :
    Function.update (edgeInput fixed K input other edge) .edgePower
      (radix fixed K other * edgeInput fixed K input other edge .edgePower) =
      edgeInput fixed K input other (edge + 1) := by
  rw [edgeInput_power]
  simp only [edgeInput, Function.update_idem, Nat.pow_succ, Nat.mul_comm]

def aggregateWidth (other : Other fixed K → Nat) (inputWidth start count : Nat) : Nat :=
  inputWidth + (start + count) * (radix fixed K other).size + 1

theorem edgeInput_size_le (input : Variable → Nat) (other : Other fixed K → Nat)
    (inputWidth start count edge : Nat) (initial : ∀ a, (input a).size ≤ inputWidth)
    (he : edge ≤ start + count) :
    ∀ a, (edgeInput fixed K input other edge a).size ≤
      aggregateWidth fixed K other inputWidth start count := by
  intro a
  by_cases h : a = .edgePower
  · subst a
    rw [edgeInput_power]
    have hp := nat_size_pow_le (radix fixed K other) edge
    have hm := Nat.mul_le_mul_right (radix fixed K other).size he
    unfold aggregateWidth
    omega
  · have hi := initial a
    simp only [edgeInput, Function.update_of_ne h]
    unfold aggregateWidth
    omega

def edgeWord (input : Variable → Nat) (other : Other fixed K → Nat) : List Bool :=
  poolWord fixed K .edgeStock (.w, .globalEdge true) input other ++
  poolWord fixed K .edgeStock (.w, .globalEdge false) input other

def bodyBudget (other : Other fixed K → Nat) (width : Nat) : Nat :=
  poolBudget fixed K .edgeStock (.w, .globalEdge true) other width +
  poolBudget fixed K .edgeStock (.w, .globalEdge false) other width +
  64 * ((radix fixed K other).size + width + 1) ^ 2 + 1

def stream (input : Variable → Nat) (other : Other fixed K → Nat) (start : Nat) :
    Nat → List Bool
  | 0 => []
  | count + 1 => edgeWord fixed K (edgeInput fixed K input other start) other ++
      stream input other (start + 1) count

theorem layout_counter (base : GraphPackingRegisters.Tape fixed K → List Bool) (input : Variable → Nat)
    (other : Other fixed K → Nat) (count : Nat) :
    tapes (Numerator fixed) denominator (counterTapes (.inr .edgeCounter) base count) input other =
      counterTapes (.inr .edgeCounter) (tapes (Numerator fixed) denominator base input other) count := by
  exact layout_external_update (Numerator fixed) denominator base input other .edgeCounter (List.replicate count true)

end BinPackingGap.GraphPackingGlobalLoop

namespace BinPackingGap.GraphPackingGlobalPhases

open FiniteTapeProgram PackingMachineBlocks GraphPackingRegisters
open PackingMachineLayout GraphPackingProgram GraphPackingPoolExec
open PackingItemExpression (Variable denominator)
open PackingItemBlockMachine (outputTapes)
open PackingCountedProgram (counterTapes guardState)

variable (fixed : InventoryData) (K : Nat)

def unitPools : List (Pool fixed) :=
  [(.upOne, (.up, .globalUnit true)), (.upZero, (.up, .globalUnit false)),
   (.umOne, (.um, .globalUnit true)), (.umZero, (.um, .globalUnit false))]

def unitInput (input : Variable → Nat) : Variable → Nat :=
  Function.update (Function.update (Function.update input .labelPower 0) .repetitionOne 0) .edgePower 1

def globalCount (other : Other fixed K → Nat) : Nat :=
  other (.inl (PackingSetupMachine.input (parameters fixed K) .m))

def globalsWord (input : Variable → Nat) (other : Other fixed K → Nat) : List Bool :=
  poolListWord fixed K (unitPools fixed) (unitInput input) other ++
  GraphPackingGlobalLoop.stream fixed K (unitInput input) other 0 (globalCount fixed K other)

def globalsInput (input : Variable → Nat) (other : Other fixed K → Nat) : Variable → Nat :=
  GraphPackingGlobalLoop.edgeInput fixed K (unitInput input) other (globalCount fixed K other)

def resetBudget (width : Nat) : Nat :=
  (PackingLayoutCommands.setInputTime (Other := Other fixed K)
    (Numerator fixed) denominator .labelPower 0).eval (width + 1) +
  (PackingLayoutCommands.setInputTime (Other := Other fixed K)
    (Numerator fixed) denominator .repetitionOne 0).eval (width + 1) +
  (PackingLayoutCommands.setInputTime (Other := Other fixed K)
    (Numerator fixed) denominator .edgePower 1).eval (width + 1)

def globalsBudget (other : Other fixed K → Nat) (width : Nat) : Nat :=
  resetBudget fixed K width + poolListBudget fixed K (unitPools fixed) other (width + 1) +
  BinaryToTallyMachine.runtimeBound (globalCount fixed K other) +
  globalCount fixed K other * (GraphPackingGlobalLoop.bodyBudget fixed K other
    (GraphPackingGlobalLoop.aggregateWidth fixed K other (width + 1) 0
      (globalCount fixed K other)) + 1) + 3

end BinPackingGap.GraphPackingGlobalPhases

namespace BinPackingGap.GraphPackingGlobalLoop

open GraphPackingRegisters
open PackingItemExpression (Variable)

theorem stream_eq_finRange (fixed : InventoryData) (K : Nat)
    (input : Variable → Nat) (other : Other fixed K → Nat) (start count : Nat) :
    stream fixed K input other start count =
      (List.finRange count).flatMap (fun j =>
        edgeWord fixed K (edgeInput fixed K input other (start + j.val)) other) := by
  induction count generalizing start with
  | zero => simp [stream]
  | succ count ih =>
      rw [stream, ih, List.finRange_succ, List.flatMap_cons, List.flatMap_map]
      simp only [Fin.val_zero, Fin.val_succ, Nat.add_zero]
      congr 1
      apply congrArg (fun f => (List.finRange count).flatMap f)
      funext j
      have index : start + 1 + j.val = start + (j.val + 1) := by omega
      rw [index]

end BinPackingGap.GraphPackingGlobalLoop

namespace BinPackingGap.GraphPackingPoolRuntime

open BinPackingGames.Foundations.Complexity
open GraphPackingRegisters GraphPackingGlobalPhases PackingInventoryDescriptors
open PackingItemExpression (denominator)

theorem poolBudget_le (fixed : InventoryData) (K : Nat)
    (stock : PackingSetupExpression.Output) (descriptor : ItemDescriptor fixed)
    (other : Other fixed K → Nat) (width : Nat) (N W : Polynomial Nat) (s : Nat)
    (hcount : other (GraphPackingProgram.otherSetup fixed K stock) ≤ N.eval s)
    (hwidth : width ≤ W.eval s) :
    GraphPackingPoolExec.poolBudget fixed K stock descriptor other width ≤
      (poolPolynomial fixed descriptor N W).eval s := by
  have ht := tally_le (other (GraphPackingProgram.otherSetup fixed K stock)) s N hcount
  have hb := MachineComposition.natPolynomial_eval_mono
    (PackingChunkMachine.timePolynomial (Numerator fixed) denominator [descriptor]) hwidth
  have hm := Nat.mul_le_mul hcount (Nat.add_le_add_right hb 2)
  rw [poolPolynomial_eval]
  dsimp only [GraphPackingPoolExec.poolBudget]
  exact Nat.add_le_add_right (Nat.add_le_add ht hm) 3

theorem poolListBudget_le (fixed : InventoryData) (K : Nat) (pools : List (Pool fixed))
    (other : Other fixed K → Nat) (width : Nat) (N W : Polynomial Nat) (s : Nat)
    (hcounts : ∀ pool ∈ pools,
      other (GraphPackingProgram.otherSetup fixed K pool.1) ≤ N.eval s)
    (hwidth : width ≤ W.eval s) :
    poolListBudget fixed K pools other width ≤
      (poolListPolynomial fixed pools N W).eval s := by
  revert hcounts
  induction pools with
  | nil =>
      intro _
      simp [poolListBudget, poolListPolynomial]
  | cons pool pools ih =>
      intro hcounts
      have headBound := poolBudget_le fixed K pool.1 pool.2 other width N W s
        (hcounts pool (by simp)) hwidth
      have tailBound := ih (fun p hp => hcounts p (by simp [hp]))
      simpa only [poolListBudget, poolListPolynomial, List.map_cons, List.sum_cons,
        Polynomial.eval_add] using Nat.add_le_add headBound tailBound

end BinPackingGap.GraphPackingPoolRuntime

namespace BinPackingGap.GraphPackingGlobalSemantics

open GraphPackingRegisters GraphPackingPreparation
open PackingDescriptorExpression PackingInventoryDescriptors GraphPackingStockStreams
open GraphPackingPoolExec GraphPackingGlobalPhases
open PackingItemExpression (Variable denominator)

variable (fixed : InventoryData) (K : Nat)

def globalOutput {G : GraphInput} : GlobalSpecies G → PackingSetupExpression.Output
  | .up true => .upOne
  | .up false => .upZero
  | .um true => .umOne
  | .um false => .umZero
  | .edge _ _ => .edgeStock

def flagOutput : FlagSpecies → PackingSetupExpression.Output
  | .tree => .treeFlags
  | .main | .edge => .jobFlags

theorem prepared_globalCount (x : GraphReductionInput) :
    globalCount fixed K (preparedOther fixed K x) = x.graph.edges.length := rfl

end BinPackingGap.GraphPackingGlobalSemantics

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_GraphPackingPreparation
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.GraphPackingPreparation

section

open Turing BinPackingGames.Foundations.Complexity
open GraphPackingRegisters GraphPackingProgram PackingMachineBlocks
open FiniteTapeProgram BinaryRegisterProgram

variable (fixed : InventoryData) (K : Nat)

def parsePhases : List (Program fixed K) :=
  [prepareGraph (graphSlots fixed K),
    tallyToBinary fixed K .vertices .n,
    tallyToBinary fixed K .edges .m,
    PackingArithmeticProgram.code (PackingFieldDecodeMachine.code (thresholdSlots fixed K))]

def parsePolynomial (_fixed : InventoryData) (_K : Nat) : Polynomial Nat :=
  Polynomial.C 6 * (Polynomial.X + 1) ^ 2 + Polynomial.C 15 * Polynomial.X + Polynomial.C 15

def fieldTapes (x : GraphReductionInput) : Tape fixed K → List Bool
  | .inr .input => graphBits x
  | .inr .threshold => BinaryEncoding.natBits x.k
  | .inr .endpoints => GraphFieldMachine.fieldBits .endpoints x
  | .inr .vertices => List.replicate x.graph.n true
  | .inr .edges => List.replicate x.graph.edges.length true
  | _ => []

theorem preparation_frame (x : GraphReductionInput) :
    GraphPreparationMachine.preparedTapes (graphSlots fixed K) (initialTapes fixed K x) x =
      fieldTapes fixed K x := by
  have atSlot (j : Fin 7) :
      GraphPreparationMachine.preparedTapes (graphSlots fixed K) (initialTapes fixed K x) x
        (graphSlots fixed K j) = fieldTapes fixed K x (graphSlots fixed K j) := by
    rw [GraphPreparationMachine.preparedTapes_register]
    fin_cases j <;> simp [initialTapes, fieldTapes]
  funext tape
  cases tape with
  | inl r =>
      simpa only [initialTapes, fieldTapes] using
        GraphPreparationMachine.preparedTapes_other (graphSlots fixed K)
          (initialTapes fixed K x) x (.inl r)
          (by simp) (by simp)
          (by simp) (by simp)
  | inr extra =>
      by_cases h₃ : extra = .threshold
      · subst extra; exact atSlot 3
      by_cases h₄ : extra = .endpoints
      · subst extra; exact atSlot 4
      by_cases h₅ : extra = .vertices
      · subst extra; exact atSlot 5
      by_cases h₆ : extra = .edges
      · subst extra; exact atSlot 6
      rw [GraphPreparationMachine.preparedTapes_other (graphSlots fixed K)
        (initialTapes fixed K x) x (.inr extra)
        (by simpa using h₃) (by simpa using h₄)
        (by simpa using h₅) (by simpa using h₆)]
      cases extra <;> simp_all [initialTapes, fieldTapes]

def vertexTapes (x : GraphReductionInput) : Tape fixed K → List Bool :=
  Function.update (Function.update (fieldTapes fixed K x) (.inr .vertices) [])
    (regTape fixed K (input fixed K .n)) x.graph.n.bits

def edgeTapes (x : GraphReductionInput) : Tape fixed K → List Bool :=
  Function.update (Function.update (vertexTapes fixed K x) (.inr .edges) [])
    (regTape fixed K (input fixed K .m)) x.graph.edges.length.bits

theorem decoded_frame (x : GraphReductionInput) :
    PackingFieldDecodeMachine.decodedTapes (thresholdSlots fixed K) (edgeTapes fixed K x)
      x.k.bits [] = parsedTapes fixed K x := by
  funext tape
  rcases tape with (r | scratch) | extra
  · change _ = registerTapes (slots fixed K) (baseTapes fixed K x)
      (PackingMachineLayout.values (Numerator fixed) PackingItemExpression.denominator
        (fun _ => 0) (parsedOther fixed K x)) (slots fixed K (.inl r))
    rw [registerTapes_reg]
    rcases r with (v | (setupReg | workReg)) | node
    · simp [PackingFieldDecodeMachine.decodedTapes, edgeTapes,
        vertexTapes, fieldTapes, regTape, slots, input,
        PackingMachineLayout.registers,
        PackingMachineLayout.values, PackingSetupMachine.input]
    · rcases setupReg with i | (o | node)
      · cases i <;> simp [PackingFieldDecodeMachine.decodedTapes,
          edgeTapes, vertexTapes, fieldTapes, regTape, slots, input,
          PackingMachineLayout.registers,
          PackingMachineLayout.values, parsedOther, PackingSetupMachine.frame,
          PackingSetupMachine.input, PackingSetupExpression.inputs]
        change Function.update (β := fun _ => List Bool) _ (thresholdSlots fixed K 2) x.k.bits
          (thresholdSlots fixed K 2) = x.k.bits
        exact Function.update_self _ _ _
      · simp [PackingFieldDecodeMachine.decodedTapes, edgeTapes,
          vertexTapes, fieldTapes, regTape, slots, input,
          PackingMachineLayout.registers,
          PackingMachineLayout.values, parsedOther, PackingSetupMachine.frame,
          PackingSetupMachine.input]
      · simp [PackingFieldDecodeMachine.decodedTapes, edgeTapes,
          vertexTapes, fieldTapes, regTape, slots, input,
          PackingMachineLayout.registers,
          PackingMachineLayout.values, parsedOther, PackingSetupMachine.frame,
          PackingSetupMachine.input]
    · simp [PackingFieldDecodeMachine.decodedTapes, edgeTapes,
        vertexTapes, fieldTapes, regTape, slots, input,
        PackingMachineLayout.registers,
        PackingMachineLayout.values, parsedOther, PackingSetupMachine.input]
    · simp [PackingFieldDecodeMachine.decodedTapes, edgeTapes,
        vertexTapes, fieldTapes, regTape, slots, input,
        PackingMachineLayout.registers,
        PackingMachineLayout.values, PackingSetupMachine.input]
  · change _ = registerTapes (slots fixed K) (baseTapes fixed K x)
      (PackingMachineLayout.values (Numerator fixed) PackingItemExpression.denominator
        (fun _ => 0) (parsedOther fixed K x)) (slots fixed K (.inr scratch))
    rw [registerTapes_scratch]
    simp [PackingFieldDecodeMachine.decodedTapes, edgeTapes,
      vertexTapes, fieldTapes, regTape, slots, PackingMachineLayout.registers]
  · change _ = PackingMachineLayout.tapes (Numerator fixed) PackingItemExpression.denominator
      (baseTapes fixed K x) (fun _ => 0) (parsedOther fixed K x) (.inr extra)
    rw [PackingMachineLayout.tapes_extra]
    cases extra <;> simp [PackingFieldDecodeMachine.decodedTapes,
      edgeTapes, vertexTapes, fieldTapes, regTape, slots, PackingMachineLayout.registers,
      baseTapes]

theorem tally_exec (source : Extra) (destination : PackingSetupExpression.Input)
    (different : source ≠ .scanScratch) (base : Tape fixed K → List Bool)
    (n : Nat) (state : State)
    (sourceWord : base (.inr source) = List.replicate n true)
    (outputEmpty : base (regTape fixed K (input fixed K destination)) = [])
    (scratchEmpty : base (.inr .scanScratch) = []) :
    ∃ steps ≤ 3 * (n + 1) ^ 2 + 1,
      Exec (tallyToBinary fixed K source destination) ⟨state, base⟩ steps
        ⟨.arithmetic (BinaryAddMachine.clean ()),
          Function.update (Function.update base (.inr source) [])
            (regTape fixed K (input fixed K destination)) n.bits⟩ := by
  have hSO : (Sum.inr source : Tape fixed K) ≠ regTape fixed K (input fixed K destination) := by
    simp [regTape, slots, PackingMachineLayout.registers]
  have hSC : (Sum.inr source : Tape fixed K) ≠ .inr .scanScratch := by simpa using different
  have hOC : regTape fixed K (input fixed K destination) ≠ Sum.inr Extra.scanScratch := by
    simp [regTape, slots, PackingMachineLayout.registers]
  have run := BinaryTallyMachine.plainTallyFromTapesInTime (.inr source)
    (regTape fixed K (input fixed K destination)) (.inr .scanScratch) hSO hSC hOC
    id none (BinaryTallyMachine.instruction (.inr source)
      (regTape fixed K (input fixed K destination)) (.inr .scanScratch) id none)
    (fun _ => rfl) base () n sourceWord outputEmpty scratchEmpty
  simpa only [tallyToBinary, arithmeticControl] using
    invokeExecInTime arithmeticControl (BinaryAddMachine.clean ()) .scan
      (BinaryTallyMachine.instruction (.inr source)
        (regTape fixed K (input fixed K destination)) (.inr .scanScratch) id none)
      ⟨state, base⟩ (BinaryAddMachine.clean ()) _ _ run

theorem parse_exec (x : GraphReductionInput) (state : State) :
    ∃ steps ≤ (parsePolynomial fixed K).eval (graphBits x).length,
      PhaseRuns (parsePhases fixed K) ⟨state, initialTapes fixed K x⟩ steps
        ⟨.arithmetic (BinaryAddMachine.clean ()), parsedTapes fixed K x⟩ := by
  have first := prepareGraph_exec (graphSlots fixed K) ⟨state, initialTapes fixed K x⟩ x
    (by rfl) (by rfl) (by rfl)
  rw [preparation_frame fixed K x] at first
  obtain ⟨a, ha, second⟩ := tally_exec fixed K .vertices .n (by decide)
    (fieldTapes fixed K x) x.graph.n (.graph (GraphFieldMachine.clean ()))
    rfl rfl rfl
  change Exec (tallyToBinary fixed K .vertices .n)
    ⟨.graph (GraphFieldMachine.clean ()), fieldTapes fixed K x⟩ a
    ⟨.arithmetic (BinaryAddMachine.clean ()), vertexTapes fixed K x⟩ at second
  obtain ⟨b, hb, third⟩ := tally_exec fixed K .edges .m (by decide)
    (vertexTapes fixed K x) x.graph.edges.length (.arithmetic (BinaryAddMachine.clean ()))
    (by simp [vertexTapes, fieldTapes, regTape, slots, PackingMachineLayout.registers])
    (by simp [vertexTapes, fieldTapes, regTape, slots, input,
      PackingMachineLayout.registers, PackingSetupMachine.input])
    (by simp [vertexTapes, fieldTapes, regTape, slots, PackingMachineLayout.registers])
  change Exec (tallyToBinary fixed K .edges .m)
    ⟨.arithmetic (BinaryAddMachine.clean ()), vertexTapes fixed K x⟩ b
    ⟨.arithmetic (BinaryAddMachine.clean ()), edgeTapes fixed K x⟩ at third
  have decoded := PackingFieldDecodeMachine.decodeNat_exec (thresholdSlots fixed K)
    (edgeTapes fixed K x) () x.k []
    (by simp [ edgeTapes, vertexTapes, fieldTapes, regTape, slots,
      PackingMachineLayout.registers])
    (by simp [ edgeTapes, vertexTapes, fieldTapes, regTape, slots,
      PackingMachineLayout.registers])
  rw [decoded_frame fixed K x] at decoded
  have fourth := PackingArithmeticProgram.exec _ _ _ _
    (.arithmetic (BinaryAddMachine.clean ())) decoded
  refine ⟨(1 + GraphPreparationMachine.steps x) + (a + (b + (1 + (2 * x.k.size + 2)))), ?_, ?_⟩
  · have hp := prepareGraph_cost x
    have hn := Nat.pow_le_pow_left (Nat.add_le_add_right (graph_vertexCount_le_bits x) 1) 2
    have hm := Nat.pow_le_pow_left (Nat.add_le_add_right (graph_edgeCount_le_bits x) 1) 2
    have hk : 2 * x.k.size + 2 ≤ (graphBits x).length + 1 := by
      rw [PackingFieldDecodeMachine.decodeNat_steps]
      simpa only [GraphFieldMachine.thresholdBits] using
        Nat.add_le_add_right (GraphFieldMachine.fieldBits_length_le .threshold x) 1
    simp only [parsePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one]
    omega
  · exact PhaseRuns.cons first (PhaseRuns.cons second
      (PhaseRuns.cons third (PhaseRuns.single fourth)))

end

open GraphPackingRegisters BinaryRegisterProgram FiniteTapeProgram PackingMachineBlocks
open GraphPackingProgram

end BinPackingGap.GraphPackingPreparation

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_GraphPackingVerticesBound
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.GraphPackingVertices

section

open FiniteTapeProgram PackingMachineBlocks BinaryRegisterProgram
open GraphPackingRegisters PackingItemExpression
open GraphPackingProgram (PhaseRuns)

variable (fixed : InventoryData) (K : Nat)

def startTapes (x : GraphReductionInput) : Tape fixed K → List Bool :=
  PackingCountedProgram.counterTapes (.inr .vertexCounter)
    (PackingMachineLayout.tapes (Numerator fixed) denominator (startBase fixed K x)
      (startInputs fixed K x) (GraphPackingPreparation.preparedOther fixed K x)) x.graph.n

theorem startInputs_width (x : GraphReductionInput) (width : Nat)
    (hi : ∀ a, (GraphPackingPreparation.preparedInputs fixed K x a).size ≤ width) :
    ∀ a, (startInputs fixed K x a).size ≤ width + 2 := by
  have initial : ∀ a,
      (GraphPackingPreparation.preparedInputs fixed K x a).size ≤ width + 2 := by
    intro a
    exact (hi a).trans (by omega)
  have threeSize : (3 : Nat).size = 2 := by decide
  have oneSize : (1 : Nat).size = 1 := by decide
  have zeroSize : (0 : Nat).size = 0 := by decide
  have first := update_width (GraphPackingPreparation.preparedInputs fixed K x)
    .labelPower 3 (width + 2) initial (by omega)
  have second := update_width (α := Variable) _ .edgePower 1 (width + 2) first (by omega)
  exact update_width (α := Variable) _ .repetitionOne 0 (width + 2) second (by omega)

def setupPhases : List (GraphPackingProgram.Program fixed K) :=
  [GraphPackingProgram.setItem fixed K .labelPower 3,
    GraphPackingProgram.setItem fixed K .edgePower 1,
    GraphPackingProgram.setItem fixed K .repetitionOne 0,
    GraphPackingProgram.tally fixed K (.input .n) .vertexCounter]

def setupBound (x : GraphReductionInput) (width : Nat) : Nat :=
  (PackingLayoutCommands.setInputTime (Other := Other fixed K)
      (Numerator fixed) denominator .labelPower 3).eval (width + 2) +
    (PackingLayoutCommands.setInputTime (Other := Other fixed K)
      (Numerator fixed) denominator .edgePower 1).eval (width + 2) +
    (PackingLayoutCommands.setInputTime (Other := Other fixed K)
      (Numerator fixed) denominator .repetitionOne 0).eval (width + 2) +
    BinaryToTallyMachine.runtimeBound x.graph.n + 1

theorem tally_frame (x : GraphReductionInput) :
    registerTapes (slots fixed K)
      (Function.update (startBase fixed K x) (.inr .vertexCounter)
        (List.replicate x.graph.n true ++ startBase fixed K x (.inr .vertexCounter)))
      (startValues fixed K x) = startTapes fixed K x := by
  rw [startBase_vertexCounter, List.append_nil]
  change registerTapes (slots fixed K)
      (Function.update (startBase fixed K x) (.inr .vertexCounter)
        (List.replicate x.graph.n true)) (startValues fixed K x) =
    Function.update (registerTapes (slots fixed K) (startBase fixed K x)
      (startValues fixed K x)) (.inr .vertexCounter) (List.replicate x.graph.n true)
  exact RegisterFrameEmission.external_update (slots fixed K) (startBase fixed K x)
    (startValues fixed K x) (.inr .vertexCounter)
    (GraphPackingTapeBlocks.slots_outside fixed K .vertexCounter)
    (List.replicate x.graph.n true)

end

open GraphPackingRegisters GraphPackingPreparation PackingItemExpression
open FiniteTapeProgram PackingMachineBlocks
open PackingItemBlockMachine (outputTapes)

variable (fixed : InventoryData) (K : Nat)

theorem startInputs_eq (x : GraphReductionInput) :
    startInputs fixed K x =
      PackingVertexLoop.vertexInput (inputValues fixed K x) .labelPower 0 := by
  funext a
  cases a <;>
    simp [startInputs, preparedInputs, inputValues, data,
      PackingDescriptorExpression.instantiate, PackingDescriptorExpression.values,
      PackingVertexLoop.vertexInput,
      InventoryData.coordinateDenominator, InventoryData.geometryBound,
      IntegerPackingArithmetic.geomDenominator,
      geometryFactor, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

theorem inputValues_width (x : GraphReductionInput) (width : Nat)
    (hi : ∀ a, (preparedInputs fixed K x a).size ≤ width) :
    ∀ a, (inputValues fixed K x a).size ≤ width + 2 := by
  intro a
  by_cases h : a = Variable.labelPower
  · subst a
    simp [inputValues, PackingDescriptorExpression.values, NaturalPackingNumerator.labelPower]
  · have bound := startInputs_width fixed K x width hi a
    rw [startInputs_eq, PackingVertexLoop.vertexInput_other _ _ _ _ h] at bound
    exact bound

theorem stream_eq_emitted (x : GraphReductionInput) :
    PackingVertexLoop.stream (Numerator fixed) denominator
      (PackingInventoryDescriptors.vertexDescriptors fixed)
      (inputValues fixed K x) .labelPower 0 x.graph.n = emitted fixed K x := by
  have numerator_eq : PackingDescriptorExpression.numerator (data fixed K x) = Numerator fixed := by
    funext descriptor
    exact PackingDescriptorExpression.numerator_instantiate fixed x.graph
      (GraphPackingPreparation.repetitions fixed K x) x.k descriptor
  have descriptors_eq : PackingInventoryDescriptors.vertexDescriptors (data fixed K x) =
      PackingInventoryDescriptors.vertexDescriptors fixed :=
    PackingDescriptorExpression.vertexDescriptors_instantiate fixed x.graph
      (GraphPackingPreparation.repetitions fixed K x) x.k
  have count_eq : (data fixed K x).graph.n = x.graph.n := rfl
  have stream := PackingVertexRecords.stream_eq_vertexStream (data fixed K x)
  rw [numerator_eq, descriptors_eq, count_eq] at stream
  simpa only [inputValues, emitted, data, PackingDescriptorExpression.instantiate] using stream

theorem finalTapes_eq_frame (x : GraphReductionInput) :
    finalTapes fixed K x =
      PackingMachineLayout.tapes (Numerator fixed) denominator (finalBase fixed K x)
        (finalInputs fixed K x) (preparedOther fixed K x) := by
  have empty : PackingMachineLayout.tapes (Numerator fixed) denominator (finalBase fixed K x)
      (finalInputs fixed K x) (preparedOther fixed K x) (.inr .vertexCounter) = [] := by
    simp [PackingMachineLayout.tapes_extra, finalBase, outputTapes, startBase, baseTapes]
  funext tape
  by_cases h : tape = .inr .vertexCounter
  · subst tape
    simp only [final_counter_empty, empty]
  · simp [finalTapes, PackingCountedProgram.counterTapes, h]

def loopBudget (_K : Nat) (x : GraphReductionInput) (width : Nat) : Nat :=
  x.graph.n * ((PackingVertexLoop.bodyTimePolynomial (Numerator fixed) denominator
    (PackingInventoryDescriptors.vertexDescriptors fixed)).eval
      (PackingVertexLoop.aggregateWidth (width + 2) 0 x.graph.n) + 1) + 1

def phaseBudget (x : GraphReductionInput) (width : Nat) : Nat :=
  setupBound fixed K x width + loopBudget fixed K x width + 1

end BinPackingGap.GraphPackingVertices

namespace BinPackingGap.GraphPackingVerticesBound

open FiniteTapeProgram PackingMachineBlocks
open GraphPackingRegisters PackingItemExpression
open BinPackingGames.Foundations.Complexity

variable (fixed : InventoryData) (K : Nat)

def setPolynomial : Polynomial Nat :=
  PackingLayoutCommands.setInputTime (Other := Other fixed K)
      (Numerator fixed) denominator .labelPower 3 +
    PackingLayoutCommands.setInputTime (Other := Other fixed K)
      (Numerator fixed) denominator .edgePower 1 +
    PackingLayoutCommands.setInputTime (Other := Other fixed K)
      (Numerator fixed) denominator .repetitionOne 0

def bodyPolynomial : Polynomial Nat :=
  PackingVertexLoop.bodyTimePolynomial (Numerator fixed) denominator
    (PackingInventoryDescriptors.vertexDescriptors fixed)

end BinPackingGap.GraphPackingVerticesBound

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_GraphPackingMachine
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.GraphPackingJobs

section

open FiniteTapeProgram PackingMachineBlocks BinaryRegisterProgram
open GraphPackingRegisters GraphPackingPreparation PackingItemExpression
open GraphPackingProgram (PhaseRuns)

variable (fixed : InventoryData) (K : Nat)

def setupPhases : List (GraphPackingProgram.Program fixed K) :=
  [GraphPackingProgram.setItem fixed K .edgePower 1,
    GraphPackingProgram.setItem fixed K .labelPower 0,
    GraphPackingProgram.setItem fixed K .repetitionOne 0,
    GraphPackingProgram.tally fixed K (.input .m) .edgeCounter]

def setupTapes (x : GraphReductionInput) : Tape fixed K → List Bool :=
  PackingCountedProgram.counterTapes (.inr .edgeCounter)
    (PackingMachineLayout.tapes (Numerator fixed) denominator
      (GraphPackingVertices.finalBase fixed K x) (inputs fixed K x 0)
      (preparedOther fixed K x)) x.graph.edges.length

def resetInputs (x : GraphReductionInput) : Variable → Nat :=
  Function.update (Function.update (Function.update
    (GraphPackingVertices.finalInputs fixed K x) .edgePower 1) .labelPower 0) .repetitionOne 0

theorem resetInputs_eq (x : GraphReductionInput) :
    resetInputs fixed K x = inputs fixed K x 0 := by
  have final_eq : GraphPackingVertices.finalInputs fixed K x =
      Function.update (GraphPackingVertices.startInputs fixed K x) .labelPower
        (3 ^ (x.graph.n + 1)) := by
    rw [GraphPackingVertices.startInputs_eq]
    simp only [GraphPackingVertices.finalInputs, PackingVertexLoop.vertexInput,
      Function.update_idem]
  unfold resetInputs
  rw [final_eq]
  funext a
  cases a <;> simp [GraphPackingVertices.startInputs, inputs, preparedInputs]

def setupValues (x : GraphReductionInput) : Register fixed K → Nat :=
  PackingMachineLayout.values (Numerator fixed) denominator (inputs fixed K x 0)
    (preparedOther fixed K x)

theorem finalBase_edgeCounter (x : GraphReductionInput) :
    GraphPackingVertices.finalBase fixed K x (.inr .edgeCounter) = [] := by
  simp [GraphPackingVertices.finalBase, PackingItemBlockMachine.outputTapes,
    GraphPackingVertices.startBase, baseTapes]

theorem tally_frame (x : GraphReductionInput) :
    registerTapes (slots fixed K)
      (Function.update (GraphPackingVertices.finalBase fixed K x) (.inr .edgeCounter)
        (List.replicate x.graph.edges.length true ++
          GraphPackingVertices.finalBase fixed K x (.inr .edgeCounter)))
      (setupValues fixed K x) = setupTapes fixed K x := by
  rw [finalBase_edgeCounter, List.append_nil]
  exact PackingRegisterFrame.external_update (slots fixed K)
    (GraphPackingVertices.finalBase fixed K x) (setupValues fixed K x) (.inr .edgeCounter)
    (GraphPackingTapeBlocks.slots_outside fixed K .edgeCounter)
    (List.replicate x.graph.edges.length true)

def setupSetPolynomial : Polynomial Nat :=
  PackingLayoutCommands.setInputTime (Other := Other fixed K)
      (Numerator fixed) denominator .edgePower 1 +
    PackingLayoutCommands.setInputTime (Other := Other fixed K)
      (Numerator fixed) denominator .labelPower 0 +
    PackingLayoutCommands.setInputTime (Other := Other fixed K)
      (Numerator fixed) denominator .repetitionOne 0

end

open FiniteTapeProgram PackingMachineBlocks GraphPackingRegisters
open GraphPackingPreparation PackingItemExpression
open GraphPackingProgram (PhaseRuns)
open PackingMachineLayout (tapes)
open PackingCountedProgram (counterTapes guardState)

variable (fixed : InventoryData) (K : Nat)

def emitted (x : GraphReductionInput) : List Bool :=
  PackingDescriptorExpression.rawRecords (PackingInventoryDescriptors.jobStream (inventory fixed K x))

def finalBase (x : GraphReductionInput) : Tape fixed K → List Bool :=
  resultBase fixed K (GraphPackingVertices.finalBase fixed K x) [false] (emitted fixed K x)

def finalTapes (x : GraphReductionInput) : Tape fixed K → List Bool :=
  tapes (Numerator fixed) denominator (finalBase fixed K x)
    (inputs fixed K x x.graph.edges.length) (preparedOther fixed K x)

@[simp] theorem finalBase_extra (x : GraphReductionInput) (e : Extra)
    (hne : e ≠ .endpoints) (hno : e ≠ .reverseOutput) (hni : e ≠ .input) :
    finalBase fixed K x (.inr e) = [] := by
  simp [finalBase, GraphPackingVertices.finalBase, GraphPackingVertices.startBase,
    PackingItemBlockMachine.outputTapes, baseTapes, hne, hno, hni]

end BinPackingGap.GraphPackingJobs

namespace BinPackingGap.GraphPackingRun

open Turing BinPackingGames.Foundations.Complexity
open FiniteTapeProgram PackingMachineBlocks GraphPackingRegisters
open GraphPackingPreparation PackingItemExpression
open GraphPackingProgram (PhaseRuns)
open PackingMachineLayout (tapes)
open PackingItemBlockMachine (outputTapes)
open PackingDescriptorExpression (rawRecords)
open PackingInventoryDescriptors

variable (fixed : InventoryData) (K : Nat)

def globalWord (x : GraphReductionInput) : List Bool :=
  rawRecords (globalStream (GraphPackingJobs.inventory fixed K x))

def flagWord (x : GraphReductionInput) : List Bool :=
  rawRecords (flagStream (GraphPackingJobs.inventory fixed K x))

def afterGlobalBase (x : GraphReductionInput) : Tape fixed K → List Bool :=
  outputTapes (.inr .reverseOutput) (GraphPackingJobs.finalBase fixed K x) (globalWord fixed K x)

def beforeFinishBase (x : GraphReductionInput) : Tape fixed K → List Bool :=
  outputTapes (.inr .reverseOutput) (afterGlobalBase fixed K x) (flagWord fixed K x)

def beforeFinishTapes (x : GraphReductionInput) : Tape fixed K → List Bool :=
  tapes (Numerator fixed) denominator (beforeFinishBase fixed K x)
    (GraphPackingJobs.inputs fixed K x 0) (preparedOther fixed K x)

def constructorWord (x : GraphReductionInput) : List Bool :=
  BinaryEncoding.natBits (binBound fixed K x) ++
    rawRecords (recipeStream (GraphPackingJobs.inventory fixed K x))

theorem beforeFinish_reverse (x : GraphReductionInput) :
    beforeFinishTapes fixed K x (.inr .reverseOutput) = (constructorWord fixed K x).reverse := by
  simp [beforeFinishTapes, beforeFinishBase, afterGlobalBase, GraphPackingJobs.finalBase,
    GraphPackingJobs.resultBase, GraphPackingVertices.finalBase,
    GraphPackingVertices.startBase, outputTapes, baseTapes, constructorWord,
    recipeStream, rawRecords, GraphPackingVertices.emitted, GraphPackingJobs.emitted,
    globalWord, flagWord, List.flatMap_append, List.reverse_append, List.append_assoc,
    GraphPackingVertices.data, GraphPackingJobs.inventory]

theorem beforeFinish_output_empty (x : GraphReductionInput) :
    beforeFinishTapes fixed K x (.inr .output) = [] := by
  simp [beforeFinishTapes, beforeFinishBase, afterGlobalBase, outputTapes]

theorem constructorWord_eq (x : GraphReductionInput) :
    constructorWord fixed K x ++ [false] =
      BinaryEncoding.rawReductionOutputBits (GraphPackingJobs.inventory fixed K x).rawOutput := by
  rw [PackingDescriptorExpression.reductionOutputBits_eq]
  simp only [constructorWord, recipeStream_eq_rawItemList, InventoryData.rawOutput,
    GraphPackingFixedParameters.binBound_eq_inventory]

def prefixPhases : List (GraphPackingProgram.Program fixed K) :=
  [GraphPackingProgram.prepare fixed K, GraphPackingProgram.vertices fixed K,
    GraphPackingProgram.jobs fixed K, GraphPackingProgram.globals fixed K,
    GraphPackingProgram.flags fixed K]

def prefixProgram : GraphPackingProgram.Program fixed K :=
  GraphPackingProgram.chain fixed K (prefixPhases fixed K)

def prefixPushBound : Nat := Runtime.programPushBound
  ((prefixProgram fixed K).machine (.inr .input) (.inr .output)
    (.arithmetic (BinaryAddMachine.clean ())))

def finalTapes (x : GraphReductionInput) : Tape fixed K → List Bool :=
  GraphPackingFinish.resultTapes fixed K (beforeFinishTapes fixed K x) (constructorWord fixed K x)

end BinPackingGap.GraphPackingRun

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_ExtensionVerifier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap

open BinPackingGames.Foundations.Complexity

noncomputable def packingExtensionVerifier : CookLevin.NPVerifier where
  witnessBound := ExtensionWitness.witnessPolynomial
  verify := ExtensionCertificate.verify
  computation := ExtensionVerifierMachine.computableInPolyTime
  finiteAlphabet _ := inferInstanceAs (Fintype Bool)

theorem packingExtensionVerifier_accepts (input : List Bool) :
    packingExtensionVerifier.Accepts input ↔ ExtensionCertificate.language input := by
  simpa only [CookLevin.NPVerifier.Accepts, packingExtensionVerifier,
    ExtensionWitness.witnessPolynomial_eval] using
      (ExtensionWitness.language_iff_bounded_witness input).symm

theorem packingExtension_inNP : CookLevin.InNP ExtensionCertificate.language := by
  refine ⟨packingExtensionVerifier, ?_⟩
  intro input
  exact (packingExtensionVerifier_accepts input).symm

end BinPackingGap

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_SearchFinalizeMachine
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.Packing.instDecidableEqTableBin _root_.OAI.BinPackingGap.Packing.instFintypeTableBin _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.SearchFinalizeMachine

open Turing BinPackingGames.Foundations.Complexity MachineComposition
open SearchSemantics SearchEncoding BinaryEncoding
open BinPackingGames.Reduction.MachineTransfer

def rawRun (s : State) :
    MachineCanonicalOutput.TerminalRun program (stateBits s)
      (packingResultBits (SearchSemantics.output s)) (rawTime.eval (stateBits s).length) := by
  cases hp : s.phase with
  | find =>
      apply rejectedRun s (false :: bodyBits s)
      · simpa only [stateBits, hp, phaseBits, bodyBits, List.cons_append,
          List.nil_append, List.append_assoc] using startFalse (false :: bodyBits s)
      · simp [SearchSemantics.output, hp, packingResultBits, optionBits]
  | fill =>
      apply rejectedRun s (true :: bodyBits s)
      · simpa only [stateBits, hp, phaseBits, bodyBits, List.cons_append,
          List.nil_append, List.append_assoc] using startFalse (true :: bodyBits s)
      · simp [SearchSemantics.output, hp, packingResultBits, optionBits]
  | invalid =>
      apply rejectedRun s (bodyBits s)
      · simpa only [stateBits, hp, phaseBits, bodyBits, List.cons_append,
          List.nil_append, List.append_assoc] using startInvalid (bodyBits s)
      · simp [SearchSemantics.output, hp, packingResultBits, optionBits]
  | done =>
      refine {
        state := ((), none)
        tapes := tapes [] [] [] [] (resultBits s.bins s.fixed)
        execution := {
          steps := doneSteps s
          evals_in_steps := ?_
          steps_le_m := doneSteps_le s }
        output_eq := ?_ }
      · change (advance machine.step)^[doneSteps s]
          (some (initList machine (stateBits s))) =
            some (cfg none [] [] [] [] (resultBits s.bins s.fixed))
        rw [init_eq]
        simpa only [stateBits, hp, phaseBits, bodyBits,
          List.cons_append, List.nil_append, List.append_assoc] using doneTrace s
      · change resultBits s.bins s.fixed = packingResultBits (SearchSemantics.output s)
        simp only [resultBits, SearchSemantics.output, hp]

noncomputable def computation :
    TM2ComputableInPolyTime stateBits packingResultBits SearchSemantics.output :=
  MachineCanonicalOutput.computableInPolyTime program cleanupTapes cleanup_complete
    stateBits packingResultBits SearchSemantics.output rawTime rawRun

theorem finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet computation.tm :=
  MachineCanonicalOutput.computableInPolyTime_finite_alphabet program cleanupTapes
    cleanup_complete stateBits packingResultBits SearchSemantics.output rawTime rawRun

end BinPackingGap.SearchFinalizeMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_SearchPrepareMachine
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.Packing.instDecidableEqTableBin _root_.OAI.BinPackingGap.Packing.instFintypeTableBin _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.SearchPrepareMachine

open Turing BinPackingGames.Foundations.Complexity MachineComposition
open SearchSemantics SearchEncoding BinaryEncoding SearchMachineComposition
open BinPackingGames.Reduction.MachineTransfer

theorem activeSteps_le (fill : Bool) (s : State) :
    initialSteps s + 1 + activeSteps fill s ≤ rawTime.eval (stateBits s).length := by
  have hb := UnaryToBinaryMachine.steps_le s.bins 0
  have hl := UnaryToBinaryMachine.steps_le s.label 0
  have hbs : s.bins.size ≤ s.bins := Nat.size_le.mpr s.bins.lt_two_pow_self
  have hls : s.label.size ≤ s.label := Nat.size_le.mpr s.label.lt_two_pow_self
  have hfixed := fixedBits_set_length_le s.fixed s.item s.label
  have hselected : (fixedBits (selectedFixed fill s)).length ≤
      (fixedBits s.fixed).length + 2 * s.label + 2 := by
    cases fill <;> simp only [selectedFixed, Bool.false_eq_true, ↓reduceIte]
    · omega
    · exact hfixed
  have hlen := stateBits_length s
  have hbN : s.bins ≤ (stateBits s).length := by omega
  have hlN : s.label ≤ (stateBits s).length := by omega
  have hbSq := Nat.mul_le_mul hbN hbN
  have hlSq := Nat.mul_le_mul hlN hlN
  simp only [Nat.zero_add] at hb hl
  simp only [fixedBits] at hselected hfixed hlen
  simp only [initialSteps, activeSteps, prefixSteps, suffixSteps, activeBits, queryBits,
    extensionBits, fixedBits, List.length_append, BinPackingCompleteness.BinaryEncoding.frame_length,
    natBits_length, Nat.size_eq_bits_len, rawTime, Polynomial.eval_mul,
    Polynomial.eval_ofNat, Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_one]
  cases fill <;> simp only [Bool.false_eq_true, ↓reduceIte] at * <;> nlinarith

def activeRun (fill : Bool) (s : State)
    (hphase : phaseBits s.phase = [false, fill]) (hquery : query s = queryBits fill s) :
    MachineCanonicalOutput.TerminalRun program (stateBits s)
      (MachineKeepDecision.typedInputBits stateBits (prepare s))
      (rawTime.eval (stateBits s).length) := by
  let saved := (BinPackingCompleteness.BinaryEncoding.frame (stateBits s)).reverse
  have middle : (advance machine.step)^[1]
      (some (cfg (some .phase) false (stateBits s) [] [] [] [] saved [])) =
      some (cfg (some (.convertBins .scan)) fill (bodyBits s) [] [] [] [] saved []) := by
    simpa only [stateBits, hphase, bodyBits, List.cons_append, List.nil_append,
      List.append_assoc, Function.iterate_one, advance_some] using
      phaseActive fill (bodyBits s) saved
  have full := joinTrace (joinTrace (initialTrace s) middle) (activeTrace fill s)
  refine {
    state := (fill, none)
    tapes := tapes [] [] []
      (if fill then [] else encodeWord s.item) (if fill then [] else natBits s.label)
      [] (activeBits fill s)
    execution := {
      steps := initialSteps s + 1 + activeSteps fill s
      evals_in_steps := ?_
      steps_le_m := activeSteps_le fill s }
    output_eq := ?_ }
  · change (advance machine.step)^[initialSteps s + 1 + activeSteps fill s]
      (some (initList machine (stateBits s))) =
        some (cfg none fill [] [] []
          (if fill then [] else encodeWord s.item) (if fill then [] else natBits s.label)
          [] (activeBits fill s))
    simpa only [init_eq] using full
  · change activeBits fill s = MachineKeepDecision.typedInputBits stateBits (prepare s)
    simp only [activeBits, MachineKeepDecision.typedInputBits,
      MachineKeepDecision.inputBits, prepare, hquery, savedFrame_eq]

def rawRun (s : State) :
    MachineCanonicalOutput.TerminalRun program (stateBits s)
      (MachineKeepDecision.typedInputBits stateBits (prepare s))
      (rawTime.eval (stateBits s).length) := by
  cases hp : s.phase with
  | find =>
      exact activeRun false s (by simp [hp, phaseBits])
        (by simp [query, hp, queryBits, selectedFixed])
  | fill =>
      exact activeRun true s (by simp [hp, phaseBits])
        (by simp [query, hp, queryBits, selectedFixed])
  | done => exact inactiveRun false s (by simp [hp, phaseBits]) (by simp [query, hp])
  | invalid => exact inactiveRun true s (by simp [hp, phaseBits]) (by simp [query, hp])

noncomputable def computation :
    TM2ComputableInPolyTime stateBits (MachineKeepDecision.typedInputBits stateBits) prepare :=
  MachineCanonicalOutput.computableInPolyTime program cleanupTapes cleanup_complete
    stateBits (MachineKeepDecision.typedInputBits stateBits) prepare rawTime rawRun

theorem finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet computation.tm :=
  MachineCanonicalOutput.computableInPolyTime_finite_alphabet program cleanupTapes
    cleanup_complete stateBits (MachineKeepDecision.typedInputBits stateBits) prepare rawTime rawRun

end BinPackingGap.SearchPrepareMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_SearchUpdateMachine
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.Packing.instDecidableEqTableBin _root_.OAI.BinPackingGap.Packing.instFintypeTableBin _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.SearchUpdateMachine

open Turing BinPackingGames.Foundations.Complexity MachineComposition
open BinPackingGames.Reduction.MachineTransfer
open SearchSemantics SearchEncoding BinaryEncoding

def choose (phase : Phase) (next : Label) : TM2.Stmt (fun _ : Tape => Bool) Label Register :=
  .load (fun _ => (ambient phase, none)) (.goto (fun _ => next))

def code : Label → TM2.Stmt (fun _ : Tape => Bool) Label Register
  | .start =>
      .pop .input (fun state head => ({state.1 with flag := head.getD false}, none))
        (.pop .input (fun state head => ({state.1 with phaseHigh := head.getD false}, none))
          (.pop .input (fun state head => ({state.1 with phaseLow := head.getD false}, none))
            (.branch (fun state => state.1.phaseHigh)
              (go .copyRest)
              (.branch (fun state => state.1.phaseLow)
                (.branch (fun state => state.1.flag)
                  (choose .fill .fillYesBins) (choose .fill .fillNoBins))
                (.branch (fun state => state.1.flag)
                  (choose .fill .findBins)
                  (.push .reversed (fun _ => true) (choose .find .copyRest)))))))
  | .copyRest => loopAt .input .reversed id false .copyRest (some .reverse)
  | .reverse => loopAt .reversed .output id false .reverse (some .finish)
  | .finish => .push .output (fun state => state.1.phaseLow)
      (.push .output (fun state => state.1.phaseHigh)
        (.load (fun state => (state.1, none)) .halt))
  | .findBins => copyBit .skipItem .findBins
  | .skipItem => skipUnary .skipItem .skipLabel
  | .skipLabel => skipUnary .skipLabel .zeroControls
  | .zeroControls => .push .reversed (fun _ => false)
      (.push .reversed (fun _ => false) (go .copyRest))
  | .fillNoBins => copyBit .fillNoItem .fillNoBins
  | .fillNoItem => copyBit .incrementLabel .fillNoItem
  | .incrementLabel => .push .reversed (fun _ => true) (go .copyRest)
  | .fillYesBins => copyBit .startItem .fillYesBins
  | .startItem => .push .reversed (fun _ => true)
      (.push .index (fun _ => false) (.push .compare (fun _ => false) (go .fillYesItem)))
  | .fillYesItem => .pop .input (fun state head => (state.1, head))
      (.push .reversed (fun state => state.2.getD false)
        (.branch (fun state => state.2.getD false)
          (.push .index (fun _ => true) (.push .compare (fun _ => true) (go .fillYesItem)))
          (.push .compare (fun _ => true) (go (.convert .scan)))))
  | .convert label => UnaryToBinaryMachine.instruction .input .binary .scratch
      Label.convert (some .frame) label
  | .frame => FrameEmitMachine.instruction .binary .scratch .frame (some .restorePayload)
  | .restorePayload => loopAt .scratch .payload id false .restorePayload (some .zeroLabel)
  | .zeroLabel => .push .reversed (fun _ => false) (go .items)
  | .items => .pop .input (fun state head => (state.1, head))
      (.push .reversed (fun state => state.2.getD false)
        (.branch (fun state => state.2.getD false)
          (.pop .compare (fun state head =>
            ({state.1 with flag := state.1.flag || !(head.getD false)}, none))
            (go .numerator))
          (.peek .compare (fun state head =>
            (ambient (if !state.1.flag && !(head.getD false) then .done else .fill), none))
            (go (.replace (.entry true))))))
  | .numerator => copyBit .denominator .numeratorDigit
  | .numeratorDigit => copyDigit .numerator
  | .denominator => copyBit .items .denominatorDigit
  | .denominatorDigit => copyDigit .denominator
  | .replace label => SearchFixedReplaceMachine.instruction replacePlace
      Label.replace (some .reverse) label

def program : MachineCanonicalOutput.Program Tape Label Register where
  input := .input
  output := .output
  main := .start
  initial := (ambient .find, none)
  code := code

abbrev machine := MachineCanonicalOutput.sourceMachine program

theorem machine_step : machine.step = TM2.step code := rfl

def cfg (label : Option Label) (phase : Ambient) (tapes : Tapes)
    (register : Option Bool := none) : machine.Cfg :=
  ⟨label, (phase, register), tapes⟩

theorem oneStepTrace {a b : machine.Cfg} (h : machine.step a = some b) :
    (advance machine.step)^[1] (some a) = some b := by
  simpa only [Function.iterate_one, advance_some] using h

theorem copyBitStep (current zero one : Label) (atLabel : code current = copyBit zero one)
    (bit : Bool) (phase : Ambient) (base : Tapes) (input reversed : List Bool) :
    machine.step (cfg (some current) phase (io base (bit :: input) reversed)) =
      some (cfg (some (if bit then one else zero)) phase
        (io base input (bit :: reversed))) := by
  change some (TM2.stepAux (code current) _ _) = _
  rw [atLabel]
  cases bit <;> simp [copyBit, go, TM2.stepAux, cfg,
    update_io_input, update_io_reversed]
  all_goals rfl

theorem copyDigitStep (current next : Label) (atLabel : code current = copyDigit next)
    (bit : Bool) (phase : Ambient) (base : Tapes) (input reversed : List Bool) :
    machine.step (cfg (some current) phase (io base (bit :: input) reversed)) =
      some (cfg (some next) phase (io base input (bit :: reversed))) := by
  change some (TM2.stepAux (code current) _ _) = _
  rw [atLabel]
  simp [copyDigit, go, TM2.stepAux, cfg, update_io_input, update_io_reversed]
  all_goals rfl

theorem unaryCopyTrace (current next : Label) (atLabel : code current = copyBit next current)
    (n : Nat) (phase : Ambient) (base : Tapes) (input reversed : List Bool) :
    (advance machine.step)^[n + 1]
      (some (cfg (some current) phase (io base (encodeWord n ++ input) reversed))) =
      some (cfg (some next) phase (io base input ((encodeWord n).reverse ++ reversed))) := by
  induction n generalizing reversed with
  | zero =>
      simpa [encodeWord, advance] using! copyBitStep current next current atLabel
        false phase base input reversed
  | succ n ih =>
      have first := copyBitStep current next current atLabel true phase base
        (encodeWord n ++ input) reversed
      have second := ih (true :: reversed)
      have full := joinTrace (oneStepTrace first) second
      simpa [encodeWord, List.replicate_succ, List.reverse_cons, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

theorem nameCopyTrace (flag digit next : Label)
    (flagCode : code flag = copyBit next digit) (digitCode : code digit = copyDigit flag)
    (bits : List Bool) (phase : Ambient) (base : Tapes) (input reversed : List Bool) :
    (advance machine.step)^[(BinPackingCompleteness.BinaryEncoding.frame bits).length]
      (some (cfg (some flag) phase
        (io base (BinPackingCompleteness.BinaryEncoding.frame bits ++ input) reversed))) =
      some (cfg (some next) phase
        (io base input ((BinPackingCompleteness.BinaryEncoding.frame bits).reverse ++ reversed))) := by
  induction bits generalizing reversed with
  | nil =>
      simpa [BinPackingCompleteness.BinaryEncoding.frame, advance] using!
        copyBitStep flag next digit flagCode false phase base input reversed
  | cons bit bits ih =>
      have first := copyBitStep flag next digit flagCode true phase base
        (bit :: (BinPackingCompleteness.BinaryEncoding.frame bits ++ input)) reversed
      have second := copyDigitStep digit flag digitCode bit phase base
        (BinPackingCompleteness.BinaryEncoding.frame bits ++ input) (true :: reversed)
      have third := ih (bit :: true :: reversed)
      have full := joinTrace (joinTrace
        (oneStepTrace first) (oneStepTrace second)) third
      have clock : 1 + 1 + (BinPackingCompleteness.BinaryEncoding.frame bits).length =
          (BinPackingCompleteness.BinaryEncoding.frame (bit :: bits)).length := by
        simp only [BinPackingCompleteness.BinaryEncoding.frame, List.length_cons]
        omega
      rw [clock] at full
      simpa only [BinPackingCompleteness.BinaryEncoding.frame, List.cons_append,
        List.reverse_cons, List.append_assoc, List.singleton_append, List.nil_append] using full

theorem itemsStep_nil (base : Tapes) (counter : List Bool × Bool)
    (input reversed : List Bool) :
    machine.step (cfg (some .items) (ambient .fill counter.2)
      (countIO base counter (false :: input) reversed)) =
      some (cfg (some (.replace (.entry true))) (ambient (countedPhase counter))
        (countIO base counter input (false :: reversed))) := by
  change some (TM2.stepAux (code .items) _ _) = _
  simp [code, go, TM2.stepAux, cfg, countIO, countedPhase, ambient, io, put]
  congr 1
  congr 1
  funext tape; cases tape <;> simp

theorem itemsStep_cons (base : Tapes) (counter : List Bool × Bool)
    (input reversed : List Bool) :
    machine.step (cfg (some .items) (ambient .fill counter.2)
      (countIO base counter (true :: input) reversed)) =
      some (cfg (some .numerator) (ambient .fill (decrement counter).2)
        (countIO base (decrement counter) input (true :: reversed))) := by
  change some (TM2.stepAux (code .items) _ _) = _
  simp [code, go, TM2.stepAux, cfg, countIO, decrement, ambient, io, put]
  congr 1
  congr 1
  funext tape; cases tape <;> simp

theorem itemsTrace (items : RawInstance) (base : Tapes) (counter : List Bool × Bool)
    (input reversed : List Bool) :
    (advance machine.step)^[(rawInstanceBits items).length]
      (some (cfg (some .items) (ambient .fill counter.2)
        (countIO base counter (rawInstanceBits items ++ input) reversed))) =
      some (cfg (some (.replace (.entry true)))
        (ambient (countedPhase (counterAfter items.length counter)))
        (countIO base (counterAfter items.length counter) input
          ((rawInstanceBits items).reverse ++ reversed))) := by
  induction items generalizing counter reversed with
  | nil =>
      simpa [rawInstanceBits, listBits, counterAfter, advance] using!
        itemsStep_nil base counter input reversed
  | cons item items ih =>
      let rest := rawInstanceBits items ++ input
      let nextCounter := decrement counter
      have first := itemsStep_cons base counter
        (natBits item.1 ++ natBits item.2 ++ rest) reversed
      have second := nameCopyTrace .numerator .numeratorDigit .denominator rfl rfl
        item.1.bits (ambient .fill nextCounter.2) (put base .compare nextCounter.1)
        (natBits item.2 ++ rest) (true :: reversed)
      have third := nameCopyTrace .denominator .denominatorDigit .items rfl rfl
        item.2.bits (ambient .fill nextCounter.2) (put base .compare nextCounter.1)
        rest ((natBits item.1).reverse ++ true :: reversed)
      have fourth := ih nextCounter
        ((natBits item.2).reverse ++ (natBits item.1).reverse ++ true :: reversed)
      simp only [rest, countIO, natBits, BinPackingCompleteness.BinaryEncoding.nameBits,
        List.append_assoc] at first second third fourth
      have full := joinTrace (joinTrace (joinTrace
        (oneStepTrace first) second) third) fourth
      have clock : 1 + (BinPackingCompleteness.BinaryEncoding.frame item.1.bits).length +
          (BinPackingCompleteness.BinaryEncoding.frame item.2.bits).length +
          (rawInstanceBits items).length = (rawInstanceBits (item :: items)).length := by
        simp only [rawInstanceBits, listBits, pairBits, natBits,
          BinPackingCompleteness.BinaryEncoding.nameBits, List.length_cons, List.length_append]
        omega
      rw [clock] at full
      simpa [rest, nextCounter, countIO, rawInstanceBits, listBits, pairBits,
        natBits, BinPackingCompleteness.BinaryEncoding.nameBits, counterAfter,
        List.reverse_cons, List.reverse_append, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

theorem transferTrace (source target : Tape) (distinct : source ≠ target)
    (current : Label) (next : Option Label)
    (atLabel : code current = loopAt source target id false current next)
    (phase : Ambient) (tapes : Tapes) :
    (advance machine.step)^[(tapes source).length + 1]
      (some (cfg (some current) phase tapes)) =
      some (cfg next phase
        (put (put tapes source []) target ((tapes source).reverse ++ tapes target))) := by
  have trace := transferAt_fromTapes source target distinct id false current next
    code atLabel tapes phase none
  have next_eq : nextAt target code = advance (TM2.step code) := by funext s; rfl
  rw [next_eq] at trace
  simpa only [machine_step, cfg, put, List.map_id_fun, id_eq, tapesAt] using! trace

theorem finishStep (phase : Ambient) (tapes : Tapes) :
    machine.step (cfg (some .finish) phase tapes) =
      some (cfg none phase
        (put tapes .output (phase.phaseHigh :: phase.phaseLow :: tapes .output))) := by
  change some (TM2.stepAux (code .finish) _ _) = _
  simp [code, TM2.stepAux, cfg, put]
  all_goals rfl

theorem reverseFinishTrace (phase : Ambient) (a b c d e f reversed : List Bool) :
    (advance machine.step)^[reversed.length + 2]
      (some (cfg (some .reverse) phase (work a b c d e f reversed []))) =
      some (cfg none phase (work a b c d e f [] (phaseWord phase ++ reversed.reverse))) := by
  have first := transferTrace .reversed .output (by decide) .reverse (some .finish)
    rfl phase (work a b c d e f reversed [])
  simp only [work, put, put_work, List.append_nil] at first
  have second := finishStep phase (work a b c d e f [] reversed.reverse)
  simp only [work, put, put_work] at second
  have full := joinTrace first (oneStepTrace second)
  simpa [phaseWord, Nat.add_assoc] using full

theorem copyRestTrace (phase : Ambient) (input b c d e f reversed : List Bool) :
    (advance machine.step)^[2 * input.length + reversed.length + 3]
      (some (cfg (some .copyRest) phase (work input b c d e f reversed []))) =
      some (cfg none phase
        (work [] b c d e f [] (phaseWord phase ++ reversed.reverse ++ input))) := by
  have first := transferTrace .input .reversed (by decide) .copyRest (some .reverse)
    rfl phase (work input b c d e f reversed [])
  simp only [work, put, put_work] at first
  have second := reverseFinishTrace phase [] b c d e f (input.reverse ++ reversed)
  have full := joinTrace first second
  simpa [List.reverse_append, List.reverse_reverse, List.length_append, List.append_assoc,
    Nat.two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

theorem itemStep_true (phase : Ambient) (base : Tapes) (n : Nat)
    (input reversed : List Bool) :
    machine.step (cfg (some .fillYesItem) phase (itemWork base n (true :: input) reversed)) =
      some (cfg (some .fillYesItem) phase (itemWork base (n + 1) input (true :: reversed))) := by
  change some (TM2.stepAux (code .fillYesItem) _ _) = _
  simp [code, go, TM2.stepAux, cfg, itemWork, io, put, encodeWord, List.replicate_succ]
  congr 1
  congr 1
  funext tape; cases tape <;> simp

theorem itemStep_false (phase : Ambient) (base : Tapes) (n : Nat)
    (input reversed : List Bool) :
    machine.step (cfg (some .fillYesItem) phase (itemWork base n (false :: input) reversed)) =
      some (cfg (some (.convert .scan)) phase
        (io (put (put base .index (encodeWord n)) .compare (encodeWord (n + 1)))
          input (false :: reversed))) := by
  change some (TM2.stepAux (code .fillYesItem) _ _) = _
  simp [code, go, TM2.stepAux, cfg, itemWork, io, put, encodeWord, List.replicate_succ]
  congr 1
  congr 1
  funext tape; cases tape <;> simp

theorem itemTrace (phase : Ambient) (base : Tapes) (n initial : Nat)
    (input reversed : List Bool) :
    (advance machine.step)^[n + 1]
      (some (cfg (some .fillYesItem) phase
        (itemWork base initial (encodeWord n ++ input) reversed))) =
      some (cfg (some (.convert .scan)) phase
        (io (put (put base .index (encodeWord (initial + n)))
          .compare (encodeWord (initial + n + 1)))
          input ((encodeWord n).reverse ++ reversed))) := by
  induction n generalizing initial reversed with
  | zero =>
      simpa [encodeWord, advance] using! itemStep_false phase base initial input reversed
  | succ n ih =>
      have first := itemStep_true phase base initial (encodeWord n ++ input) reversed
      have second := ih (initial + 1) (true :: reversed)
      have full := joinTrace (oneStepTrace first) second
      simpa [encodeWord, List.replicate_succ, List.reverse_cons, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

theorem startItemStep (phase : Ambient) (input reversed : List Bool) :
    machine.step (cfg (some .startItem) phase (work input [] [] [] [] [] reversed [])) =
      some (cfg (some .fillYesItem) phase (work input [false] [false] [] [] [] (true :: reversed) [])) := by
  change some (TM2.stepAux (code .startItem) _ _) = _
  simp [code, go, TM2.stepAux, cfg, put_work, work]
  all_goals rfl

theorem convertTrace (phase : Ambient) (n : Nat) (input index compare reversed : List Bool) :
    (advance machine.step)^[UnaryToBinaryMachine.steps n 0]
      (some (cfg (some (.convert .scan)) phase
        (work (encodeWord n ++ input) index compare [] [] [] reversed []))) =
      some (cfg (some .frame) phase (work input index compare n.bits [] [] reversed [])) := by
  have trace := UnaryToBinaryMachine.convertTrace (K := Tape) (A := Ambient)
    .input .binary .scratch (by decide) (by decide) (by decide)
    Label.convert (some .frame) code (fun _ => rfl)
    (work [] index compare [] [] [] reversed []) phase n 0 input
  have ht : ∀ a b c,
      UnaryToBinaryMachine.tapes .input .binary .scratch
        (work [] index compare [] [] [] reversed []) a b c =
      work a index compare b c [] reversed [] := by
    intro a b c; funext k; cases k <;> rfl
  simpa only [machine_step, UnaryToBinaryMachine.tapes, put_work, Nat.zero_add,
    Nat.zero_bits, cfg] using! trace

theorem frameTrace (phase : Ambient) (n : Nat) (input index compare reversed : List Bool) :
    (advance machine.step)^[n.bits.length + 1]
      (some (cfg (some .frame) phase (work input index compare n.bits [] [] reversed []))) =
      some (cfg (some .restorePayload) phase
        (work input index compare [] (natBits n).reverse [] reversed [])) := by
  have trace := FrameEmitMachine.trace (K := Tape) (A := Ambient) .binary .scratch
    (by decide) .frame (some .restorePayload) code rfl
    (work input index compare [] [] [] reversed []) phase n.bits []
  simpa only [machine_step, tapesAt, put_work, List.append_nil, natBits,
    BinPackingCompleteness.BinaryEncoding.nameBits, cfg] using! trace

theorem restorePayloadTrace (phase : Ambient) (n : Nat)
    (input index compare reversed : List Bool) :
    (advance machine.step)^[(natBits n).length + 1]
      (some (cfg (some .restorePayload) phase
        (work input index compare [] (natBits n).reverse [] reversed []))) =
      some (cfg (some .zeroLabel) phase
        (work input index compare [] [] (natBits n) reversed [])) := by
  have trace := transferTrace .scratch .payload (by decide) .restorePayload
    (some .zeroLabel) rfl phase
    (work input index compare [] (natBits n).reverse [] reversed [])
  simpa only [work, put, put_work, List.length_reverse, List.reverse_reverse,
    List.append_nil] using trace

theorem zeroLabelStep (phase : Ambient) (input index compare payload reversed : List Bool) :
    machine.step (cfg (some .zeroLabel) phase
      (work input index compare [] [] payload reversed [])) =
      some (cfg (some .items) phase
        (work input index compare [] [] payload (false :: reversed) [])) := by
  change some (TM2.stepAux (code .zeroLabel) _ _) = _
  simp [code, go, TM2.stepAux, cfg, put_work, work]
  all_goals rfl

def fillHeader (s : State) : List Bool :=
  encodeWord s.bins ++ encodeWord (s.item + 1) ++ [false]

def fillPhase (s : State) : Phase := if s.item + 1 = s.items.length then .done else .fill

def fillCounter (s : State) : List Bool × Bool :=
  counterAfter s.items.length (encodeWord (s.item + 1), false)

def fillPrefixSteps (s : State) : Nat :=
  (s.bins + 1) + 1 + (s.item + 1) + UnaryToBinaryMachine.steps s.label 0 +
    (s.label.bits.length + 1) + ((natBits s.label).length + 1) + 1 +
    (rawInstanceBits s.items).length

theorem fillPrefixTrace (s : State) :
    (advance machine.step)^[fillPrefixSteps s]
      (some (cfg (some .fillYesBins) (ambient .fill)
        (work (bodyBits s) [] [] [] [] [] [] []))) =
      some (cfg (some (.replace (.entry true))) (ambient (fillPhase s))
        (work (fixedBits s.fixed) (encodeWord s.item) (fillCounter s).1 [] []
          (natBits s.label) ((rawInstanceBits s.items).reverse ++ (fillHeader s).reverse) [])) := by
  let tail := rawInstanceBits s.items ++ fixedBits s.fixed
  let afterBins := encodeWord s.item ++ encodeWord s.label ++ tail
  let revBins := (encodeWord s.bins).reverse
  let revItem := (encodeWord s.item).reverse ++ true :: revBins
  have first := unaryCopyTrace .fillYesBins .startItem rfl s.bins (ambient .fill)
    (work [] [] [] [] [] [] [] []) afterBins []
  have second := startItemStep (ambient .fill) afterBins revBins
  have third := itemTrace (ambient .fill) (work [] [] [] [] [] [] [] [])
    s.item 0 (encodeWord s.label ++ tail) (true :: revBins)
  have fourth := convertTrace (ambient .fill) s.label tail
    (encodeWord s.item) (encodeWord (s.item + 1)) revItem
  have fifth := frameTrace (ambient .fill) s.label tail
    (encodeWord s.item) (encodeWord (s.item + 1)) revItem
  have sixth := restorePayloadTrace (ambient .fill) s.label tail
    (encodeWord s.item) (encodeWord (s.item + 1)) revItem
  have seventh := zeroLabelStep (ambient .fill) tail
    (encodeWord s.item) (encodeWord (s.item + 1)) (natBits s.label) revItem
  have eighth := itemsTrace s.items
    (work [] (encodeWord s.item) [] [] [] (natBits s.label) [] [])
    (encodeWord (s.item + 1), false) (fixedBits s.fixed) (false :: revItem)
  simp only [io_work, List.append_nil, afterBins, List.append_assoc] at first
  simp only [afterBins, List.append_assoc] at second
  simp only [itemWork, Nat.zero_add, put, put_work, io_work,
    show encodeWord 0 = [false] from rfl] at third
  simp only [countIO, put, put_work, io_work, countedPhase_counterAfter] at eighth
  have full := joinTrace (joinTrace (joinTrace (joinTrace (joinTrace (joinTrace
    (joinTrace first (oneStepTrace second)) third)
      fourth) fifth) sixth) (oneStepTrace seventh)) eighth
  simpa [fillPrefixSteps, bodyBits, tail, afterBins, revBins, revItem, fillCounter,
    fillPhase, fillHeader, encodeWord, List.replicate_succ, List.reverse_cons,
    List.reverse_append, List.append_assoc, eq_comm,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

theorem incrementLabelStep (phase : Ambient) (input reversed : List Bool) :
    machine.step (cfg (some .incrementLabel) phase (work input [] [] [] [] [] reversed [])) =
      some (cfg (some .copyRest) phase (work input [] [] [] [] [] (true :: reversed) [])) := by
  change some (TM2.stepAux (code .incrementLabel) _ _) = _
  simp [code, go, TM2.stepAux, cfg, put_work, work]
  all_goals rfl

def findBody (s : State) : List Bool :=
  encodeWord s.bins ++ [false, false] ++ rawInstanceBits s.items ++ fixedBits s.fixed

def findSteps (s : State) : Nat :=
  (s.bins + 1) + (s.item + 1) + (s.label + 1) + 1 +
    (2 * (rawInstanceBits s.items ++ fixedBits s.fixed).length +
      (false :: false :: (encodeWord s.bins).reverse).length + 3)

def fillNoBody (s : State) : List Bool :=
  encodeWord s.bins ++ encodeWord s.item ++ encodeWord (s.label + 1) ++
    rawInstanceBits s.items ++ fixedBits s.fixed

def fillNoSteps (s : State) : Nat :=
  (s.bins + 1) + (s.item + 1) + 1 +
    (2 * (encodeWord s.label ++ rawInstanceBits s.items ++ fixedBits s.fixed).length +
      (true :: (encodeWord s.item).reverse ++ (encodeWord s.bins).reverse).length + 3)

theorem fillNoTrace (s : State) :
    (advance machine.step)^[fillNoSteps s]
      (some (cfg (some .fillNoBins) (ambient .fill)
        (work (bodyBits s) [] [] [] [] [] [] []))) =
      some (cfg none (ambient .fill)
        (work [] [] [] [] [] [] [] (phaseBits .fill ++ fillNoBody s))) := by
  let tail := encodeWord s.label ++ rawInstanceBits s.items ++ fixedBits s.fixed
  let header := (encodeWord s.item).reverse ++ (encodeWord s.bins).reverse
  have first := unaryCopyTrace .fillNoBins .fillNoItem rfl s.bins (ambient .fill)
    (work [] [] [] [] [] [] [] []) (encodeWord s.item ++ tail) []
  have second := unaryCopyTrace .fillNoItem .incrementLabel rfl s.item (ambient .fill)
    (work [] [] [] [] [] [] [] []) tail (encodeWord s.bins).reverse
  have third := incrementLabelStep (ambient .fill) tail header
  have fourth := copyRestTrace (ambient .fill) tail [] [] [] [] [] (true :: header)
  simp only [io_work, List.append_nil] at first second
  have full := joinTrace (joinTrace (joinTrace first second)
    (oneStepTrace third)) fourth
  simpa [fillNoSteps, bodyBits, fillNoBody, tail, header, encodeWord, List.replicate_succ,
    List.reverse_cons, List.reverse_append, List.reverse_reverse, List.append_assoc,
    Nat.add_assoc] using full

theorem fillNoBudget_le (s : State) :
    1 + fillNoSteps s ≤ rawTime.eval ((stateBits s).length + 1) := by
  have lengths := stateBits_length s
  simp only [fillNoSteps, List.length_append, List.length_cons, List.length_reverse,
    encodeWord_length, rawTime, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
  nlinarith

theorem init_eq (input : List Bool) :
    initList machine input = cfg (some .start) (ambient .find)
      (work input [] [] [] [] [] [] []) := by
  unfold initList cfg
  congr 1
  funext k; cases k <;> rfl

theorem cleanup_complete (k : Tape) : k ∈ cleanupTapes ↔ k ≠ program.output := by
  cases k <;> simp [cleanupTapes, program]

end BinPackingGap.SearchUpdateMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_SearchStageMachines
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.Packing.instDecidableEqTableBin _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.SearchInitialEmitMachine

open Turing
open BinPackingGames.Foundations.Complexity
open MachineComposition
open BinPackingGames.Reduction.MachineTransfer
open BinPackingGames.Reduction.MachineSubstitution
open SearchInitializeEncoding

theorem startStep (valid : Bool) (input : List Bool) :
    machine.step (cfg (some .start) (false, false) (valid :: input) [] [] [] [] [] []) =
      some (cfg (some .count) (valid, false) input [false] [false] [false] [] [false] []) := by
  change some (TM2.stepAux (code .start) _ _) = _
  simp [code, cfg, clean, TM2.stepAux]
  all_goals rfl

theorem countStep_true (valid seen : Bool) (m : Nat) (input output : List Bool) :
    machine.step (cfg (some .count) (valid, seen) (true :: input) output
      (encodeWord m) (encodeWord m) [] (encodeWord m) []) =
      some (cfg (some .count) (valid, true) input output
        (encodeWord (m + 1)) (encodeWord (m + 1)) [] (encodeWord (m + 1)) []) := by
  change some (TM2.stepAux (code .count) _ _) = _
  simp [code, cfg, clean, TM2.stepAux, encodeWord, List.replicate_succ]
  all_goals rfl

theorem countStep_false (valid seen : Bool) (m : Nat) (input output : List Bool) :
    machine.step (cfg (some .count) (valid, seen) (false :: input) output
      (encodeWord m) (encodeWord m) [] (encodeWord m) []) =
      some (cfg (some (dispatch valid)) (valid, seen) input output
        (encodeWord m) (encodeWord (m + 1)) [] (encodeWord m) []) := by
  change some (TM2.stepAux (code .count) _ _) = _
  simp [code, cfg, clean, TM2.stepAux, encodeWord, List.replicate_succ]
  all_goals rfl

theorem countTrace (n m : Nat) (input output : List Bool) (valid seen : Bool) :
    (advance machine.step)^[n + 1]
      (some (cfg (some .count) (valid, seen) (encodeWord n ++ input) output
        (encodeWord m) (encodeWord m) [] (encodeWord m) [])) =
      some (cfg (some (dispatch valid)) (valid, observed n seen) input output
        (encodeWord (m + n)) (encodeWord (m + n + 1)) [] (encodeWord (m + n)) []) := by
  induction n generalizing m seen with
  | zero =>
      simpa only [Nat.zero_add, Nat.add_zero, observed_zero, Function.iterate_one,
        advance_some, encodeWord, List.replicate_zero, List.nil_append,
        List.singleton_append] using countStep_false valid seen m input output
  | succ n ih =>
      rw [show encodeWord (n + 1) ++ input = true :: (encodeWord n ++ input) by rfl]
      rw [Function.iterate_succ_apply]
      simp only [advance_some]
      rw [countStep_true]
      simpa only [observed_true, observed_succ, Nat.add_assoc, Nat.add_comm 1 n] using
        ih (m + 1) true

def countInTime (valid seen : Bool) (n m : Nat) (input output : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (cfg (some .count) (valid, seen) (encodeWord n ++ input) output
        (encodeWord m) (encodeWord m) [] (encodeWord m) [])
      (some (cfg (some (dispatch valid)) (valid, observed n seen) input output
        (encodeWord (m + n)) (encodeWord (m + n + 1)) [] (encodeWord (m + n)) []))
      (n + 1) where
  steps := n + 1
  evals_in_steps := countTrace n m input output valid seen
  steps_le_m := Nat.le_refl _

theorem fixedStep_true (flags : Flags) (n m : Nat) (input left right : List Bool) :
    machine.step (cfg (some .fixed) flags input (fixedWord m)
      left right [] (encodeWord (n + 1)) []) =
      some (cfg (some .fixed) flags input (fixedWord (m + 1))
        left right [] (encodeWord n) []) := by
  change some (TM2.stepAux (code .fixed) _ _) = _
  simp [code, cfg, clean, TM2.stepAux, encodeWord, List.replicate_succ]
  all_goals rfl

theorem fixedStep_zero (flags : Flags) (m : Nat) (input left right : List Bool) :
    machine.step (cfg (some .fixed) flags input (fixedWord m)
      left right [] (encodeWord 0) []) =
      some (cfg (some .reverseRaw) flags input (fixedWord m) left right [] [] []) := by
  change some (TM2.stepAux (code .fixed) _ _) = _
  simp [code, cfg, clean, TM2.stepAux, encodeWord]
  all_goals rfl

theorem fixedTrace (n m : Nat) (flags : Flags) (input left right : List Bool) :
    (advance machine.step)^[n + 1]
      (some (cfg (some .fixed) flags input (fixedWord m)
        left right [] (encodeWord n) [])) =
      some (cfg (some .reverseRaw) flags input (fixedWord (m + n)) left right [] [] []) := by
  induction n generalizing m with
  | zero =>
      simpa only [Nat.zero_add, Nat.add_zero, Function.iterate_one, advance_some] using
        fixedStep_zero flags m input left right
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      simp only [advance_some]
      rw [fixedStep_true]
      simpa only [Nat.add_assoc, Nat.add_comm 1 n] using ih (m + 1)

def fixedInTime (n m : Nat) (flags : Flags) (input left right : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (cfg (some .fixed) flags input (fixedWord m) left right [] (encodeWord n) [])
      (some (cfg (some .reverseRaw) flags input (fixedWord (m + n)) left right [] [] []))
      (n + 1) where
  steps := n + 1
  evals_in_steps := fixedTrace n m flags input left right
  steps_le_m := Nat.le_refl _

def prepareInTime (valid : Bool) (n : Nat) (input : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (cfg (some .start) (false, false) (valid :: (encodeWord n ++ input)) [] [] [] [] [] [])
      (some (cfg (some .reverseRaw) (initialFlags valid n) input (selectedFixed valid n)
        (encodeWord n) (encodeWord (n + 1)) [] (residualFixed valid n) []))
      (2 * n + 3) := by
  have first := oneStep (startStep valid (encodeWord n ++ input))
  have counted := countInTime valid false n 0 input [false]
  simp only [Nat.zero_add] at counted
  have initialRun := join first counted
  cases valid with
  | false =>
      simpa only [dispatch, Bool.false_eq_true, ↓reduceIte, initialFlags, selectedFixed,
        residualFixed, fixedWord_zero] using
        enlarge initialRun (by omega : 1 + (n + 1) ≤ 2 * n + 3)
  | true =>
      have fixed := fixedInTime n 0 (initialFlags true n) input
        (encodeWord n) (encodeWord (n + 1))
      simp only [Nat.zero_add] at fixed
      have full := join initialRun fixed
      simpa [dispatch, ↓reduceIte, initialFlags, selectedFixed,
        residualFixed, fixedWord_zero] using
        enlarge full (by omega : (1 + (n + 1)) + (n + 1) ≤ 2 * n + 3)

theorem headerStep (valid seen : Bool) (output left right fixed : List Bool) :
    machine.step (cfg (some .pushHeader) (valid, seen) [] output left right [] fixed []) =
      some (cfg (some (finishLabel valid)) (valid, seen) []
        (header (valid, seen) ++ output) left right [] fixed []) := by
  cases valid <;> cases seen <;>
    change some (TM2.stepAux (code .pushHeader) _ _) = _ <;>
    simp [code, header, finishLabel, cfg, clean, TM2.stepAux, pushWord]
  all_goals rfl

theorem zeroFuelStep (seen : Bool) (output left right fixed : List Bool) :
    machine.step (cfg (some .zeroFuel) (false, seen) [] output left right [] fixed []) =
      some (cfg none (false, seen) [] (false :: output) left right [] fixed []) := by
  change some (TM2.stepAux (code .zeroFuel) _ _) = _
  simp [code, cfg, clean, TM2.stepAux]
  all_goals rfl

theorem bodyWord_eq (items : RawInstance) (valid : Bool) :
    bodyWord valid items.length (BinaryEncoding.rawInstanceBits items) =
      SearchEncoding.stateBits (SearchSemantics.initial items valid) := by
  cases valid with
  | false =>
      simp [bodyWord, header, initialFlags, selectedFixed, SearchSemantics.initial,
        SearchEncoding.stateBits, SearchEncoding.phaseBits, fixedWord,
        SearchEncoding.fixedBits, BinaryEncoding.listBits, encodeWord]
  | true =>
      cases items with
      | nil =>
          simp [bodyWord, header, initialFlags, observed, selectedFixed,
            SearchSemantics.initial, SearchEncoding.stateBits, SearchEncoding.phaseBits,
            fixedWord, SearchEncoding.fixedBits, BinaryEncoding.listBits, encodeWord]
      | cons item items =>
          simp [bodyWord, header, initialFlags, observed, selectedFixed,
            SearchSemantics.initial, SearchEncoding.stateBits, SearchEncoding.phaseBits,
            fixedWord, encodeWord]

theorem outputWord_eq (items : RawInstance) (valid : Bool) :
    outputWord valid items.length (BinaryEncoding.rawInstanceBits items) =
      MachineBoundedIteration.inputBits SearchEncoding.stateBits (emit (items, valid)) := by
  simp only [outputWord, bodyWord_eq, MachineBoundedIteration.inputBits,
    emit, fuelValue, SearchSemantics.fuel]

theorem rawSteps_le (items : RawInstance) (valid : Bool) :
    rawSteps valid items.length (BinaryEncoding.rawInstanceBits items).length ≤
      rawTime.eval (dataBits (items, valid)).length := by
  have hlen : (dataBits (items, valid)).length =
      items.length + (BinaryEncoding.rawInstanceBits items).length + 2 := by
    simp only [dataBits, List.length_cons, List.length_append, encodeWord_length]
    omega
  let n := items.length
  let r := (BinaryEncoding.rawInstanceBits items).length
  have hn : n ≤ n + r + 2 := by omega
  have hn' : n + 1 ≤ (n + r + 2) + 1 := by omega
  have hp := Nat.mul_le_mul hn hn'
  rw [hlen]
  change rawSteps valid n r ≤ rawTime.eval (n + r + 2)
  simp only [rawTime, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
  cases valid <;>
    simp [rawSteps, fuelTime, Bool.false_eq_true, ↓reduceIte,
      MachineUnaryMultiply.steps] <;>
    nlinarith [Nat.zero_le ((n + r + 2) * (n + r + 2))]

theorem cleanup_complete (k : Tape) : k ∈ cleanupTapes ↔ k ≠ program.output := by
  fin_cases k <;> simp [cleanupTapes, program]

end BinPackingGap.SearchInitialEmitMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Results_OptimalSearch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap

open Turing BinPackingGames.Foundations.Complexity

namespace OptimalSearch

noncomputable def decider (h : PEqualsNP) : List Bool → Bool :=
  Classical.choose (h.inP packingExtension_inNP)

noncomputable def decisionComputation (h : PEqualsNP) :
    TM2ComputableInPolyTime (id : List Bool → List Bool) (fun answer => [answer])
      (decider h) :=
  Classical.choose (Classical.choose_spec (h.inP packingExtension_inNP))

theorem decisionSpec (h : PEqualsNP) :
    MachineFiniteAlphabet.FiniteAlphabet (decisionComputation h).tm ∧
      ∀ input, ExtensionCertificate.language input ↔ decider h input = true :=
  Classical.choose_spec (Classical.choose_spec (h.inP packingExtension_inNP))

theorem decidesExtension (h : PEqualsNP) : SearchSemantics.DecidesExtension (decider h) :=
  SearchOptimalConstruction.decidesExtension_of_language (decisionSpec h).2

end OptimalSearch

end BinPackingGap

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_ApproximationImpliesP
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap

open Turing BinPackingGames.Foundations.Complexity

def PackingGapReduction.approximationComputation {c : Nat} {L : BitLanguage}
    (reduction : PackingGapReduction c L) (algorithm : AbsoluteAdditiveAlgorithm c) :
    TM2ComputableInPolyTime (id : List Bool → List Bool) (fun bit => [bit])
      (fun x => approximationAccepts c
        (algorithm.run (BinaryEncoding.rawInstanceBits (reduction.reduce x).2))) :=
by
  let projected := MachineSequential.composeBits reduction.computation
    DropPackingBoundMachine.computation
  let approximated := MachineSequential.composeBits projected algorithm.rawComputation
  let decided := MachineSequential.composeBits approximated
    (ApproximationDecisionMachine.computation c)
  exact decided

end BinPackingGap

end

end OAI
end


