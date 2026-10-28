-- Prove2me | Definitions.Def_OAIQ085D019
-- name    : OAIQ085D019
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T16:35:15.231516+00:00
-- url     : https://prove2.me/theorems/7a2d2e86-f8d3-4e0a-81d1-43cfb7b1016c
-- title:
--   Definitions bundle OAIQ085D019 of the split of OpenAI, Constant-factor hardness of directed feedback vertex set (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DirectedFeedback.main`, carved from OpenAI's openai/math development (OpenAI, *Constant-factor hardness of directed feedback vertex set (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 397 declarations of OpenAI's Lean: 149 definitions, 10 inductive types or structures, 3 instances and 235 theorems. The definitions and types are `OAI.DFVSGames.Decoder.ActualConditionalLaw.datumAgreement`, `OAI.DFVSGames.Decoder.ActualEvents.homFintype`, `OAI.DFVSGames.Decoder.ActualGoodRows.homFintype`, `OAI.DFVSGames.Decoder.ActualSeedVariation.homFintype`, `OAI.DFVSGames.Decoder.ActualSpectral.homFintype`, `OAI.DFVSGames.Decoder.MatrixCoordinates.homFintype`, `OAI.DFVSGames.Decoder.SelectedDecoding.homFintype`, `OAI.DFVSGames.Decoder.SelectedDecoding.transferredAgreement`, `OAI.DFVSGames.Decoder.SelectedFiberLaw.homFintype`, `OAI.DFVSGames.Decoder.SurrogateFibers.shortcodeAcceptance`, `OAI.DFVSGames.Explicit.MachineClone100Cleanup.cleanupFourInTime`, `OAI.DFVSGames.Explicit.MachineClone100Cleanup.cleanupSteps`, `OAI.DFVSGames.Explicit.MachineClone100Headers.headersInTime`, `OAI.DFVSGames.Explicit.MachineClone100Headers.parsedTapes`, `OAI.DFVSGames.Explicit.MachineClone100Loop.bodyCost`, `OAI.DFVSGames.Explicit.MachineClone100Loop.bodyInTime`, `OAI.DFVSGames.Explicit.MachineClone100Loop.clonedRecordBits`, `OAI.DFVSGames.Explicit.MachineClone100Loop.clonedRecordsBits`, `OAI.DFVSGames.Explicit.MachineClone100Loop.loopCost`, `OAI.DFVSGames.Explicit.MachineClone100Loop.loopInTime`, `OAI.DFVSGames.Explicit.MachineClone100Loop.loopInTime_linear`, `OAI.DFVSGames.Explicit.MachineClone100Loop.recordBits`, `OAI.DFVSGames.Explicit.MachineClone100Loop.recordFields`, `OAI.DFVSGames.Explicit.MachineClone100Loop.recordsBits`, `OAI.DFVSGames.Explicit.MachineClone100Loop.sourceLoopInTime_table`, `OAI.DFVSGames.Explicit.MachineClone100Loop.tapes`, `OAI.DFVSGames.Explicit.MachineClone100Model.machine`, `OAI.DFVSGames.Explicit.MachineClone100Model.program`, `OAI.DFVSGames.Explicit.MachineClone100Run.outputBits`, `OAI.DFVSGames.Explicit.MachineClone100Run.outputBody`, `OAI.DFVSGames.Explicit.MachineClone100Run.outputHeaders`, `OAI.DFVSGames.Explicit.MachineClone100Run.sourceBody`, `OAI.DFVSGames.Explicit.MachineClone100Run.tm`, `OAI.DFVSGames.Explicit.MachineClone100Triples.rowOutput`, `OAI.DFVSGames.Explicit.MachineClone100Triples.rowSteps`, `OAI.DFVSGames.Explicit.MachineProductField.Label`, `OAI.DFVSGames.Explicit.MachineProductField.entry`, `OAI.DFVSGames.Explicit.MachineProductField.instruction`, `OAI.DFVSGames.Explicit.MachineProductFinish.afterRows`, `OAI.DFVSGames.Explicit.MachineProductGather.Label` and 119 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `DirectedFeedback_Encoding_ActualGoodRows`, `DirectedFeedback_Encoding_CanonicalWordTemplate`, `DirectedFeedback_Encoding_CompareLoop`, `DirectedFeedback_Encoding_FinalCNFPattern`, `DirectedFeedback_Encoding_Lookup`, `DirectedFeedback_Encoding_ProductTarget`, `DirectedFeedback_Encoding_SelectedPolicies`, `DirectedFeedback_Encoding_TableIteration`, `DirectedFeedback_Encoding_VerifierCNF`, `DirectedFeedback_Games_AddressTupleBody`, `DirectedFeedback_Games_AddressTupleLoaded`, `DirectedFeedback_Games_AffineWitnessNormalization`, `DirectedFeedback_Games_Collision`, `DirectedFeedback_Games_FinishReduction`, `DirectedFeedback_Games_InitialGraph`, `DirectedFeedback_Games_PositiveMultiplier`, `DirectedFeedback_Games_PoweringFinalConstants`, `DirectedFeedback_Games_PoweringReach`, `DirectedFeedback_Games_Product`, `DirectedFeedback_Games_RowErasureSliceUniform`, `DirectedFeedback_Games_SharedSampling`, `DirectedFeedback_Games_Target`, `DirectedFeedback_Games_TensorDomination`, `DirectedFeedback_Games_UniformReduction`, `DirectedFeedback_Games_VisibleTransfer`, `DirectedFeedback_Machines_FinalCNFHeader`, `DirectedFeedback_Machines_FinalCNFStream`, `DirectedFeedback_Machines_FinalCNFTime`, `DirectedFeedback_Machines_GraphCounterFinish`, `DirectedFeedback_Machines_MachineAddressHeaders`, `DirectedFeedback_Machines_MachineAffineLookup`, `DirectedFeedback_Machines_MachineBinaryTokenMachine`, `DirectedFeedback_Machines_MachineLookupSpec`, `DirectedFeedback_Machines_MachineOutcomeRows`, `DirectedFeedback_Machines_MachineProductField`, `DirectedFeedback_Machines_MachineProductFinish`, `DirectedFeedback_Machines_MachineProductProgram`, `DirectedFeedback_Machines_MachineSingleOrbitBridge`, `DirectedFeedback_Machines_MachineSingleOrbitCodec`, `DirectedFeedback_Machines_MachineTuple`, `DirectedFeedback_Machines_RawInitialMachineFinish`, `DirectedFeedback_RankGraph_Clone100Counting`, `DirectedFeedback_RankGraph_MachineClone100Cleanup`, `DirectedFeedback_RankGraph_MachineClone100Finish`.
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
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_Target
attribute [-instance] _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Complexity.MachineDrainMany

open Turing MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

theorem trace (chosen : List K) (labels : Label chosen → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLabels : ∀ l, program (labels l) = instruction chosen labels exit l)
    (base : Tapes K) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[steps chosen base]
      (some ⟨entry chosen labels exit, (ambient, register), base⟩) =
    some ⟨exit, (ambient, finalRegister chosen register), finalTapes chosen base⟩ := by
  have run := MachineFiniteSequence.trace
    (LocalLabel := LocalLabel (K := K)) (main := fun _ => ())
    (localInstruction := localInstruction (σ := σ)) (result := result) (cost := cost)
    program (fun _ : Data K => True) (fun data => (ambient, data.2)) (fun data => data.1)
    chosen (by intros; trivial)
    (by
      intro source _ localLabels localExit atLocal data _
      rcases data with ⟨tapes, reg⟩
      simpa only [cost, result, Function.update_eq_self] using
        MachineDrain.drainTrace source (localLabels ()) localExit program (atLocal ())
          tapes (tapes source) ambient reg)
    labels exit atLabels (base, register) trivial
  simpa only [sequence_steps, sequence_result, entry] using run

end DFVSGames.Foundations.Complexity.MachineDrainMany

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_ProductTarget
attribute [-instance] _root_.OAI.DFVSGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.DFVSGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.DFVSGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DFVSGames.Quadratic.blockOrientationFintype _root_.OAI.DFVSGames.Quadratic.fieldLineFintype _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Explicit.ProductTarget

open DFVSGames.Foundations
open Target
open MachineOutputContract
open scoped BigOperators

variable {L R E : Type*} {q N M : ℕ}

section Value

variable [Fintype L] [Fintype R] [Fintype E]

omit [Fintype L] [Fintype R] in

theorem render_count (G : BipartiteGame L R E (Fin q))
    (vertices : (L ⊕ R) ≃ Fin N) (edges : Fin M ≃ E)
    (tables : E → PermutationTable q) (hM : 0 < M)
    (htable : ∀ e, permutationEquiv (tables e) = G.permutation e)
    (labeling : Fin N → Fin q) :
    countSatisfied labeling (render G vertices edges tables hM).constraints =
      G.satisfiedCount (fun x => labeling (vertices (Sum.inl x)))
        (fun y => labeling (vertices (Sum.inr y))) := by
  classical
  have ht (e : E) (a : Fin q) : (tables e).images[a] = G.permutation e a :=
    congrArg (fun p : Equiv.Perm (Fin q) => p a) (htable e)
  change countSatisfied labeling (List.ofFn (row G vertices edges tables)) = _
  rw [Integration.GapSemantics.countSatisfied_ofFn]
  unfold BipartiteGame.satisfiedCount
  apply Fintype.sum_equiv edges
  intro i
  simp [row, Constraint.satisfied, ht]

omit [Fintype L] [Fintype R] in
theorem render_count_merge (G : BipartiteGame L R E (Fin q))
    (vertices : (L ⊕ R) ≃ Fin N) (edges : Fin M ≃ E)
    (tables : E → PermutationTable q) (hM : 0 < M)
    (htable : ∀ e, permutationEquiv (tables e) = G.permutation e)
    (left : L → Fin q) (right : R → Fin q) :
    countSatisfied (mergeLabelings vertices left right)
      (render G vertices edges tables hM).constraints = G.satisfiedCount left right := by
  simpa only [mergeLabelings_left, mergeLabelings_right] using
    render_count G vertices edges tables hM htable (mergeLabelings vertices left right)

theorem render_maxSatisfied (G : BipartiteGame L R E (Fin q))
    (vertices : (L ⊕ R) ≃ Fin N) (edges : Fin M ≃ E)
    (tables : E → PermutationTable q) (hM : 0 < M)
    (htable : ∀ e, permutationEquiv (tables e) = G.permutation e) :
    Integration.InstanceValue.maxSatisfied (render G vertices edges tables hM) =
      G.maxSatisfied := by
  classical
  apply Nat.le_antisymm
  · unfold Integration.InstanceValue.maxSatisfied
    apply Finset.sup_le
    intro labeling _
    change Fin N → Fin q at labeling
    exact (render_count G vertices edges tables hM htable labeling).le.trans
      (G.satisfiedCount_le_maxSatisfied _ _)
  · unfold BipartiteGame.maxSatisfied
    apply Finset.sup_le
    intro labeling _
    rw [← render_count_merge G vertices edges tables hM htable]
    exact Integration.InstanceValue.countSatisfied_le_maxSatisfied
      (render G vertices edges tables hM) (mergeLabelings vertices labeling.1 labeling.2)

theorem render_value (G : BipartiteGame L R E (Fin q))
    (vertices : (L ⊕ R) ≃ Fin N) (edges : Fin M ≃ E)
    (tables : E → PermutationTable q) (hM : 0 < M)
    (htable : ∀ e, permutationEquiv (tables e) = G.permutation e) :
    Integration.InstanceValue.value (render G vertices edges tables hM) = G.value := by
  unfold Integration.InstanceValue.value BipartiteGame.value
  rw [render_maxSatisfied G vertices edges tables hM htable, render_length]
  have hcard : M = Fintype.card E := by simpa using Fintype.card_congr edges
  rw [hcard]

end Value

end DFVSGames.Explicit.ProductTarget


namespace DFVSGames.Explicit.SubdivisionTarget

open DFVSGames.Foundations Target
open MachineOutputContract
open scoped BigOperators

theorem ofInstance_count {q : Nat} (H : Instance q) (a : Fin H.vertices → Fin q) :
    (ofInstance H).satisfiedCount a = countSatisfied a H.constraints := by
  have h := Integration.GapSemantics.countSatisfied_ofFn a
    (fun i : Fin H.constraints.length => H.constraints[i.val])
  rw [List.ofFn_getElem] at h
  rw [h]
  simp only [OccurrenceGame.satisfiedCount, ofInstance, permutationEquiv,
    Equiv.coe_fn_mk, Constraint.satisfied, decide_eq_true_eq, Fin.getElem_fin]
  rfl

theorem ofInstance_maxSatisfied {q : Nat} (H : Instance q) :
    (ofInstance H).maxSatisfied = Integration.InstanceValue.maxSatisfied H := by
  classical
  unfold OccurrenceGame.maxSatisfied Integration.InstanceValue.maxSatisfied
  apply Finset.sup_congr
  · ext a
    simp only [Finset.mem_univ]
  · intro a _
    exact ofInstance_count H a

theorem ofInstance_value {q : Nat} (H : Instance q) :
    (ofInstance H).value = Integration.InstanceValue.value H := by
  unfold OccurrenceGame.value Integration.InstanceValue.value
  rw [ofInstance_maxSatisfied]
  simp

theorem subdivide_value {q : Nat} (H : Instance q) :
    Integration.InstanceValue.value (subdivide H) =
      (Subdivision.game (ofInstance H)).value :=
  ProductTarget.render_value _ _ _ _ _ (tables_correspond H)

theorem value_eq {q : Nat} (H : Instance q) (hq : 0 < q) :
    Integration.InstanceValue.value (subdivide H) =
      1 - (1 - Integration.InstanceValue.value H) / 4 := by
  let : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  let : Nonempty (Fin H.constraints.length) := ⟨⟨0, H.constraintCount_positive⟩⟩
  rw [subdivide_value, Subdivision.value_eq, ofInstance_value]

end DFVSGames.Explicit.SubdivisionTarget


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_Product
attribute [-instance] _root_.OAI.DFVSGames.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.DFVSGames.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.DFVSGames.Clean.AdviceImageLaw.kernelFintype _root_.OAI.DFVSGames.Clean.AdviceImageLaw.rangeFintype _root_.OAI.DFVSGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.DFVSGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.DFVSGames.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.DFVSGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DFVSGames.Quadratic.blockOrientationFintype _root_.OAI.DFVSGames.Quadratic.fieldLineFintype _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype _root_.OAI.DFVSGames.Reduction.ActualSource.sourceIndexNonempty _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Explicit.ProductPaddedOutput

open DFVSGames.Foundations
open Target
open MachineOutputContract
open ProductTarget
open scoped BigOperators

variable {q : ℕ} (H : Instance q) (presentation : SimpleBipartite H)

noncomputable section

attribute [local instance] OAI.DFVSGames.Explicit.ProductPaddedOutput.productConstraintIndicesNonempty
theorem output_value_eq_repetition [Nonempty (Fin q)] (t : ℕ) (ht : 0 < t) :
    Integration.InstanceValue.value (output H presentation t ht) =
      (presentation.toBipartiteGame.toGame.repetition t).value := by
  classical
  let : Nonempty (Fin H.constraints.length) := ⟨⟨0, H.constraintCount_positive⟩⟩
  let : Nonempty (Fin (q ^ t)) :=
    ⟨finFunctionFinEquiv (fun _ : Fin t => Classical.choice inferInstance)⟩
  rw [output, Embedded.value, ← BipartiteGame.toGame_value, graph,
    BipartiteGame.relabel_value, BipartiteGame.product_value_eq_repetition]

theorem output_completeness [Nonempty (Fin q)] (t : ℕ) (ht : 0 < t) {error : ℝ}
    (hcomplete : 1 - error ≤ Integration.InstanceValue.value H) :
    1 - (t : ℝ) * error ≤ Integration.InstanceValue.value (output H presentation t ht) := by
  classical
  let : Nonempty (Fin H.constraints.length) := ⟨⟨0, H.constraintCount_positive⟩⟩
  rw [output_value_eq_repetition, ← BipartiteGame.product_value_eq_repetition]
  exact presentation.toBipartiteGame.product_completeness t
    (by simpa only [BipartiteGame.toGame_value, presentation.toBipartiteGame_value] using hcomplete)

end

end DFVSGames.Explicit.ProductPaddedOutput


namespace DFVSGames.Foundations.Complexity.MachineLookup

open Turing

variable {K Λ σ : Type} [DecidableEq K]

theorem fieldTapes_eq (index source destination : K) (hsd : source ≠ destination)
    (base : K → List Bool) (counter input output input' output' : List Bool) :
    Hastad.SourceMachine.fieldTapes source destination
      (tapes index source destination base counter input output) input' output' =
      tapes index source destination base counter input' output' := by
  rw [Hastad.SourceMachine.fieldTapes, update_source _ _ _ hsd, update_destination]

end DFVSGames.Foundations.Complexity.MachineLookup

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineLookupSpec
attribute [-instance] _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Complexity.MachineLookup

open Turing
open MachineComposition

variable {K σ : Type} [DecidableEq K]

theorem guard_step_succ (index source destination : K)
    (his : index ≠ source) (hid : index ≠ destination)
    (base : K → List Bool) (i : Nat) (indexSuffix input output : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step (program index source destination)
      ⟨some .guard, (ambient, register), tapes index source destination base
        (encodeWord (i + 1) ++ indexSuffix) input output⟩ =
      some ⟨some .skip, (ambient, none), tapes index source destination base
        (encodeWord i ++ indexSuffix) input output⟩ := by
  change some (TM2.stepAux (program index source destination .guard) _ _) = _
  simp [program, MachineUnaryCounter.guard, TM2.stepAux,
    tapes_index, his, hid, encodeWord, List.replicate_succ, update_index]

theorem guard_step_zero (index source destination : K)
    (his : index ≠ source) (hid : index ≠ destination)
    (base : K → List Bool) (indexSuffix input output : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step (program index source destination)
      ⟨some .guard, (ambient, register), tapes index source destination base
        (encodeWord 0 ++ indexSuffix) input output⟩ =
      some ⟨some .select, (ambient, none), tapes index source destination base
        (encodeWord 0 ++ indexSuffix) input output⟩ := by
  change some (TM2.stepAux (program index source destination .guard) _ _) = _
  simp [program, MachineUnaryCounter.guard, TM2.stepAux,
    tapes_index, his, hid, encodeWord]

theorem select_step_nonempty (index source destination : K)
    (hsd : source ≠ destination) (base : K → List Bool)
    (counter input output : List Bool) (hinput : input ≠ [])
    (ambient : σ) (register : Option Bool) :
    TM2.step (program index source destination)
      ⟨some .select, (ambient, register),
        tapes index source destination base counter input output⟩ =
      some ⟨some .copy, (ambient, input.head?),
        tapes index source destination base counter input (false :: output)⟩ := by
  change some (TM2.stepAux (program index source destination .select) _ _) = _
  cases input with
  | nil => exact (hinput rfl).elim
  | cons head tail =>
    simp [program, select, Hastad.SourceMachine.fieldStart, TM2.stepAux,
      tapes_source, hsd, update_destination]

theorem copyTrace (index source destination : K)
    (hsd : source ≠ destination) (base : K → List Bool)
    (counter : List Bool) (n : Nat) (suffix output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program index source destination)))^[n + 1]
      (some ⟨some .copy, (ambient, register), tapes index source destination base
        counter (encodeWord n ++ suffix) (false :: output)⟩) =
      some ⟨some .accepted, (ambient, none), tapes index source destination base
        counter suffix (encodeWord n ++ output)⟩ := by
  have h := Hastad.SourceMachine.fieldLoopTrace source destination hsd
    Label.copy (some Label.accepted) (program index source destination) rfl
    (Function.update base index counter) n suffix (false :: output) ambient register
  simpa only [Hastad.SourceMachine.fieldTapes, tapes, encodeWord,
    List.append_assoc, List.singleton_append] using h

theorem selectTrace (index source destination : K)
    (hsd : source ≠ destination) (base : K → List Bool)
    (counter : List Bool) (n : Nat) (suffix output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program index source destination)))^[n + 2]
      (some ⟨some .select, (ambient, register), tapes index source destination base
        counter (encodeWord n ++ suffix) output⟩) =
      some ⟨some .accepted, (ambient, none), tapes index source destination base
        counter suffix (encodeWord n ++ output)⟩ := by
  rw [show n + 2 = (n + 1) + 1 by omega, Function.iterate_succ_apply]
  simp only [advance_some]
  rw [select_step_nonempty index source destination hsd base counter
    (encodeWord n ++ suffix) output (by simp [encodeWord]) ambient register]
  exact copyTrace index source destination hsd base counter n suffix output ambient _

theorem skipCycleTrace (index source destination : K)
    (his : index ≠ source) (hid : index ≠ destination) (hsd : source ≠ destination)
    (base : K → List Bool) (i n : Nat) (indexSuffix suffix output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program index source destination)))^[n + 2]
      (some ⟨some .guard, (ambient, register), tapes index source destination base
        (encodeWord (i + 1) ++ indexSuffix) (encodeWord n ++ suffix) output⟩) =
      some ⟨some .guard, (ambient, none), tapes index source destination base
        (encodeWord i ++ indexSuffix) suffix output⟩ := by
  rw [show n + 2 = (n + 1) + 1 by omega, Function.iterate_succ_apply]
  simp only [advance_some]
  rw [guard_step_succ index source destination his hid]
  have h := discardTrace source Label.skip Label.guard
    (program index source destination) rfl
    (tapes index source destination base (encodeWord i ++ indexSuffix)
      (encodeWord n ++ suffix) output) n suffix (by simp [hsd]) ambient none
  simpa only [update_source index source destination hsd] using h

theorem successPrefixTrace (index source destination : K)
    (his : index ≠ source) (hid : index ≠ destination) (hsd : source ≠ destination)
    (base : K → List Bool) (prior : List Nat) (value : Nat)
    (indexSuffix suffix output : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program index source destination)))^[
        (encodeWords prior).length + prior.length + value + 3]
      (some ⟨some .guard, (ambient, register), tapes index source destination base
        (encodeWord prior.length ++ indexSuffix)
        (encodeWords prior ++ (encodeWord value ++ suffix)) output⟩) =
      some ⟨some .accepted, (ambient, none), tapes index source destination base
        (encodeWord 0 ++ indexSuffix) suffix (encodeWord value ++ output)⟩ := by
  induction prior generalizing register with
  | nil =>
    simp only [encodeWords, List.length_nil, Nat.zero_add, List.nil_append]
    rw [show value + 3 = (value + 2) + 1 by omega, Function.iterate_succ_apply]
    simp only [advance_some]
    rw [guard_step_zero index source destination his hid]
    exact selectTrace index source destination hsd base _ value suffix output ambient none
  | cons n prior ih =>
    simp only [encodeWords, List.length_cons, List.length_append, encodeWord_length]
    rw [show n + 1 + (encodeWords prior).length + (prior.length + 1) + value + 3 =
      ((encodeWords prior).length + prior.length + value + 3) + (n + 2) by omega,
      Function.iterate_add_apply]
    rw [List.append_assoc,
      skipCycleTrace index source destination his hid hsd base prior.length n]
    exact ih none

theorem lookupTrace_some (index source destination : K)
    (his : index ≠ source) (hid : index ≠ destination) (hsd : source ≠ destination)
    (base : K → List Bool) (values : List Nat) (i value : Nat)
    (selected : values[i]? = some value)
    (indexSuffix suffix output : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program index source destination)))^[MachineLookupSpec.steps values i]
      (some ⟨some .guard, (ambient, register), tapes index source destination base
        (encodeWord i ++ indexSuffix) (encodeWords values ++ suffix) output⟩) =
      some ⟨some .accepted, (ambient, none), tapes index source destination base
        (encodeWord 0 ++ indexSuffix) (encodeWords (values.drop (i + 1)) ++ suffix)
        (encodeWord value ++ output)⟩ := by
  have hi := (List.getElem?_eq_some_iff.mp selected).1
  have hlength : (values.take i).length = i := by
    simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]
  have hsource : encodeWords (values.take i) ++
      (encodeWord value ++ (encodeWords (values.drop (i + 1)) ++ suffix)) =
      encodeWords values ++ suffix := by
    rw [MachineLookupSpec.encoded_selected_split values i value selected]
    simp only [List.append_assoc]
  have htime : MachineLookupSpec.steps values i =
      (encodeWords (values.take i)).length + i + value + 3 := by
    rw [MachineLookupSpec.steps_eq_scannedBits_of_some values i value selected,
      MachineLookupSpec.scannedBits_of_some values i value selected]
    omega
  have h := successPrefixTrace index source destination his hid hsd base (values.take i)
    value indexSuffix (encodeWords (values.drop (i + 1)) ++ suffix) output ambient register
  rw [hlength, hsource] at h
  simpa only [htime] using h

end DFVSGames.Foundations.Complexity.MachineLookup


namespace DFVSGames.Foundations.Complexity.MachinePreservingLookup

open Turing
open MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

theorem lookupFramedHaltTrace_some (index source destination : K)
    (his : index ≠ source) (hid : index ≠ destination) (hsd : source ≠ destination)
    (base : K → List Bool) (values : List Nat) (i value : Nat)
    (selected : values[i]? = some value) (indexSuffix suffix output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (MachineLookup.program index source destination)))^[
      MachineLookupSpec.steps values i + 1]
      (some ⟨some MachineLookup.Label.guard, (ambient,register),
        MachineLookup.tapes index source destination base (encodeWord i ++ indexSuffix)
          (encodeWords values ++ suffix) output⟩) =
      some ⟨none, (ambient,none), MachineLookup.tapes index source destination base
        (encodeWord 0 ++ indexSuffix) (encodeWords (values.drop (i + 1)) ++ suffix)
        (encodeWord value ++ output)⟩ := by
  rw [Function.iterate_succ_apply',
    MachineLookup.lookupTrace_some index source destination his hid hsd
      base values i value selected indexSuffix suffix output ambient register]
  simp only [advance_some, TM2.step, MachineLookup.program, TM2.stepAux]

theorem preservingLookupTrace (tape : Fin 5 → K) (distinct : Function.Injective tape)
    (firstLabel secondLabel : Λ) (lookupLabels : MachineLookup.Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atFirst : program firstLabel = Reduction.MachineTransfer.loopAt
      (tape 0) (tape 4) id false firstLabel (some secondLabel))
    (atSecond : program secondLabel = MachineCopy.forkLoop
      (tape 4) (tape 0) (tape 2) false secondLabel (some (lookupLabels .guard)))
    (atLookup : ∀ l, program (lookupLabels l) =
      MachineSubroutine.statement lookupLabels exit (MachineLookup.program (tape 1) (tape 2) (tape 3) l))
    (base : K → List Bool) (values : List Nat) (tableWord : base (tape 0) = encodeWords values)
    (scratchEmpty : base (tape 4) = []) (i value : Nat) (selected : values[i]? = some value)
    (indexSuffix workSuffix output : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[
      2 * ((encodeWords values).length + 1) + MachineLookupSpec.steps values i + 1]
      (some ⟨some firstLabel, (ambient,register),
        initialTapes tape base i indexSuffix workSuffix output⟩) =
      some ⟨exit, (ambient,none), finalTapes tape base values i value indexSuffix workSuffix output⟩ := by
  have hd (a b : Fin 5) (hne : a ≠ b) : tape a ≠ tape b := fun h => hne (distinct h)
  let start := initialTapes tape base i indexSuffix workSuffix output
  have htable : start (tape 0) = encodeWords values := by
    simpa only [start, initialTapes, MachineLookup.tapes_other _ _ _ _
      (hd 0 1 (by decide)) (hd 0 2 (by decide)) (hd 0 3 (by decide))] using tableWord
  have hs : start (tape 4) = [] := by
    simpa only [start, initialTapes, MachineLookup.tapes_other _ _ _ _
      (hd 4 1 (by decide)) (hd 4 2 (by decide)) (hd 4 3 (by decide))] using scratchEmpty
  have hwork : start (tape 2) = workSuffix := by
    simp only [start, initialTapes, MachineLookup.tapes_source _ _ _ (hd 2 3 (by decide))]
  have hcopy := MachineCopy.copyTrace (tape 0) (tape 2) (tape 4)
    (hd 0 2 (by decide)) (hd 0 4 (by decide)) (hd 2 4 (by decide)) false
    firstLabel secondLabel (some (lookupLabels .guard)) program atFirst atSecond start hs ambient register
  rw [htable, hwork] at hcopy
  simp only [start, initialTapes, MachineLookup.update_source _ _ _ (hd 2 3 (by decide))] at hcopy
  have hlookup := MachineSubroutine.trace lookupLabels exit
    (MachineLookup.program (tape 1) (tape 2) (tape 3)) program atLookup
    (MachineLookupSpec.steps values i + 1) _ _
    (lookupFramedHaltTrace_some (tape 1) (tape 2) (tape 3)
      (hd 1 2 (by decide)) (hd 1 3 (by decide)) (hd 2 3 (by decide))
      base values i value selected indexSuffix workSuffix output ambient none)
  simp only [MachineSubroutine.configuration, MachineSubroutine.label] at hlookup
  rw [show 2 * ((encodeWords values).length + 1) + MachineLookupSpec.steps values i + 1 =
      (MachineLookupSpec.steps values i + 1) + 2 * ((encodeWords values).length + 1) by omega,
    Function.iterate_add_apply]
  change (advance (TM2.step program))^[MachineLookupSpec.steps values i + 1]
    ((advance (TM2.step program))^[2 * ((encodeWords values).length + 1)]
      (some ⟨some firstLabel, (ambient,register),
        MachineLookup.tapes (tape 1) (tape 2) (tape 3) base
          (encodeWord i ++ indexSuffix) workSuffix output⟩)) = _
  rw [hcopy]
  exact hlookup

end DFVSGames.Foundations.Complexity.MachinePreservingLookup

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineAffineLookup
attribute [-instance] _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Soundness.ConditionalIncidences.zeroBits _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Complexity.MachineAffineLookup

open Turing
open MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

theorem affineLookupTrace (source : K) (tape : Fin 5 → K)
    (distinct : Function.Injective tape) (outside : ∀ i, source ≠ tape i)
    (coefficient offset : Nat) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLabels : ∀ l, program (labels l) = instruction source tape coefficient offset labels exit l)
    (base : K → List Bool) (values : List Nat)
    (tableWord : base (tape 0) = encodeWords values) (scratchEmpty : base (tape 4) = [])
    (a : Nat) (suffix : List Bool) (sourceWord : base source = encodeWord a ++ suffix)
    (value : Nat) (selected : values[coefficient * a + offset]? = some value)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[steps values a coefficient offset]
      (some ⟨some (labels .seed), (ambient,register), base⟩) =
      some ⟨exit, (ambient,none), finalTapes tape base values (coefficient * a + offset) value⟩ := by
  have hd (i j : Fin 5) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  have haffine := MachineUnaryAffineAt.seededAffineTrace source (tape 4) (tape 1)
    (outside 4) (outside 1) (hd 4 1 (by decide)) coefficient offset
    (labels .seed) (labels .scan) (labels .restore) (some (labels .copyFirst))
    program (atLabels .seed) (atLabels .scan) (atLabels .restore)
    base a suffix sourceWord scratchEmpty ambient register
  have hlookup := MachinePreservingLookup.preservingLookupTrace tape distinct
    (labels .copyFirst) (labels .copySecond) (fun q => labels (.lookup q)) exit
    program (atLabels .copyFirst) (atLabels .copySecond) (fun q => atLabels (.lookup q))
    base values tableWord scratchEmpty (coefficient * a + offset) value selected
    (base (tape 1)) (base (tape 2)) (base (tape 3)) ambient none
  rw [initialTapes_eq_update tape distinct] at hlookup
  rw [steps, Nat.add_comm, Function.iterate_add_apply, haffine]
  exact hlookup

end DFVSGames.Foundations.Complexity.MachineAffineLookup


namespace DFVSGames.Explicit.MachineProductGather

open Turing
open DFVSGames.Foundations.Complexity
open MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

def Label : Nat → Type
  | 0 => Unit
  | width + 1 => MachineAffineLookup.Label ⊕ Label width

instance labelFintype (width : Nat) : Fintype (Label width) := by
  induction width with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ width ih =>
    letI := ih
    exact inferInstanceAs (Fintype (MachineAffineLookup.Label ⊕ Label width))

instance labelDecidableEq (width : Nat) : DecidableEq (Label width) := by
  induction width with
  | zero => exact inferInstanceAs (DecidableEq Unit)
  | succ width ih =>
    letI := ih
    exact inferInstanceAs (DecidableEq (MachineAffineLookup.Label ⊕ Label width))

def entry : (width : Nat) → Label width
  | 0 => ()
  | _ + 1 => .inl .seed

def instruction : (width : Nat) → (Tape width → K) → Nat → (Fin width → Nat) →
    (Label width → Λ) → Option Λ → Label width →
    TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool)
  | 0, placement, _, _, _, exit, _ =>
    .load (fun state => (state.1, none))
      (DFVSGames.Reduction.MachineTransfer.exitAt (placement (.inl 0)) exit)
  | width + 1, placement, coefficient, offsets, labels, exit, label =>
    match label with
    | .inl inner => MachineAffineLookup.instruction (placement (.inr (.inl 0)))
        (placement ∘ lookupRole width) coefficient (offsets 0)
        (fun l => labels (.inl l)) (some (labels (.inr (entry width)))) inner
    | .inr inner => instruction width (placement ∘ shift width) coefficient
        (fun i => offsets i.succ) (fun l => labels (.inr l)) exit inner

theorem gatherTrace (values : List Nat) (coefficient width : Nat)
    (placement : Tape width → K) (distinct : Function.Injective placement)
    (indices offsets fields : Fin width → Nat)
    (selected : ∀ i, values[coefficient * indices i + offsets i]? = some (fields i))
    (labels : Label width → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool))
    (atLabels : ∀ l, program (labels l) = instruction width placement coefficient offsets labels exit l)
    (base : K → List Bool) (suffixes : Fin width → List Bool)
    (tableWord : base (placement (.inl 0)) = encodeWords values)
    (scratchEmpty : base (placement (.inl 3)) = [])
    (sourceWords : ∀ i, base (placement (.inr (.inl i))) = encodeWord (indices i) ++ suffixes i)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[steps values coefficient width indices offsets]
      (some ⟨some (labels (entry width)), (ambient, register), base⟩) =
      some ⟨exit, (ambient, none),
        finalTapes values coefficient width placement indices offsets fields base⟩ := by
  induction width generalizing base register with
  | zero =>
    change some (TM2.stepAux (program (labels (entry 0))) _ _) = _
    rw [atLabels]
    cases exit <;> simp [instruction, TM2.stepAux, finalTapes,
      DFVSGames.Reduction.MachineTransfer.exitAt]
  | succ width ih =>
    have hd (a b : Tape (width + 1)) (hne : a ≠ b) : placement a ≠ placement b :=
      fun h => hne (distinct h)
    have outside : ∀ i : Fin 5,
        placement (.inr (.inl 0)) ≠ (placement ∘ lookupRole width) i := by
      intro i
      apply hd
      fin_cases i <;> simp [lookupRole]
    have first := MachineAffineLookup.affineLookupTrace (placement (.inr (.inl 0)))
      (placement ∘ lookupRole width) (distinct.comp (lookupRole_injective width)) outside
      coefficient (offsets 0) (fun l => labels (.inl l))
      (some (labels (.inr (entry width)))) program (fun l => atLabels (.inl l))
      base values tableWord scratchEmpty (indices 0) (suffixes 0) (sourceWords 0)
      (fields 0) (selected 0) ambient register
    let mid := MachineAffineLookup.finalTapes (placement ∘ lookupRole width) base values
      (coefficient * indices 0 + offsets 0) (fields 0)
    have frame (k : Tape (width + 1)) (h1 : k ≠ .inl 1) (h2 : k ≠ .inl 2)
        (h3 : k ≠ .inr (.inr 0)) : mid (placement k) = base (placement k) :=
      MachineAffineLookup.finalTapes_other _ _ _ _ _ _ (hd _ _ h1) (hd _ _ h2) (hd _ _ h3)
    have middleTable : mid (placement (.inl 0)) = encodeWords values := by
      rw [frame (.inl 0) (by simp) (by simp) (by simp)]
      exact tableWord
    have middleScratch : mid (placement (.inl 3)) = [] := by
      rw [frame (.inl 3) (by simp) (by simp) (by simp)]
      exact scratchEmpty
    have middleSources (i : Fin width) : mid (placement (.inr (.inl i.succ))) =
        encodeWord (indices i.succ) ++ suffixes i.succ := by
      rw [frame (.inr (.inl i.succ)) (by simp) (by simp) (by simp)]
      exact sourceWords i.succ
    have rest := ih (placement ∘ shift width) (distinct.comp (shift_injective width))
      (fun i => indices i.succ) (fun i => offsets i.succ) (fun i => fields i.succ)
      (fun i => selected i.succ) (fun l => labels (.inr l))
      (fun l => atLabels (.inr l)) mid (fun i => suffixes i.succ)
      middleTable middleScratch middleSources none
    simp only [entry]
    rw [steps, Nat.add_comm, Function.iterate_add_apply, first]
    exact rest

end DFVSGames.Explicit.MachineProductGather


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineProductField
attribute [-instance] _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Explicit.MachineProductField

open Turing
open DFVSGames.Foundations.Complexity
open MachineComposition
open DFVSGames.Reduction.MachineTransfer

variable {K Λ σ : Type} [DecidableEq K] {width : Nat}

abbrev Label (slots : Layout width ↪ K) :=
  MachineProductGather.Label width ⊕
    (MachineHorner.Label width ⊕ (Unit ⊕ MachineDrainMany.Label (clearTapes slots)))

def entry (slots : Layout width ↪ K) : Label slots :=
  .inl (MachineProductGather.entry width)

def instruction (slots : Layout width ↪ K) (coefficient : Nat) (offsets : Fin width → Nat)
    (labels : Label slots → Λ) (exit : Option Λ) :
    Label slots → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ)
  | .inl l => MachineProductGather.instruction width (gatherSlots slots) coefficient offsets
      (fun x => labels (.inl x)) (some (labels (.inr (.inl .start)))) l
  | .inr (.inl l) => MachineHorner.statement (hornerSlots slots)
      (fun x => labels (.inr (.inl x))) (some (labels (.inr (.inr (.inl ()))))) l
  | .inr (.inr (.inl _)) => loopAt (slots (.inr 5)) (slots (.inr 6)) id false
      (labels (.inr (.inr (.inl ()))))
      (MachineDrainMany.entry (clearTapes slots) (fun x => labels (.inr (.inr (.inr x)))) exit)
  | .inr (.inr (.inr l)) => MachineDrainMany.instruction (clearTapes slots)
      (fun x => labels (.inr (.inr (.inr x)))) exit l

theorem fieldTrace (slots : Layout width ↪ K) (values : List Nat) (coefficient : Nat)
    (indices offsets fields : Fin width → Nat)
    (selected : ∀ i, values[coefficient * indices i + offsets i]? = some (fields i))
    (labels : Label slots → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ l, program (labels l) = instruction slots coefficient offsets labels exit l)
    (base : K → List Bool) (suffixes : Fin width → List Bool) (ready : Ready slots base)
    (tableWord : base (slots (.inl (.inl 0))) = encodeWords values)
    (sourceWords : ∀ i, base (slots (.inl (.inr (.inl i)))) =
      encodeWord (indices i) ++ suffixes i)
    (radix : Nat) (digits : Nat → Nat)
    (radixWord : base (slots (.inr 0)) = encodeWord radix)
    (digitWords : ∀ i : Fin width, digits i.val = fields i.rev)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[steps slots values coefficient indices offsets fields base radix digits]
      (some ⟨some (labels (entry slots)), ((ambient, ()), register), base⟩) =
      some ⟨exit, ((ambient, ()), none), finalTapes slots values coefficient indices offsets fields
        base (MachineHorner.value radix digits width)⟩ := by
  let middle := gathered slots values coefficient indices offsets fields base
  have gather := MachineProductGather.gatherTrace values coefficient width (gatherSlots slots)
    (gatherSlots slots).injective indices offsets fields selected (fun x => labels (.inl x))
    (some (labels (.inr (.inl .start)))) program (fun x => atLabels (.inl x))
    base suffixes tableWord ready.gatherScratch sourceWords (ambient, ()) register
  have preserved (i : Fin 7) : middle (slots (.inr i)) = base (slots (.inr i)) :=
    gathered_extra slots values coefficient indices offsets fields base i
  have middleRadix : middle (hornerSlots slots (.inl 0)) = encodeWord radix := by
    rw [show hornerSlots slots (.inl 0) = slots (.inr 0) from rfl, preserved]
    exact radixWord
  have middleDigits (i : Fin width) :
      middle (hornerSlots slots (.inr i)) = encodeWord (digits i.val) := by
    rw [show hornerSlots slots (.inr i) =
      gatherSlots slots (.inr (.inr i.rev)) from rfl]
    dsimp only [middle, gathered]
    rw [MachineProductGather.finalTapes_field values coefficient width (gatherSlots slots)
      (gatherSlots slots).injective indices offsets fields base i.rev]
    rw [show base (gatherSlots slots (.inr (.inr i.rev))) = [] from ready.fields i.rev,
      List.append_nil, digitWords i]
  have clean : MachineHorner.Clean (hornerSlots slots) middle := by
    constructor
    · change middle (slots (.inr 1)) = []; rw [preserved]; exact ready.accA
    · change middle (slots (.inr 2)) = []; rw [preserved]; exact ready.accB
    · change middle (slots (.inr 3)) = []; rw [preserved]; exact ready.counter
    · change middle (slots (.inr 4)) = []; rw [preserved]; exact ready.hornerScratch
  have horner := MachineHorner.hornerTrace (hornerSlots slots)
    (fun x => labels (.inr (.inl x))) (some (labels (.inr (.inr (.inl ())))))
    program (fun x => atLabels (.inr (.inl x))) middle radix digits middleRadix
    middleDigits clean ambient none
  let value := MachineHorner.value radix digits width
  let after := evaluated slots values coefficient indices offsets fields base value
  have outputWord : after (slots (.inr 5)) = encodeWord value := by
    change MachineHorner.resultTapes (hornerSlots slots) middle value
      (hornerSlots slots (.inl 3)) = _
    rw [MachineHorner.resultTapes_output]
    rw [show hornerSlots slots (.inl 3) = slots (.inr 5) from rfl,
      preserved, ready.output, List.append_nil]
  have accWord : after (slots (.inr 6)) = base (slots (.inr 6)) := by
    change MachineHorner.resultTapes (hornerSlots slots) middle value (slots (.inr 6)) = _
    rw [MachineHorner.resultTapes_other _ _ _ _ (slots.injective.ne (by simp [hornerRole])), preserved]
  have emit := transferAt_fromTapes (Γ := fun _ : K => Bool)
    (slots (.inr 5)) (slots (.inr 6)) (slots.injective.ne (by simp [])) id false
    (labels (.inr (.inr (.inl ()))))
    (MachineDrainMany.entry (clearTapes slots) (fun x => labels (.inr (.inr (.inr x)))) exit)
    program (atLabels (.inr (.inr (.inl ())))) after (ambient, ()) none
  rw [outputWord, accWord, List.map_id] at emit
  simp only [encodeWord_length] at emit
  have drain := MachineDrainMany.trace (clearTapes slots)
    (fun x => labels (.inr (.inr (.inr x)))) exit program
    (fun x => atLabels (.inr (.inr (.inr x))))
    (emitted slots values coefficient indices offsets fields base value) (ambient, ()) none
  rw [MachineDrainMany.finalRegister_none] at drain
  have emit' : (advance (TM2.step program))^[value + 2]
      (some ⟨some (labels (.inr (.inr (.inl ())))), ((ambient, ()), none), after⟩) =
      some ⟨MachineDrainMany.entry (clearTapes slots) (fun x => labels (.inr (.inr (.inr x)))) exit,
        ((ambient, ()), none), emitted slots values coefficient indices offsets fields base value⟩ := emit
  have compose {a b : Nat} {x y z : Option (TM2.Cfg (fun _ : K => Bool) Λ (MachineHorner.State σ))}
      (first : (advance (TM2.step program))^[a] x = y)
      (second : (advance (TM2.step program))^[b] y = z) :
      (advance (TM2.step program))^[a + b] x = z := by
    rw [Nat.add_comm, Function.iterate_add_apply, first, second]
  have gh := compose gather horner
  have ghe := compose gh emit'
  have whole := compose ghe drain
  simpa only [steps, value, entry, finalTapes] using whole

end DFVSGames.Explicit.MachineProductField


namespace DFVSGames.Explicit.MachineProductRow

open Turing
open DFVSGames.Foundations.Complexity
open MachineComposition

variable {K Λ σ : Type} [DecidableEq K] {width : Nat}

abbrev LocalLabel (slots : Layout width ↪ K) (command : Command width) :=
  MachineProductField.Label (fieldSlots slots command.1)

abbrev Label (slots : Layout width ↪ K) (commands : List (Command width)) :=
  MachineFiniteSequence.Label (LocalLabel slots) commands

def localMain (slots : Layout width ↪ K) (command : Command width) : LocalLabel slots command :=
  MachineProductField.entry (fieldSlots slots command.1)

def localInstruction (slots : Layout width ↪ K) (coefficient : Nat) (command : Command width)
    (labels : LocalLabel slots command → Λ) (exit : Option Λ) :
    LocalLabel slots command → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ) :=
  MachineProductField.instruction (fieldSlots slots command.1) coefficient command.2 labels exit

def entry (slots : Layout width ↪ K) (commands : List (Command width))
    (labels : Label slots commands → Λ) (exit : Option Λ) : Option Λ :=
  MachineFiniteSequence.entry (LocalLabel slots) (localMain slots) commands labels exit

def instruction (slots : Layout width ↪ K) (coefficient : Nat) (commands : List (Command width))
    (labels : Label slots commands → Λ) (exit : Option Λ) :
    Label slots commands → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ) :=
  MachineFiniteSequence.instruction (LocalLabel slots) (localMain slots)
    (localInstruction slots coefficient) commands labels exit

theorem rowTrace (slots : Layout width ↪ K) (table : List Nat) (coefficient : Nat)
    (indices : Fin width → Nat) (radices : Bool → Nat) (commands : List (Command width))
    (fields : Command width → Fin width → Nat) (digits : Command width → Nat → Nat)
    (selected : ∀ command ∈ commands, ∀ i,
      table[coefficient * indices i + command.2 i]? = some (fields command i))
    (reversed : ∀ command ∈ commands, ∀ i : Fin width,
      digits command i.val = fields command i.rev)
    (labels : Label slots commands → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ l, program (labels l) = instruction slots coefficient commands labels exit l)
    (base : K → List Bool) (ready : Ready slots table indices radices base) (ambient : σ) :
    let values := fun c : Command width => MachineHorner.value (radices c.1) (digits c) width
    let cost := fun (c : Command width) (tapes : K → List Bool) =>
      MachineProductField.steps (fieldSlots slots c.1) table coefficient indices c.2 (fields c)
        tapes (radices c.1) (digits c)
    (advance (TM2.step program))^[MachineFiniteSequence.steps (result slots values) cost commands base]
      (some ⟨entry slots commands labels exit, ((ambient, ()), none), base⟩) =
      some ⟨exit, ((ambient, ()), none),
        Function.update base (outputTape slots)
          ((rowBits values commands).reverse ++ base (outputTape slots))⟩ := by
  dsimp only
  let values := fun c : Command width => MachineHorner.value (radices c.1) (digits c) width
  let cost := fun (c : Command width) (tapes : K → List Bool) =>
    MachineProductField.steps (fieldSlots slots c.1) table coefficient indices c.2 (fields c)
      tapes (radices c.1) (digits c)
  have run := MachineFiniteSequence.trace (LocalLabel slots) (localMain slots)
    (localInstruction slots coefficient) (result slots values) cost program
    (Ready slots table indices radices) (fun _ => ((ambient, ()), none)) id commands
    (by intro c hc tapes ht; exact ht.appendField slots table indices radices tapes (values c))
    (by
      intro c hc fieldLabels fieldExit atField tapes ht
      have h := MachineProductField.fieldTrace (fieldSlots slots c.1) table coefficient
        indices c.2 (fields c) (selected c hc) fieldLabels fieldExit program atField tapes
        (fun _ => []) (ht.work c.1) ht.tableWord
        (fun i => by simpa [fieldSlots, fieldRole] using ht.sourceWords i) (radices c.1) (digits c)
        (ht.radixWords c.1) (reversed c hc) ambient none
      rw [MachineProductField.finalTapes_eq _ _ _ _ _ _ _ (ht.work c.1)] at h
      exact h)
    labels exit atLabels base ready
  rw [resultOf_eq] at run
  exact run

end DFVSGames.Explicit.MachineProductRow


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineProductProgram
attribute [-instance] _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Explicit.MachineProductProgram

open Turing
open DFVSGames.Foundations
open Complexity Hastad
open DFVSGames.Reduction.MachineTransfer

noncomputable section

inductive Label (q t : Nat)
  | headerStart (i : Fin 3)
  | headerRead (i : Fin 3)
  | seedStart
  | seed (inner : MachineProductSeed.Label (seedCommands t))
  | power (edgeCount : Bool) (inner : MachineProductPower.Label t)
  | alphabetHeader
  | initialize_ (inner : MachineOdometerInit.Label t)
  | row (inner : MachineProductRow.Label (rowSlots t) (ProductMachineSemantics.commands q t))
  | check (i : Fin t)
  | reset (i : Fin t)
  | finishStart
  | finish (inner : SourceRuntimeFinish.Label (clearKeys t))
  deriving DecidableEq, Fintype

def rowMain (q t : Nat) : Label q t :=
  .row (.inl (MachineProductRow.localMain (rowSlots t) (ProductMachineSemantics.sourceCommand t)))

def nextCheck (q t i : Nat) : Label q t := if h : i < t then .check ⟨i, h⟩ else .finishStart

def resetAt (q t i : Nat) : Label q t := if h : i < t then .reset ⟨i, h⟩ else .finishStart

def headerNext (q t : Nat) (i : Fin 3) : Label q t :=
  if h : i.val + 1 < 3 then .headerStart ⟨i.val + 1, h⟩ else .seedStart

end

end DFVSGames.Explicit.MachineProductProgram


namespace DFVSGames.Explicit.MachineProductHeaders

open Turing
open DFVSGames.Foundations Target Complexity Hastad
open MachineProductProgram

noncomputable section

def powerExit (q t : Nat) (edgeCount : Bool) : Label q t :=
  if edgeCount then MachineOdometerInit.labelAt Label.initialize_ 0 else .alphabetHeader

end
end DFVSGames.Explicit.MachineProductHeaders


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineProductFinish
attribute [-instance] _root_.OAI.DFVSGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.DFVSGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.DFVSGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DFVSGames.Quadratic.blockOrientationFintype _root_.OAI.DFVSGames.Quadratic.fieldLineFintype _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype _root_.OAI.DFVSGames.Soundness.ConditionalIncidences.zeroBits _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Explicit.MachineProductFinish

open Turing
open DFVSGames.Foundations
open Complexity Hastad
open MachineComposition
open MachineProductProgram

variable {q t : Nat}

noncomputable section

def afterRows (H : Target.Instance q) (t : Nat) :
    TM2.Cfg (fun _ : Tape t => Bool) (Label q t) State :=
  SourceOdometerSchedule.finalConfiguration (nextCheck q t t) ((), ())
    (Sum.inl (6 : Fin 10)) (MachineProductHeaders.baseTapes H t) (MachineProductLoop.rowBits (t := t) H)

theorem afterRows_output (H : Target.Instance q) (t : Nat) :
    (afterRows H t).stk (output t) = [] := by
  simp [afterRows, SourceOdometerSchedule.finalConfiguration, SourceOdometerSchedule.configuration,
    SourceOdometerSchedule.setDigits, SourceOdometerSchedule.setAcc, output, auxiliary,
    MachineProductHeaders.baseTapes, MachineProductHeaders.frame]

theorem afterRows_accumulator (H : Target.Instance q)
    (presentation : MachineOutputContract.SimpleBipartite H) (t : Nat) (ht : 0 < t) :
    ((afterRows H t).stk (accumulator t)).reverse =
      gameBits (ProductPaddedOutput.output H presentation t ht) := by
  change ((SourceOdometerSchedule.allBits (MachineProductLoop.rowBits (t := t) H)).reverse ++
    MachineProductHeaders.baseTapes H t (accumulator t)).reverse = _
  rw [MachineProductHeaders.baseTapes, MachineProductHeaders.frame_accumulator,
    List.reverse_append, List.reverse_reverse, List.reverse_reverse]
  rw [SourceOdometerSchedule.allBits, allRows_eq]
  exact ProductMachineSemantics.gameBits_eq H presentation t ht

end

end DFVSGames.Explicit.MachineProductFinish


namespace DFVSGames.Repetition

open scoped BigOperators
open Foundations.Games

noncomputable section

variable {V A Ω E : Type*} [Fintype V] [Fintype Ω] [Fintype E]

theorem pairEnergy_le_padded [DecidableEq V] (ν : FiniteDistribution E)
    (left right : E → V) (R : E → A → A → Bool)
    (a : V → Ω → A) (f : V → Ω → ℝ)
    (hf : ∀ v ω, 0 ≤ f v ω) (fallback : A) :
    pairEnergy ν left right R a f ≤
      pairEnergy ν left right R (paddedLabel a fallback) (paddedAmplitude f) := by
  unfold pairEnergy FiniteDistribution.expectation
  apply Finset.sum_le_sum
  intro e _
  apply mul_le_mul_of_nonneg_left _ (ν.nonnegative e)
  dsimp only
  rw [Fintype.sum_sum_type]
  simp only [paddedLabel, paddedAmplitude]
  have hnonneg : 0 ≤ ∑ w : V,
      if R e fallback fallback then
        (if left e = w then Real.sqrt (1 - rowSquareMass f (left e)) else 0) *
          (if right e = w then Real.sqrt (1 - rowSquareMass f (right e)) else 0)
      else 0 := by
    apply Finset.sum_nonneg
    intro w _
    split
    · exact mul_nonneg (paddedAmplitude_nonnegative f hf (left e) (Sum.inr w))
        (paddedAmplitude_nonnegative f hf (right e) (Sum.inr w))
    · exact le_rfl
  exact le_add_of_nonneg_right hnonneg

end
end DFVSGames.Repetition


namespace DFVSGames.Repetition

open scoped BigOperators
open Foundations.Games

noncomputable section

variable {V A Ω E : Type*} [Fintype V] [Fintype Ω] [Fintype E]

omit [Fintype V] in
theorem pairGatedCorrelation_eq_energy (ν : FiniteDistribution E) (left right : E → V)
    (R : E → A → A → Bool) (a : V → Ω → A) (f : V → Ω → ℝ) :
    Analytic.gatedCorrelation (fun p : E × Ω => ν.weight p.1)
      (fun p => f (left p.1) p.2) (fun p => f (right p.1) p.2)
      (fun p => R p.1 (a (left p.1) p.2) (a (right p.1) p.2)) =
      pairEnergy ν left right R a f := by
  simp only [Analytic.gatedCorrelation, pairEnergy, FiniteDistribution.expectation,
    Fintype.sum_prod_type, Finset.mul_sum, mul_ite, mul_zero, mul_assoc]

omit [Fintype V] in
theorem pairEnergy_le_one_of_unit_rows (ν : FiniteDistribution E) (left right : E → V)
    (R : E → A → A → Bool) (a : V → Ω → A) (f : V → Ω → ℝ)
    (hrow : ∀ v, rowSquareMass f v = 1) : pairEnergy ν left right R a f ≤ 1 := by
  have h := Analytic.gatedCorrelation_le_mass (fun p : E × Ω => ν.weight p.1)
    (fun p => f (left p.1) p.2) (fun p => f (right p.1) p.2)
    (fun p => R p.1 (a (left p.1) p.2) (a (right p.1) p.2))
    (fun p => ν.nonnegative p.1)
  rw [pairGatedCorrelation_eq_energy, pairQuadraticMass_eq_one ν left right f hrow] at h
  exact h

omit [Fintype V] in

theorem pairOverlap_ge_energy (ν : FiniteDistribution E) (left right : E → V)
    (R : E → A → A → Bool) (a : V → Ω → A) (f : V → Ω → ℝ)
    (hf : ∀ v ω, 0 ≤ f v ω) (hrow : ∀ v, rowSquareMass f v = 1) :
    1 - Real.sqrt (2 * (1 - pairEnergy ν left right R a f)) ≤
      pairOverlap ν left right R a f := by
  have h := Analytic.gatedMinimum_unit_mass (fun p : E × Ω => ν.weight p.1)
    (fun p => f (left p.1) p.2) (fun p => f (right p.1) p.2)
    (fun p => R p.1 (a (left p.1) p.2) (a (right p.1) p.2))
    (fun p => ν.nonnegative p.1) (fun p => hf (left p.1) p.2)
    (fun p => hf (right p.1) p.2) (pairQuadraticMass_eq_one ν left right f hrow)
  rw [pairGatedCorrelation_eq_energy, pairGatedMinimum_eq_overlap] at h
  exact h

end
end DFVSGames.Repetition


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_SharedSampling
attribute [-instance] _root_.OAI.DFVSGames.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.DFVSGames.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.DFVSGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.DFVSGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.DFVSGames.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.DFVSGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DFVSGames.Quadratic.blockOrientationFintype _root_.OAI.DFVSGames.Quadratic.fieldLineFintype _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype _root_.OAI.DFVSGames.Soundness.ConditionalIncidences.zeroBits _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Repetition

open scoped BigOperators
open Foundations.Games

noncomputable section

variable {V E A Ω : Type*} [Fintype V] [Fintype E] [Fintype A] [Fintype Ω]
  [Nonempty V] [Nonempty A] [Nonempty Ω]

theorem exists_labeling_high_value (ν : FiniteDistribution E)
    (left right : E → V) (R : E → A → A → Bool)
    (a : V → Ω → A) (f : V → Ω → ℝ)
    (hf : ∀ v ω, 0 ≤ f v ω) (hrow : ∀ v, rowSquareMass f v = 1) :
    ∃ labels : V → A,
      1 - 2 * Real.sqrt (2 * (1 - pairEnergy ν left right R a f)) ≤
        partialLabelScore ν left right R labels := by
  obtain ⟨labels, hlabels⟩ := exists_labeling_ge_partial
    (thresholdDistribution f) ν (thresholdAccept f) (thresholdLabel f a)
    left right R (thresholdRate Ω) thresholdRate_positive
    (threshold_acceptance_mass f hrow)
  rw [threshold_average_good_mass ν left right R a f hrow,
    mul_div_cancel_left₀ _ (ne_of_gt (thresholdRate_positive (Ω := Ω)))] at hlabels
  have hoverlap := pairOverlap_ge_energy ν left right R a f hf hrow
  refine ⟨labels, ?_⟩
  linarith

omit [Nonempty Ω] in

theorem exists_labeling_high_value_of_rows_le_one (ν : FiniteDistribution E)
    (left right : E → V) (R : E → A → A → Bool)
    (a : V → Ω → A) (f : V → Ω → ℝ)
    (hf : ∀ v ω, 0 ≤ f v ω) (hrow : ∀ v, rowSquareMass f v ≤ 1) :
    ∃ labels : V → A,
      1 - 2 * Real.sqrt (2 * (1 - pairEnergy ν left right R a f)) ≤
        partialLabelScore ν left right R labels := by
  classical
  let fallback : A := Classical.choice inferInstance
  obtain ⟨labels, hlabels⟩ := exists_labeling_high_value ν left right R
    (paddedLabel a fallback) (paddedAmplitude f)
    (paddedAmplitude_nonnegative f hf) (paddedAmplitude_row f hrow)
  have henergy := pairEnergy_le_padded ν left right R a f hf fallback
  have hsqrt := Real.sqrt_le_sqrt (show
      2 * (1 - pairEnergy ν left right R (paddedLabel a fallback) (paddedAmplitude f)) ≤
        2 * (1 - pairEnergy ν left right R a f) by linarith)
  exact ⟨labels, (by linarith :
    1 - 2 * Real.sqrt (2 * (1 - pairEnergy ν left right R a f)) ≤
      1 - 2 * Real.sqrt
        (2 * (1 - pairEnergy ν left right R (paddedLabel a fallback)
          (paddedAmplitude f)))).trans hlabels⟩

omit [Nonempty Ω] in

theorem pairEnergy_le_of_labeling_gap (ν : FiniteDistribution E)
    (left right : E → V) (R : E → A → A → Bool)
    (a : V → Ω → A) (f : V → Ω → ℝ)
    (hf : ∀ v ω, 0 ≤ f v ω) (hrow : ∀ v, rowSquareMass f v ≤ 1)
    {g : ℝ} (hg : 0 < g)
    (hgap : ∀ labels : V → A, partialLabelScore ν left right R labels ≤ 1 - g) :
    pairEnergy ν left right R a f ≤ 1 - g ^ 2 / 8 := by
  obtain ⟨labels, hlabels⟩ := exists_labeling_high_value_of_rows_le_one
    ν left right R a f hf hrow
  have hbound := hlabels.trans (hgap labels)
  have he : pairEnergy ν left right R a f ≤ 1 := by
    by_contra h
    have hneg : 2 * (1 - pairEnergy ν left right R a f) ≤ 0 := by linarith
    rw [Real.sqrt_eq_zero_of_nonpos hneg] at hbound
    linarith
  have hs := Real.sq_sqrt (show 0 ≤ 2 * (1 - pairEnergy ν left right R a f) by linarith)
  have hgs : g ≤ 2 * Real.sqrt (2 * (1 - pairEnergy ν left right R a f)) := by
    linarith
  have hsq := mul_self_le_mul_self hg.le hgs
  nlinarith

end
end DFVSGames.Repetition


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_Collision
attribute [-instance] _root_.OAI.DFVSGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.DFVSGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.DFVSGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DFVSGames.Quadratic.blockOrientationFintype _root_.OAI.DFVSGames.Quadratic.fieldLineFintype _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype _root_.OAI.DFVSGames.Soundness.ConditionalIncidences.zeroBits _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Repetition.ProjectionKernel

open Foundations.Games
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

variable {Q₁ Q₂ A₁ A₂ Ω : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂] [Fintype Ω]

theorem vectorEnergy_singleLabelVector (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (a : Q₁ → Ω → A₁) (f : Q₁ → Ω → ℝ) :
    K.vectorEnergy (singleLabelVector a f) =
      pairEnergy K.symmetricDistribution symmetricLeft symmetricRight K.symmetricAccept a f := by
  classical
  unfold vectorEnergy singleLabelVector
  simp_rw [K.energy_single_label]
  unfold pairEnergy FiniteDistribution.expectation
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [Finset.mul_sum]

end
end DFVSGames.Repetition.ProjectionKernel


namespace DFVSGames.Repetition.ProjectionKernel

open scoped BigOperators
open Foundations.Games

noncomputable section

variable {Q₁ Q₂ A₁ A₂ Ω : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂] [Fintype Ω]

theorem vectorEnergy_le_gap_rate [Nonempty A₁] [Nonempty A₂]
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂) (f : Ω → Q₁ → A₁ → ℝ)
    (hf : ∀ ω x a, 0 ≤ f ω x a) (hmass : ∀ x, vectorMass f x ≤ 1)
    {g : ℝ} (hg0 : 0 ≤ g) (hg1 : g ≤ 1)
    (hvalue : K.toGame.value ≤ 1 - g) :
    K.vectorEnergy f ≤ 1 - g ^ 2 / 8 := by
  classical
  let : Nonempty Q₂ := distribution_nonempty_inline_RoundingKernel K.outer
  let : Nonempty Q₁ := distribution_nonempty_inline_RoundingKernel
    (K.inner (Classical.choice (inferInstance : Nonempty Q₂)))
  rcases isEmpty_or_nonempty Ω with hΩ | hΩ
  · let : IsEmpty Ω := hΩ
    have hzero : K.vectorEnergy f = 0 := by simp [vectorEnergy]
    rw [hzero]
    have hsq : g * g ≤ (1 : ℝ) * 1 := mul_le_mul hg1 hg1 hg0 (by norm_num)
    nlinarith
  · let : Nonempty Ω := hΩ
    obtain ⟨labels, hdet⟩ := K.exists_vectorEnergy_le_singleLabelVector f hf
    have hnonneg := vectorAmplitude_nonnegative f hf
    have hrow : ∀ x, rowSquareMass (vectorAmplitude f) x ≤ 1 := by
      intro x
      rw [rowSquareMass_vectorAmplitude]
      exact hmass x
    rw [K.vectorEnergy_singleLabelVector] at hdet
    by_cases hg : g = 0
    · subst g
      simp only [zero_pow (by decide : 2 ≠ 0), zero_div, sub_zero]
      let fallback : A₁ := Classical.choice inferInstance
      have hpad := pairEnergy_le_padded K.symmetricDistribution symmetricLeft
        symmetricRight K.symmetricAccept labels (vectorAmplitude f) hnonneg fallback
      have hone := pairEnergy_le_one_of_unit_rows K.symmetricDistribution
        symmetricLeft symmetricRight K.symmetricAccept
        (paddedLabel labels fallback) (paddedAmplitude (vectorAmplitude f))
        (paddedAmplitude_row (vectorAmplitude f) hrow)
      exact hdet.trans (hpad.trans hone)
    · have hgpos : 0 < g := lt_of_le_of_ne hg0 (Ne.symm hg)
      have hscore (a : Q₁ → A₁) :
          partialLabelScore K.symmetricDistribution symmetricLeft symmetricRight
            K.symmetricAccept a ≤ 1 - g := by
        unfold partialLabelScore
        rw [K.symmetric_probability_eq_assignmentEnergy]
        exact (K.assignmentEnergy_le_collisionValue a).trans
          (K.collisionValue_le_value.trans hvalue)
      exact hdet.trans (pairEnergy_le_of_labeling_gap K.symmetricDistribution
        symmetricLeft symmetricRight K.symmetricAccept labels (vectorAmplitude f)
        hnonneg hrow hgpos hscore)

end
end DFVSGames.Repetition.ProjectionKernel


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_TensorDomination
attribute [-instance] _root_.OAI.DFVSGames.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.DFVSGames.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.DFVSGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.DFVSGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.DFVSGames.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.DFVSGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DFVSGames.Quadratic.blockOrientationFintype _root_.OAI.DFVSGames.Quadratic.fieldLineFintype _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype _root_.OAI.DFVSGames.Soundness.ConditionalIncidences.zeroBits _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Repetition


open DFVSGames.Foundations.Games
noncomputable section

namespace ProjectionKernel
variable {Q₁ Q₂ A₁ A₂ R₁ R₂ B₁ B₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [Fintype R₁] [Fintype R₂] [Fintype B₁] [Fintype B₂]
  [Nonempty A₁] [Nonempty A₂] [Nonempty B₁] [Nonempty B₂]

omit [Nonempty B₂] in
theorem collisionValue_product_le_gap_rate
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (H : ProjectionKernel R₁ R₂ B₁ B₂) {gap : ℝ}
    (hgap₀ : 0 ≤ gap) (hgap₁ : gap ≤ 1)
    (hvalue : K.toGame.value ≤ 1 - gap) :
    (K.product H).collisionValue ≤ (1 - gap ^ 2 / 8) * H.collisionValue := by
  apply ((K.product H).collisionValue_le_iff _).2
  intro labels
  rw [← vectorEnergy_tensorSlice]
  apply K.vectorEnergy_le_of_unit_bound (1 - gap ^ 2 / 8) H.collisionValue
    (fun f hf hmass => K.vectorEnergy_le_gap_rate f hf hmass hgap₀ hgap₁ hvalue)
    H.collisionValue_nonneg (H.tensorSlice labels)
    (H.tensorSlice_nonnegative labels) (H.vectorMass_tensorSlice_le labels)

theorem repetition_value_le_dsRate
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂) {gap : ℝ}
    (hgap₀ : 0 ≤ gap) (hgap₁ : gap ≤ 1)
    (hvalue : K.toGame.value ≤ 1 - gap) (n : ℕ) :
    (K.toGame.repetition n).value ≤ dsRate gap ^ n := by
  have hstep : ∀ m, (K.repetition (m + 1)).collisionValue ≤
      (1 - gap ^ 2 / 8) * (K.repetition m).collisionValue := by
    intro m
    rw [K.collisionValue_repetition_succ]
    exact K.collisionValue_product_le_gap_rate (K.repetition m) hgap₀ hgap₁ hvalue
  have h := rate_of_squared_collision_recurrence hgap₀ hgap₁
    (fun m => (K.repetition m).collisionValue)
    (fun m => (K.repetition m).toGame.value)
    K.collisionValue_repetition_zero_le_one hstep
    (fun m => (K.repetition m).value_sq_le_collisionValue) n
  simpa only [toGame_repetition] using h

end ProjectionKernel

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [Nonempty A₁] [Nonempty A₂]

theorem projection_repetition_value
    (G : Game Q₁ Q₂ A₁ A₂) (hG : IsProjection G) (n : ℕ)
    {gap : ℝ} (hgap₀ : 0 < gap) (hgap₁ : gap < 1)
    (hvalue : G.value ≤ 1 - gap) :
    (G.repetition n).value ≤ (1 - gap ^ 2 / 16) ^ n := by
  have h := (kernelOfGame G hG).repetition_value_le_dsRate hgap₀.le hgap₁.le
    (by simpa only [kernelOfGame_value] using hvalue) n
  simpa only [toGame_kernelOfGame, dsRate] using h

theorem final_repetition_value
    (G : Game Q₁ Q₂ A₁ A₂) (hG : IsProjection G) (n : ℕ)
    (hvalue : G.value ≤ 1 - (1 : ℝ) / 800) :
    (G.repetition n).value ≤ (1 - (1 : ℝ) / 10240000) ^ n := by
  have h := projection_repetition_value G hG n
    (gap := (1 : ℝ) / 800) (by norm_num) (by norm_num) hvalue
  norm_num at h ⊢
  exact h

end
end DFVSGames.Repetition

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_FinishReduction
attribute [-instance] _root_.OAI.DFVSGames.Clean.AdviceImageLaw.kernelFintype _root_.OAI.DFVSGames.Clean.AdviceImageLaw.rangeFintype _root_.OAI.DFVSGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.DFVSGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.DFVSGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DFVSGames.Quadratic.blockOrientationFintype _root_.OAI.DFVSGames.Quadratic.fieldLineFintype _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

namespace DFVSGames.Explicit.ProductPaddedOutput

open DFVSGames.Foundations
open Target
open MachineOutputContract

noncomputable section

variable {q : ℕ} [Nonempty (Fin q)]

theorem output_soundness_rate (H : Instance q) (presentation : SimpleBipartite H)
    (t : ℕ) (ht : 0 < t)
    (hvalue : Integration.InstanceValue.value H ≤ 1 - (1 : ℝ) / 800) :
    Integration.InstanceValue.value (output H presentation t ht) ≤
      (1 - (1 : ℝ) / 10240000) ^ t := by
  let : Nonempty (Fin H.constraints.length) := ⟨⟨0, H.constraintCount_positive⟩⟩
  rw [output_value_eq_repetition]
  apply DFVSGames.Repetition.final_repetition_value
    presentation.toBipartiteGame.toGame presentation.toBipartiteGame.toGame_isProjection
  simpa only [BipartiteGame.toGame_value, presentation.toBipartiteGame_value] using hvalue

theorem output_soundness (H : Instance q) (presentation : SimpleBipartite H)
    (t : ℕ) (ht : 0 < t) {δ : ℝ}
    (hcount : (1 - (1 : ℝ) / 10240000) ^ t ≤ δ)
    (hvalue : Integration.InstanceValue.value H ≤ 1 - (1 : ℝ) / 800) :
    Integration.InstanceValue.value (output H presentation t ht) ≤ δ :=
  (output_soundness_rate H presentation t ht hvalue).trans hcount

end
end DFVSGames.Explicit.ProductPaddedOutput
end


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_PoweringReach
attribute [-instance] _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Foundations.PCP.GenericGraphTables

open DFVSGames.Foundations.Complexity

variable {q : Nat}

theorem darts_le_tableBits_length (table : (Table q)) :
    table.darts ≤ (tableBits table).length := by
  simp only [tableBits, tableWords, encodeWords_append, List.length_append,
    encodeWords, encodeWord_length, List.length_nil]
  omega

end DFVSGames.Foundations.PCP.GenericGraphTables

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_VerifierCNF
attribute [-instance] _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Foundations.PCP.FinalBooleanVerifier

open Target

variable {V E : Type*} {n m : Nat}

theorem query_tail (G : ConstraintGraph V E Label) (vertices : V ≃ Fin n)
    (edges : E ≃ Fin m) (e : Fin m) (j : Fin 6) :
    (verifier G vertices edges).query e (Fin.castAdd 6 j) =
      bitIndex vertices (G.tail (edges.symm e)) j := by
  simp only [verifier, Fin.addCases_left]

theorem query_head (G : ConstraintGraph V E Label) (vertices : V ≃ Fin n)
    (edges : E ≃ Fin m) (e : Fin m) (j : Fin 6) :
    (verifier G vertices edges).query e (Fin.natAdd 6 j) =
      bitIndex vertices (G.head (edges.symm e)) j := by
  simp only [verifier, Fin.addCases_right]

end DFVSGames.Foundations.PCP.FinalBooleanVerifier

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

abbrev Input := {table : GraphTables.Table // 0 < table.darts}

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

namespace DFVSGames.Foundations.Complexity.FinalCNFPattern

open PCP
open scoped BigOperators

abbrev tableVerifier (table : GraphTables.Table) : VerifierToCNF.FiniteVerifier 12 :=
  FinalBooleanVerifier.verifier (tableGraph table) (Equiv.refl _) (Equiv.refl _)

theorem pattern_lookup_eq_verifier_accepts (table : GraphTables.Table)
    (e : Fin table.darts) (p : VerifierToCNF.PatternIndex 12) :
    table.rows[e].relation[patternRelationIndex p] =
      (tableVerifier table).accepts e (VerifierToCNF.patternAt 12 p) := rfl

end DFVSGames.Foundations.Complexity.FinalCNFPattern

namespace DFVSGames.Foundations.PCP.GraphTableComplexity

open DFVSGames.Foundations.Complexity
open Polynomial

theorem size_add_two_le_bits (table : GraphTables.Table) :
    table.vertices + table.darts + 2 ≤ (GraphTables.tableBits table).length := by
  simp only [GraphTables.tableBits, GraphTables.tableWords,
    encodeWords_append, List.length_append, encodeWords, encodeWord_length, List.length_nil]
  omega

end DFVSGames.Foundations.PCP.GraphTableComplexity

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_PoweringFinalConstants
attribute [-instance] _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Foundations.PCP.FinalTableFormula

open Target Complexity

theorem formulaBits_length_le_polynomial (table : GraphTables.Table) :
    (formulaBits (output table)).length ≤
      sizePolynomial.eval (GraphTables.tableBits table).length := by
  have hinput := GraphTableComplexity.size_add_two_le_bits table
  have hv : (output table).«variables» ≤ 36864 * (GraphTables.tableBits table).length := by
    rw [variable_count]
    omega
  have hc : (output table).clauses.length ≤ 40960 * (GraphTables.tableBits table).length := by
    rw [clause_count]
    omega
  have hsum : (output table).«variables» + (output table).clauses.length + 2 ≤
      77824 * (GraphTables.tableBits table).length + 2 := by omega
  have hproduct := Nat.mul_le_mul hc (Nat.mul_le_mul_left 3 (Nat.add_le_add_right hv 2))
  rw [sizePolynomial_eval]
  exact (formulaBits_length_le (output table)).trans (Nat.add_le_add hsum hproduct)

end DFVSGames.Foundations.PCP.FinalTableFormula

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

namespace DFVSGames.Foundations.PCP.AlphabetTable.Input

open DFVSGames.Foundations.Complexity

export GenericGraphTables (Label RelationTable DartRow Rows Valid Table
  relationIndex relationAt relationOf relationAt_relationOf
  reverseAt acceptsAt rowList rowList_length semantics semantics_reverse
  semantics_tail semantics_accepts ofGraph semantics_ofGraph ofEnumeratedGraph
  bitWord relationWords relationWords_length rowWords rowWords_length
  tableWords tableBits darts_le_tableBits_length)

variable {q n m : Nat}

theorem tableBits_header (table : Table q) :
    tableBits table = encodeWord table.vertices ++
      (encodeWord table.darts ++ encodeWords ((rowList table).flatMap rowWords)) := by
  simp [tableBits, tableWords, encodeWords]

end DFVSGames.Foundations.PCP.AlphabetTable.Input

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_Lookup
attribute [-instance] _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Foundations.PCP.AlphabetTable.Lookup

open Turing
open DFVSGames.Foundations.Complexity
open MachineComposition GenericGraphTables

variable {K Λ σ : Type} [DecidableEq K]

section Ambient

variable {q n m : Nat} (counter source destination : K) (labels : Label → Λ)
  (exit : Option Λ)
  (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
  (atStatement : ∀ label, P (labels label) = statement q counter source destination labels exit label)

include atStatement

theorem selectTrace (hsd : source ≠ destination) (base : K → List Bool)
    (row : DartRow q n m) (suffix : List Bool)
    (hinput : base source = rowBits row ++ suffix) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step P))^[row.tail.val + 2]
      (some ⟨some (labels .select), (ambient, register), base⟩) =
      some ⟨exit, (ambient, none), Hastad.SourceMachine.fieldTapes source destination base
        (encodeWord row.reverseIndex.val ++ (encodeWords (relationWords row.relation) ++ suffix))
        (encodeWord row.tail.val ++ base destination)⟩ := by
  let ht := Hastad.SourceMachine.fieldInTime source destination hsd
    (labels .select) (labels .copy) exit P (atStatement .select) (atStatement .copy)
    base row.tail.val
    (encodeWord row.reverseIndex.val ++ (encodeWords (relationWords row.relation) ++ suffix))
    (by simpa only [rowBits_eq, List.append_assoc] using hinput) ambient register
  have hsteps : ht.steps = row.tail.val + 2 := rfl
  have htrace := ht.evals_in_steps
  rw [hsteps] at htrace
  exact htrace

end Ambient

def headLookupCost {q : Nat} (table : Table q) (e : Fin table.darts) : Nat :=
  2 * ((tableBits table).length + 1) +
    2 * ((encodeWord (headIndex table e).val).length + 1) + tableTailCost table (headIndex table e)

end DFVSGames.Foundations.PCP.AlphabetTable.Lookup

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_CompareLoop
attribute [-instance] _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Foundations.PCP.AlphabetTable.Emitter

open Turing
open DFVSGames.Foundations.Complexity
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)

variable {K Λ σ : Type} {h bound : Nat} [DecidableEq K]

theorem commandTrace (sources : Fin h → K) (scratch output : K)
    (sourceScratch : ∀ i, sources i ≠ scratch)
    (sourceOutput : ∀ i, sources i ≠ output) (scratchOutput : scratch ≠ output)
    (labels : Phase bound → Λ) (next : Λ) (command : Command h σ bound)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ phase,
      program (labels phase) = commandStatement sources scratch output labels next command phase)
    (values : Fin h → Nat) (base : K → List Bool)
    (operands : ∀ i, base (sources i) = encodeWord (values i))
    (scratchEmpty : base scratch = []) (ambient : σ) :
    (MachineComposition.advance (TM2.step program))^[commandSteps values command]
      (some ⟨some (labels .entry), ((ambient, ()), none), base⟩) =
      some ⟨some next, ((ambient, ()), none),
        Function.update base output ((commandBits values ambient command).reverse ++ base output)⟩ := by
  cases command with
  | literal word =>
    change some (TM2.stepAux (program (labels .entry)) ((ambient, ()), none) base) = _
    rw [atLabels]
    simp only [commandStatement, stepAux_pushWord, TM2.stepAux, commandBits]
  | bit value =>
    change some (TM2.stepAux (program (labels .entry)) ((ambient, ()), none) base) = _
    rw [atLabels]
    cases hb : value ambient <;>
      simp [commandStatement, TM2.stepAux, pushWord, commandBits, hb, encodeWord]
  | bounded value =>
    change (TM2.step program ⟨some (labels .entry), ((ambient, ()), none), base⟩).bind
      (TM2.step program) = _
    have first : TM2.step program ⟨some (labels .entry), ((ambient, ()), none), base⟩ =
        some ⟨some (labels (.offset (value ambient))), ((ambient, ()), none), base⟩ := by
      change some (TM2.stepAux (program (labels .entry)) _ _) = _
      rw [atLabels]
      rfl
    rw [first]
    change some (TM2.stepAux (program (labels (.offset (value ambient)))) _ _) = _
    rw [atLabels]
    simp only [commandStatement, stepAux_pushWord, TM2.stepAux, commandBits]
  | scaled source coefficient =>
    have emitAt : ∀ control symbol, program (labels (.emit symbol)) =
        MachineTransducerCopy.emitter output transition (payload coefficient)
          (labels .entry) control symbol := by
      intro control symbol
      cases control
      exact atLabels (.emit symbol)
    have run := MachineTransducerCopy.transduceCopyTrace (sources source) scratch output
      (sourceScratch source) (sourceOutput source) scratchOutput () transition (payload coefficient)
      (labels .entry) (labels .restore) (fun _ symbol => labels (.emit symbol)) (some next)
      program (atLabels .entry) emitAt (atLabels .restore) base scratchEmpty ambient () none
    rw [operands source, encodeWord_length, output_encodeWord_inline_Emitter] at run
    exact run
  | scaledIf source coefficient active =>
    have first : TM2.step program ⟨some (labels .entry), ((ambient, ()), none), base⟩ =
        some ⟨some (labels (.scanIf (active ambient))), ((ambient, ()), none), base⟩ := by
      change some (TM2.stepAux (program (labels .entry)) _ _) = _
      rw [atLabels]
      rfl
    have emitAt : ∀ control symbol, program (labels (.emitIf (active ambient) symbol)) =
        MachineTransducerCopy.emitter output transition
          (payload (if active ambient then coefficient else 0))
          (labels (.scanIf (active ambient))) control symbol := by
      intro control symbol
      cases control
      exact atLabels (.emitIf (active ambient) symbol)
    have run := MachineTransducerCopy.transduceCopyTrace (sources source) scratch output
      (sourceScratch source) (sourceOutput source) scratchOutput () transition
      (payload (if active ambient then coefficient else 0))
      (labels (.scanIf (active ambient))) (labels .restore)
      (fun _ symbol => labels (.emitIf (active ambient) symbol)) (some next)
      program (atLabels (.scanIf (active ambient))) emitAt (atLabels .restore)
      base scratchEmpty ambient () none
    rw [operands source, encodeWord_length, output_encodeWord_inline_Emitter] at run
    change (MachineComposition.advance (TM2.step program))^[
      (3 * (values source + 1) + 2) + 1] _ = _
    rw [Function.iterate_succ_apply]
    simp only [MachineComposition.advance_some]
    rw [first]
    exact run

theorem prefixTrace {count : Nat} (commands : Fin count → Command h σ bound)
    (sources : Fin h → K) (scratch output : K)
    (sourceScratch : ∀ i, sources i ≠ scratch)
    (sourceOutput : ∀ i, sources i ≠ output) (scratchOutput : scratch ≠ output)
    (labels : Label count bound → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement commands sources scratch output labels exit label)
    (values : Fin h → Nat) (base : K → List Bool)
    (operands : ∀ i, base (sources i) = encodeWord (values i))
    (scratchEmpty : base scratch = []) (ambient : σ) (r : Nat) (hr : r ≤ count) :
    (MachineComposition.advance (TM2.step p))^[prefixSteps commands values r]
      (some ⟨some (labels (labelAt count bound 0 .entry)), ((ambient, ()), none), base⟩) =
      some ⟨some (labels (labelAt count bound r .entry)), ((ambient, ()), none),
        resultTapes output base (prefixBits commands values ambient r)⟩ := by
  induction r with
  | zero => simp [prefixSteps, prefixBits, resultTapes]
  | succ r ih =>
    have hrc : r < count := by omega
    let prior := resultTapes output base (prefixBits commands values ambient r)
    have priorOperands : ∀ i, prior (sources i) = encodeWord (values i) := by
      intro i
      simpa [prior, resultTapes, sourceOutput i] using operands i
    have priorScratch : prior scratch = [] := by
      simpa [prior, resultTapes, scratchOutput] using scratchEmpty
    have commandAtLabels : ∀ phase, p (labels (labelAt count bound r phase)) =
        commandStatement sources scratch output (fun phase => labels (labelAt count bound r phase))
          (labels (labelAt count bound (r + 1) .entry)) (commandAt commands r) phase := by
      intro phase
      rw [atLabels]
      simp only [statement, labelAt, Nat.min_eq_left (Nat.le_of_lt hrc), hrc, ite_true, if_true]
    have one := commandTrace sources scratch output sourceScratch sourceOutput scratchOutput
      (fun phase => labels (labelAt count bound r phase))
      (labels (labelAt count bound (r + 1) .entry)) (commandAt commands r)
      p commandAtLabels values prior priorOperands priorScratch ambient
    rw [prefixSteps, Nat.add_comm, Function.iterate_add_apply, ih (by omega)]
    rw [one]
    congr 2
    simp [prior, prefixBits, resultTapes, List.reverse_append, List.append_assoc]

theorem planTrace {count : Nat} (commands : Fin count → Command h σ bound)
    (sources : Fin h → K) (scratch output : K)
    (sourceScratch : ∀ i, sources i ≠ scratch)
    (sourceOutput : ∀ i, sources i ≠ output) (scratchOutput : scratch ≠ output)
    (labels : Label count bound → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement commands sources scratch output labels exit label)
    (values : Fin h → Nat) (base : K → List Bool)
    (operands : ∀ i, base (sources i) = encodeWord (values i))
    (scratchEmpty : base scratch = []) (ambient : σ) :
    (MachineComposition.advance (TM2.step p))^[prefixSteps commands values count + 1]
      (some ⟨some (labels (labelAt count bound 0 .entry)), ((ambient, ()), none), base⟩) =
      some ⟨exit, ((ambient, ()), none),
        resultTapes output base (prefixBits commands values ambient count)⟩ := by
  rw [Function.iterate_succ_apply', prefixTrace commands sources scratch output sourceScratch
    sourceOutput scratchOutput labels exit p atLabels values base operands scratchEmpty ambient count
    (Nat.le_refl _)]
  change some (TM2.stepAux (p (labels (labelAt count bound count .entry))) _ _) = _
  rw [atLabels]
  cases exit <;> simp [statement, labelAt, Reduction.MachineTransfer.exitAt, TM2.stepAux]

def planInTime {count : Nat} (commands : Fin count → Command h σ bound)
    (sources : Fin h → K) (scratch output : K)
    (sourceScratch : ∀ i, sources i ≠ scratch)
    (sourceOutput : ∀ i, sources i ≠ output) (scratchOutput : scratch ≠ output)
    (labels : Label count bound → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement commands sources scratch output labels exit label)
    (values : Fin h → Nat) (base : K → List Bool)
    (operands : ∀ i, base (sources i) = encodeWord (values i))
    (scratchEmpty : base scratch = []) (ambient : σ)
    (N : Nat) (bounded : ∀ i, values i ≤ N) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels (labelAt count bound 0 .entry)), ((ambient, ()), none), base⟩
      (some ⟨exit, ((ambient, ()), none),
        resultTapes output base (prefixBits commands values ambient count)⟩)
      (count * (3 * (N + 1) + 3) + 1) where
  steps := prefixSteps commands values count + 1
  evals_in_steps := planTrace commands sources scratch output sourceScratch sourceOutput
    scratchOutput labels exit p atLabels values base operands scratchEmpty ambient
  steps_le_m := Nat.add_le_add_right (prefixSteps_le commands values N bounded count) 1

end DFVSGames.Foundations.PCP.AlphabetTable.Emitter

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

namespace DFVSGames.Foundations.Complexity.GraphCounterPrefix

open Turing PCP GraphCounterModel GraphCounterFinish

def count (table : GraphTables.Table) : Nat := (table.vertices + table.darts).log2 + 1

end DFVSGames.Foundations.Complexity.GraphCounterPrefix

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_RawInitialMachineFinish
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

namespace DFVSGames.Foundations.Complexity.FinalCNFMachine

open Turing
open PCP

section RelationReader

variable {K Λ σ : Type} {N : Nat}

def readUnarySlots (source : K) : List (Fin N) →
    TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N) →
    TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N)
  | [], next => next
  | i :: slots, next =>
      .pop source (fun state head =>
        (state.1, Function.update state.2 i (head.getD false)))
        (.branch (fun state => state.2 i)
          (.pop source (fun state _ => state) (readUnarySlots source slots next))
          (readUnarySlots source slots next))

def unaryBits (slots : List (Fin N)) (bits : Buffer N) : List Bool :=
  slots.flatMap fun i => encodeWord (GraphTables.bitWord (bits i))

end RelationReader

def readerStateEquiv (σ : Type) (N : Nat) :
    (((σ × Unit) × Option Bool) × Buffer N) ≃ (((σ × Buffer N) × Unit) × Option Bool) where
  toFun state := (((state.1.1.1, state.2), state.1.1.2), state.1.2)
  invFun state := (((state.1.1.1, state.1.2), state.2), state.1.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

section AmbientRelation

variable {K Λ σ : Type} [DecidableEq K]

abbrev State (σ : Type) := ((σ × Buffer 4096) × Unit) × Option Bool

def readRelationAt (source : K) (exit : Λ) :
    TM2.Stmt (fun _ : K => Bool) Λ (State σ) :=
  MachineControl.statement id (readerStateEquiv σ 4096)
    (readUnarySlots source (List.ofFn id) (.goto fun _ => exit))

end AmbientRelation

namespace Program

open PCP.AlphabetTable

def headerPlan : Plan :=
  Emitter.affineCommands [(0, 6), (1, 36864)] (fun _ => 0) ++
    Emitter.affineCommands [(1, 40960)] (fun _ => 0)

theorem headerPlan_length : headerPlan.length = 7 := by
  simp [headerPlan]

theorem headerPlan_bits (vertices darts tail head row : Nat) (ambient : Ambient) :
    headerPlan.flatMap (Emitter.commandBits (values vertices darts tail head row) ambient) =
      encodeWords [6 * vertices + 36864 * darts, 40960 * darts] := by
  rw [headerPlan, List.flatMap_append, Emitter.affineCommands_bits,
    Emitter.affineCommands_bits]
  simp [Emitter.affineValue, values, encodeWords]
  rfl

inductive Label (headerCount rowCount : Nat)
  | copyFirst | copySecond | startVertices | readVertices | startDarts | readDarts | seedIndex
  | header (label : Emitter.Label headerCount 36864)
  | headerClearTail | headerClearHead
  | guard | startTail | readTail | startReverse | readReverse
  | headTableFirst | headTableSecond | headIndexFirst | headIndexSecond
  | headHeaderVertices | headHeaderDarts | headLookup (label : Lookup.Label)
  | readRelation
  | row (label : Emitter.Label rowCount 36864)
  | clearTail | clearHead | clearReverse | nextRow | reverseOutput
  deriving DecidableEq, Fintype

def guard {hc rc : Nat} (again finish : Label hc rc) :
    TM2.Stmt (fun _ : Tape => Bool) (Label hc rc) (State Unit) :=
  .peek .input (fun state head => (state.1, head))
    (.branch (fun state => state.2.isSome)
      (.load (fun state => (state.1, none)) (.goto fun _ => again))
      (.load (fun state => (state.1, none)) (.goto fun _ => finish)))

def program (headerPlan rowPlan : Plan) :
    Label headerPlan.length rowPlan.length →
      TM2.Stmt (fun _ : Tape => Bool) (Label headerPlan.length rowPlan.length) (State Unit)
  | .copyFirst => Reduction.MachineTransfer.loopAt .input .scratch id false .copyFirst
      (some .copySecond)
  | .copySecond => MachineCopy.forkLoop .scratch .input .archive false .copySecond
      (some .startVertices)
  | .startVertices => Hastad.SourceMachine.fieldStart .vertices .readVertices
  | .readVertices => Hastad.SourceMachine.fieldLoop .input .vertices .readVertices (some .startDarts)
  | .startDarts => Hastad.SourceMachine.fieldStart .darts .readDarts
  | .readDarts => Hastad.SourceMachine.fieldLoop .input .darts .readDarts (some .seedIndex)
  | .seedIndex => .push .rowIndex (fun _ => false)
      (.push .tail (fun _ => false) (.push .head (fun _ => false)
        (.goto fun _ => .header (Emitter.labelAt headerPlan.length 36864 0 .entry))))
  | .header label => Emitter.statement (Emitter.listCommands headerPlan)
      source .scratch .accumulator Label.header (some .headerClearTail) label
  | .headerClearTail => MachineLookup.discard .tail .headerClearTail .headerClearHead
  | .headerClearHead => MachineLookup.discard .head .headerClearHead .guard
  | .guard => guard .startTail .reverseOutput
  | .startTail => Hastad.SourceMachine.fieldStart .tail .readTail
  | .readTail => Hastad.SourceMachine.fieldLoop .input .tail .readTail (some .startReverse)
  | .startReverse => Hastad.SourceMachine.fieldStart .reverseIndex .readReverse
  | .readReverse => Hastad.SourceMachine.fieldLoop .input .reverseIndex .readReverse
      (some .headTableFirst)
  | .headTableFirst => Reduction.MachineTransfer.loopAt .archive .scratch id false
      .headTableFirst (some .headTableSecond)
  | .headTableSecond => MachineCopy.forkLoop .scratch .archive .scanWork false
      .headTableSecond (some .headIndexFirst)
  | .headIndexFirst => Reduction.MachineTransfer.loopAt .reverseIndex .scratch id false
      .headIndexFirst (some .headIndexSecond)
  | .headIndexSecond => MachineCopy.forkLoop .scratch .reverseIndex .indexWork false
      .headIndexSecond (some .headHeaderVertices)
  | .headHeaderVertices => MachineLookup.discard .scanWork .headHeaderVertices .headHeaderDarts
  | .headHeaderDarts => MachineLookup.discard .scanWork .headHeaderDarts (.headLookup .guard)
  | .headLookup label => Lookup.statement 64 .indexWork .scanWork .head Label.headLookup
      (some .readRelation) label
  | .readRelation => readRelationAt .input
      (.row (Emitter.labelAt rowPlan.length 36864 0 .entry))
  | .row label => Emitter.statement (Emitter.listCommands rowPlan)
      source .scratch .accumulator Label.row (some .clearTail) label
  | .clearTail => MachineLookup.discard .tail .clearTail .clearHead
  | .clearHead => MachineLookup.discard .head .clearHead .clearReverse
  | .clearReverse => MachineLookup.discard .reverseIndex .clearReverse .nextRow
  | .nextRow => .push .rowIndex (fun _ => true) (.goto fun _ => .guard)
  | .reverseOutput => Reduction.MachineTransfer.loopAt .accumulator .output id false
      .reverseOutput none

def machine (headerPlan rowPlan : Plan) : FinTM2 where
  K := Tape
  k₀ := .input
  k₁ := .output
  Γ _ := Bool
  Λ := Label headerPlan.length rowPlan.length
  main := .copyFirst
  σ := State Unit
  initialState := ((((), fun _ => false), ()), none)
  m := program headerPlan rowPlan

end Program

end DFVSGames.Foundations.Complexity.FinalCNFMachine
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_FinalCNFHeader
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

namespace DFVSGames.Foundations.Complexity.FinalCNFMachine.Program

open Turing
open PCP.AlphabetTable

@[simp] theorem headerTimePolynomial_eval (length : Nat) :
    headerTimePolynomial.eval length = 25 * length + 52 := by
  simp [headerTimePolynomial]

def headerInTime (rowPlan : Plan) (n m : Nat) (rowsBits : List Bool) (ambient : Ambient) :
    StateTransition.EvalsToInTime (TM2.step (program headerPlan rowPlan))
      ⟨some .copyFirst, ((ambient, ()), none),
        headerInputTapes (encodeWords [n, m] ++ rowsBits)⟩
      (some ⟨some .guard, ((ambient, ()), none), headerResultTapes n m rowsBits⟩)
      (headerTimePolynomial.eval (encodeWords [n, m] ++ rowsBits).length) := by
  let word := encodeWords [n, m] ++ rowsBits
  let bits := encodeWords [6 * n + 36864 * m, 40960 * m]
  let b₀ := headerInputTapes word
  let b₁ := headerFrame word word [] [] [] [] [] []
  let b₂ := headerFrame (encodeWord m ++ rowsBits) word (encodeWord n) [] [] [] [] []
  let b₃ := headerFrame rowsBits word (encodeWord n) (encodeWord m) [] [] [] []
  let b₄ := headerFrame rowsBits word (encodeWord n) (encodeWord m)
    (encodeWord 0) (encodeWord 0) (encodeWord 0) []
  let b₅ := headerFrame rowsBits word (encodeWord n) (encodeWord m)
    (encodeWord 0) (encodeWord 0) (encodeWord 0) bits.reverse
  let b₆ := headerFrame rowsBits word (encodeWord n) (encodeWord m)
    (encodeWord 0) [] (encodeWord 0) bits.reverse
  let b₇ := headerResultTapes n m rowsBits
  have h₀ : Function.update b₀ Tape.archive (b₀ .input ++ b₀ .archive) = b₁ := by
    funext tape; cases tape <;> simp [b₀, b₁, headerInputTapes, headerFrame]
  have h₁ : Hastad.SourceMachine.fieldTapes Tape.input Tape.vertices b₁
      (encodeWord m ++ rowsBits) (encodeWord n ++ b₁ .vertices) = b₂ := by
    funext tape; cases tape <;> simp [Hastad.SourceMachine.fieldTapes, b₁, b₂, headerFrame]
  have h₂ : Hastad.SourceMachine.fieldTapes Tape.input Tape.darts b₂
      rowsBits (encodeWord m ++ b₂ .darts) = b₃ := by
    funext tape; cases tape <;> simp [Hastad.SourceMachine.fieldTapes, b₂, b₃, headerFrame]
  have h₄ : Emitter.resultTapes Tape.accumulator b₄
      (Emitter.prefixBits (Emitter.listCommands headerPlan) (values n m 0 0 0)
        ambient headerPlan.length) = b₅ := by
    rw [Emitter.bits_listCommands, headerPlan_bits]
    funext tape; cases tape <;> simp [Emitter.resultTapes, b₄, b₅, bits, headerFrame]
  have h₅ : Function.update b₅ Tape.tail [] = b₆ := by
    funext tape; cases tape <;> simp [b₅, b₆, headerFrame]
  have h₆ : Function.update b₆ Tape.head [] = b₇ := by
    funext tape; cases tape <;> simp [b₆, b₇, headerResultTapes, bits, word, headerFrame]
  have hn : n ≤ word.length := by
    simp only [word, List.length_append, encodeWords_length, List.sum_cons,
      List.sum_nil, List.length_cons, List.length_nil] ; omega
  have hm : m ≤ word.length := by
    simp only [word, List.length_append, encodeWords_length, List.sum_cons,
      List.sum_nil, List.length_cons, List.length_nil] ; omega
  let p₀ := MachineCopy.copyInTime Tape.input Tape.archive Tape.scratch
    (by decide) (by decide) (by decide) false .copyFirst .copySecond (some .startVertices)
    (program headerPlan rowPlan) rfl rfl b₀ (by rfl) (ambient, ()) none
  have p₀' : StateTransition.EvalsToInTime (TM2.step (program headerPlan rowPlan))
      ⟨some .copyFirst, ((ambient, ()), none), b₀⟩
      (some ⟨some .startVertices, ((ambient, ()), none), b₁⟩) (2 * (word.length + 1)) := by
    have h := p₀
    rw [h₀] at h
    simpa only [show b₀ .input = word from rfl] using h
  let p₁ := Hastad.SourceMachine.fieldInTime Tape.input Tape.vertices (by decide)
    .startVertices .readVertices (some .startDarts) (program headerPlan rowPlan)
    rfl rfl b₁ n (encodeWord m ++ rowsBits)
    (by simp [b₁, headerFrame, word, encodeWords, List.append_assoc]) (ambient, ()) none
  have p₁' : StateTransition.EvalsToInTime (TM2.step (program headerPlan rowPlan))
      ⟨some .startVertices, ((ambient, ()), none), b₁⟩
      (some ⟨some .startDarts, ((ambient, ()), none), b₂⟩) (n + 2) := by
    simpa only [h₁] using p₁
  let p₂ := Hastad.SourceMachine.fieldInTime Tape.input Tape.darts (by decide)
    .startDarts .readDarts (some .seedIndex) (program headerPlan rowPlan)
    rfl rfl b₂ m rowsBits rfl (ambient, ()) none
  have p₂' : StateTransition.EvalsToInTime (TM2.step (program headerPlan rowPlan))
      ⟨some .startDarts, ((ambient, ()), none), b₂⟩
      (some ⟨some .seedIndex, ((ambient, ()), none), b₃⟩) (m + 2) := by
    simpa only [h₂] using p₂
  let p₃ : StateTransition.EvalsToInTime (TM2.step (program headerPlan rowPlan))
      ⟨some .seedIndex, ((ambient, ()), none), b₃⟩
      (some ⟨some (.header (Emitter.labelAt headerPlan.length 36864 0 .entry)),
        ((ambient, ()), none), b₄⟩) 1 := {
    steps := 1
    evals_in_steps := by
      simp only [Function.iterate_one]
      change TM2.step (program headerPlan rowPlan)
        ⟨some .seedIndex, ((ambient, ()), none), b₃⟩ = _
      have ht : Function.update (Function.update (Function.update b₃ Tape.rowIndex [false])
          Tape.tail [false]) Tape.head [false] = b₄ := by
        funext tape; cases tape <;> simp [b₃, b₄, headerFrame, encodeWord]
      simp only [TM2.step, program, TM2.stepAux]
      apply congrArg some
      exact congrArg (TM2.Cfg.mk _ _) ht
    steps_le_m := Nat.le_refl _ }
  let p₄ := Emitter.planInTime (Emitter.listCommands headerPlan) source Tape.scratch
    Tape.accumulator source_ne_scratch source_ne_accumulator (by decide)
    Label.header (some .headerClearTail) (program headerPlan rowPlan) (fun _ => rfl)
    (values n m 0 0 0) b₄
    (by intro i; fin_cases i <;> rfl) rfl ambient word.length
    (by
      intro i
      fin_cases i
      · exact hn
      · exact hm
      · exact Nat.zero_le _
      · exact Nat.zero_le _
      · exact Nat.zero_le _)
  have p₄' : StateTransition.EvalsToInTime (TM2.step (program headerPlan rowPlan))
      ⟨some (.header (Emitter.labelAt headerPlan.length 36864 0 .entry)),
        ((ambient, ()), none), b₄⟩
      (some ⟨some .headerClearTail, ((ambient, ()), none), b₅⟩)
      (7 * (3 * (word.length + 1) + 3) + 1) := by
    have h := p₄
    rw [h₄] at h
    simpa only [headerPlan_length] using h
  let p₅ := MachineLookup.discardInTime Tape.tail .headerClearTail .headerClearHead
    (program headerPlan rowPlan) rfl b₅ 0 [] (by simp [b₅, headerFrame]) (ambient, ()) none
  have p₅' : StateTransition.EvalsToInTime (TM2.step (program headerPlan rowPlan))
      ⟨some .headerClearTail, ((ambient, ()), none), b₅⟩
      (some ⟨some .headerClearHead, ((ambient, ()), none), b₆⟩) 1 := by
    simpa only [h₅] using p₅
  let p₆ := MachineLookup.discardInTime Tape.head .headerClearHead .guard
    (program headerPlan rowPlan) rfl b₆ 0 [] (by simp [b₆, headerFrame]) (ambient, ()) none
  have p₆' : StateTransition.EvalsToInTime (TM2.step (program headerPlan rowPlan))
      ⟨some .headerClearHead, ((ambient, ()), none), b₆⟩
      (some ⟨some .guard, ((ambient, ()), none), b₇⟩) 1 := by
    simpa only [h₆] using p₆
  let p₀₁ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀' p₁'
  let p₀₁₂ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀₁ p₂'
  let p₀₁₂₃ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀₁₂ p₃
  let p₀₁₂₃₄ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀₁₂₃ p₄'
  let p₀₁₂₃₄₅ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀₁₂₃₄ p₅'
  let p := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀₁₂₃₄₅ p₆'
  exact {
    toEvalsTo := p.toEvalsTo
    steps_le_m := by
      have h := p.steps_le_m
      change _ ≤ headerTimePolynomial.eval word.length
      rw [headerTimePolynomial_eval]
      omega }

def tableRowsBits (table : PCP.GenericGraphTables.Table 64) : List Bool :=
  encodeWords ((PCP.GenericGraphTables.rowList table).flatMap PCP.GenericGraphTables.rowWords)

theorem tableBits_header_rows (table : PCP.GenericGraphTables.Table 64) :
    PCP.GenericGraphTables.tableBits table =
      encodeWords [table.vertices, table.darts] ++ tableRowsBits table := by
  simp only [PCP.GenericGraphTables.tableBits, PCP.GenericGraphTables.tableWords,
    encodeWords_append, tableRowsBits]

def tableHeaderInTime (rowPlan : Plan) (table : PCP.GenericGraphTables.Table 64)
    (ambient : Ambient) :
    StateTransition.EvalsToInTime (TM2.step (program headerPlan rowPlan))
      ⟨some .copyFirst, ((ambient, ()), none),
        headerInputTapes (PCP.GenericGraphTables.tableBits table)⟩
      (some ⟨some .guard, ((ambient, ()), none),
        headerResultTapes table.vertices table.darts (tableRowsBits table)⟩)
      (headerTimePolynomial.eval (PCP.GenericGraphTables.tableBits table).length) := by
  rw [tableBits_header_rows]
  exact headerInTime rowPlan table.vertices table.darts (tableRowsBits table) ambient

theorem headerInput_configuration (rowPlan : Plan) (input : List Bool) :
    initList (machine headerPlan rowPlan) input =
      ⟨some .copyFirst, ((((), fun _ => false), ()), none), headerInputTapes input⟩ := by
  have ht : (initList (machine headerPlan rowPlan) input).stk = headerInputTapes input := by
    funext tape
    cases tape <;> simp [initList, machine, headerInputTapes, headerFrame]
    rfl
  exact congrArg (TM2.Cfg.mk _ _) ht

def initializedTableHeaderInTime (rowPlan : Plan) (table : PCP.GenericGraphTables.Table 64) :
    StateTransition.EvalsToInTime (machine headerPlan rowPlan).step
      (initList (machine headerPlan rowPlan) (PCP.GenericGraphTables.tableBits table))
      (some ⟨some .guard, ((((), fun _ => false), ()), none),
        headerResultTapes table.vertices table.darts (tableRowsBits table)⟩)
      (headerTimePolynomial.eval (PCP.GenericGraphTables.tableBits table).length) := by
  rw [headerInput_configuration]
  exact tableHeaderInTime rowPlan table ((), fun _ => false)

end DFVSGames.Foundations.Complexity.FinalCNFMachine.Program

end

section

namespace DFVSGames.Foundations.Complexity.FinalCNFMachine.Program

open Turing PCP PCP.AlphabetTable

def endpointsInTime (headerPlan plan : Plan) (base : Tape → List Bool)
    (tail reverse : Nat) (rest : List Bool)
    (hinput : base .input = encodeWord tail ++ encodeWord reverse ++ rest)
    (ambient : Ambient) :
    StateTransition.EvalsToInTime (TM2.step (program headerPlan plan))
      ⟨some .startTail, ((ambient, ()), none), base⟩
      (some ⟨some .headTableFirst, ((ambient, ()), none),
        endpointTapes base tail reverse rest⟩) (tail + reverse + 4) := by
  let first := Hastad.SourceMachine.fieldTapes Tape.input Tape.tail base
    (encodeWord reverse ++ rest) (encodeWord tail ++ base .tail)
  let run₁ := Hastad.SourceMachine.fieldInTime Tape.input Tape.tail (by decide)
    .startTail .readTail (some .startReverse) (program headerPlan plan) rfl rfl
    base tail (encodeWord reverse ++ rest) (by simpa only [List.append_assoc] using hinput)
    (ambient, ()) none
  have input₁ : first .input = encodeWord reverse ++ rest := by
    simp [first, Hastad.SourceMachine.fieldTapes]
  have reverse₁ : first .reverseIndex = base .reverseIndex := by
    simp [first, Hastad.SourceMachine.fieldTapes]
  let run₂ := Hastad.SourceMachine.fieldInTime Tape.input Tape.reverseIndex (by decide)
    .startReverse .readReverse (some .headTableFirst) (program headerPlan plan) rfl rfl
    first reverse rest input₁ (ambient, ()) none
  have joined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ run₁ run₂
  simpa only [first, reverse₁, endpointTapes, Nat.add_assoc,
    Nat.add_left_comm, Nat.add_comm] using joined

def emitInTime (headerPlan plan : Plan) (base : Tape → List Bool)
    (operands : Fin 5 → Nat) (hoperands : ∀ i, base (source i) = encodeWord (operands i))
    (hscratch : base .scratch = []) (ambient : Ambient)
    (N : Nat) (hbounded : ∀ i, operands i ≤ N) :
    StateTransition.EvalsToInTime (TM2.step (program headerPlan plan))
      ⟨some (.row (Emitter.labelAt plan.length 36864 0 .entry)),
        ((ambient, ()), none), base⟩
      (some ⟨some .clearTail, ((ambient, ()), none),
        Function.update base .accumulator
          ((plan.flatMap (Emitter.commandBits operands ambient)).reverse ++ base .accumulator)⟩)
      (plan.length * (3 * (N + 1) + 3) + 1) := by
  have run := Emitter.planInTime (Emitter.listCommands plan)
    source Tape.scratch Tape.accumulator source_ne_scratch source_ne_accumulator (by decide)
    Label.row (some .clearTail) (program headerPlan plan) (fun _ => rfl)
    operands base hoperands hscratch ambient N hbounded
  simpa only [Emitter.bits_listCommands, Emitter.resultTapes] using run

def finishInTime (headerPlan plan : Plan) (base : Tape → List Bool)
    (tail head reverse row : Nat)
    (htail : base .tail = encodeWord tail) (hhead : base .head = encodeWord head)
    (hreverse : base .reverseIndex = encodeWord reverse)
    (hrow : base .rowIndex = encodeWord row) (ambient : Ambient) :
    StateTransition.EvalsToInTime (TM2.step (program headerPlan plan))
      ⟨some .clearTail, ((ambient, ()), none), base⟩
      (some ⟨some .guard, ((ambient, ()), none), finishTapes base row⟩)
      (tail + head + reverse + 4) := by
  let t₁ := Function.update base Tape.tail []
  let t₂ := Function.update t₁ Tape.head []
  let t₃ := Function.update t₂ Tape.reverseIndex []
  let run₁ := MachineLookup.discardInTime Tape.tail .clearTail .clearHead
    (program headerPlan plan) rfl base tail [] (by simpa using htail) (ambient, ()) none
  have hhead₁ : t₁ .head = encodeWord head := by simp [t₁, hhead]
  let run₂ := MachineLookup.discardInTime Tape.head .clearHead .clearReverse
    (program headerPlan plan) rfl t₁ head [] (by simpa using hhead₁) (ambient, ()) none
  have hreverse₂ : t₂ .reverseIndex = encodeWord reverse := by simp [t₂, t₁, hreverse]
  let run₃ := MachineLookup.discardInTime Tape.reverseIndex .clearReverse .nextRow
    (program headerPlan plan) rfl t₂ reverse [] (by simpa using hreverse₂) (ambient, ()) none
  let run₄ : StateTransition.EvalsToInTime (TM2.step (program headerPlan plan))
      ⟨some .nextRow, ((ambient, ()), none), t₃⟩
      (some ⟨some .guard, ((ambient, ()), none), finishTapes base row⟩) 1 := {
    steps := 1
    evals_in_steps := by
      change some (TM2.stepAux (program headerPlan plan .nextRow) _ _) = _
      simp only [program, TM2.stepAux]
      congr 2
      simp [t₃, t₂, t₁, finishTapes, hrow, encodeWord, List.replicate_succ]
    steps_le_m := Nat.le_refl _ }
  let r₁₂ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ run₁ run₂
  let r₁₂₃ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ r₁₂ run₃
  have run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ r₁₂₃ run₄
  simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using run

end DFVSGames.Foundations.Complexity.FinalCNFMachine.Program
end

section

namespace DFVSGames.Foundations.Complexity.FinalCNFMachine.Program

open Turing PCP PCP.AlphabetTable FinalCNFTableAdapter

def guardRowInTime (headerPlan plan : Plan) (base : Tape → List Bool)
    (ambient : Ambient) (hinput : base .input ≠ []) :
    StateTransition.EvalsToInTime (TM2.step (program headerPlan plan))
      ⟨some .guard, ((ambient, ()), none), base⟩
      (some ⟨some .startTail, ((ambient, ()), none), base⟩) 1 where
  steps := 1
  evals_in_steps := by
    change some (TM2.stepAux (program headerPlan plan .guard) _ _) = _
    cases hb : base .input with
    | nil => exact False.elim (hinput hb)
    | cons b bs => simp [program, guard, TM2.stepAux, hb]
  steps_le_m := Nat.le_refl _

def guardEndInTime (headerPlan plan : Plan) (base : Tape → List Bool)
    (ambient : Ambient) (hinput : base .input = []) :
    StateTransition.EvalsToInTime (TM2.step (program headerPlan plan))
      ⟨some .guard, ((ambient, ()), none), base⟩
      (some ⟨some .reverseOutput, ((ambient, ()), none), base⟩) 1 where
  steps := 1
  evals_in_steps := by
    change some (TM2.stepAux (program headerPlan plan .guard) _ _) = _
    simp [program, guard, TM2.stepAux, hinput]
  steps_le_m := Nat.le_refl _

def rowTime (plan : Plan) (N : Nat) : Nat :=
  plan.length * (3 * (N + 1) + 3) + 12 * N + 15

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

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_FinalCNFStream
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

open PCP PCP.AlphabetTable FinalCNFTableAdapter

def outputStream (plan : Plan) (table : GraphTables.Table)
    (events : List (Fin table.darts)) : List Bool :=
  events.flatMap (fun e => plan.flatMap (Emitter.commandBits (rowOperands table e)
    (rowRelation table e)))

theorem remainingEvents_cons (table : GraphTables.Table) (r : Nat) (h : r < table.darts) :
    remainingEvents table r = ⟨r, h⟩ :: remainingEvents table (r + 1) := by
  unfold remainingEvents
  rw [List.drop_eq_getElem_cons (l := List.finRange table.darts) (i := r)
    (by simpa using h)]
  simp

@[simp] theorem inputStream_append (table : GraphTables.Table)
    (first rest : List (Fin table.darts)) :
    inputStream table (first ++ rest) = inputStream table first ++ inputStream table rest := by
  simp only [inputStream, List.flatMap_append]

@[simp] theorem outputStream_nil (plan : Plan) (table : GraphTables.Table) :
    outputStream plan table [] = [] := rfl

@[simp] theorem outputStream_cons (plan : Plan) (table : GraphTables.Table)
    (e : Fin table.darts) (events : List (Fin table.darts)) :
    outputStream plan table (e :: events) =
      plan.flatMap (Emitter.commandBits (rowOperands table e) (rowRelation table e)) ++
        outputStream plan table events := rfl

@[simp] theorem outputStream_append (plan : Plan) (table : GraphTables.Table)
    (first rest : List (Fin table.darts)) :
    outputStream plan table (first ++ rest) =
      outputStream plan table first ++ outputStream plan table rest := by
  simp only [outputStream, List.flatMap_append]

theorem inputStream_remaining_cons (table : GraphTables.Table) (r : Nat)
    (h : r < table.darts) :
    inputStream table (remainingEvents table r) =
      encodeWords (GraphTables.rowWords table.rows[(⟨r, h⟩ : Fin table.darts)]) ++
        inputStream table (remainingEvents table (r + 1)) := by
  rw [remainingEvents_cons table r h, inputStream_cons]

theorem outputStream_remaining_cons (plan : Plan) (table : GraphTables.Table) (r : Nat)
    (h : r < table.darts) :
    outputStream plan table (remainingEvents table r) =
      plan.flatMap (Emitter.commandBits (rowOperands table ⟨r, h⟩)
        (rowRelation table ⟨r, h⟩)) ++
          outputStream plan table (remainingEvents table (r + 1)) := by
  rw [remainingEvents_cons table r h, outputStream_cons]

theorem encodeWords_flatMap_rows_inline_FinalCNFStream {α : Type} (rows : List α) (words : α → List Nat) :
    encodeWords (rows.flatMap words) = rows.flatMap (fun row => encodeWords (words row)) := by
  induction rows with
  | nil => rfl
  | cons row rows ih => simp only [List.flatMap_cons, encodeWords_append, ih]

theorem rowList_eq_finRange_map (table : GraphTables.Table) :
    GraphTables.rowList table = (List.finRange table.darts).map (fun e => table.rows[e]) := by
  rw [← List.ofFn_eq_map, ← Vector.toList_ofFn]
  change table.rows.toList = (Vector.ofFn (fun i => table.rows[i.val])).toList
  rw [Vector.ofFn_getElem]

theorem inputStream_all (table : GraphTables.Table) :
    inputStream table (List.finRange table.darts) = tableRowsBits (genericTable table) := by
  rw [tableRowsBits, genericTable_rowList]
  change inputStream table (List.finRange table.darts) =
    encodeWords (((GraphTables.rowList table).map genericRow).flatMap GenericGraphTables.rowWords)
  rw [List.flatMap_map]
  simp only [genericRow_words]
  rw [rowList_eq_finRange_map, List.flatMap_map, encodeWords_flatMap_rows_inline_FinalCNFStream]
  rfl

theorem inputStream_remaining_zero (table : GraphTables.Table) :
    inputStream table (remainingEvents table 0) = tableRowsBits (genericTable table) := by
  rw [remainingEvents_zero, inputStream_all]

end DFVSGames.Foundations.Complexity.FinalCNFMachine.Program

end

section

namespace DFVSGames.Foundations.Complexity.FinalCNFMachine.Program

open Turing PCP PCP.AlphabetTable

structure LoopInvariant (table : GraphTables.Table) (r : Nat) (base : Tape → List Bool) : Prop where
  input : base .input = inputStream table (remainingEvents table r)
  archive : base .archive = GraphTables.tableBits table
  vertices : base .vertices = encodeWord table.vertices
  darts : base .darts = encodeWord table.darts
  index : base .rowIndex = encodeWord r
  tail : base .tail = []
  head : base .head = []
  reverse : base .reverseIndex = []
  scratch : base .scratch = []

structure LoopRun (headerPlan plan : Plan) (table : GraphTables.Table) (r remaining : Nat)
    (base : Tape → List Bool) (ambient : Ambient) where
  finalAmbient : Ambient
  finalTapes : Tape → List Bool
  execution : StateTransition.EvalsToInTime (TM2.step (program headerPlan plan))
    ⟨some .guard, ((ambient, ()), none), base⟩
    (some ⟨some .reverseOutput, ((finalAmbient, ()), none), finalTapes⟩)
    (remaining * (rowTime plan (GraphTables.tableBits table).length + 1) + 1)
  accumulator : finalTapes .accumulator =
    (outputStream plan table (remainingEvents table r)).reverse ++ base .accumulator
  output : finalTapes .output = base .output

end DFVSGames.Foundations.Complexity.FinalCNFMachine.Program
end

section

namespace DFVSGames.Foundations.Complexity.FinalCNFMachine.Program

open Turing PCP PCP.AlphabetTable FinalCNFTableAdapter

def emittedBytes (plan : Plan) (table : GraphTables.Table) : List Bool :=
  encodeWords [6 * table.vertices + 36864 * table.darts, 40960 * table.darts] ++
    outputStream plan table (List.finRange table.darts)

noncomputable def rawBudget (plan : Plan) (table : GraphTables.Table) : Nat :=
  headerTimePolynomial.eval (GraphTables.tableBits table).length +
    table.darts * (rowTime plan (GraphTables.tableBits table).length + 1) + 1 +
      (emittedBytes plan table).length + 1

structure RawRun (plan : Plan) (table : GraphTables.Table) where
  finalAmbient : Ambient
  finalTapes : Tape → List Bool
  execution : StateTransition.EvalsToInTime (machine headerPlan plan).step
    (initList (machine headerPlan plan) (GraphTables.tableBits table))
    (some ⟨none, ((finalAmbient, ()), none), finalTapes⟩) (rawBudget plan table)
  output : finalTapes .output = emittedBytes plan table

theorem header_loopInvariant (_plan : Plan) (table : GraphTables.Table) :
    LoopInvariant table 0 (headerResultTapes table.vertices table.darts
      (tableRowsBits (genericTable table))) := by
  constructor
  · rw [headerResultTapes_input, inputStream_remaining_zero]
  · rw [headerResultTapes_archive]
    exact (tableBits_header_rows (genericTable table)).symm.trans (genericTable_tableBits table)
  · rfl
  · rfl
  · exact headerResultTapes_rowIndex _ _ _
  · rfl
  · rfl
  · rfl
  · rfl

end DFVSGames.Foundations.Complexity.FinalCNFMachine.Program
end

section

namespace DFVSGames.Foundations.Complexity.FinalCNFTemplate

open Target PCP

@[simp] theorem templates_length (accepted : Bool) (bits : Fin 12 → Bool) :
    (templates accepted bits).length = 10 := Vector.length_toList

theorem templates_true (bits : Fin 12 → Bool) :
    templates true bits = List.replicate 10 tautologyTemplate := by rfl

theorem templates_false (bits : Fin 12 → Bool) :
    templates false bits = (chainTemplates bits).toList := by rfl

def clauseWords (index : Reference → Nat) (clause : ClauseTemplate) : List Nat :=
  literalWords index clause[0] ++ literalWords index clause[1] ++ literalWords index clause[2]

def words (accepted : Bool) (bits : Fin 12 → Bool) (index : Reference → Nat) : List Nat :=
  (templates accepted bits).flatMap (clauseWords index)

variable (V : VerifierToCNF.FiniteVerifier 12) (e : Fin V.events)
  (p : VerifierToCNF.PatternIndex 12)

def resolve : Reference → Fin (VerifierToCNF.outputVariables V)
  | .query i => VerifierToCNF.oldIndex V (V.query e i)
  | .auxiliary j => VerifierToCNF.freshIndex V e p j

theorem resolve_query_value (i : Fin 12) :
    (resolve V e p (.query i)).val = (V.query e i).val := by
  simp only [resolve, VerifierToCNF.oldIndex, Fin.val_castAdd]

theorem resolve_auxiliary_value (j : Fin 9) :
    (resolve V e p (.auxiliary j)).val =
      V.«variables» + ((e.val * 4096 + p.val) * 9 + j.val) := by
  change (VerifierToCNF.freshIndex V e p j).val = _
  exact (VerifierToCNF.freshIndex_value V e p j).trans
    (congrArg (fun k : Nat => V.«variables» + ((e.val * k + p.val) * 9 + j.val))
      (show (VerifierToCNF.patterns 12).length = 4096 from VerifierToCNF.patterns_length 12))

def instantiateLiteral (literal : LiteralTemplate) : Literal (VerifierToCNF.outputVariables V) :=
  ⟨resolve V e p literal.reference, literal.positive⟩

def instantiateClause (clause : ClauseTemplate) : Clause (VerifierToCNF.outputVariables V) :=
  #v[instantiateLiteral V e p clause[0], instantiateLiteral V e p clause[1],
    instantiateLiteral V e p clause[2]]

theorem splitLong_twelve {n : Nat} (ls : Fin 12 → Literal n) (ys : Fin 9 → Fin n) :
    VerifierToCNF.splitLong (List.ofFn ls) (List.ofFn ys) =
      [#v[ls 0, ls 1, ⟨ys 0, true⟩],
       #v[⟨ys 0, false⟩, ls 2, ⟨ys 1, true⟩],
       #v[⟨ys 1, false⟩, ls 3, ⟨ys 2, true⟩],
       #v[⟨ys 2, false⟩, ls 4, ⟨ys 3, true⟩],
       #v[⟨ys 3, false⟩, ls 5, ⟨ys 4, true⟩],
       #v[⟨ys 4, false⟩, ls 6, ⟨ys 5, true⟩],
       #v[⟨ys 5, false⟩, ls 7, ⟨ys 6, true⟩],
       #v[⟨ys 6, false⟩, ls 8, ⟨ys 7, true⟩],
       #v[⟨ys 7, false⟩, ls 9, ⟨ys 8, true⟩],
       #v[⟨ys 8, false⟩, ls 10, ls 11]] := by
  simp only [List.ofFn_succ, List.ofFn_zero, VerifierToCNF.splitLong]
  rfl

theorem instantiate_templates :
    (templates (V.accepts e (VerifierToCNF.patternAt 12 p))
      (VerifierToCNF.patternAt 12 p)).map (instantiateClause V e p) =
        VerifierToCNF.block V (by decide) e p := by
  cases h : V.accepts e (VerifierToCNF.patternAt 12 p) with
  | false =>
      simp only [h, templates_false, VerifierToCNF.block, Bool.false_eq_true, ↓reduceIte,
        VerifierToCNF.forbiddenClause, VerifierToCNF.auxiliaryNames]
      rw [splitLong_twelve]
      rfl
  | true =>
      simp only [h, templates_true, VerifierToCNF.block, ↓reduceIte, List.map_replicate]
      rfl

theorem instantiateClause_words (clause : ClauseTemplate) :
    Complexity.clauseWords (instantiateClause V e p clause) =
      clauseWords (fun r => (resolve V e p r).val) clause := rfl

theorem words_eq_block :
    words (V.accepts e (VerifierToCNF.patternAt 12 p)) (VerifierToCNF.patternAt 12 p)
      (fun r => (resolve V e p r).val) =
        (VerifierToCNF.block V (by decide) e p).flatMap Complexity.clauseWords := by
  rw [← instantiate_templates V e p]
  simp only [List.flatMap_map, instantiateClause_words]
  rfl

end DFVSGames.Foundations.Complexity.FinalCNFTemplate

end

section

namespace DFVSGames.Foundations.Complexity.FinalCNFMachine.Program

open PCP PCP.AlphabetTable FinalCNFTemplate

def referenceValue (vertices tail head row pattern : Nat) : Reference → Nat
  | .query i => if i.val < 6 then 6 * tail + i.val else 6 * head + (i.val - 6)
  | .auxiliary j => 6 * vertices + 36864 * row + (9 * pattern + j.val)

def auxiliaryFlag : Reference → Bool
  | .query _ => false
  | .auxiliary _ => true

def tailFlag : Reference → Bool
  | .query i => decide (i.val < 6)
  | .auxiliary _ => false

def headFlag : Reference → Bool
  | .query i => decide (6 ≤ i.val)
  | .auxiliary _ => false

theorem pattern_lt (p : VerifierToCNF.PatternIndex 12) : p.val < 4096 := by
  have hlen : (VerifierToCNF.patterns 12).length = 4096 := VerifierToCNF.patterns_length 12
  exact lt_of_lt_of_eq p.isLt hlen

def referenceOffset (p : VerifierToCNF.PatternIndex 12) : Reference → Fin 36864
  | .query i => ⟨if i.val < 6 then i.val else i.val - 6, by split <;> omega⟩
  | .auxiliary j => ⟨9 * p.val + j.val, by have hp := pattern_lt p; omega⟩

def literalPlan (p : VerifierToCNF.PatternIndex 12) (literal : Ambient → LiteralTemplate) : Plan :=
  [.scaledIf 0 6 (fun state => auxiliaryFlag (literal state).reference),
   .scaledIf 2 6 (fun state => tailFlag (literal state).reference),
   .scaledIf 3 6 (fun state => headFlag (literal state).reference),
   .scaledIf 4 36864 (fun state => auxiliaryFlag (literal state).reference),
   .bounded (fun state => referenceOffset p (literal state).reference),
   .literal [false],
   .bit (fun state => (literal state).positive)]

theorem literalPlan_length (p : VerifierToCNF.PatternIndex 12)
    (literal : Ambient → LiteralTemplate) : (literalPlan p literal).length = 7 := rfl

theorem literalPlan_bits (p : VerifierToCNF.PatternIndex 12)
    (literal : Ambient → LiteralTemplate) (vertices darts tail head row : Nat)
    (ambient : Ambient) :
    (literalPlan p literal).flatMap
      (Emitter.commandBits (values vertices darts tail head row) ambient) =
      encodeWords (FinalCNFTemplate.literalWords
        (referenceValue vertices tail head row p.val) (literal ambient)) := by
  rcases h : literal ambient with ⟨reference, positive⟩
  cases reference with
  | query i =>
      by_cases hi : i.val < 6
      · simp [literalPlan, Emitter.commandBits, h, auxiliaryFlag, tailFlag, headFlag,
          referenceOffset, referenceValue, FinalCNFTemplate.literalWords, values,
          hi, show ¬ 6 ≤ i.val by omega, encodeWords, encodeWord, List.replicate_add,
          List.append_assoc, -List.replicate_append_replicate]
        rfl
      · simp [literalPlan, Emitter.commandBits, h, auxiliaryFlag, tailFlag, headFlag,
          referenceOffset, referenceValue, FinalCNFTemplate.literalWords, values,
          hi, show 6 ≤ i.val by omega, encodeWords, encodeWord, List.replicate_add,
          List.append_assoc, -List.replicate_append_replicate]
        rfl
  | auxiliary j =>
      simp [literalPlan, Emitter.commandBits, h, auxiliaryFlag, tailFlag, headFlag,
        referenceOffset, referenceValue, FinalCNFTemplate.literalWords, values,
        encodeWords, encodeWord, List.replicate_add, List.append_assoc,
        -List.replicate_append_replicate]
      rfl

def patternLiteral (p : VerifierToCNF.PatternIndex 12) (clause : Fin 10) (slot : Fin 3)
    (ambient : Ambient) : LiteralTemplate :=
  literalAt (ambient.2 (FinalCNFPattern.patternRelationIndex p))
    (VerifierToCNF.patternAt 12 p) clause slot

def patternPlan (p : VerifierToCNF.PatternIndex 12) : Plan :=
  (List.finRange 10).flatMap fun clause =>
    (List.finRange 3).flatMap fun slot => literalPlan p (patternLiteral p clause slot)

def rowPlan : Plan :=
  (List.finRange (VerifierToCNF.patterns 12).length).flatMap patternPlan

theorem patternPlan_length (p : VerifierToCNF.PatternIndex 12) :
    (patternPlan p).length = 210 := by
  unfold patternPlan
  rw [VerifierToCNF.length_flatMap_constant _ _ 21]
  · simp
  · intro clause hclause
    rw [VerifierToCNF.length_flatMap_constant _ _ 7]
    · simp
    · intro slot hslot
      exact literalPlan_length _ _

theorem rowPlan_length : rowPlan.length = 860160 := by
  unfold rowPlan
  rw [VerifierToCNF.length_flatMap_constant _ _ 210]
  · rw [List.length_finRange, VerifierToCNF.patterns_length]; norm_num
  · intro p hp
    exact patternPlan_length p

theorem encodeWords_flatMap {α : Type*} (xs : List α) (words : α → List Nat) :
    encodeWords (xs.flatMap words) = xs.flatMap (fun x => encodeWords (words x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, encodeWords_append, ih]

theorem patternPlan_bits (p : VerifierToCNF.PatternIndex 12)
    (vertices darts tail head row : Nat) (ambient : Ambient) :
    (patternPlan p).flatMap
      (Emitter.commandBits (values vertices darts tail head row) ambient) =
      encodeWords (FinalCNFTemplate.words
        (ambient.2 (FinalCNFPattern.patternRelationIndex p))
        (VerifierToCNF.patternAt 12 p) (referenceValue vertices tail head row p.val)) := by
  unfold patternPlan
  simp only [List.flatMap_assoc]
  simp_rw [literalPlan_bits]
  have hclauses :
      (List.finRange 10).map
        (fun c => (blockTemplates (ambient.2 (FinalCNFPattern.patternRelationIndex p))
          (VerifierToCNF.patternAt 12 p))[c]) =
      templates (ambient.2 (FinalCNFPattern.patternRelationIndex p))
        (VerifierToCNF.patternAt 12 p) := by
    rw [← List.ofFn_eq_map]
    change List.ofFn (fun c : Fin 10 =>
      (blockTemplates (ambient.2 (FinalCNFPattern.patternRelationIndex p))
        (VerifierToCNF.patternAt 12 p))[c.val]) = _
    rw [← Vector.toList_ofFn, Vector.ofFn_getElem]
    rfl
  unfold FinalCNFTemplate.words
  rw [← hclauses, List.flatMap_map, encodeWords_flatMap]
  apply List.flatMap_congr
  intro clause hclause
  simp only [List.finRange, List.ofFn_succ, List.ofFn_zero, List.flatMap_cons,
    List.flatMap_nil, patternLiteral, literalAt, FinalCNFTemplate.clauseWords,
    encodeWords_append, List.append_nil, List.append_assoc]
  rfl

theorem referenceValue_eq_resolve (table : GraphTables.Table) (e : Fin table.darts)
    (p : VerifierToCNF.PatternIndex 12) (reference : Reference) :
    referenceValue table.vertices table.rows[e].tail.val
      table.rows[table.rows[e].reverseIndex].tail.val e.val p.val reference =
      (resolve (FinalCNFPattern.tableVerifier table) e p reference).val := by
  cases reference with
  | query i =>
      rw [resolve_query_value]
      refine Fin.addCases (m := 6) (n := 6) (fun j => ?_) (fun j => ?_) i
      · rw [FinalBooleanVerifier.query_tail]
        simp only [referenceValue, Fin.val_castAdd, j.isLt, ite_true, if_true]
        change 6 * table.rows[e].tail.val + j.val = j.val + 6 * table.rows[e].tail.val
        omega
      · rw [FinalBooleanVerifier.query_head]
        simp only [referenceValue, Fin.val_natAdd]
        split
        · omega
        · change 6 * table.rows[table.rows[e].reverseIndex].tail.val +
              (6 + j.val - 6) = j.val + 6 * table.rows[table.rows[e].reverseIndex].tail.val
          omega
  | auxiliary j =>
      rw [resolve_auxiliary_value]
      change 6 * table.vertices + 36864 * e.val + (9 * p.val + j.val) =
        table.vertices * 6 + ((e.val * 4096 + p.val) * 9 + j.val)
      omega

theorem rowPlan_bits (table : GraphTables.Table) (e : Fin table.darts) :
    rowPlan.flatMap (Emitter.commandBits
      (values table.vertices table.darts table.rows[e].tail.val
        table.rows[table.rows[e].reverseIndex].tail.val e.val)
      ((), fun i => table.rows[e].relation[i])) =
      encodeWords ((VerifierToCNF.eventBlock (FinalCNFPattern.tableVerifier table)
        (by decide) e).flatMap Complexity.clauseWords) := by
  unfold rowPlan VerifierToCNF.eventBlock
  simp only [List.flatMap_assoc]
  rw [encodeWords_flatMap]
  apply List.flatMap_congr
  intro p hp
  rw [patternPlan_bits]
  dsimp only
  rw [FinalCNFPattern.pattern_lookup_eq_verifier_accepts]
  have href := funext (referenceValue_eq_resolve table e p)
  rw [href]
  exact congrArg encodeWords (words_eq_block (FinalCNFPattern.tableVerifier table) e p)

end DFVSGames.Foundations.Complexity.FinalCNFMachine.Program

end

section

namespace DFVSGames.Foundations.Complexity.FinalCNFMachine.Program

open PCP PCP.AlphabetTable

def formulaHeader (table : GraphTables.Table) : List Bool :=
  encodeWords [6 * table.vertices + 36864 * table.darts, 40960 * table.darts]

theorem formulaHeader_eq (table : GraphTables.Table) :
    formulaHeader table = encodeWords [(FinalTableFormula.output table).«variables»,
      (FinalTableFormula.output table).clauses.length] := by
  simp only [formulaHeader, FinalTableFormula.variable_count, FinalTableFormula.clause_count,
    Nat.mul_comm]

theorem outputStream_eq_clauseBits (table : GraphTables.Table) :
    outputStream rowPlan table (List.finRange table.darts) =
      encodeWords ((FinalTableFormula.output table).clauses.flatMap Complexity.clauseWords) := by
  calc
    _ = (List.finRange table.darts).flatMap (fun e =>
          encodeWords ((VerifierToCNF.eventBlock (FinalCNFPattern.tableVerifier table)
            (by decide) e).flatMap Complexity.clauseWords)) := by
      apply List.flatMap_congr
      intro e he
      exact rowPlan_bits table e
    _ = encodeWords ((List.finRange table.darts).flatMap (fun e =>
          (VerifierToCNF.eventBlock (FinalCNFPattern.tableVerifier table)
            (by decide) e).flatMap Complexity.clauseWords)) :=
      (encodeWords_flatMap _ _).symm
    _ = _ := by
      congr 1
      rw [← List.flatMap_assoc]
      rfl

theorem header_append_outputStream (table : GraphTables.Table) :
    formulaHeader table ++ outputStream rowPlan table (List.finRange table.darts) =
      formulaBits (FinalTableFormula.output table) := by
  rw [formulaHeader_eq, outputStream_eq_clauseBits]
  exact (encodeWords_append _ _).symm

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

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_FinalCNFTime
attribute [-instance] _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Foundations.Complexity.FinalCNFMachine.Program

open PCP

theorem rowTimePolynomial_eval (N : Nat) :
    rowTimePolynomial.eval N = rowTime rowPlan N := by
  simp only [rowTimePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, rowTime, rowPlan_length]

noncomputable def phaseTimePolynomial : Polynomial Nat :=
  headerTimePolynomial +
    (Polynomial.X * (rowTimePolynomial + Polynomial.C 1) + Polynomial.C 1) +
    (FinalTableFormula.sizePolynomial + Polynomial.C 1)

theorem phaseTimePolynomial_eval (N : Nat) :
    phaseTimePolynomial.eval N =
      headerTimePolynomial.eval N + (N * (rowTime rowPlan N + 1) + 1) +
        (FinalTableFormula.sizePolynomial.eval N + 1) := by
  simp only [phaseTimePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, rowTimePolynomial_eval]

theorem phaseTime_le {N rows outputLength : Nat} (rowBound : rows ≤ N)
    (outputBound : outputLength ≤ FinalTableFormula.sizePolynomial.eval N) :
    headerTimePolynomial.eval N + (rows * (rowTime rowPlan N + 1) + 1) +
      (outputLength + 1) ≤ phaseTimePolynomial.eval N := by
  have hrows := Nat.mul_le_mul_right (rowTime rowPlan N + 1) rowBound
  rw [phaseTimePolynomial_eval]
  omega

theorem table_phaseTime_le (table : GraphTables.Table) :
    headerTimePolynomial.eval (GraphTables.tableBits table).length +
      (table.darts * (rowTime rowPlan (GraphTables.tableBits table).length + 1) + 1) +
      ((formulaBits (FinalTableFormula.output table)).length + 1) ≤
        phaseTimePolynomial.eval (GraphTables.tableBits table).length :=
  phaseTime_le (GraphTables.darts_le_tableBits_length table)
    (FinalTableFormula.formulaBits_length_le_polynomial table)

noncomputable def finalTimePolynomial (C : Nat) : Polynomial Nat :=
  phaseTimePolynomial + Polynomial.C 12 *
    (Polynomial.X + phaseTimePolynomial * Polynomial.C C + Polynomial.C 1) + Polynomial.C 1

theorem finalTimePolynomial_eval (C N : Nat) :
    (finalTimePolynomial C).eval N = phaseTimePolynomial.eval N +
      12 * (N + phaseTimePolynomial.eval N * C + 1) + 1 := by
  simp only [finalTimePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]

end DFVSGames.Foundations.Complexity.FinalCNFMachine.Program

namespace DFVSGames.Foundations.Complexity.FinalCNFCleanup

open Turing MachineComposition
open FinalCNFMachine (State)
open FinalCNFMachine.Program (Tape Plan)

def chosen : List Tape :=
  [.input, .accumulator, .scratch, .vertices, .darts, .tail, .head,
    .rowIndex, .archive, .reverseIndex, .scanWork, .indexWork]

@[simp] theorem chosen_length : chosen.length = 12 := rfl

@[simp] theorem mem_chosen (tape : Tape) : tape ∈ chosen ↔ tape ≠ .output := by
  cases tape <;> simp [chosen]

abbrev Label (headerPlan rowPlan : Plan) :=
  FinalCNFMachine.Program.Label headerPlan.length rowPlan.length ⊕
    (MachineDrainMany.Label chosen ⊕ Unit)

def cleanupLabel (headerPlan rowPlan : Plan) : MachineDrainMany.Label chosen → Label headerPlan rowPlan :=
  fun label => .inr (.inl label)

def resetLabel (headerPlan rowPlan : Plan) : Label headerPlan rowPlan := .inr (.inr ())

def cleanupEntry (headerPlan rowPlan : Plan) : Option (Label headerPlan rowPlan) :=
  MachineDrainMany.entry chosen (cleanupLabel headerPlan rowPlan) (some (resetLabel headerPlan rowPlan))

def completedProgram (headerPlan rowPlan : Plan) : Label headerPlan rowPlan →
    TM2.Stmt (fun _ : Tape => Bool) (Label headerPlan rowPlan) (State Unit)
  | .inl label => redirectStmt Sum.inl (cleanupEntry headerPlan rowPlan)
      (FinalCNFMachine.Program.program headerPlan rowPlan label)
  | .inr (.inl label) => MachineDrainMany.instruction chosen (cleanupLabel headerPlan rowPlan)
      (some (resetLabel headerPlan rowPlan)) label
  | .inr (.inr _) => .load (fun _ => (FinalCNFMachine.Program.machine headerPlan rowPlan).initialState) .halt

def completedMachine (headerPlan rowPlan : Plan) : FinTM2 where
  K := Tape
  k₀ := .input
  k₁ := .output
  Γ _ := Bool
  Λ := Label headerPlan rowPlan
  main := .inl .copyFirst
  σ := State Unit
  initialState := (FinalCNFMachine.Program.machine headerPlan rowPlan).initialState
  m := completedProgram headerPlan rowPlan

def embeddedCfg (headerPlan rowPlan : Plan)
    (cfg : (FinalCNFMachine.Program.machine headerPlan rowPlan).Cfg) :
    (completedMachine headerPlan rowPlan).Cfg :=
  redirectCfg Sum.inl (cleanupEntry headerPlan rowPlan) cfg

theorem step_simulation (headerPlan rowPlan : Plan)
    (a b : (FinalCNFMachine.Program.machine headerPlan rowPlan).Cfg)
    (step : (FinalCNFMachine.Program.machine headerPlan rowPlan).step a = some b) :
    (completedMachine headerPlan rowPlan).step (embeddedCfg headerPlan rowPlan a) =
      some (embeddedCfg headerPlan rowPlan b) := by
  cases a with
  | mk label state tapes =>
    cases label with
    | none => simp [FinTM2.step, TM2.step] at step
    | some label =>
      have hb : TM2.stepAux (FinalCNFMachine.Program.program headerPlan rowPlan label)
          state tapes = b := Option.some.inj step
      rw [← hb]
      change some (TM2.stepAux
        (redirectStmt Sum.inl (cleanupEntry headerPlan rowPlan)
          (FinalCNFMachine.Program.program headerPlan rowPlan label)) state tapes) = _
      exact congrArg some (stepAux_redirect Sum.inl (cleanupEntry headerPlan rowPlan)
        (FinalCNFMachine.Program.program headerPlan rowPlan label) state tapes)

@[simp] theorem embedded_init (headerPlan rowPlan : Plan) (input : List Bool) :
    embeddedCfg headerPlan rowPlan (initList (FinalCNFMachine.Program.machine headerPlan rowPlan) input) =
      initList (completedMachine headerPlan rowPlan) input := rfl

theorem finalTapes_eq (base : Tape → List Bool) :
    MachineDrainMany.finalTapes chosen base = MachineDrainMany.haltTapes .output (base .output) := by
  funext tape
  rw [MachineDrainMany.finalTapes_apply]
  simp only [mem_chosen]
  by_cases h : tape = .output
  · subst tape
    simp [MachineDrainMany.haltTapes]
  · simp [MachineDrainMany.haltTapes, h]

theorem haltList_eq (headerPlan rowPlan : Plan) (output : List Bool) :
    haltList (completedMachine headerPlan rowPlan) output =
      ⟨none, (FinalCNFMachine.Program.machine headerPlan rowPlan).initialState,
        MachineDrainMany.haltTapes .output output⟩ := by
  congr 1

def cleanupExecution (headerPlan rowPlan : Plan) (state : State Unit) (base : Tape → List Bool) :
    StateTransition.EvalsToInTime (completedMachine headerPlan rowPlan).step
      ⟨cleanupEntry headerPlan rowPlan, state, base⟩
      (some (haltList (completedMachine headerPlan rowPlan) (base .output)))
      (MachineDrainMany.steps chosen base + 1) := by
  let after : (completedMachine headerPlan rowPlan).Cfg :=
    ⟨some (resetLabel headerPlan rowPlan),
      (state.1, MachineDrainMany.finalRegister chosen state.2),
      MachineDrainMany.finalTapes chosen base⟩
  have drains : StateTransition.EvalsToInTime (completedMachine headerPlan rowPlan).step
      ⟨cleanupEntry headerPlan rowPlan, state, base⟩ (some after)
      (MachineDrainMany.steps chosen base) := {
    steps := MachineDrainMany.steps chosen base
    evals_in_steps := MachineDrainMany.trace chosen (cleanupLabel headerPlan rowPlan)
      (some (resetLabel headerPlan rowPlan)) (completedProgram headerPlan rowPlan)
      (fun _ => rfl) base state.1 state.2
    steps_le_m := le_rfl }
  have reset : StateTransition.EvalsToInTime (completedMachine headerPlan rowPlan).step
      after (some (haltList (completedMachine headerPlan rowPlan) (base .output))) 1 := {
    steps := 1
    evals_in_steps := by
      change some (⟨none, (FinalCNFMachine.Program.machine headerPlan rowPlan).initialState,
        MachineDrainMany.finalTapes chosen base⟩ : (completedMachine headerPlan rowPlan).Cfg) =
          some (haltList (completedMachine headerPlan rowPlan) (base .output))
      exact congrArg some ((congrArg
        (fun tapes : Tape → List Bool =>
          (⟨none, (FinalCNFMachine.Program.machine headerPlan rowPlan).initialState,
            tapes⟩ : (completedMachine headerPlan rowPlan).Cfg))
        (finalTapes_eq base)).trans (haltList_eq headerPlan rowPlan (base .output)).symm)
    steps_le_m := le_rfl }
  simpa only [Nat.add_comm] using
    StateTransition.EvalsToInTime.trans _ (MachineDrainMany.steps chosen base) 1
      _ after _ drains reset

def outputsInTime (headerPlan rowPlan : Plan) (input output : List Bool)
    (state : State Unit) (base : Tape → List Bool) (budget : Nat)
    (raw : StateTransition.EvalsToInTime
      (FinalCNFMachine.Program.machine headerPlan rowPlan).step
      (initList (FinalCNFMachine.Program.machine headerPlan rowPlan) input)
      (some ⟨none, state, base⟩) budget)
    (correctOutput : base .output = output) :
    TM2OutputsInTime (completedMachine headerPlan rowPlan) input (some output)
      (budget + 12 * (input.length + budget *
        Runtime.programPushBound (FinalCNFMachine.Program.machine headerPlan rowPlan) + 1) + 1) := by
  let lifted := liftExecutionInTime
    (FinalCNFMachine.Program.machine headerPlan rowPlan).step
    (completedMachine headerPlan rowPlan).step (embeddedCfg headerPlan rowPlan)
    (step_simulation headerPlan rowPlan) raw
  have joined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ lifted
    (cleanupExecution headerPlan rowPlan state base)
  have stackBound : ∀ tape, (base tape).length ≤ input.length + budget *
      Runtime.programPushBound (FinalCNFMachine.Program.machine headerPlan rowPlan) := by
    intro tape
    have h := Runtime.executionSizeBound
      (FinalCNFMachine.Program.machine headerPlan rowPlan).step
      (fun cfg => (cfg.stk tape).length)
      (Runtime.programPushBound (FinalCNFMachine.Program.machine headerPlan rowPlan))
      (Runtime.stepStackLength (FinalCNFMachine.Program.machine headerPlan rowPlan) tape) raw
    exact h.trans (Nat.add_le_add_right
      (Runtime.initialStackLength (FinalCNFMachine.Program.machine headerPlan rowPlan) input tape) _)
  have cleanupBound := MachineDrainMany.steps_le_uniform chosen base _ stackBound
  rw [chosen_length] at cleanupBound
  rw [embedded_init, correctOutput] at joined
  exact { toEvalsTo := joined.toEvalsTo
          steps_le_m := joined.steps_le_m.trans (by omega) }

end DFVSGames.Foundations.Complexity.FinalCNFCleanup

namespace DFVSGames.Foundations.Complexity.FinalCNFMachine.Program

open Turing PCP

theorem emittedBytes_eq_formulaBits (table : GraphTables.Table) :
    emittedBytes rowPlan table = formulaBits (FinalTableFormula.output table) :=
  header_append_outputStream table

theorem rawBudget_le_phaseTime (table : GraphTables.Table) :
    rawBudget rowPlan table ≤ phaseTimePolynomial.eval (GraphTables.tableBits table).length := by
  unfold rawBudget
  rw [emittedBytes_eq_formulaBits]
  simpa only [Nat.add_assoc] using table_phaseTime_le table

end DFVSGames.Foundations.Complexity.FinalCNFMachine.Program

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_RankGraph_Clone100Counting
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

namespace DFVSGames.Outer.Clone100

open DFVSGames.Reduction CloneGap ActualSource
open Clone100Triples Clone100Counting
open scoped BigOperators

noncomputable section

theorem clonedInput_bits_length_le (input : SourceEncoding.Input) :
    (SourceEncoding.inputBits (clonedInput input)).length ≤
      input.«variables» * 100 + input.equations.length * 970200 + 2 +
        input.equations.length * 970200 * (300 * input.«variables» + 2) := by
  have h := SourceEncoding.inputBits_length_le (clonedInput input)
  simpa [clonedInput, equations_length, Nat.mul_comm, Nat.mul_left_comm,
    Nat.mul_assoc] using h

end
end DFVSGames.Outer.Clone100

end

section

namespace DFVSGames.Explicit.MachineClone100Model

open DFVSGames.Reduction

open Turing
open DFVSGames.Foundations.Complexity
open DFVSGames.Foundations.Hastad

def program (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ []) :
    Label triples.length → TM2.Stmt Alphabet (Label triples.length) (State triples.length)
  | .headerStart j => SourceMachine.fieldStart (headerTape j) (.headerLoop j)
  | .headerLoop j => SourceMachine.fieldLoop .input (headerTape j) (.headerLoop j)
      (if j.val = 0 then some (.headerStart 1) else some (.setup (.inl 0)))
  | .setup c => .load (fun _ => (((), c), none)) (.goto fun _ => .scan c)
  | .scan c => MachineTransducerCopy.scanLoop (contextSource c) .scratch
      (defaultControl _) (fun q b => .emit c q b) (.restore c)
  | .emit c q b => MachineTransducerCopy.emitter .reversed (fun q _ => q)
      (emission triples) (.scan c) q b
  | .restore c => MachineTransfer.loopAt .scratch (contextSource c) id false
      (.restore c) (contextNext c)
  | .clearHeader => drain .header .clearHeader .guard
  | .guard => MachineUnaryCounter.guard .counter (.fieldStart 0) .finalCounter
  | .fieldStart j => SourceMachine.fieldStart (.field j) (.fieldLoop j)
  | .fieldLoop j => SourceMachine.fieldLoop .input (.field j) (.fieldLoop j)
      (SourceMachine.fieldNext Label.fieldStart
        (some (.setup (.inr (⟨0, List.length_pos_iff.mpr nonempty⟩, 0)))) j)
  | .cleanup j => drain (.field j) (.cleanup j) (cleanupNext j)
  | .finalCounter => .pop .counter (fun state _ => (state.1, none))
      (.goto fun _ => .finalReverse)
  | .finalReverse => MachineTransfer.loopAt .reversed .output id false .finalReverse none

def machine (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ []) : FinTM2 where
  K := Tape
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label triples.length
  main := .headerStart 0
  σ := State triples.length
  initialState := initialState _
  m := program triples nonempty

end DFVSGames.Explicit.MachineClone100Model
end

section

namespace DFVSGames.Explicit.MachineClone100Context

open DFVSGames.Reduction

open Turing
open DFVSGames.Foundations.Complexity
open MachineClone100Model

theorem setupStep (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    (context : Context triples.length) (base : Tape → List Bool)
    (state : State triples.length) :
    TM2.step (program triples nonempty) ⟨some (.setup context), state, base⟩ =
      some ⟨some (.scan context), (((), context), none), base⟩ := rfl

theorem contextTrace (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    (context : Context triples.length) (base : Tape → List Bool)
    (scratchEmpty : base .scratch = []) (state : State triples.length) :
    (MachineComposition.advance (TM2.step (program triples nonempty)))^[
        3 * (base (contextSource context)).length + 3]
      (some ⟨some (.setup context), state, base⟩) =
      some ⟨contextNext context, initialState _, contextTapes triples context base⟩ := by
  have copied := MachineTransducerCopy.transduceCopyTrace
    (contextSource context) Tape.scratch Tape.reversed
    (contextSource_ne_scratch context) (contextSource_ne_reversed context) (by decide)
    (defaultControl triples.length) (fun control _ => control) (emission triples)
    (.scan context) (.restore context) (fun control symbol => .emit context control symbol)
    (contextNext context) (program triples nonempty)
    rfl (by intros; rfl) rfl base scratchEmpty () context none
  rw [show 3 * (base (contextSource context)).length + 3 =
      (3 * (base (contextSource context)).length + 2) + 1 by omega,
    Function.iterate_succ_apply]
  change (MachineComposition.advance (TM2.step (program triples nonempty)))^[
    3 * (base (contextSource context)).length + 2]
    (TM2.step (program triples nonempty) ⟨some (.setup context), state, base⟩) = _
  rw [setupStep]
  exact copied

end DFVSGames.Explicit.MachineClone100Context
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ085_DF.DirectedFeedback_RankGraph_MachineClone100Cleanup
attribute [-instance] _root_.OAI.DFVSGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DFVSGames.Quadratic.blockOrientationFintype _root_.OAI.DFVSGames.Quadratic.fieldLineFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain
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

namespace DFVSGames.Explicit.MachineClone100Affine

open DFVSGames.Reduction

open DFVSGames.Foundations.Complexity
open MachineClone100Model

theorem output_eq_flatMap {Q : Type} [Fintype Q]
    (emit : Q → Bool → List Bool) (q : Q) (input : List Bool) :
    MachineTransducer.output (fun state _ => state) emit q input =
      input.flatMap (emit q) := by
  induction input with
  | nil => rfl
  | cons b input ih =>
    simp only [MachineTransducer.output, List.flatMap_cons, ih]

theorem affineEmit_replicate_true (scale offset v : Nat) :
    (List.replicate v true).flatMap (affineEmit scale offset) =
      List.replicate (scale * v) true := by
  rw [List.flatMap_replicate]
  change (List.replicate v (List.replicate scale true)).flatten = _
  rw [List.flatten_replicate_replicate, Nat.mul_comm v scale]

theorem affineEmit_word (scale offset v : Nat) :
    (encodeWord v).flatMap (affineEmit scale offset) =
      encodeWord (offset + scale * v) := by
  simp only [encodeWord, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, affineEmit_replicate_true, affineEmit]
  rw [← List.append_assoc, List.replicate_append_replicate, Nat.add_comm (scale * v) offset]

theorem output_word (triples : List (Nat × Nat × Nat))
    (c : Context triples.length) (v : Nat) :
    MachineTransducer.output (fun q _ => q) (emission triples) c (encodeWord v) =
      encodeWord (contextOffset triples c + contextScale c * v) := by
  rw [output_eq_flatMap]
  exact affineEmit_word (contextScale c) (contextOffset triples c) v

end DFVSGames.Explicit.MachineClone100Affine
end

section

namespace DFVSGames.Explicit.MachineClone100Cleanup

open DFVSGames.Reduction

open Turing
open DFVSGames.Foundations.Complexity
open MachineClone100Model

variable {D : Nat}

theorem drainStep_cons (tape : Tape) (again next : Label D)
    (program : Label D → TM2.Stmt Alphabet (Label D) (State D))
    (atAgain : program again = drain tape again next)
    (base : Tape → List Bool) (bit : Bool) (input : List Bool)
    (control : Unit × Context D) (register : Option Bool) :
    TM2.step program
      ⟨some again, (control, register), Function.update base tape (bit :: input)⟩ =
      some ⟨some again, (control, some bit), Function.update base tape input⟩ := by
  change some (TM2.stepAux (program again) (control, register)
    (Function.update base tape (bit :: input))) = _
  rw [atAgain]
  simp [drain, TM2.stepAux]

theorem drainStep_nil (tape : Tape) (again next : Label D)
    (program : Label D → TM2.Stmt Alphabet (Label D) (State D))
    (atAgain : program again = drain tape again next)
    (base : Tape → List Bool) (control : Unit × Context D) (register : Option Bool) :
    TM2.step program
      ⟨some again, (control, register), Function.update base tape []⟩ =
      some ⟨some next, (control, none), Function.update base tape []⟩ := by
  change some (TM2.stepAux (program again) (control, register)
    (Function.update base tape [])) = _
  rw [atAgain]
  simp [drain, TM2.stepAux]

theorem drainTrace (tape : Tape) (again next : Label D)
    (program : Label D → TM2.Stmt Alphabet (Label D) (State D))
    (atAgain : program again = drain tape again next)
    (base : Tape → List Bool) (input : List Bool)
    (control : Unit × Context D) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[input.length + 1]
      (some ⟨some again, (control, register), Function.update base tape input⟩) =
      some ⟨some next, (control, none), Function.update base tape []⟩ := by
  induction input generalizing register with
  | nil =>
    simpa only [List.length_nil, Nat.zero_add, Function.iterate_one,
      MachineComposition.advance_some] using
      drainStep_nil tape again next program atAgain base control register
  | cons bit input ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    change (MachineComposition.advance (TM2.step program))^[input.length + 1]
      (TM2.step program ⟨some again, (control, register),
        Function.update base tape (bit :: input)⟩) = _
    rw [drainStep_cons tape again next program atAgain, ih]

theorem drainTrace_base (tape : Tape) (again next : Label D)
    (program : Label D → TM2.Stmt Alphabet (Label D) (State D))
    (atAgain : program again = drain tape again next)
    (base : Tape → List Bool) (control : Unit × Context D) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[(base tape).length + 1]
      (some ⟨some again, (control, register), base⟩) =
      some ⟨some next, (control, none), Function.update base tape []⟩ := by
  simpa only [Function.update_eq_self] using
    drainTrace tape again next program atAgain base (base tape) control register

theorem clearHeaderTrace (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    (base : Tape → List Bool) (control : Unit × Context triples.length)
    (register : Option Bool) :
    (MachineComposition.advance (TM2.step (program triples nonempty)))^[(base .header).length + 1]
      (some ⟨some .clearHeader, (control, register), base⟩) =
      some ⟨some .guard, (control, none), Function.update base .header []⟩ :=
  drainTrace_base .header .clearHeader .guard (program triples nonempty) rfl base control register

def cleanupSteps (base : Tape → List Bool) : Nat :=
  (base (.field 0)).length + (base (.field 1)).length +
    (base (.field 2)).length + (base (.field 3)).length + 4

theorem cleanupTrace (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    (slot : Fin 4) (base : Tape → List Bool)
    (control : Unit × Context triples.length) (register : Option Bool) :
    (MachineComposition.advance (TM2.step (program triples nonempty)))^[
      (base (.field slot)).length + 1]
      (some ⟨some (.cleanup slot), (control, register), base⟩) =
      some ⟨some (cleanupNext slot), (control, none), Function.update base (.field slot) []⟩ :=
  drainTrace_base (.field slot) (.cleanup slot) (cleanupNext slot)
    (program triples nonempty) rfl base control register

theorem cleanupFourTrace (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    (base : Tape → List Bool) (control : Unit × Context triples.length)
    (register : Option Bool) :
    (MachineComposition.advance (TM2.step (program triples nonempty)))^[cleanupSteps base]
      (some ⟨some (.cleanup 0), (control, register), base⟩) =
      some ⟨some .guard, (control, none), clearFields base⟩ := by
  let t₀ := Function.update base (.field 0) []
  let t₁ := Function.update t₀ (.field 1) []
  let t₂ := Function.update t₁ (.field 2) []
  have h₀ := cleanupTrace triples nonempty 0 base control register
  have h₁ := cleanupTrace triples nonempty 1 t₀ control none
  have h₂ := cleanupTrace triples nonempty 2 t₁ control none
  have h₃ := cleanupTrace triples nonempty 3 t₂ control none
  have hn₀ : cleanupNext (D := triples.length) 0 = .cleanup 1 := by simp [cleanupNext]
  have hn₁ : cleanupNext (D := triples.length) 1 = .cleanup 2 := by simp [cleanupNext]
  have hn₂ : cleanupNext (D := triples.length) 2 = .cleanup 3 := by simp [cleanupNext]
  have hn₃ : cleanupNext (D := triples.length) 3 = .guard := by simp [cleanupNext]
  rw [hn₀] at h₀
  rw [hn₁] at h₁
  rw [hn₂] at h₂
  rw [hn₃] at h₃
  have ht₁ : t₀ (.field 1) = base (.field 1) := by simp [t₀]
  have ht₂ : t₁ (.field 2) = base (.field 2) := by simp [t₁, t₀]
  have ht₃ : t₂ (.field 3) = base (.field 3) := by simp [t₂, t₁, t₀]
  rw [ht₁] at h₁
  rw [ht₂] at h₂
  rw [ht₃] at h₃
  have time : cleanupSteps base =
      ((base (.field 3)).length + 1) +
      (((base (.field 2)).length + 1) +
      (((base (.field 1)).length + 1) + ((base (.field 0)).length + 1))) := by
    unfold cleanupSteps
    omega
  rw [time, Function.iterate_add_apply]
  rw [Function.iterate_add_apply (m := (base (.field 2)).length + 1)]
  rw [Function.iterate_add_apply (m := (base (.field 1)).length + 1)]
  rw [h₀, h₁, h₂, h₃]
  rfl

def cleanupFourInTime (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    (base : Tape → List Bool) (control : Unit × Context triples.length)
    (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step (program triples nonempty))
      ⟨some (.cleanup 0), (control, register), base⟩
      (some ⟨some .guard, (control, none), clearFields base⟩)
      (cleanupSteps base) where
  steps := cleanupSteps base
  evals_in_steps := by
    change (MachineComposition.advance (TM2.step (program triples nonempty)))^[_] _ = _
    exact cleanupFourTrace triples nonempty base control register
  steps_le_m := Nat.le_refl _

end DFVSGames.Explicit.MachineClone100Cleanup
end

section

namespace DFVSGames.Explicit.MachineClone100Headers

open DFVSGames.Reduction

open Turing
open DFVSGames.Foundations.Complexity
open DFVSGames.Foundations.Hastad
open MachineClone100Model

def parsedTapes (base : Tape → List Bool) (n m : Nat) (suffix : List Bool) :
    Tape → List Bool
  | .input => suffix
  | .header => encodeWord n
  | .counter => encodeWord m
  | tape => base tape

@[simp] theorem resultTapes_scratch (triples) (base) (n m) (suffix) :
    resultTapes triples base n m suffix .scratch = base .scratch := rfl
@[simp] theorem resultTapes_field (triples) (base) (n m) (suffix) (j : Fin 4) :
    resultTapes triples base n m suffix (.field j) = base (.field j) := rfl
@[simp] theorem resultTapes_output (triples) (base) (n m) (suffix) :
    resultTapes triples base n m suffix .output = base .output := rfl

theorem twoFieldsTapes_inline_MachineClone100Headers (base : Tape → List Bool) (n m : Nat) (suffix : List Bool)
    (hheader : base .header = []) (hcounter : base .counter = []) :
    SourceMachine.afterField .input .counter
      (SourceMachine.afterField .input .header base n (encodeWord m ++ suffix)) m suffix =
      parsedTapes base n m suffix := by
  funext tape
  cases tape <;>
    simp [SourceMachine.afterField, SourceMachine.fieldTapes, parsedTapes, hheader, hcounter]

theorem firstContextTapes_inline_MachineClone100Headers (triples : List (Nat × Nat × Nat))
    (base : Tape → List Bool) (n m : Nat) (suffix : List Bool)
    (hreversed : base .reversed = []) :
    MachineClone100Context.contextTapes triples (.inl 0) (parsedTapes base n m suffix) =
      Function.update (parsedTapes base n m suffix) .reversed (encodeWord (100 * n)).reverse := by
  simp [MachineClone100Context.contextTapes, contextSource, headerTape, parsedTapes,
    MachineClone100Affine.output_word, contextOffset, contextScale, hreversed]

theorem secondContextTapes_inline_MachineClone100Headers (triples : List (Nat × Nat × Nat))
    (base : Tape → List Bool) (n m : Nat) (suffix : List Bool) :
    MachineClone100Context.contextTapes triples (.inl 1)
      (Function.update (parsedTapes base n m suffix) .reversed (encodeWord (100 * n)).reverse) =
      Function.update (parsedTapes base n m suffix) .reversed
        (encodeWords [100 * n, triples.length * m]).reverse := by
  simp [MachineClone100Context.contextTapes, contextSource, headerTape, parsedTapes,
    MachineClone100Affine.output_word, contextOffset, contextScale,
    encodeWords, List.reverse_append]

theorem clearHeaderTapes_inline_MachineClone100Headers (triples : List (Nat × Nat × Nat))
    (base : Tape → List Bool) (n m : Nat) (suffix : List Bool) :
    Function.update
      (Function.update (parsedTapes base n m suffix) .reversed
        (encodeWords [100 * n, triples.length * m]).reverse) .header [] =
      resultTapes triples base n m suffix := by
  funext tape
  cases tape <;> simp [parsedTapes, resultTapes]

theorem headersTrace (triples : List (Nat × Nat × Nat)) (hne : triples ≠ [])
    (base : Tape → List Bool) (n m : Nat) (suffix : List Bool)
    (hinput : base .input = encodeWords [n, m] ++ suffix)
    (hheader : base .header = []) (hcounter : base .counter = [])
    (hscratch : base .scratch = []) (hreversed : base .reversed = []) :
    (MachineComposition.advance (TM2.step (program triples hne)))^[5 * n + 4 * m + 18]
      (some ⟨some (.headerStart 0), initialState triples.length, base⟩) =
      some ⟨some .guard, initialState triples.length,
        resultTapes triples base n m suffix⟩ := by
  let t₀ := SourceMachine.afterField .input .header base n (encodeWord m ++ suffix)
  let t₁ := parsedTapes base n m suffix
  let t₂ := Function.update t₁ .reversed (encodeWord (100 * n)).reverse
  let t₃ := Function.update t₁ .reversed (encodeWords [100 * n, triples.length * m]).reverse
  have h₀ : base .input = encodeWord n ++ (encodeWord m ++ suffix) := by
    simpa only [encodeWords, List.append_nil, List.append_assoc] using hinput
  have p₀ := (SourceMachine.fieldInTime .input .header (by decide)
    (.headerStart 0) (.headerLoop 0) (some (.headerStart 1))
    (program triples hne) rfl rfl base n (encodeWord m ++ suffix) h₀
    ((), defaultControl triples.length) none).evals_in_steps
  change (MachineComposition.advance (TM2.step (program triples hne)))^[n + 2]
    (some ⟨some (.headerStart 0), initialState triples.length, base⟩) =
    some ⟨some (.headerStart 1), initialState triples.length, t₀⟩ at p₀
  have h₁ : t₀ .input = encodeWord m ++ suffix := by
    simp [t₀, SourceMachine.afterField]
  have p₁ := (SourceMachine.fieldInTime .input .counter (by decide)
    (.headerStart 1) (.headerLoop 1) (some (.setup (.inl 0)))
    (program triples hne) rfl rfl t₀ m suffix h₁
    ((), defaultControl triples.length) none).evals_in_steps
  change (MachineComposition.advance (TM2.step (program triples hne)))^[m + 2]
    (some ⟨some (.headerStart 1), initialState triples.length, t₀⟩) =
    some ⟨some (.setup (.inl 0)), initialState triples.length,
      SourceMachine.afterField .input .counter t₀ m suffix⟩ at p₁
  have ht₁ : SourceMachine.afterField .input .counter t₀ m suffix = t₁ :=
    twoFieldsTapes_inline_MachineClone100Headers base n m suffix hheader hcounter
  rw [ht₁] at p₁
  have hs₁ : t₁ .scratch = [] := by simpa [t₁, parsedTapes] using hscratch
  have p₂ := MachineClone100Context.contextTrace triples hne (.inl 0) t₁ hs₁
    (initialState triples.length)
  have ht₂ : MachineClone100Context.contextTapes triples (.inl 0) t₁ = t₂ :=
    firstContextTapes_inline_MachineClone100Headers triples base n m suffix hreversed
  rw [ht₂] at p₂
  have hlen₂ : (t₁ (contextSource (.inl 0 : Context triples.length))).length = n + 1 := by
    simp [contextSource, headerTape, t₁, parsedTapes]
  rw [hlen₂] at p₂
  change (MachineComposition.advance (TM2.step (program triples hne)))^[3 * (n + 1) + 3]
    (some ⟨some (.setup (.inl 0)), initialState triples.length, t₁⟩) =
    some ⟨some (.setup (.inl 1)), initialState triples.length, t₂⟩ at p₂
  have hs₂ : t₂ .scratch = [] := by simp [t₂, t₁, parsedTapes, hscratch]
  have p₃ := MachineClone100Context.contextTrace triples hne (.inl 1) t₂ hs₂
    (initialState triples.length)
  have ht₃ : MachineClone100Context.contextTapes triples (.inl 1) t₂ = t₃ :=
    secondContextTapes_inline_MachineClone100Headers triples base n m suffix
  rw [ht₃] at p₃
  have hlen₃ : (t₂ (contextSource (.inl 1 : Context triples.length))).length = m + 1 := by
    simp [contextSource, headerTape, t₂, t₁, parsedTapes]
  rw [hlen₃] at p₃
  change (MachineComposition.advance (TM2.step (program triples hne)))^[3 * (m + 1) + 3]
    (some ⟨some (.setup (.inl 1)), initialState triples.length, t₂⟩) =
    some ⟨some .clearHeader, initialState triples.length, t₃⟩ at p₃
  have p₄ := MachineClone100Cleanup.clearHeaderTrace triples hne t₃
    ((), defaultControl triples.length) none
  have ht₄ : Function.update t₃ .header [] = resultTapes triples base n m suffix :=
    clearHeaderTapes_inline_MachineClone100Headers triples base n m suffix
  rw [ht₄] at p₄
  have hh₃ : t₃ .header = encodeWord n := by simp [t₃, t₁, parsedTapes]
  rw [hh₃, encodeWord_length] at p₄
  change (MachineComposition.advance (TM2.step (program triples hne)))^[(n + 1) + 1]
    (some ⟨some .clearHeader, initialState triples.length, t₃⟩) =
    some ⟨some .guard, initialState triples.length, resultTapes triples base n m suffix⟩ at p₄
  rw [show 5 * n + 4 * m + 18 =
      (n + 2) + (3 * (m + 1) + 3) + (3 * (n + 1) + 3) + (m + 2) + (n + 2) by omega,
    Function.iterate_add_apply, p₀, Function.iterate_add_apply, p₁,
    Function.iterate_add_apply, p₂, Function.iterate_add_apply, p₃]
  exact p₄

def headersInTime (triples : List (Nat × Nat × Nat)) (hne : triples ≠ [])
    (base : Tape → List Bool) (n m : Nat) (suffix : List Bool)
    (hinput : base .input = encodeWords [n, m] ++ suffix)
    (hheader : base .header = []) (hcounter : base .counter = [])
    (hscratch : base .scratch = []) (hreversed : base .reversed = []) :
    StateTransition.EvalsToInTime (TM2.step (program triples hne))
      ⟨some (.headerStart 0), initialState triples.length, base⟩
      (some ⟨some .guard, initialState triples.length,
        resultTapes triples base n m suffix⟩) (5 * n + 4 * m + 18) where
  steps := 5 * n + 4 * m + 18
  evals_in_steps := headersTrace triples hne base n m suffix hinput hheader hcounter hscratch hreversed
  steps_le_m := Nat.le_refl _

end DFVSGames.Explicit.MachineClone100Headers
end

section

namespace DFVSGames.Explicit.MachineClone100Triples

open DFVSGames.Reduction

open Turing
open DFVSGames.Foundations.Complexity
open MachineClone100Model MachineClone100Context MachineClone100Affine

def rowOutput (t : Nat × Nat × Nat) (base : Tape → List Bool) : List Bool :=
  (base (.field 0)).flatMap (affineEmit 100 t.1) ++
    (base (.field 1)).flatMap (affineEmit 100 t.2.1) ++
    (base (.field 2)).flatMap (affineEmit 100 t.2.2) ++
    (base (.field 3)).flatMap (affineEmit 1 0)

def rowSteps (base : Tape → List Bool) : Nat :=
  3 * ((base (.field 0)).length + (base (.field 1)).length +
    (base (.field 2)).length + (base (.field 3)).length) + 12

@[simp] theorem contextTapes_field (triples : List (Nat × Nat × Nat))
    (c : Context triples.length) (base : Tape → List Bool) (j : Fin 4) :
    contextTapes triples c base (.field j) = base (.field j) :=
  contextTapes_other triples c base _ (by intro h; cases h)

@[simp] theorem rowOutput_update (t : Nat × Nat × Nat) (base : Tape → List Bool)
    (out : List Bool) :
    rowOutput t (Function.update base .reversed out) = rowOutput t base := by
  simp [rowOutput]

@[simp] theorem rowSteps_update (base : Tape → List Bool) (out : List Bool) :
    rowSteps (Function.update base .reversed out) = rowSteps base := by
  simp [rowSteps]

theorem fourContexts_tapes (triples : List (Nat × Nat × Nat))
    (i : Fin triples.length) (base : Tape → List Bool) :
    contextTapes triples (.inr (i, 3))
      (contextTapes triples (.inr (i, 2))
        (contextTapes triples (.inr (i, 1))
          (contextTapes triples (.inr (i, 0)) base))) =
      Function.update base .reversed ((rowOutput (triples.get i) base).reverse ++
        base .reversed) := by
  simp [contextTapes, output_eq_flatMap, emission, contextSource, contextScale,
    contextOffset, tripleField, rowOutput, List.reverse_append, List.append_assoc]

theorem rowTrace (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    (i : Fin triples.length) (base : Tape → List Bool)
    (scratchEmpty : base .scratch = []) (state : State triples.length) :
    (MachineComposition.advance (TM2.step (program triples nonempty)))^[rowSteps base]
      (some ⟨some (.setup (.inr (i, 0))), state, base⟩) =
      some ⟨startAt triples.length (i.val + 1), initialState _,
        Function.update base .reversed ((rowOutput (triples.get i) base).reverse ++
          base .reversed)⟩ := by
  let b1 := contextTapes triples (.inr (i, 0)) base
  let b2 := contextTapes triples (.inr (i, 1)) b1
  let b3 := contextTapes triples (.inr (i, 2)) b2
  have h0 := contextTrace triples nonempty (.inr (i, 0)) base scratchEmpty state
  have h1 := contextTrace triples nonempty (.inr (i, 1)) b1
    (by simpa [b1] using scratchEmpty) (initialState _)
  have h2 := contextTrace triples nonempty (.inr (i, 2)) b2
    (by simpa [b2, b1] using scratchEmpty) (initialState _)
  have h3 := contextTrace triples nonempty (.inr (i, 3)) b3
    (by simpa [b3, b2, b1] using scratchEmpty) (initialState _)
  have next0 : contextNext (.inr (i, (0 : Fin 4))) = some (.setup (.inr (i, 1))) := rfl
  have next1 : contextNext (.inr (i, (1 : Fin 4))) = some (.setup (.inr (i, 2))) := rfl
  have next2 : contextNext (.inr (i, (2 : Fin 4))) = some (.setup (.inr (i, 3))) := rfl
  have next3 : contextNext (.inr (i, (3 : Fin 4))) =
      startAt triples.length (i.val + 1) := by simp [contextNext, startAt]
  rw [next0] at h0
  rw [next1] at h1
  rw [next2] at h2
  rw [next3] at h3
  have combined := chain_inline_MachineClone100Triples (chain_inline_MachineClone100Triples (chain_inline_MachineClone100Triples h0 h1) h2) h3
  simp only [contextSource, b3, b2, b1, contextTapes_field] at combined
  rw [fourContexts_tapes] at combined
  convert combined using 1
  all_goals try with_reducible_and_instances rfl
  unfold rowSteps
  congr 1
  omega

theorem tailTrace_inline_MachineClone100Triples (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    (remaining : Nat) :
    ∀ (i : Nat), i + remaining = triples.length →
      ∀ (base : Tape → List Bool) (_scratchEmpty : base .scratch = [])
        (state : State triples.length),
        (remaining = 0 → state = initialState _) →
        (MachineComposition.advance (TM2.step (program triples nonempty)))^[remaining * rowSteps base]
          (some ⟨startAt triples.length i, state, base⟩) =
          some ⟨some (.cleanup 0), initialState _, Function.update base .reversed
            (((triples.drop i).flatMap (fun t => rowOutput t base)).reverse ++ base .reversed)⟩ := by
  induction remaining with
  | zero =>
      intro i hi base scratchEmpty state finalState
      have heq : i = triples.length := by omega
      subst i
      rw [finalState rfl]
      simp [startAt]
  | succ remaining ih =>
      intro i hi base scratchEmpty state finalState
      have hiLt : i < triples.length := by omega
      let index : Fin triples.length := ⟨i, hiLt⟩
      let after := Function.update base .reversed
        ((rowOutput (triples.get index) base).reverse ++ base .reversed)
      have row := rowTrace triples nonempty index base scratchEmpty state
      have rest := ih (i + 1) (by omega) after
        (by simpa [after] using scratchEmpty) (initialState _) (by intro _; rfl)
      have combined := chain_inline_MachineClone100Triples row rest
      have dropHead : triples.drop i = triples.get index :: triples.drop (i + 1) :=
        List.drop_eq_getElem_cons hiLt
      have hstart : startAt triples.length i = some (.setup (.inr (index, 0))) := by
        simp [startAt, hiLt, index]
      rw [hstart]
      simp only [after, rowSteps_update, rowOutput_update] at combined
      simp only [Function.update_self, Function.update_idem] at combined
      rw [dropHead]
      simp only [List.flatMap_cons, List.reverse_append, List.append_assoc]
      convert combined using 1
      all_goals try with_reducible_and_instances rfl
      congr 1
      simp [Nat.add_mul]

theorem tableTrace_raw (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    (base : Tape → List Bool) (scratchEmpty : base .scratch = [])
    (state : State triples.length) :
    (MachineComposition.advance (TM2.step (program triples nonempty)))^[triples.length * rowSteps base]
      (some ⟨some (.setup (.inr (⟨0, List.length_pos_iff.mpr nonempty⟩, 0))), state, base⟩) =
      some ⟨some (.cleanup 0), initialState _, Function.update base .reversed
        ((triples.flatMap (fun t => rowOutput t base)).reverse ++ base .reversed)⟩ := by
  have h := tailTrace_inline_MachineClone100Triples triples nonempty triples.length 0 (by omega) base scratchEmpty state
    (by intro hz; exact False.elim (by have := List.length_pos_iff.mpr nonempty; omega))
  simpa [startAt, List.length_pos_iff.mpr nonempty] using h

theorem rowOutput_words (t : Nat × Nat × Nat) (base : Tape → List Bool)
    (a b c rhs : Nat)
    (h0 : base (.field 0) = encodeWord a) (h1 : base (.field 1) = encodeWord b)
    (h2 : base (.field 2) = encodeWord c) (h3 : base (.field 3) = encodeWord rhs) :
    rowOutput t base = encodeWords (affineRecord a b c rhs t) := by
  simp [rowOutput, h0, h1, h2, h3, affineEmit_word, affineRecord, encodeWords,
    List.append_assoc]

theorem tableOutput_words (triples : List (Nat × Nat × Nat)) (base : Tape → List Bool)
    (a b c rhs : Nat)
    (h0 : base (.field 0) = encodeWord a) (h1 : base (.field 1) = encodeWord b)
    (h2 : base (.field 2) = encodeWord c) (h3 : base (.field 3) = encodeWord rhs) :
    triples.flatMap (fun t => rowOutput t base) =
      encodeWords (triples.flatMap (affineRecord a b c rhs)) := by
  induction triples with
  | nil => rfl
  | cons t ts ih =>
      simp only [List.flatMap_cons, encodeWords_append, ih,
        rowOutput_words t base a b c rhs h0 h1 h2 h3]

theorem tableTrace (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    (base : Tape → List Bool) (scratchEmpty : base .scratch = [])
    (state : State triples.length) (a b c rhs : Nat)
    (h0 : base (.field 0) = encodeWord a) (h1 : base (.field 1) = encodeWord b)
    (h2 : base (.field 2) = encodeWord c) (h3 : base (.field 3) = encodeWord rhs) :
    (MachineComposition.advance (TM2.step (program triples nonempty)))^[
      triples.length * (3 * ((a + 1) + (b + 1) + (c + 1) + (rhs + 1)) + 12)]
      (some ⟨some (.setup (.inr (⟨0, List.length_pos_iff.mpr nonempty⟩, 0))), state, base⟩) =
      some ⟨some (.cleanup 0), initialState _, Function.update base .reversed
        ((encodeWords (triples.flatMap (affineRecord a b c rhs))).reverse ++ base .reversed)⟩ := by
  have h := tableTrace_raw triples nonempty base scratchEmpty state
  rw [tableOutput_words triples base a b c rhs h0 h1 h2 h3] at h
  simpa only [rowSteps, h0, h1, h2, h3, encodeWord_length] using h

end DFVSGames.Explicit.MachineClone100Triples
end

section

namespace DFVSGames.Explicit.MachineClone100Loop

open DFVSGames.Reduction

open Turing
open DFVSGames.Foundations.Complexity
open DFVSGames.Foundations.Hastad
open MachineClone100Model

def recordBits (r : Record) : List Bool := encodeWords (recordWords r)
def recordsBits (rs : List Record) : List Bool := rs.flatMap recordBits

def clonedRecordBits (triples : List (Nat × Nat × Nat)) (r : Record) : List Bool :=
  encodeWords (triples.flatMap (MachineClone100Triples.affineRecord r.a r.b r.c r.rhs))

def clonedRecordsBits (triples : List (Nat × Nat × Nat)) (rs : List Record) : List Bool :=
  rs.flatMap (clonedRecordBits triples)

def recordFields (r : Record) (j : Fin 4) : List Bool :=
  encodeWord (match j.val with | 0 => r.a | 1 => r.b | 2 => r.c | _ => r.rhs)

def tapes (base : Tape → List Bool) (input counter accumulator : List Bool)
    (fields : Fin 4 → List Bool) : Tape → List Bool
  | .input => input
  | .header => base .header
  | .counter => counter
  | .field j => fields j
  | .scratch => []
  | .reversed => accumulator
  | .output => base .output

theorem update_reversed (base : Tape → List Bool) (input counter acc out : List Bool)
    (fields : Fin 4 → List Bool) :
    Function.update (tapes base input counter acc fields) .reversed out =
      tapes base input counter out fields := by
  funext tape
  cases tape <;> simp [tapes]

theorem counterTapes_eq (base : Tape → List Bool) (input counter acc : List Bool)
    (fields : Fin 4 → List Bool) (n : Nat) :
    MachineUnaryCounter.counterTapes .counter
      (tapes base input counter acc fields) n [] =
      tapes base input (encodeWord n) acc fields := by
  funext tape
  cases tape <;> simp [MachineUnaryCounter.counterTapes, tapes]

theorem fourTapes_eq (base : Tape → List Bool) (input counter acc suffix : List Bool)
    (r : Record) :
    SourceMachine.fourTapes .input Tape.field
      (tapes base input counter acc (fun _ => [])) r.a r.b r.c r.rhs suffix =
      tapes base suffix counter acc (recordFields r) := by
  funext tape
  cases tape with
  | field j =>
    fin_cases j <;>
      simp [SourceMachine.fourTapes, SourceMachine.afterField, SourceMachine.fieldTapes,
        tapes, recordFields]
  | _ =>
    simp [SourceMachine.fourTapes, SourceMachine.afterField, SourceMachine.fieldTapes,
      tapes]

theorem clearFields_eq (base : Tape → List Bool) (input counter acc : List Bool)
    (fields : Fin 4 → List Bool) :
    MachineClone100Cleanup.clearFields (tapes base input counter acc fields) =
      tapes base input counter acc (fun _ => []) := by
  funext tape
  cases tape <;> simp [tapes]

theorem cleanupSteps_eq (base : Tape → List Bool) (input counter acc : List Bool)
    (r : Record) :
    MachineClone100Cleanup.cleanupSteps (tapes base input counter acc (recordFields r)) =
      r.a + r.b + r.c + r.rhs + 8 := by
  simp [MachineClone100Cleanup.cleanupSteps, tapes, recordFields]
  omega

theorem recordBits_length (r : Record) :
    (recordBits r).length = r.a + r.b + r.c + r.rhs + 4 := by
  simp [recordBits, recordWords, encodeWords]
  omega

def bodyCost (D : Nat) (r : Record) : Nat :=
  (2 + 3 * D) * (recordBits r).length + (8 + 12 * D)

theorem bodyCost_eq_inline_MachineClone100Loop (D : Nat) (r : Record) :
    ((r.a + r.b + r.c + r.rhs + 8) +
      D * (3 * ((r.a + 1) + (r.b + 1) + (r.c + 1) + (r.rhs + 1)) + 12)) +
      (r.a + r.b + r.c + r.rhs + 8) = bodyCost D r := by
  rw [bodyCost, recordBits_length]
  ring

def bodyInTime (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    (base : Tape → List Bool) (r : Record) (suffix counter acc : List Bool) :
    StateTransition.EvalsToInTime (TM2.step (program triples nonempty))
      ⟨some (.fieldStart 0), initialState _,
        tapes base (recordBits r ++ suffix) counter acc (fun _ => [])⟩
      (some ⟨some .guard, initialState _,
        tapes base suffix counter ((clonedRecordBits triples r).reverse ++ acc)
          (fun _ => [])⟩)
      (bodyCost triples.length r) := by
  let before := tapes base (recordBits r ++ suffix) counter acc (fun _ => [])
  let parsed := tapes base suffix counter acc (recordFields r)
  let out := (clonedRecordBits triples r).reverse ++ acc
  let emitted := tapes base suffix counter out (recordFields r)
  let parse := SourceMachine.fourFieldsInTime .input Tape.field
    (by intro j h; cases h) Label.fieldStart Label.fieldLoop
    (some (.setup (.inr (⟨0, List.length_pos_iff.mpr nonempty⟩, 0))))
    (program triples nonempty) (by intro j; rfl) (by intro j; rfl)
    before r.a r.b r.c r.rhs suffix rfl ((), defaultControl _) none
  have parsed_eq : SourceMachine.fourTapes .input Tape.field before
      r.a r.b r.c r.rhs suffix = parsed := fourTapes_eq _ _ _ _ _ _
  rw [parsed_eq] at parse
  let table : StateTransition.EvalsToInTime (TM2.step (program triples nonempty))
      ⟨some (.setup (.inr (⟨0, List.length_pos_iff.mpr nonempty⟩, 0))), initialState _, parsed⟩
      (some ⟨some (.cleanup 0), initialState _, emitted⟩)
      (triples.length * (3 * ((r.a + 1) + (r.b + 1) + (r.c + 1) + (r.rhs + 1)) + 12)) := {
    steps := triples.length *
      (3 * ((r.a + 1) + (r.b + 1) + (r.c + 1) + (r.rhs + 1)) + 12)
    evals_in_steps := by
      change (MachineComposition.advance (TM2.step (program triples nonempty)))^[_] _ = _
      have h := MachineClone100Triples.tableTrace triples nonempty parsed rfl
        (initialState _) r.a r.b r.c r.rhs rfl rfl rfl rfl
      simpa only [parsed, tapes, update_reversed, clonedRecordBits, emitted, out] using h
    steps_le_m := Nat.le_refl _ }
  let cleanup := MachineClone100Cleanup.cleanupFourInTime triples nonempty emitted
    ((), defaultControl _) none
  have cleared : MachineClone100Cleanup.clearFields emitted =
      tapes base suffix counter out (fun _ => []) := clearFields_eq _ _ _ _ _
  rw [cleared] at cleanup
  let first := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ parse table
  let combined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first cleanup
  exact {
    toEvalsTo := combined.toEvalsTo
    steps_le_m := by
      apply Nat.le_trans combined.steps_le_m
      have hc : MachineClone100Cleanup.cleanupSteps emitted =
          r.a + r.b + r.c + r.rhs + 8 := cleanupSteps_eq _ _ _ _ _
      have hb := bodyCost_eq_inline_MachineClone100Loop triples.length r
      omega }

def loopCost (D : Nat) : List Record → Nat
  | [] => 1
  | r :: rs => (1 + bodyCost D r) + loopCost D rs

theorem loopCost_eq (D : Nat) (rs : List Record) :
    loopCost D rs = (2 + 3 * D) * (recordsBits rs).length +
      (9 + 12 * D) * rs.length + 1 := by
  induction rs with
  | nil => simp [loopCost, recordsBits]
  | cons r rs ih =>
    simp only [loopCost, ih, recordsBits, List.flatMap_cons, List.length_append,
      List.length_cons, bodyCost]
    ring

def loopInTime (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    (base : Tape → List Bool) (suffix : List Bool) (rs : List Record) (acc : List Bool) :
    StateTransition.EvalsToInTime (TM2.step (program triples nonempty))
      ⟨some .guard, initialState _,
        tapes base (recordsBits rs ++ suffix) (encodeWord rs.length) acc (fun _ => [])⟩
      (some ⟨some .finalCounter, initialState _,
        tapes base suffix (encodeWord 0) ((clonedRecordsBits triples rs).reverse ++ acc)
          (fun _ => [])⟩)
      (loopCost triples.length rs) := by
  induction rs generalizing acc with
  | nil =>
    let guard := MachineUnaryCounter.guardInTime_zero .counter Label.guard
      (.fieldStart 0) .finalCounter (program triples nonempty) rfl
      (tapes base suffix (encodeWord 0) acc (fun _ => [])) []
      ((), defaultControl _) none
    simpa only [counterTapes_eq, loopCost, recordsBits, clonedRecordsBits,
      List.flatMap_nil, List.reverse_nil, List.nil_append, List.length_nil,
      initialState] using guard
  | cons r rs ih =>
    let before := tapes base (recordBits r ++ (recordsBits rs ++ suffix))
      (encodeWord (rs.length + 1)) acc (fun _ => [])
    let guard := MachineUnaryCounter.guardInTime_succ .counter Label.guard
      (.fieldStart 0) .finalCounter (program triples nonempty) rfl before rs.length []
      ((), defaultControl _) none
    simp only [before, counterTapes_eq] at guard
    let body := bodyInTime triples nonempty base r (recordsBits rs ++ suffix)
      (encodeWord rs.length) acc
    let rest := ih ((clonedRecordBits triples r).reverse ++ acc)
    let first := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ guard body
    let combined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first rest
    simpa only [loopCost, recordsBits, clonedRecordsBits, List.flatMap_cons,
      List.length_cons, List.reverse_append, List.append_assoc, initialState,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using combined

def loopInTime_linear (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    (base : Tape → List Bool) (suffix : List Bool) (rs : List Record) (acc : List Bool) :
    StateTransition.EvalsToInTime (TM2.step (program triples nonempty))
      ⟨some .guard, initialState _,
        tapes base (recordsBits rs ++ suffix) (encodeWord rs.length) acc (fun _ => [])⟩
      (some ⟨some .finalCounter, initialState _,
        tapes base suffix (encodeWord 0) ((clonedRecordsBits triples rs).reverse ++ acc)
          (fun _ => [])⟩)
      ((2 + 3 * triples.length) * (recordsBits rs).length +
        (9 + 12 * triples.length) * rs.length + 1) := by
  simpa only [loopCost_eq] using loopInTime triples nonempty base suffix rs acc

theorem recordsBits_equations {n : Nat} (es : List (CloneGap.Equation (Fin n))) :
    recordsBits (es.map recordOfEquation) =
      encodeWords (es.flatMap SourceEncoding.equationWords) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [List.map_cons, recordsBits, List.flatMap_cons, encodeWords_append] at *
    rw [ih]
    rfl

theorem clonedRecordsBits_equations_table (triples : List (Nat × Nat × Nat))
    {n : Nat} (es : List (CloneGap.Equation (Fin n))) :
    clonedRecordsBits triples (es.map recordOfEquation) =
      encodeWords (es.flatMap fun e => triples.flatMap (MachineClone100Table.cloneEquationWords e)) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [List.map_cons, clonedRecordsBits, List.flatMap_cons, encodeWords_append] at *
    rw [ih]
    rfl

def sourceLoopInTime_table (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    {n : Nat} (es : List (CloneGap.Equation (Fin n)))
    (base : Tape → List Bool) (suffix acc : List Bool) :
    StateTransition.EvalsToInTime (TM2.step (program triples nonempty))
      ⟨some .guard, initialState _, tapes base
        (encodeWords (es.flatMap SourceEncoding.equationWords) ++ suffix)
        (encodeWord es.length) acc (fun _ => [])⟩
      (some ⟨some .finalCounter, initialState _, tapes base suffix (encodeWord 0)
        ((encodeWords (es.flatMap fun e => triples.flatMap
          (MachineClone100Table.cloneEquationWords e))).reverse ++ acc) (fun _ => [])⟩)
      ((2 + 3 * triples.length) *
        (encodeWords (es.flatMap SourceEncoding.equationWords)).length +
        (9 + 12 * triples.length) * es.length + 1) := by
  simpa only [recordsBits_equations, clonedRecordsBits_equations_table, List.length_map] using
    loopInTime_linear triples nonempty base suffix (es.map recordOfEquation) acc

end DFVSGames.Explicit.MachineClone100Loop

end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ085_DF.DirectedFeedback_RankGraph_MachineClone100Finish
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

namespace DFVSGames.Explicit.MachineClone100Run

open DFVSGames.Reduction

open Turing
open DFVSGames.Foundations.Complexity
open MachineClone100Model

def tm (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ []) : FinTM2 :=
  machine triples nonempty

def sourceBody (input : SourceEncoding.Input) : List Bool :=
  encodeWords (input.equations.flatMap SourceEncoding.equationWords)

def outputHeaders (triples : List (Nat × Nat × Nat)) (input : SourceEncoding.Input) :
    List Bool :=
  encodeWords [100 * input.«variables», triples.length * input.equations.length]

def outputBody (triples : List (Nat × Nat × Nat)) (input : SourceEncoding.Input) :
    List Bool :=
  encodeWords (input.equations.flatMap fun equation =>
    triples.flatMap (MachineClone100Table.cloneEquationWords equation))

def outputBits (triples : List (Nat × Nat × Nat)) (input : SourceEncoding.Input) :
    List Bool :=
  outputHeaders triples input ++ outputBody triples input

theorem inputBits_eq (input : SourceEncoding.Input) :
    SourceEncoding.inputBits input =
      encodeWords [input.«variables», input.equations.length] ++ sourceBody input := by
  simp only [SourceEncoding.inputBits, SourceEncoding.inputWords, encodeWords_append, sourceBody]

end DFVSGames.Explicit.MachineClone100Run
end

section

namespace DFVSGames.Explicit.MachineClone100

open Turing DFVSGames.Reduction
open DFVSGames.Foundations.Complexity

noncomputable section

theorem input_bits_eq (input : SourceEncoding.Input) :
    SourceEncoding.inputBits (Outer.Clone100.clonedInput input) =
      MachineClone100Run.outputBits triples input := by
  rw [SourceEncoding.inputBits, input_words_eq, encodeWords_append]
  rfl

theorem size_bound (input : SourceEncoding.Input) :
    (SourceEncoding.inputBits (Outer.Clone100.clonedInput input)).length ≤
      (300 * triples.length) * (SourceEncoding.inputBits input).length *
        (SourceEncoding.inputBits input).length +
      (100 + 3 * triples.length) * (SourceEncoding.inputBits input).length + 2 := by
  rw [triples_length]
  exact (Outer.Clone100.clonedInput_bits_length_le input).trans
    (serialized_polynomial_inline_MachineClone100 970200 (SourceEncoding.inputBits input).length
      input.«variables» input.equations.length
      (SourceEncoding.inputBits_length_ge_variables input)
      (SourceEncoding.inputBits_length_ge_equations input))

end

end DFVSGames.Explicit.MachineClone100
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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

namespace DFVSGames.BinaryRenameWords

open BinaryFormula DFVSGames.Foundations

theorem encodeWords_flatMap_inline_MachineBinaryRenameWords {α : Type} (xs : List α) (f : α → List Nat) :
    Complexity.encodeWords (xs.flatMap f) =
      xs.flatMap (fun x => Complexity.encodeWords (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, Complexity.encodeWords_append, ih]

end DFVSGames.BinaryRenameWords

end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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

namespace DFVSGames.Explicit.MachineSingleOrbitCodec

open DFVSGames.Foundations.Target DFVSGames.Foundations.Complexity

theorem gameBits_eq {q : Nat} (I : Instance q) :
    gameBits I = encodeWord I.vertices ++ encodeWord q ++
      encodeWord I.constraints.length ++ rowsBits I.constraints := by
  simp [gameBits, gameWords, encodeWords, rowsBits, List.append_assoc]

theorem doubled_gameBits_eq {q : Nat} (I : Instance q) :
    gameBits (doubleInstance I) = encodeWord (2 * I.vertices) ++ encodeWord q ++
      encodeWord I.constraints.length ++ doubledRowsBits I.constraints := by
  simp [gameBits, gameWords, doubleInstance, encodeWords, doubledRowsBits,
    List.flatMap_map, List.append_assoc]

theorem input_length_eq {q : Nat} (I : Instance q) :
    (gameBits (doubleInstance I)).length =
      2 * I.vertices + q + I.constraints.length + 3 +
        (doubledRowsBits I.constraints).length := by
  rw [doubled_gameBits_eq]
  simp only [List.length_append, encodeWord_length]
  omega

theorem vertices_le_input_length {q : Nat} (I : Instance q) :
    I.vertices ≤ (gameBits (doubleInstance I)).length := by
  rw [input_length_eq]
  omega

theorem rows_le_input_length {q : Nat} (I : Instance q) :
    I.constraints.length ≤ (gameBits (doubleInstance I)).length := by
  rw [input_length_eq]
  omega

end DFVSGames.Explicit.MachineSingleOrbitCodec
end

section

namespace DFVSGames.Explicit.MachineSingleOrbitRows

open Turing DFVSGames.Foundations.Complexity DFVSGames.Foundations.Target
open MachineComposition MachineSingleOrbitProgram MachineSingleOrbitStreams
open MachineSingleOrbitCodec

def rowCost {C q : Nat} (c : Constraint C q) : Nat :=
  (doubledRowBits c).length + C + 3

def rowsCost {C q : Nat} (cs : List (Constraint C q)) : Nat :=
  (doubledRowsBits cs).length + (C + 4) * cs.length + 1

theorem rowsCost_cons {C q : Nat} (c : Constraint C q) (cs : List (Constraint C q)) :
    rowsCost (c :: cs) = rowsCost cs + rowCost c + 1 := by
  simp only [rowsCost, rowCost, doubledRowsBits_cons, List.length_append,
    List.length_cons, Nat.mul_add, Nat.mul_one]
  omega

end DFVSGames.Explicit.MachineSingleOrbitRows
end

section

namespace DFVSGames.Explicit.MachineSingleOrbitRuntime

open Turing DFVSGames.Foundations.Complexity DFVSGames.Foundations.Target
open MachineComposition MachineSingleOrbitProgram MachineSingleOrbitStreams
open MachineSingleOrbitCodec MachineSingleOrbitRows

noncomputable section

def finalTapes {q : Nat} (I : Instance q) : Tape → List Bool :=
  tapes [] (encodeWord I.vertices) [] (encodeWord 0) (gameBits I).reverse []

def prefixCost {q : Nat} (I : Instance q) : Nat :=
  (gameBits (doubleInstance I)).length + (I.vertices + 4) * I.constraints.length + 2

theorem prefixCost_le {q : Nat} (I : Instance q) :
    prefixCost I ≤ prefixPolynomial.eval (gameBits (doubleInstance I)).length := by
  have hC := vertices_le_input_length I
  have hm := rows_le_input_length I
  have hp := Nat.mul_le_mul (Nat.add_le_add_right hC 4) hm
  simp only [prefixCost, prefixPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_C]
  omega

end

end DFVSGames.Explicit.MachineSingleOrbitRuntime
end

section

namespace DFVSGames.Reduction.SourceEquationLookup

open Turing
open DFVSGames.Foundations.Complexity
open DFVSGames.Foundations.Hastad
open MachineComposition SourceMachine SourceEncoding
open SourceClauseLookup (discardFieldsTrace)

variable {σ : Type}

theorem scanTapes_other (base : Tape → List Bool) (i : Nat)
    (indexSuffix input : List Bool) (p : Tape) (hi : p ≠ .index) (hw : p ≠ .work) :
    scanTapes base i indexSuffix input p = base p := by
  simp [scanTapes, MachineUnaryCounter.counterTapes, hi, hw]

theorem update_scanTapes_work (base : Tape → List Bool) (i : Nat)
    (indexSuffix input replacement : List Bool) :
    Function.update (scanTapes base i indexSuffix input) .work replacement =
      scanTapes base i indexSuffix replacement := by
  funext p
  cases p <;> simp [scanTapes, MachineUnaryCounter.counterTapes]

theorem fieldDestination_eq (j : Fin 4) : fieldDestination j.val = .field j := by
  unfold fieldDestination
  congr 1
  apply Fin.ext
  exact Nat.min_eq_left (by omega)

theorem fieldDestination_injective_below (r s : Nat) (hr : r < 4) (hs : s < 4)
    (he : fieldDestination r = fieldDestination s) : r = s := by
  have hv := congrArg (fun t : Tape => match t with | .field j => j.val | _ => 4) he
  simpa [fieldDestination, Nat.min_eq_left (show r ≤ 3 by omega),
    Nat.min_eq_left (show s ≤ 3 by omega)] using hv

theorem readFour_output_field (base : Tape → List Bool) (values : List Nat)
    (hlen : values.length = 4) (suffix : List Bool) (j : Fin 4) :
    SourceFieldArray.sequenceTapes .work fieldDestination base 0 values suffix (.field j) =
      encodeWord (values[j.val]'(by omega)) ++ base (.field j) := by
  have ht := SourceFieldArray.sequenceTapes_selected .work fieldDestination base 0 values
    suffix j.val (by omega) (by intro r hr; simp [fieldDestination])
    (by
      intro r s hr hs he
      apply fieldDestination_injective_below r s (by omega) (by omega)
      simpa only [Nat.zero_add] using he)
  simpa only [Nat.zero_add, fieldDestination_eq] using ht

theorem readFour_output_work (base : Tape → List Bool) (values : List Nat)
    (_hlen : values.length = 4) (suffix : List Bool)
    (hinput : base .work = encodeWords values ++ suffix) :
    SourceFieldArray.sequenceTapes .work fieldDestination base 0 values suffix .work = suffix := by
  apply SourceFieldArray.sequenceTapes_source _ _ _ _ _ _ _ hinput
  intro r hr
  simp [fieldDestination]

theorem readFour_output_frame (base : Tape → List Bool) (values : List Nat)
    (suffix : List Bool) (p : Tape) (hwork : p ≠ .work)
    (hfield : ∀ j : Fin 4, p ≠ .field j) :
    SourceFieldArray.sequenceTapes .work fieldDestination base 0 values suffix p = base p := by
  apply SourceFieldArray.sequenceTapes_other _ _ _ hwork
  intro r hr
  exact hfield _

def outputTapes {n : Nat} (base : Tape → List Bool) (equation : CloneGap.Equation (Fin n))
    (indexSuffix suffix : List Bool) : Tape → List Bool :=
  SourceFieldArray.sequenceTapes .work fieldDestination
    (scanTapes base 0 indexSuffix (encodeWords (equationWords equation) ++ suffix))
    0 (equationWords equation) suffix

def scanSteps {n : Nat} (variableCount declaredEquations : Nat)
    (prior : List (CloneGap.Equation (Fin n))) (equation : CloneGap.Equation (Fin n)) : Nat :=
  variableCount + declaredEquations + 2 +
    (encodeWords (prior.flatMap equationWords)).length + prior.length + 1 +
    (encodeWords (equationWords equation)).length + 5

def lookupSteps {n : Nat} (F : SourceEncoding.Input) (prior : List (CloneGap.Equation (Fin n)))
    (equation : CloneGap.Equation (Fin n)) : Nat :=
  2 * ((inputBits F).length + 1) + scanSteps F.«variables» F.equations.length prior equation

theorem output_source {n : Nat} (base : Tape → List Bool) (equation : CloneGap.Equation (Fin n))
    (indexSuffix suffix : List Bool) :
    outputTapes base equation indexSuffix suffix .source = base .source := by
  rw [outputTapes, readFour_output_frame _ _ _ .source (by decide) (by intro j; simp)]
  exact scanTapes_other _ _ _ _ _ (by decide) (by decide)

theorem output_index {n : Nat} (base : Tape → List Bool) (equation : CloneGap.Equation (Fin n))
    (indexSuffix suffix : List Bool) :
    outputTapes base equation indexSuffix suffix .index = encodeWord 0 ++ indexSuffix := by
  rw [outputTapes, readFour_output_frame _ _ _ .index (by decide) (by intro j; simp),
    scanTapes_index]

theorem output_work {n : Nat} (base : Tape → List Bool) (equation : CloneGap.Equation (Fin n))
    (indexSuffix suffix : List Bool) :
    outputTapes base equation indexSuffix suffix .work = suffix := by
  apply readFour_output_work _ _ (equationWords_length equation) _
  simp

theorem output_field {n : Nat} (base : Tape → List Bool) (equation : CloneGap.Equation (Fin n))
    (indexSuffix suffix : List Bool) (j : Fin 4) :
    outputTapes base equation indexSuffix suffix (.field j) =
      encodeWord ((equationWords equation)[j.val]'(by simp)) ++ base (.field j) := by
  rw [outputTapes, readFour_output_field _ _ (equationWords_length equation)]
  rw [scanTapes_other _ _ _ _ (.field j) (by simp) (by simp)]

theorem output_frame {n : Nat} (base : Tape → List Bool) (equation : CloneGap.Equation (Fin n))
    (indexSuffix suffix : List Bool) (p : Tape) (hindex : p ≠ .index) (hwork : p ≠ .work)
    (hfield : ∀ j : Fin 4, p ≠ .field j) :
    outputTapes base equation indexSuffix suffix p = base p := by
  rw [outputTapes, readFour_output_frame _ _ _ p hwork hfield]
  exact scanTapes_other _ _ _ _ p hindex hwork

theorem lookupSteps_le_input (F : SourceEncoding.Input) (prior : List (CloneGap.Equation (Fin F.«variables»)))
    (equation : CloneGap.Equation (Fin F.«variables»)) (after : List (CloneGap.Equation (Fin F.«variables»)))
    (hsplit : F.equations = prior ++ equation :: after) :
    lookupSteps F prior equation ≤ 4 * (inputBits F).length + 8 := by
  have hlength : (inputBits F).length = F.«variables» + F.equations.length + 2 +
      (encodeWords (prior.flatMap equationWords)).length +
      (encodeWords (equationWords equation)).length +
      (encodeWords (after.flatMap equationWords)).length := by
    simp only [inputBits, inputWords, encodeWords_append, List.length_append,
      encodeWords, encodeWord_length, List.length_nil]
    rw [hsplit]
    simp only [List.flatMap_append, List.flatMap_cons, encodeWords_append, List.length_append]
    omega
  have hp : prior.length ≤ F.equations.length := by
    rw [hsplit, List.length_append, List.length_cons]
    omega
  unfold lookupSteps scanSteps
  omega

theorem timePolynomial_eval (L : Nat) : timePolynomial.eval L = 4 * L + 8 := by
  simp [timePolynomial]

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

namespace DFVSGames.Reduction.MachineSourceTuple

open Turing DFVSGames.Foundations.Complexity
open SourceEncoding
open MachineComposition

variable {width : Nat} {Extra σ : Type}

variable [DecidableEq Extra]

theorem fill_update (j : Fin width) (base : Tape width Extra → List Bool)
    (localTapes : SourceEquationLookup.Tape → List Bool) (p : SourceEquationLookup.Tape)
    (value : List Bool) :
    fill j base (Function.update localTapes p value) =
      Function.update (fill j base localTapes) (place j p) value := by
  funext k
  cases k <;> cases p <;> simp [fill, place, Function.update_apply]
  all_goals split <;> simp_all

def placedConfiguration (j : Fin width) (base : Tape width Extra → List Bool)
    (c : TM2.Cfg (fun _ : SourceEquationLookup.Tape => Bool)
      SourceEquationLookup.Label ((σ × Unit) × Option Bool)) :
    TM2.Cfg (fun _ : Tape width Extra => Bool) (Label width) ((σ × Unit) × Option Bool) :=
  ⟨placedLabel j c.l, c.var, fill j base c.stk⟩

def lookupOutput (j : Fin width) (F : SourceEncoding.Input) (i : Fin F.equations.length)
    (base : Tape width Extra → List Bool) (suffix : List Bool) : Tape width Extra → List Bool :=
  fill j base (SourceEquationLookup.outputTapes (base ∘ place j) F.equations[i.val] suffix
    (encodeWords ((F.equations.drop (i.val + 1)).flatMap equationWords)))

def copiedTapes (j : Fin width) (base : Tape width Extra → List Bool) : Tape width Extra → List Bool :=
  Function.update base .index (base (.savedIndex j))

theorem cleanup_lookupOutput (j : Fin width) (F : SourceEncoding.Input) (i : Fin F.equations.length)
    (base : Tape width Extra → List Bool) (suffix : List Bool) :
    Function.update (Function.update
      (lookupOutput j F i (copiedTapes j base) suffix) .work []) .index [] =
      coordinateOutput j F.equations[i.val] base := by
  funext p
  cases p with
  | source => simp [lookupOutput, fill, coordinateOutput, SourceEquationLookup.output_source,
      copiedTapes, place]
  | index => simp [coordinateOutput]
  | work => simp [coordinateOutput]
  | scratch =>
    simp only [Function.update_of_ne (by simp : (Tape.scratch : Tape width Extra) ≠ .index),
      Function.update_of_ne (by simp : (Tape.scratch : Tape width Extra) ≠ .work), lookupOutput, fill,
      coordinateOutput]
    rw [SourceEquationLookup.output_frame _ _ _ _ .scratch (by simp) (by simp) (by intro s; simp)]
    simp [copiedTapes, place]
  | field k s =>
    by_cases hk : k = j
    · subst k
      simp [lookupOutput, fill, coordinateOutput, SourceEquationLookup.output_field,
        copiedTapes, place]
    · simp [lookupOutput, fill, coordinateOutput, hk, copiedTapes]
  | copyScratch => simp [lookupOutput, fill, coordinateOutput, copiedTapes]
  | savedIndex k => simp [lookupOutput, fill, coordinateOutput, copiedTapes]
  | extra k => simp [lookupOutput, fill, coordinateOutput, copiedTapes]

omit [DecidableEq Extra] in
theorem coordinateOutput_other_field {n : Nat} (j k : Fin width) (s : Fin 4)
    (equation : CloneGap.Equation (Fin n)) (base : Tape width Extra → List Bool) (h : k ≠ j) :
    coordinateOutput j equation base (.field k s) = base (.field k s) := by
  simp [coordinateOutput, h]

theorem suffix_length_le_input (F : SourceEncoding.Input) (i : Nat) :
    (encodeWords ((F.equations.drop i).flatMap equationWords)).length ≤ (inputBits F).length := by
  have hs := List.take_append_drop i F.equations
  have he : inputBits F = encodeWords [F.«variables», F.equations.length] ++
      encodeWords ((F.equations.take i).flatMap equationWords) ++
      encodeWords ((F.equations.drop i).flatMap equationWords) := by
    conv_lhs => rw [inputBits, inputWords, ← hs]
    simp only [List.flatMap_append, encodeWords_append, List.append_assoc]
    rw [hs]
  rw [he, List.length_append, List.length_append]
  omega

def stageTapes (F : SourceEncoding.Input) (tuple : Fin width → Fin F.equations.length)
    (base : Tape width Extra → List Bool) : Nat → Tape width Extra → List Bool
  | 0 => base
  | r + 1 => if h : r < width then
      coordinateOutput ⟨r, h⟩ F.equations[(tuple ⟨r, h⟩).val] (stageTapes F tuple base r)
    else stageTapes F tuple base r

omit [DecidableEq Extra] in
theorem stageTapes_frame (F : SourceEncoding.Input) (tuple : Fin width → Fin F.equations.length)
    (base : Tape width Extra → List Bool) (r : Nat) (p : Tape width Extra)
    (hi : p ≠ .index) (hw : p ≠ .work) (hf : ∀ j s, p ≠ .field j s) :
    stageTapes F tuple base r p = base p := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [stageTapes]
    split
    · cases p <;> simp_all [coordinateOutput]
    · exact ih

omit [DecidableEq Extra] in
theorem stageTapes_clean (F : SourceEncoding.Input) (tuple : Fin width → Fin F.equations.length)
    (base : Tape width Extra → List Bool) (r : Nat) (hi : base .index = []) (hw : base .work = []) :
    stageTapes F tuple base r .index = [] ∧ stageTapes F tuple base r .work = [] := by
  induction r with
  | zero => exact ⟨hi, hw⟩
  | succ r ih =>
    simp only [stageTapes]
    split
    · exact ⟨rfl, rfl⟩
    · exact ih

omit [DecidableEq Extra] in
theorem stageTapes_field (F : SourceEncoding.Input) (tuple : Fin width → Fin F.equations.length)
    (base : Tape width Extra → List Bool) (r : Nat) (j : Fin width) (s : Fin 4) :
    stageTapes F tuple base r (.field j s) = if j.val < r then
      encodeWord ((equationWords F.equations[(tuple j).val])[s.val]'(by simp)) ++ base (.field j s)
      else base (.field j s) := by
  induction r with
  | zero => simp [stageTapes]
  | succ r ih =>
    simp only [stageTapes]
    split
    next hr =>
      by_cases hj : j = (⟨r, hr⟩ : Fin width)
      · subst j
        simp only [coordinateOutput_field, ih]
        simp
      · rw [coordinateOutput_other_field _ _ _ _ _ hj, ih]
        have hval : j.val ≠ r := by intro h; apply hj; exact Fin.ext h
        have he : j.val < r + 1 ↔ j.val < r := by omega
        simp only [he]
    next hr =>
      rw [ih]
      have hjr : j.val < r := by omega
      have hjr' : j.val < r + 1 := by omega
      simp only [hjr, hjr', ite_true, if_true]

theorem equations_length_le_input (F : SourceEncoding.Input) :
    F.equations.length ≤ (inputBits F).length := by
  simp only [inputBits, encodeWords_length, inputWords_length]
  omega

def rhsField (j : Fin width) : Tape width Extra := .field j 3

def equationName {n : Nat} (e : CloneGap.Equation (Fin n)) (s : Fin 3) : Nat :=
  match s.val with
  | 0 => e.first.val
  | 1 => e.second.val
  | _ => e.third.val

theorem equationWords_name {n : Nat} (e : CloneGap.Equation (Fin n)) (s : Fin 3) :
    (equationWords e)[(nameSlot s).val]'(by simp) = equationName e s := by
  obtain ⟨s, hs⟩ := s
  have h : s = 0 ∨ s = 1 ∨ s = 2 := by omega
  rcases h with rfl | rfl | rfl <;> rfl

omit [DecidableEq Extra] in
theorem output_name (F : SourceEncoding.Input) (tuple : Fin width → Fin F.equations.length)
    (base : Tape width Extra → List Bool) (j : Fin width) (s : Fin 3) :
    stageTapes F tuple base width (nameField j s) =
      encodeWord (equationName F.equations[(tuple j).val] s) ++ base (nameField j s) := by
  rw [nameField, stageTapes_field, ite_eq_left j.isLt, equationWords_name]

omit [DecidableEq Extra] in
theorem output_rhs (F : SourceEncoding.Input) (tuple : Fin width → Fin F.equations.length)
    (base : Tape width Extra → List Bool) (j : Fin width) :
    stageTapes F tuple base width (rhsField j) =
      encodeWord (if F.equations[(tuple j).val].rhs then 1 else 0) ++ base (rhsField j) := by
  rw [rhsField, stageTapes_field, ite_eq_left j.isLt]
  rfl

omit [DecidableEq Extra] in
theorem output_savedIndex (F : SourceEncoding.Input) (tuple : Fin width → Fin F.equations.length)
    (base : Tape width Extra → List Bool) (j : Fin width) :
    stageTapes F tuple base width (.savedIndex j) = base (.savedIndex j) :=
  stageTapes_frame F tuple base width (.savedIndex j) (by simp) (by simp) (by simp)

omit [DecidableEq Extra] in
theorem output_savedIndex_unary (F : SourceEncoding.Input)
    (tuple : Fin width → Fin F.equations.length) (base : Tape width Extra → List Bool)
    (hsaved : ∀ j, base (.savedIndex j) = encodeWord (tuple j).val) (j : Fin width) :
    stageTapes F tuple base width (.savedIndex j) = encodeWord (tuple j).val :=
  (output_savedIndex F tuple base j).trans (hsaved j)

end DFVSGames.Reduction.MachineSourceTuple
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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

namespace DFVSGames.Reduction.CloneMachineAffine

open DFVSGames.Foundations.Complexity

theorem output_eq_flatMap {Q : Type} [Fintype Q]
    (emit : Q → Bool → List Bool) (q : Q) (input : List Bool) :
    MachineTransducer.output (fun state _ => state) emit q input =
      input.flatMap (emit q) := by
  induction input with
  | nil => rfl
  | cons b input ih =>
    simp only [MachineTransducer.output, List.flatMap_cons, ih]

end DFVSGames.Reduction.CloneMachineAffine
end

section

namespace DFVSGames.Reduction.MachineAddressHeaders

open Turing
open DFVSGames.Foundations.Complexity
open DFVSGames.Foundations.Hastad
open MachineComposition

namespace Prefix

variable {K Λ σ : Type} [DecidableEq K]

theorem clear_readTapes (slots : Fin 5 ↪ K) (base : K → List Bool)
    (n m : Nat) (suffix : List Bool) :
    Function.update (readTapes slots base n m suffix) (slots 1) [] =
      resultTapes slots base n m := by
  funext tape
  by_cases hw : tape = slots 1
  · subst tape
    simp [readTapes, resultTapes, SourceFieldArray.sequenceTapes, SourceMachine.afterField,
      SourceMachine.fieldTapes, copied, destination, slots.injective.eq_iff]
  · by_cases hn : tape = slots 2
    · subst tape
      simp [readTapes, resultTapes, SourceFieldArray.sequenceTapes, SourceMachine.afterField,
        SourceMachine.fieldTapes, copied, destination, slots.injective.eq_iff]
    · by_cases hm : tape = slots 3
      · subst tape
        simp [readTapes, resultTapes, SourceFieldArray.sequenceTapes, SourceMachine.afterField,
          SourceMachine.fieldTapes, copied, destination, slots.injective.eq_iff]
      · simp [readTapes, resultTapes, SourceFieldArray.sequenceTapes, SourceMachine.afterField,
          SourceMachine.fieldTapes, copied, destination, slots.injective.eq_iff, hw, hn, hm]

theorem readTapes_work (slots : Fin 5 ↪ K) (base : K → List Bool)
    (n m : Nat) (suffix : List Bool) : readTapes slots base n m suffix (slots 1) = suffix := by
  simp [readTapes, SourceFieldArray.sequenceTapes, SourceMachine.afterField,
    SourceMachine.fieldTapes, copied, destination, slots.injective.eq_iff, encodeWords]

def inTime (slots : Fin 5 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ label, program (labels label) = statement slots labels exit label)
    (base : K → List Bool) (n m : Nat) (suffix : List Bool)
    (hinput : base (slots 0) = encodeWords [n, m] ++ suffix)
    (hwork : base (slots 1) = []) (hscratch : base (slots 4) = [])
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .copyOut), ((ambient, ()), register), base⟩
      (some ⟨exit, ((ambient, ()), none), resultTapes slots base n m⟩)
      (3 * (base (slots 0)).length + 6) := by
  have copying := MachineCopy.copyInTime (slots 0) (slots 1) (slots 4)
    (by simp [slots.injective.eq_iff]) (by simp [slots.injective.eq_iff])
    (by simp [slots.injective.eq_iff]) false (labels .copyOut) (labels .copyBack)
    (some (labels (readStart 0))) program (atLabels .copyOut) (atLabels .copyBack)
    base hscratch (ambient, ()) register
  have hc : Function.update base (slots 1) (base (slots 0) ++ base (slots 1)) =
      copied slots base := by simp [copied, hwork]
  rw [hc] at copying
  have reading := SourceFieldArray.sequenceInTime (slots 1) (destination slots)
    (fun r => labels (readStart r)) (fun r => labels (readLoop r)) (some (labels .clear))
    program (copied slots base) 0 [n, m] suffix
    (by
      intro r hr
      simp only [destination]
      split <;> simp [slots.injective.eq_iff])
    (by
      intro r hr
      simpa only [Nat.zero_add] using
        (atLabels (readStart r)).trans (atReadStart slots labels exit r (by simpa using hr)))
    (by
      intro r hr
      simpa only [Nat.zero_add] using
        (atLabels (readLoop r)).trans (atReadLoop slots labels exit r (by simpa using hr)))
    (by simpa using (atLabels (readStart 2)).trans (atReadDone slots labels exit))
    (by simp [copied, hinput]) (ambient, ()) none
  have draining := MachineDrain.drainInTime (slots 1) (labels .clear) exit program
    (atLabels .clear) (readTapes slots base n m suffix) (ambient, ()) none
  have joined := StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _
    (StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ copying reading) draining
  refine { steps := joined.steps, evals_in_steps := ?_, steps_le_m := ?_ }
  · simpa only [clear_readTapes] using joined.evals_in_steps
  · apply Nat.le_trans joined.steps_le_m
    rw [readTapes_work, hinput]
    simp only [List.length_append, encodeWords_length, List.sum_cons, List.sum_nil,
      List.length_cons, List.length_nil]
    omega

end Prefix

noncomputable section

namespace Arithmetic

variable {k s d noiseCount : Nat} {K Λ σ : Type}

variable [DecidableEq K]

structure WorkClean (slots : Layout k s d noiseCount ↪ K) (base : K → List Bool) : Prop where
  accA : base (control slots .accA) = []
  accB : base (control slots .accB) = []
  counter : base (control slots .counter) = []
  scratch : base (control slots .scratch) = []
  coefficients : ∀ i : Coefficients k s d noiseCount, base (slots (.inr i)) = []

structure Clean (slots : Layout k s d noiseCount ↪ K) (base : K → List Bool) : Prop
    extends WorkClean slots base where
  baseValue : base (control slots .baseValue) = []
  capacity : base (control slots .capacity) = []
  temporary : base (control slots .temporary) = []

theorem WorkClean.update_control {slots : Layout k s d noiseCount ↪ K} {base : K → List Bool}
    (clean : WorkClean slots base) (c : Control)
    (other : c ≠ .accA ∧ c ≠ .accB ∧ c ≠ .counter ∧ c ≠ .scratch) (word : List Bool) :
    WorkClean slots (Function.update base (control slots c) word) := by
  constructor
  · simpa [other.1.symm] using clean.accA
  · simpa [other.2.1.symm] using clean.accB
  · simpa [other.2.2.1.symm] using clean.counter
  · simpa [other.2.2.2.symm] using clean.scratch
  · intro i
    simpa [control, slots.injective.eq_iff] using clean.coefficients i

def steps (k s d noiseCount n m : Nat) : Nat :=
  2 * n + 3 * m + 10 +
    SourceHeaderCounts.Eval.steps (polynomial k s d noiseCount .capacity) (radix s d n m) +
    SourceHeaderCounts.Eval.steps (polynomial k s d noiseCount .edges) m +
    3 * capacity k s d n m + edgeCount k s d noiseCount m + 8

def preparedBase (slots : Layout k s d noiseCount ↪ K) (base : K → List Bool)
    (n m : Nat) : K → List Bool :=
  Function.update base (control slots .baseValue) (encodeWord (radix s d n m))

def timePolynomial (k s d noiseCount : Nat) : Polynomial Nat :=
  let B : Polynomial Nat := Polynomial.C 2 * Polynomial.X + Polynomial.C (baseConstant s d)
  (CookLevin.PolynomialMachine.timePolynomial (polynomial k s d noiseCount .capacity)).comp B +
    CookLevin.PolynomialMachine.timePolynomial (polynomial k s d noiseCount .edges) +
    Polynomial.C 3 * (polynomial k s d noiseCount .capacity).comp B +
    polynomial k s d noiseCount .edges + Polynomial.C 5 * Polynomial.X + Polynomial.C 18

theorem steps_le_timePolynomial (k s d noiseCount n m L : Nat) (hn : n ≤ L) (hm : m ≤ L) :
    steps k s d noiseCount n m ≤ (timePolynomial k s d noiseCount).eval L := by
  have hB : radix s d n m ≤ 2 * L + baseConstant s d := by unfold radix; omega
  have hEval (p : Polynomial Nat) (a b : Nat) (hab : a ≤ b) :
      SourceHeaderCounts.Eval.steps p a ≤ (CookLevin.PolynomialMachine.timePolynomial p).eval b := by
    apply Nat.le_trans (m := (CookLevin.PolynomialMachine.timePolynomial p).eval a)
    · rw [CookLevin.PolynomialMachine.timePolynomial_eval]
      unfold SourceHeaderCounts.Eval.steps
      omega
    · exact natPolynomial_eval_mono _ hab
  have h1 := hEval (polynomial k s d noiseCount .capacity) _ _ hB
  have h2 := hEval (polynomial k s d noiseCount .edges) _ _ hm
  have hc : capacity k s d n m ≤ (2 * L + baseConstant s d) ^ (1 + 9 * k) :=
    Nat.pow_le_pow_left hB _
  have he : edgeCount k s d noiseCount m ≤ edgeCount k s d noiseCount L :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hm _)
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_comp, polynomial_capacity_eval, polynomial_edges_eval]
  unfold steps
  omega

end Arithmetic

variable {k s d noiseCount : Nat} {K Λ σ : Type} [DecidableEq K]

structure Clean (slots : Layout k s d noiseCount ↪ K) (base : K → List Bool) : Prop
    extends Arithmetic.Clean (arithmeticSlots slots) base where
  readCopy : base (slots (.inl 1)) = []
  variableCount : base (Arithmetic.control (arithmeticSlots slots) .variableCount) = []
  occurrenceCount : base (Arithmetic.control (arithmeticSlots slots) .occurrenceCount) = []

theorem prefixResult_coefficient (slots : Layout k s d noiseCount ↪ K)
    (base : K → List Bool) (n m : Nat) (i : Arithmetic.Coefficients k s d noiseCount) :
    Prefix.resultTapes (prefixSlots slots) base n m (arithmeticSlots slots (.inr i)) =
      base (arithmeticSlots slots (.inr i)) := by
  apply Prefix.resultTapes_other <;>
    simp [prefixSlots_apply, arithmeticSlots, slots.injective.eq_iff]

theorem Clean.afterPrefix {slots : Layout k s d noiseCount ↪ K} {base : K → List Bool}
    (clean : Clean slots base) (n m : Nat) :
    Arithmetic.Clean (arithmeticSlots slots) (Prefix.resultTapes (prefixSlots slots) base n m) := by
  constructor
  · constructor
    · rw [prefixResult_control _ _ _ _ _ (by decide) (by decide)]; exact clean.accA
    · rw [prefixResult_control _ _ _ _ _ (by decide) (by decide)]; exact clean.accB
    · rw [prefixResult_control _ _ _ _ _ (by decide) (by decide)]; exact clean.counter
    · rw [prefixResult_control _ _ _ _ _ (by decide) (by decide)]; exact clean.scratch
    · intro i; rw [prefixResult_coefficient]; exact clean.coefficients i
  · rw [prefixResult_control _ _ _ _ _ (by decide) (by decide)]; exact clean.baseValue
  · rw [prefixResult_control _ _ _ _ _ (by decide) (by decide)]; exact clean.capacity
  · rw [prefixResult_control _ _ _ _ _ (by decide) (by decide)]; exact clean.temporary

def timePolynomial (k s d noiseCount : Nat) : Polynomial Nat :=
  Arithmetic.timePolynomial k s d noiseCount + Polynomial.C 3 * Polynomial.X + Polynomial.C 6

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
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_CanonicalWordTemplate
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

namespace DFVSGames.Reduction.AddressMachineSpace

open DFVSGames.Foundations.Complexity

variable (k s d noiseCount : Nat)

theorem tupleOutput_headerTape (F : SourceEncoding.Input)
    (tuple : Fin k → Fin F.equations.length) (base : Tape k s d noiseCount → List Bool)
    (c : MachineAddressHeaders.Arithmetic.Control) :
    MachineSourceTuple.stageTapes F tuple base k (headerTape k s d noiseCount c) =
      base (headerTape k s d noiseCount c) :=
  MachineSourceTuple.stageTapes_frame F tuple base k _
    (by simp [headerTape])
    (by simp [headerTape])
    (by intros; simp [headerTape])

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

namespace DFVSGames.Integration.AddressTupleLoaded

open DFVSGames.Reduction DFVSGames.Foundations.Complexity

abbrev Arena (k s d noiseCount : Nat) := AddressMachineSpace.Tape k s d noiseCount

variable {k s d noiseCount : Nat}

def fieldAssignment (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (baseArena : Arena k s d noiseCount → List Bool) : Arena k s d noiseCount → List Bool
  | .field j slot => encodeWord
      ((SourceEncoding.equationWords F.equations[(tuple j).val])[slot.val]'(by simp)) ++
        baseArena (.field j slot)
  | tape => baseArena tape

theorem stageTapes_eq (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (baseArena : Arena k s d noiseCount → List Bool)
    (hindex : baseArena .index = []) (hwork : baseArena .work = []) :
    MachineSourceTuple.stageTapes F tuple baseArena k = fieldAssignment F tuple baseArena := by
  funext tape
  cases tape with
  | index => exact (MachineSourceTuple.stageTapes_clean F tuple baseArena k hindex hwork).1.trans hindex.symm
  | work => exact (MachineSourceTuple.stageTapes_clean F tuple baseArena k hindex hwork).2.trans hwork.symm
  | field j slot =>
    simp only [MachineSourceTuple.stageTapes_field, ite_eq_left j.isLt, fieldAssignment]
  | source =>
    exact MachineSourceTuple.stageTapes_frame F tuple baseArena k _
      (by simp) (by simp) (by intros; simp)
  | scratch =>
    exact MachineSourceTuple.stageTapes_frame F tuple baseArena k _
      (by simp) (by simp) (by intros; simp)
  | copyScratch =>
    exact MachineSourceTuple.stageTapes_frame F tuple baseArena k _
      (by simp) (by simp) (by intros; simp)
  | savedIndex j =>
    exact MachineSourceTuple.stageTapes_frame F tuple baseArena k _
      (by simp) (by simp) (by intros; simp)
  | extra value =>
    exact MachineSourceTuple.stageTapes_frame F tuple baseArena k _
      (by simp) (by simp) (by intros; simp)

theorem loaded_field (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (baseArena : Arena k s d noiseCount → List Bool)
    (hempty : ∀ j slot, baseArena (.field j slot) = []) (j : Fin k) (slot : Fin 4) :
    MachineSourceTuple.stageTapes F tuple baseArena k (.field j slot) =
      encodeWord ((SourceEncoding.equationWords F.equations[(tuple j).val])[slot.val]'(by simp)) := by
  rw [MachineSourceTuple.stageTapes_field, ite_eq_left j.isLt, hempty, List.append_nil]

theorem loaded_extra (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (baseArena : Arena k s d noiseCount → List Bool)
    (extra : AddressMachineSpace.Extra k s d noiseCount) :
    MachineSourceTuple.stageTapes F tuple baseArena k (.extra extra) = baseArena (.extra extra) :=
  MachineSourceTuple.stageTapes_frame F tuple baseArena k _
    (by simp) (by simp) (by intros; simp)

theorem loaded_header (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (baseArena : Arena k s d noiseCount → List Bool)
    (header : MachineAddressHeaders.Arithmetic.Control) :
    MachineSourceTuple.stageTapes F tuple baseArena k
      (AddressMachineSpace.headerTape k s d noiseCount header) =
        baseArena (AddressMachineSpace.headerTape k s d noiseCount header) :=
  AddressMachineSpace.tupleOutput_headerTape k s d noiseCount F tuple baseArena header

theorem loaded_radix (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (baseArena : Arena k s d noiseCount → List Bool) (B : Nat)
    (hB : baseArena (AddressMachineSpace.headerTape k s d noiseCount .baseValue) = encodeWord B) :
    MachineSourceTuple.stageTapes F tuple baseArena k
      (MachineAddressEdge.addressSlots (AddressMachineSpace.addressEdgeSlots k s d noiseCount)
        .radix) = encodeWord B := by
  rw [AddressMachineSpace.addressSlots_radix, loaded_header, hB]

theorem loaded_capacity (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (baseArena : Arena k s d noiseCount → List Bool) (C : Nat)
    (hC : baseArena (AddressMachineSpace.headerTape k s d noiseCount .capacity) = encodeWord C) :
    MachineSourceTuple.stageTapes F tuple baseArena k
      (MachineAddressEdge.capacityTape (AddressMachineSpace.addressEdgeSlots k s d noiseCount)) =
        encodeWord C := by
  rw [AddressMachineSpace.addressSlots_capacity, loaded_header, hC]

theorem loaded_privateAddress (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (baseArena : Arena k s d noiseCount → List Bool)
    (tape : MachineTemplateAddress.Tape (4 * k) (1 + 9 * k)) :
    MachineSourceTuple.stageTapes F tuple baseArena k
      (AddressMachineSpace.privateAddress k s d noiseCount tape) =
        baseArena (AddressMachineSpace.privateAddress k s d noiseCount tape) :=
  loaded_extra F tuple baseArena _

theorem loaded_clean (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (baseArena : Arena k s d noiseCount → List Bool)
    (clean : MachineAddressEdge.Clean (AddressMachineSpace.addressEdgeSlots k s d noiseCount)
      baseArena) :
    MachineAddressEdge.Clean (AddressMachineSpace.addressEdgeSlots k s d noiseCount)
      (MachineSourceTuple.stageTapes F tuple baseArena k) := by
  constructor
  · constructor
    · exact (loaded_privateAddress F tuple baseArena .reversed).trans clean.address.reversed
    · exact (loaded_privateAddress F tuple baseArena .forward).trans clean.address.forward
    · exact (loaded_privateAddress F tuple baseArena .copyScratch).trans clean.address.copyScratch
    · exact (loaded_privateAddress F tuple baseArena .accA).trans clean.address.accA
    · exact (loaded_privateAddress F tuple baseArena .accB).trans clean.address.accB
    · exact (loaded_privateAddress F tuple baseArena .counter).trans clean.address.counter
    · exact (loaded_privateAddress F tuple baseArena .hornerScratch).trans clean.address.hornerScratch
    · intro j
      exact (loaded_privateAddress F tuple baseArena (.digit j)).trans (clean.address.digit j)
  · exact (loaded_privateAddress F tuple baseArena .output).trans clean.work

theorem loaded_name (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (baseArena : Arena k s d noiseCount → List Bool)
    (hempty : ∀ j slot, baseArena (.field j slot) = []) (j : Fin k) (slot : Fin 3) :
    MachineSourceTuple.stageTapes F tuple baseArena k (MachineSourceTuple.nameField j slot) =
      encodeWord (MachineSourceTuple.equationName F.equations[(tuple j).val] slot) := by
  rw [MachineSourceTuple.output_name]
  change _ ++ baseArena (.field j (MachineSourceTuple.nameSlot slot)) = _
  rw [hempty, List.append_nil]

theorem loaded_occurrence (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (baseArena : Arena k s d noiseCount → List Bool)
    (hsaved : ∀ j, baseArena (.savedIndex j) = encodeWord (tuple j).val) (j : Fin k) :
    MachineSourceTuple.stageTapes F tuple baseArena k (.savedIndex j) = encodeWord (tuple j).val :=
  MachineSourceTuple.output_savedIndex_unary F tuple baseArena hsaved j

def canonicalValues (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (j : Fin k) : Fin 4 → Nat :=
  CanonicalBodyTemplate.recordFields
    (MachineSourceTuple.equationName F.equations[(tuple j).val]) (tuple j).val

theorem loaded_canonicalField (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (baseArena : Arena k s d noiseCount → List Bool)
    (hsaved : ∀ j, baseArena (.savedIndex j) = encodeWord (tuple j).val)
    (hempty : ∀ j slot, baseArena (.field j slot) = []) (j : Fin k) (slot : Fin 4) :
    MachineSourceTuple.stageTapes F tuple baseArena k
      (AddressMachineSpace.canonicalField k s d noiseCount j slot) =
        encodeWord (canonicalValues F tuple j slot) := by
  fin_cases slot
  · simpa [AddressMachineSpace.canonicalField, canonicalValues, CanonicalBodyTemplate.recordFields,
      MachineSourceTuple.nameField, MachineSourceTuple.nameSlot, MachineSourceTuple.equationName] using
      loaded_name F tuple baseArena hempty j 0
  · simpa [AddressMachineSpace.canonicalField, canonicalValues, CanonicalBodyTemplate.recordFields,
      MachineSourceTuple.nameField, MachineSourceTuple.nameSlot, MachineSourceTuple.equationName] using
      loaded_name F tuple baseArena hempty j 1
  · simpa [AddressMachineSpace.canonicalField, canonicalValues, CanonicalBodyTemplate.recordFields,
      MachineSourceTuple.nameField, MachineSourceTuple.nameSlot, MachineSourceTuple.equationName] using
      loaded_name F tuple baseArena hempty j 2
  · simpa [AddressMachineSpace.canonicalField, canonicalValues, CanonicalBodyTemplate.recordFields] using
      loaded_occurrence F tuple baseArena hsaved j

theorem loaded_savedFields (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (baseArena : Arena k s d noiseCount → List Bool)
    (hsaved : ∀ j, baseArena (.savedIndex j) = encodeWord (tuple j).val)
    (hempty : ∀ j slot, baseArena (.field j slot) = []) :
    (fun i => MachineSourceTuple.stageTapes F tuple baseArena k
      (MachineAddressEdge.addressSlots (AddressMachineSpace.addressEdgeSlots k s d noiseCount)
        (.field i))) = CanonicalBodyMachine.savedFields (canonicalValues F tuple) := by
  funext i
  change MachineSourceTuple.stageTapes F tuple baseArena k
    (AddressMachineSpace.canonicalField k s d noiseCount
      ((CanonicalBodyMachine.fieldEquiv k).symm i).1
      ((CanonicalBodyMachine.fieldEquiv k).symm i).2) = _
  exact loaded_canonicalField F tuple baseArena hsaved hempty _ _

end DFVSGames.Integration.AddressTupleLoaded
end

section

namespace DFVSGames.Integration.AddressTupleCleanup

open Turing DFVSGames.Reduction DFVSGames.Foundations.Complexity

variable (k s d noiseCount : Nat)

noncomputable abbrev steps (base : AddressMachineSpace.Tape k s d noiseCount → List Bool) :=
  MachineDrainMany.steps (loadedFields k s d noiseCount) base

noncomputable abbrev budget (base : AddressMachineSpace.Tape k s d noiseCount → List Bool) :=
  MachineDrainMany.lengthSum (loadedFields k s d noiseCount) base + 4 * k

theorem steps_le (base : AddressMachineSpace.Tape k s d noiseCount → List Bool) :
    steps k s d noiseCount base ≤ budget k s d noiseCount base := by
  simpa only [loadedFields_length] using
    MachineDrainMany.steps_le (loadedFields k s d noiseCount) base

end DFVSGames.Integration.AddressTupleCleanup
end

section

namespace DFVSGames.Integration.AddressTupleFrame

open DFVSGames.Reduction DFVSGames.Foundations.Complexity

variable {k s d noiseCount : Nat}

abbrev Arena (k s d noiseCount : Nat) := AddressMachineSpace.Tape k s d noiseCount

theorem cleared_outputTapes (base : Arena k s d noiseCount → List Bool)
    (output : Arena k s d noiseCount) (bits : List Bool)
    (outside : ∀ j : Fin k, ∀ slot : Fin 4, output ≠ .field j slot) :
    AddressTupleCleanup.cleared k s d noiseCount
        (MachineFieldTemplate.outputTapes base output bits) =
      MachineFieldTemplate.outputTapes
        (AddressTupleCleanup.cleared k s d noiseCount base) output bits := by
  funext tape
  by_cases h : tape = output
  · subst tape
    rw [AddressTupleCleanup.cleared_outside k s d noiseCount _ output outside,
      MachineFieldTemplate.outputTapes_output, MachineFieldTemplate.outputTapes_output,
      AddressTupleCleanup.cleared_outside k s d noiseCount base output outside]
  · rw [MachineFieldTemplate.outputTapes_other _ output bits tape h]
    change MachineDrainMany.finalTapes (AddressTupleCleanup.loadedFields k s d noiseCount)
        (MachineFieldTemplate.outputTapes base output bits) tape =
      MachineDrainMany.finalTapes (AddressTupleCleanup.loadedFields k s d noiseCount) base tape
    rw [MachineDrainMany.finalTapes_apply, MachineDrainMany.finalTapes_apply,
      MachineFieldTemplate.outputTapes_other base output bits tape h]

theorem cleared_appended (base : Arena k s d noiseCount → List Bool) (bits : List Bool) :
    AddressTupleCleanup.cleared k s d noiseCount
        (MachineAddressEdge.appended (AddressMachineSpace.addressEdgeSlots k s d noiseCount)
          base bits) =
      MachineAddressEdge.appended (AddressMachineSpace.addressEdgeSlots k s d noiseCount)
        (AddressTupleCleanup.cleared k s d noiseCount base) bits := by
  apply cleared_outputTapes
  intro j slot
  simp [AddressMachineSpace.addressSlots_output, AddressMachineSpace.headerTape,
    ]

theorem cleared_fieldAssignment (F : SourceEncoding.Input)
    (tuple : Fin k → Fin F.equations.length) (base : Arena k s d noiseCount → List Bool)
    (hfields : ∀ j slot, base (.field j slot) = []) :
    AddressTupleCleanup.cleared k s d noiseCount
      (AddressTupleLoaded.fieldAssignment F tuple base) = base := by
  funext tape
  cases tape <;> simp [AddressTupleLoaded.fieldAssignment, hfields]

theorem cleared_loaded (F : SourceEncoding.Input)
    (tuple : Fin k → Fin F.equations.length) (base : Arena k s d noiseCount → List Bool)
    (hindex : base .index = []) (hwork : base .work = [])
    (hfields : ∀ j slot, base (.field j slot) = []) :
    AddressTupleCleanup.cleared k s d noiseCount
      (MachineSourceTuple.stageTapes F tuple base k) = base := by
  rw [AddressTupleLoaded.stageTapes_eq F tuple base hindex hwork]
  exact cleared_fieldAssignment F tuple base hfields

theorem cleared_appended_loaded (F : SourceEncoding.Input)
    (tuple : Fin k → Fin F.equations.length) (base : Arena k s d noiseCount → List Bool)
    (hindex : base .index = []) (hwork : base .work = [])
    (hfields : ∀ j slot, base (.field j slot) = []) (bits : List Bool) :
    AddressTupleCleanup.cleared k s d noiseCount
        (MachineAddressEdge.appended (AddressMachineSpace.addressEdgeSlots k s d noiseCount)
          (MachineSourceTuple.stageTapes F tuple base k) bits) =
      MachineAddressEdge.appended (AddressMachineSpace.addressEdgeSlots k s d noiseCount)
        base bits := by
  rw [cleared_appended, cleared_loaded F tuple base hindex hwork hfields]

end DFVSGames.Integration.AddressTupleFrame
end

section

namespace DFVSGames.Reduction.MachineRhsLoad

open Turing
open DFVSGames.Foundations.Complexity

section Program

variable {k : Nat} {K Λ σ : Type} [DecidableEq K]

omit [DecidableEq K] in
theorem readRhs_of_unary (field : Fin k → K) (tapes : K → List Bool)
    (values : Fin k → Bool) (suffix : Fin k → List Bool)
    (encoded : ∀ i, tapes (field i) = encodeWord (if values i then 1 else 0) ++ suffix i) :
    readRhs field tapes = values := by
  funext i
  rw [readRhs, encoded]
  cases values i <;> rfl

theorem loadStep (field : Fin k → K) (entry : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State k σ))
    (atEntry : program entry = statement field exit)
    (state : State k σ) (tapes : K → List Bool) (values : Fin k → Bool)
    (suffix : Fin k → List Bool)
    (encoded : ∀ i, tapes (field i) = encodeWord (if values i then 1 else 0) ++ suffix i) :
    TM2.step program ⟨some entry, state, tapes⟩ =
      some ⟨exit, setRhs state values, tapes⟩ := by
  change some (TM2.stepAux (program entry) state tapes) = _
  rw [atEntry, stepAux_statement, readRhs_of_unary field tapes values suffix encoded]

def loadInTime (field : Fin k → K) (entry : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State k σ))
    (atEntry : program entry = statement field exit)
    (state : State k σ) (tapes : K → List Bool) (values : Fin k → Bool)
    (suffix : Fin k → List Bool)
    (encoded : ∀ i, tapes (field i) = encodeWord (if values i then 1 else 0) ++ suffix i) :
    StateTransition.EvalsToInTime (TM2.step program) ⟨some entry, state, tapes⟩
      (some ⟨exit, setRhs state values, tapes⟩) 1 where
  steps := 1
  evals_in_steps := by
    change (MachineComposition.advance (TM2.step program))^[1] _ = _
    simpa only [Function.iterate_one, MachineComposition.advance_some] using
      loadStep field entry exit program atEntry state tapes values suffix encoded
  steps_le_m := Nat.le_refl _

end Program

end DFVSGames.Reduction.MachineRhsLoad
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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

namespace DFVSGames.Reduction.MachineOutcomeRows

open Turing
open DFVSGames.Foundations.Complexity

variable {k q width : Nat} {K Λ σ : Type} [DecidableEq K]

def payload (B C : Nat) (values : Spec q width → Values width) (row : Spec q width) :
    List Bool :=
  MachineAddressEdge.edgeBits B C (values row).left (values row).right row.permutation

def rowResult (slots : MachineAddressEdge.Tape q width ↪ K)
    (B C : Nat) (values : Spec q width → Values width) (row : Spec q width)
    (base : K → List Bool) : K → List Bool :=
  MachineAddressEdge.appended slots base (payload B C values row)

def rowCost (slots : MachineAddressEdge.Tape q width ↪ K)
    (B C : Nat) (values : Spec q width → Values width) (row : Spec q width)
    (base : K → List Bool) : Nat :=
  MachineAddressEdge.phaseSteps row.left row.right slots base B C
    (values row).left (values row).right

def rowCosts (slots : MachineAddressEdge.Tape q width ↪ K)
    (B C : Nat) (values : Spec q width → Values width) :
    List (Spec q width) → (K → List Bool) → List Nat
  | [], _ => []
  | row :: rows, base => rowCost slots B C values row base ::
      rowCosts slots B C values rows (rowResult slots B C values row base)

structure Invariant (slots : MachineAddressEdge.Tape q width ↪ K)
    (B C : Nat) (values : Spec q width → Values width) (rows : List (Spec q width))
    (base : K → List Bool) : Prop where
  clean : MachineAddressEdge.Clean slots base
  radix : base (MachineAddressEdge.addressSlots slots .radix) = encodeWord B
  capacity : base (MachineAddressEdge.capacityTape slots) = encodeWord C
  correct : ∀ row ∈ rows,
    MachineFieldTemplate.templateOutput row.left
      (fun j => base (MachineAddressEdge.addressSlots slots (.field j))) =
        encodeWords (values row).left ∧
    MachineFieldTemplate.templateOutput row.right
      (fun j => base (MachineAddressEdge.addressSlots slots (.field j))) =
        encodeWords (values row).right

theorem Invariant.appended (slots : MachineAddressEdge.Tape q width ↪ K)
    (B C : Nat) (values : Spec q width → Values width) (rows : List (Spec q width))
    (base : K → List Bool) (valid : Invariant slots B C values rows base) (bits : List Bool) :
    Invariant slots B C values rows (MachineAddressEdge.appended slots base bits) := by
  constructor
  · exact MachineAddressEdge.Clean.appended slots base valid.clean bits
  · simpa only [MachineAddressEdge.appended_address] using valid.radix
  · simpa only [MachineAddressEdge.appended_capacity] using valid.capacity
  · intro row hrow
    simpa only [MachineAddressEdge.appended_address] using valid.correct row hrow

theorem appended_nil (slots : MachineAddressEdge.Tape q width ↪ K) (base : K → List Bool) :
    MachineAddressEdge.appended slots base [] = base := by
  simp [MachineAddressEdge.appended, MachineFieldTemplate.outputTapes]

theorem sequence_result (slots : MachineAddressEdge.Tape q width ↪ K)
    (B C : Nat) (values : Spec q width → Values width) (rows : List (Spec q width))
    (base : K → List Bool) :
    MachineFiniteSequence.resultOf (rowResult slots B C values) rows base =
      MachineAddressEdge.appended slots base (rows.flatMap (payload B C values)) := by
  induction rows generalizing base with
  | nil => simpa only [MachineFiniteSequence.resultOf, List.flatMap_nil] using
      (appended_nil slots base).symm
  | cons row rows ih =>
    rw [MachineFiniteSequence.resultOf, ih]
    exact MachineAddressEdge.appended_append slots base _ _

theorem sequence_steps (slots : MachineAddressEdge.Tape q width ↪ K)
    (B C : Nat) (values : Spec q width → Values width) (rows : List (Spec q width))
    (base : K → List Bool) :
    MachineFiniteSequence.steps (rowResult slots B C values) (rowCost slots B C values)
      rows base = (rowCosts slots B C values rows base).sum := by
  induction rows generalizing base with
  | nil => rfl
  | cons row rows ih => simp only [MachineFiniteSequence.steps, rowCosts, List.sum_cons, ih]

noncomputable def timePolynomial (rows : List (Spec q width)) : Polynomial Nat :=
  (rows.map (fun row => MachineAddressEdge.timePolynomial
    row.left.length row.right.length width)).sum + 1

theorem rowCosts_sum_le (slots : MachineAddressEdge.Tape q width ↪ K)
    (rows : List (Spec q width)) (base : K → List Bool)
    (B C : Nat) (values : Spec q width → Values width) (M : Nat)
    (clean : MachineAddressEdge.Clean slots base)
    (fieldsBound : ∀ j, (base (MachineAddressEdge.addressSlots slots (.field j))).length ≤ M)
    (radixBound : B ≤ M) (capacityBound : C ≤ M)
    (valuesBound : ∀ row ∈ rows,
      (encodeWords (values row).left).length ≤ M ∧
      (encodeWords (values row).right).length ≤ M ∧
      (∀ i, i < width → MachineTemplateAddress.digits (values row).left i ≤ M) ∧
      (∀ i, i < width → MachineTemplateAddress.digits (values row).right i ≤ M)) :
    (rowCosts slots B C values rows base).sum ≤
      ((rows.map (fun row => MachineAddressEdge.timePolynomial
        row.left.length row.right.length width)).sum).eval M := by
  induction rows generalizing base with
  | nil => simp [rowCosts]
  | cons row rows ih =>
    have bounds := valuesBound row (by simp)
    have first := MachineAddressEdge.phaseSteps_le_timePolynomial row.left row.right
      slots base B C (values row).left (values row).right
      (values row).left_length (values row).right_length clean M fieldsBound
      bounds.1 bounds.2.1 radixBound capacityBound bounds.2.2.1 bounds.2.2.2
    have rest := ih (rowResult slots B C values row base)
      (MachineAddressEdge.Clean.appended slots base clean (payload B C values row))
      (by simpa only [rowResult, MachineAddressEdge.appended_address] using fieldsBound)
      (fun r hr => valuesBound r (List.mem_cons_of_mem row hr))
    simpa only [rowCosts, List.sum_cons, List.map_cons, Polynomial.eval_add, rowCost] using
      Nat.add_le_add first rest

theorem phaseCost_le_timePolynomial (slots : MachineAddressEdge.Tape q width ↪ K)
    (rows : List (Spec q width)) (base : K → List Bool)
    (B C : Nat) (values : Spec q width → Values width) (M : Nat)
    (clean : MachineAddressEdge.Clean slots base)
    (fieldsBound : ∀ j, (base (MachineAddressEdge.addressSlots slots (.field j))).length ≤ M)
    (radixBound : B ≤ M) (capacityBound : C ≤ M)
    (valuesBound : ∀ row ∈ rows,
      (encodeWords (values row).left).length ≤ M ∧
      (encodeWords (values row).right).length ≤ M ∧
      (∀ i, i < width → MachineTemplateAddress.digits (values row).left i ≤ M) ∧
      (∀ i, i < width → MachineTemplateAddress.digits (values row).right i ≤ M)) :
    (rowCosts slots B C values rows base).sum + 1 ≤ (timePolynomial rows).eval M := by
  have h := rowCosts_sum_le slots rows base B C values M clean fieldsBound
    radixBound capacityBound valuesBound
  simpa only [timePolynomial, Polynomial.eval_add, Polynomial.eval_one] using
    Nat.add_le_add_right h 1

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

namespace DFVSGames.Reduction.AddressGame

open ActualSource
open Foundations.Target
open Integration.VertexEmbedding

def tableOutput (S : Source) (k : Nat) {s d : Nat} (T : Integration.NoiseTables.Table s d) :
    Instance (2^s) :=
  outputInstance S k (Integration.TableReduction.tableSkeleton T)
    (Integration.TableReduction.tableEnumeration T Prod.fst (fun _ _ => rfl))

end DFVSGames.Reduction.AddressGame
end

section

namespace DFVSGames.Reduction.AddressByteSemantics

open Integration.BinaryLinear Foundations.Complexity ActualSource

def queryRank {k s d : Nat} (base : Nat) (fields : Fin k → Fin 4 → Nat)
    (X : ActualGame.Map k s d) (b : Fin k → F2) : Nat :=
  CanonicalAddress.radix base (queryWords fields X b)

def edgeWords {k s d : Nat} (base capacity : Nat) (fields : Fin k → Fin 4 → Nat)
    (X Y : ActualGame.Map k s d) (b : Fin k → F2) : List Nat :=
  [queryRank base fields X b, capacity + queryRank base fields Y b] ++
    permutationWords X Y b

def edgeBits {k s d : Nat} (base capacity : Nat) (fields : Fin k → Fin 4 → Nat)
    (X Y : ActualGame.Map k s d) (b : Fin k → F2) : List Bool :=
  encodeWords (edgeWords base capacity fields X Y b)

theorem queryWords_actual (S : Source) {k s d : Nat}
    (q : ActualGame.Query S k s d) :
    queryWords (CanonicalBodyTemplate.sourceFields q.1 (ActualGame.names S)) q.2
        (fun j => ActualGame.rhs S (q.1 j)) =
      CanonicalEncoding.bodyWords (ActualOrbit.body (ActualGame.canonical S k s d) q) :=
  CanonicalBodyTemplate.eval_actualQuery S q

theorem queryAddress_false (S : Source) {k s d : Nat}
    (q : ActualGame.Query S k s d) :
    (AddressGame.queryAddress S k s d false q).val =
      queryRank (CanonicalAddress.base S.«variables» S.occurrences s d)
        (CanonicalBodyTemplate.sourceFields q.1 (ActualGame.names S)) q.2
        (fun j => ActualGame.rhs S (q.1 j)) := by
  rw [queryRank, queryWords_actual]
  exact Encoding.sideEquiv_false_val _

theorem queryAddress_true (S : Source) {k s d : Nat}
    (q : ActualGame.Query S k s d) :
    (AddressGame.queryAddress S k s d true q).val =
      AddressGame.bodyCapacity S k s d +
      queryRank (CanonicalAddress.base S.«variables» S.occurrences s d)
        (CanonicalBodyTemplate.sourceFields q.1 (ActualGame.names S)) q.2
        (fun j => ActualGame.rhs S (q.1 j)) := by
  rw [queryRank, queryWords_actual]
  exact Encoding.sideEquiv_true_val _

theorem addressEdge_words (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (omega : ActualGame.Outcome S k g) :
    constraintWords (AddressGame.addressEdge S k g omega) =
      edgeWords (CanonicalAddress.base S.«variables» S.occurrences s d)
        (AddressGame.bodyCapacity S k s d)
        (CanonicalBodyTemplate.sourceFields omega.1.1 (ActualGame.names S))
        omega.1.2 (ActualGame.rightQuery S k g omega).2
        (fun j => ActualGame.rhs S (omega.1.1 j)) := by
  unfold constraintWords
  change [ (AddressGame.queryAddress S k s d false (ActualGame.leftQuery S k g omega)).val,
      (AddressGame.queryAddress S k s d true (ActualGame.rightQuery S k g omega)).val ] ++ _ = _
  rw [queryAddress_false, queryAddress_true]
  rfl

theorem addressEdge_bits (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (omega : ActualGame.Outcome S k g) :
    encodeWords (constraintWords (AddressGame.addressEdge S k g omega)) =
      edgeBits (CanonicalAddress.base S.«variables» S.occurrences s d)
        (AddressGame.bodyCapacity S k s d)
        (CanonicalBodyTemplate.sourceFields omega.1.1 (ActualGame.names S))
        omega.1.2 (ActualGame.rightQuery S k g omega).2
        (fun j => ActualGame.rhs S (omega.1.1 j)) := by
  rw [addressEdge_words]
  rfl

theorem edgeBits_split {k s d : Nat} (base capacity : Nat)
    (fields : Fin k → Fin 4 → Nat) (X Y : ActualGame.Map k s d) (b : Fin k → F2) :
    edgeBits base capacity fields X Y b =
      encodeWords [queryRank base fields X b, capacity + queryRank base fields Y b] ++
        encodeWords (permutationWords X Y b) := by
  exact encodeWords_append _ _

end DFVSGames.Reduction.AddressByteSemantics
end

section

namespace DFVSGames.Reduction.AddressOutcomeSpecs

open Integration.BinaryLinear Foundations.Complexity ActualSource
open Integration

theorem correct_rows {k s d : Nat} (T : NoiseTables.Table s d)
    (fields : Fin k → Fin 4 → Nat) (b : Fin k → Bool) :
    ∀ spec ∈ MachineOutcomeRows.selected (rows k T) b,
      MachineFieldTemplate.templateOutput spec.left (CanonicalBodyMachine.savedFields fields) =
        encodeWords (values fields spec).left ∧
      MachineFieldTemplate.templateOutput spec.right (CanonicalBodyMachine.savedFields fields) =
        encodeWords (values fields spec).right := by
  rw [selected_rows]
  intro spec hspec
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp hspec
  constructor
  · rw [values_row_left]
    exact row_left_output T p b fields
  · rw [values_row_right]
    exact row_right_output T p b fields

theorem payload_row {k s d : Nat} (T : NoiseTables.Table s d)
    (p : Parameter k T) (b : Fin k → Bool) (fields : Fin k → Fin 4 → Nat)
    (B C : Nat) :
    MachineOutcomeRows.payload B C (values fields) (row T p b) =
      AddressByteSemantics.edgeBits B C fields p.1 (rightMap T p) (bitVector b) := by
  unfold MachineOutcomeRows.payload MachineAddressEdge.edgeBits
  rw [values_row_left, values_row_right, AddressByteSemantics.edgeBits_split]
  rfl

theorem encodeWords_flatMap_inline_AddressOutcomeSpecs {α : Type*}
    (items : List α) (words : α → List Nat) :
    encodeWords (items.flatMap words) = items.flatMap (fun x => encodeWords (words x)) := by
  induction items with
  | nil => rfl
  | cons x items ih => simp only [List.flatMap_cons, encodeWords_append, ih]

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

namespace DFVSGames.Integration.AddressTupleBody

open Turing Reduction Foundations.Complexity
open AddressMachineSpace

variable {k s d noiseCount : Nat} {Λ : Type}

variable {rows : Rows k}

def rhs (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length) : Fin k → Bool :=
  fun j => F.equations[(tuple j).val].rhs

def loaded (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (base : Arena k s d noiseCount → List Bool) : Arena k s d noiseCount → List Bool :=
  MachineSourceTuple.stageTapes F tuple base k

def tupleBits (rows : Rows k) (B C : Nat)
    (values : MachineOutcomeRows.Spec (4*k) (1+9*k) → MachineOutcomeRows.Values (1+9*k))
    (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length) : List Bool :=
  (MachineOutcomeRows.selected rows (rhs F tuple)).flatMap (MachineOutcomeRows.payload B C values)

noncomputable def emitted (rows : Rows k) (B C : Nat)
    (values : MachineOutcomeRows.Spec (4*k) (1+9*k) → MachineOutcomeRows.Values (1+9*k))
    (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (base : Arena k s d noiseCount → List Bool) : Arena k s d noiseCount → List Bool :=
  MachineAddressEdge.appended (Slots k s d noiseCount) (loaded F tuple base)
    (tupleBits rows B C values F tuple)

noncomputable def finalTapes (rows : Rows k) (B C : Nat)
    (values : MachineOutcomeRows.Spec (4*k) (1+9*k) → MachineOutcomeRows.Values (1+9*k))
    (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (base : Arena k s d noiseCount → List Bool) : Arena k s d noiseCount → List Bool :=
  AddressTupleCleanup.cleared k s d noiseCount (emitted rows B C values F tuple base)

structure Ready (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (base : Arena k s d noiseCount → List Bool) : Prop where
  source : base .source = SourceEncoding.inputBits F
  saved : ∀j, base (.savedIndex j) = encodeWord (tuple j).val
  index : base .index = []
  work : base .work = []
  scratch : base .scratch = []
  copy : base .copyScratch = []
  fields : ∀j slot, base (.field j slot) = []

noncomputable def budget (rows : Rows k) (B C : Nat)
    (values : MachineOutcomeRows.Spec (4*k) (1+9*k) → MachineOutcomeRows.Values (1+9*k))
    (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (base : Arena k s d noiseCount → List Bool) : Nat :=
  (k * (10 * (SourceEncoding.inputBits F).length + 20) + 1) + 1 +
    ((MachineOutcomeRows.rowCosts (Slots k s d noiseCount) B C values
      (MachineOutcomeRows.selected rows (rhs F tuple)) (loaded F tuple base)).sum + 1) +
    AddressTupleCleanup.budget k s d noiseCount (emitted rows B C values F tuple base) + 1

theorem rhs_eq_actual (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length) :
    rhs F tuple = AddressOutcomeSpecs.rhsBits (source F) tuple := rfl

theorem canonicalValues_eq_actual (F : SourceEncoding.Input)
    (tuple : Fin k → Fin F.equations.length) :
    AddressTupleLoaded.canonicalValues F tuple =
      CanonicalBodyTemplate.sourceFields tuple (ActualGame.names (source F)) := by
  funext j
  apply congrArg (fun names => CanonicalBodyTemplate.recordFields names (tuple j).val)
  funext slot
  fin_cases slot <;> rfl

theorem actualInvariant (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (T : NoiseTables.Table s d) (base : Arena k s d noiseCount → List Bool)
    (ready : Ready F tuple base)
    (clean : MachineAddressEdge.Clean (Slots k s d noiseCount) base) (B C : Nat)
    (hB : base (headerTape k s d noiseCount .baseValue) = encodeWord B)
    (hC : base (headerTape k s d noiseCount .capacity) = encodeWord C) :
    MachineOutcomeRows.Invariant (Slots k s d noiseCount) B C
      (AddressOutcomeSpecs.values (AddressTupleLoaded.canonicalValues F tuple))
      (MachineOutcomeRows.selected (AddressOutcomeSpecs.rows k T) (rhs F tuple))
      (loaded F tuple base) := by
  constructor
  · exact AddressTupleLoaded.loaded_clean F tuple base clean
  · exact AddressTupleLoaded.loaded_radix F tuple base B hB
  · exact AddressTupleLoaded.loaded_capacity F tuple base C hC
  · intro spec member
    have fields := AddressTupleLoaded.loaded_savedFields F tuple base ready.saved ready.fields
    change (fun i => loaded F tuple base (MachineAddressEdge.addressSlots
      (Slots k s d noiseCount) (.field i))) = _ at fields
    rw [fields]
    exact AddressOutcomeSpecs.correct_rows T (AddressTupleLoaded.canonicalValues F tuple)
      (rhs F tuple) spec member

theorem finalTapes_eq (rows : Rows k) (B C : Nat)
    (values : MachineOutcomeRows.Spec (4*k) (1+9*k) → MachineOutcomeRows.Values (1+9*k))
    (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (base : Arena k s d noiseCount → List Bool) (ready : Ready F tuple base) :
    finalTapes rows B C values F tuple base = MachineAddressEdge.appended
      (Slots k s d noiseCount) base (tupleBits rows B C values F tuple) :=
  AddressTupleFrame.cleared_appended_loaded F tuple base ready.index ready.work ready.fields _

end DFVSGames.Integration.AddressTupleBody
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
attribute [-instance] _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Explicit.MachineSingleOrbitBridge

open Turing DFVSGames.Reduction DFVSGames.Foundations.Complexity
open ActualSource MachineSingleOrbitCodec

namespace SingleAddress

abbrev addressEdge := Decoder.TableKeysAddressGame.addressEdge
abbrev outputInstance := Decoder.TableKeysAddressGame.outputInstance

end SingleAddress

theorem old_addressEdge_eq_double (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (ω : ActualGame.Outcome S k g) :
    AddressGame.addressEdge S k g ω = doubleConstraint (SingleAddress.addressEdge S k g ω) := by
  unfold AddressGame.addressEdge doubleConstraint SingleAddress.addressEdge
    Decoder.TableKeysAddressGame.addressEdge
  congr 1
  apply Fin.ext
  exact Encoding.sideEquiv_true_val _

theorem old_outputInstance_eq_double (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (en : NoiseEnumeration g) :
    AddressGame.outputInstance S k g en = doubleInstance (SingleAddress.outputInstance S k g en) := by
  unfold AddressGame.outputInstance doubleInstance SingleAddress.outputInstance
    Decoder.TableKeysAddressGame.outputInstance
  congr 1
  simp only [List.map_map, Function.comp_def, ← old_addressEdge_eq_double]
  rfl

end DFVSGames.Explicit.MachineSingleOrbitBridge

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_PositiveMultiplier
attribute [-instance] _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DFVSGames.Quadratic.blockOrientationFintype _root_.OAI.DFVSGames.Quadratic.fieldLineFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Decoder.SurrogateFibers

open DFVSGames.Integration.BinaryLinear
open DFVSGames.Fourier
open PositiveMultiplier
open scoped BigOperators

noncomputable section

variable {E K W C : Type*}
variable [AddCommGroup E] [Module F2 E]
variable [AddCommGroup K] [Module F2 K] [Fintype K]
variable [AddCommGroup W] [Module F2 W] [Fintype W]
variable [Fintype (E →ₗ[F2] F2)]
variable [Fintype (E →ₗ[F2] K)] [Fintype (E →ₗ[F2] W)]
variable [Fintype (E →ₗ[F2] K × W)]

def shortcodeAcceptance (f : (E →ₗ[F2] K) → C) : ℝ := by
  classical
  exact 𝔼 M, 𝔼 a : K, 𝔼 l : E →ₗ[F2] F2,
    if f M = f (M + l.smulRight a) then (1 : ℝ) else 0

end
end DFVSGames.Decoder.SurrogateFibers

noncomputable section
open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear
open DFVSGames.Reduction DFVSGames.Reduction.ActualSource
open DFVSGames.Fourier.MatrixNoise

namespace DFVSGames.Decoder.ActualSpectral

open TableKeysGame PositiveMultiplier NoiseSampler SurrogateFibers

local instance homFintype {D F : Type*}
    [AddCommGroup D] [Module F2 D] [AddCommGroup F] [Module F2 F]
    [Fintype D] [Fintype F] : Fintype (D →ₗ[F2] F) :=
  Fintype.ofInjective (fun M : D →ₗ[F2] F => (M : D → F)) DFunLike.coe_injective

end DFVSGames.Decoder.ActualSpectral
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_AffineWitnessNormalization
attribute [-instance] _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DFVSGames.Quadratic.blockOrientationFintype _root_.OAI.DFVSGames.Quadratic.fieldLineFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain
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

local instance homFintype {D F : Type*}
    [AddCommGroup D] [Module F2 D] [AddCommGroup F] [Module F2 F]
    [Fintype D] [Fintype F] : Fintype (D →ₗ[F2] F) :=
  Fintype.ofInjective (fun M : D →ₗ[F2] F => (M : D → F)) DFunLike.coe_injective

end
end DFVSGames.Decoder.MatrixCoordinates

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_ActualGoodRows
attribute [-instance] _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DFVSGames.Quadratic.blockOrientationFintype _root_.OAI.DFVSGames.Quadratic.fieldLineFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain
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

local instance homFintype {D F : Type*}
    [AddCommGroup D] [Module F2 D] [AddCommGroup F] [Module F2 F]
    [Fintype D] [Fintype F] : Fintype (D →ₗ[F2] F) :=
  Fintype.ofInjective (fun M : D →ₗ[F2] F => (M : D → F)) DFunLike.coe_injective

end
end DFVSGames.Decoder.ActualGoodRows

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_RowErasureSliceUniform
attribute [-instance] _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DFVSGames.Quadratic.blockOrientationFintype _root_.OAI.DFVSGames.Quadratic.fieldLineFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Decoder.ActualEvents

open Integration.BinaryLinear Reduction ActualSource Foundations.Games
open Inverse Inverse.RowErasure
open Inverse.Shortcode (Mat)
open scoped BigOperators Classical

noncomputable section

local instance homFintype {D F : Type*}
    [AddCommGroup D] [Module F2 D] [AddCommGroup F] [Module F2 F]
    [Fintype D] [Fintype F] : Fintype (D →ₗ[F2] F) :=
  Fintype.ofInjective (fun M : D →ₗ[F2] F => (M : D → F)) DFunLike.coe_injective

end
end DFVSGames.Decoder.ActualEvents

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_SelectedPolicies
attribute [-instance] _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DFVSGames.Quadratic.blockOrientationFintype _root_.OAI.DFVSGames.Quadratic.fieldLineFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Decoder.ActualSeedVariation

open Integration.BinaryLinear Reduction ActualSource Foundations.Games
open scoped BigOperators Classical

noncomputable section
attribute [local instance] Fintype.ofFinite

local instance homFintype {D F : Type*}
    [AddCommGroup D] [Module F2 D] [AddCommGroup F] [Module F2 F]
    [Fintype D] [Fintype F] : Fintype (D →ₗ[F2] F) :=
  Fintype.ofInjective (fun M : D →ₗ[F2] F => (M : D → F)) DFunLike.coe_injective

end
end DFVSGames.Decoder.ActualSeedVariation

noncomputable section

namespace DFVSGames.Decoder.SelectedDecoding

open DFVSGames.Integration.BinaryLinear DFVSGames.Reduction DFVSGames.Soundness
open DFVSGames.Inverse
open ActualSource VisiblePolicies MatrixCoordinates
open scoped BigOperators Classical

attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

local instance homFintype {D F : Type*}
    [AddCommGroup D] [Module F2 D] [AddCommGroup F] [Module F2 F]
    [Fintype D] [Fintype F] : Fintype (D →ₗ[F2] F) :=
  Fintype.ofInjective (fun M : D →ₗ[F2] F => (M : D → F)) DFunLike.coe_injective

instance affineSliceFintype {E K L : Type*}
    [AddCommGroup E] [Module F2 E] [AddCommGroup K] [Module F2 K]
    [AddCommGroup L] [Module F2 L] [Fintype (E →ₗ[F2] K)]
    (A : K →ₗ[F2] L) (Q : Submodule F2 E) (Mstar : E →ₗ[F2] K) :
    Fintype (RowErasureSliceQuotient.AffineSlice A Q Mstar) := by
  unfold RowErasureSliceQuotient.AffineSlice
  infer_instance

variable {k s d r : ℕ}

def transferredAgreement (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (draw : AdviceExperiment.Draw k (Fin S.occurrences) (Alphabet s) (Vector d) (Vector r))
    (w : ResponseWitness k) (u : Alphabet s)
    (Mstar : RawPartnerTarget.RawPoint draw.singletons →ₗ[F2] Alphabet s) : ℝ :=
  𝔼 M : RowErasureSliceQuotient.AffineSlice draw.rowMap
      (w.columns.map (AdviceExperiment.projection (ActualGame.rhs S) draw)) Mstar,
    if TableKeysRestoration.projectedAnswer S k s d labeling draw.singletons
        (RawPrivateTable.supported draw.singletons (ActualGame.names S)
          draw.occurrences draw.positions) (M.val.prod draw.complement) =
      M.val (AdviceExperiment.projection (ActualGame.rhs S) draw w.coefficient) + u
    then (1 : ℝ) else 0

end DFVSGames.Decoder.SelectedDecoding
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_VisibleTransfer
attribute [-instance] _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DFVSGames.Quadratic.blockOrientationFintype _root_.OAI.DFVSGames.Quadratic.fieldLineFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain
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

variable {k s d r : ℕ}

local instance homFintype_rdc5143_1 {D F : Type*}
    [AddCommGroup D] [Module F2 D] [AddCommGroup F] [Module F2 F]
    [Fintype D] [Fintype F] : Fintype (D →ₗ[F2] F) :=
  Fintype.ofInjective (fun M : D →ₗ[F2] F => (M : D → F)) DFunLike.coe_injective
def datumAgreement (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : VisiblePolicies.LeftInput S k s d (Vector r) → VisiblePolicies.ResponseWitness k → Prop)
    (data : AdviceLaw.CompleteData k (Fin S.occurrences) (Alphabet s) (Vector d) (Vector r)) : ℝ :=
  VisiblePolicies.observedAgreement S labeling good (AdviceLaw.completeDraw data 0)

end
end DFVSGames.Decoder.ActualConditionalLaw

noncomputable section

namespace DFVSGames.Decoder.SelectedFiberLaw

open DFVSGames.Integration.BinaryLinear DFVSGames.Reduction DFVSGames.Soundness
open DFVSGames.Inverse DFVSGames.Foundations.Games
open ActualSource VisiblePolicies MatrixCoordinates ActualSeedEvents
open scoped BigOperators Classical

attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

local instance homFintype {D F : Type*}
    [AddCommGroup D] [Module F2 D] [AddCommGroup F] [Module F2 F]
    [Fintype D] [Fintype F] : Fintype (D →ₗ[F2] F) :=
  Fintype.ofInjective (fun M : D →ₗ[F2] F => (M : D → F)) DFunLike.coe_injective

end DFVSGames.Decoder.SelectedFiberLaw
end

end OAI
end


