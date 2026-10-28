-- Prove2me | Definitions.Def_OAIQ086U010
-- name    : OAIQ086U010
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T16:44:56.334382+00:00
-- url     : https://prove2.me/theorems/20ef4ce1-faa8-4be5-890e-f368e480bf31
-- title:
--   Definitions bundle OAIQ086U010 of the split of OpenAI, The Unique Games Theorem
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.UniqueGamesTheorem.theorem11`, carved from OpenAI's openai/math development (OpenAI, *The Unique Games Theorem*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 782 declarations of OpenAI's Lean: 314 definitions, 7 inductive types or structures, 10 instances and 451 theorems. The definitions and types are `OAI.UniqueGamesTheorem.Explicit.ProductPaddedOutput.simpleBipartite`, `OAI.UniqueGamesTheorem.Explicit.SubdivisionTarget.simpleBipartite`, `OAI.UniqueGamesTheorem.FinishReduction.of_matrix_reduction`, `OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.computableInPolyTime`, `OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.formulaHeader`, `OAI.UniqueGamesTheorem.Foundations.Complexity.GraphIterationBounds.count`, `OAI.UniqueGamesTheorem.Foundations.Complexity.GraphIterationBounds.countedBits`, `OAI.UniqueGamesTheorem.Foundations.Complexity.GraphIterationBounds.inputBits`, `OAI.UniqueGamesTheorem.Foundations.Complexity.GraphIterationBounds.words`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedOverlay.execution`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedOverlay.machine`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedOverlay.paddingInTime`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedOverlayRuntime.cleanupTapes`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedOverlayRuntime.computableInPolyTime`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedOverlayRuntime.rawProgram`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedOverlayRuntime.terminalRun`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddingTable.execution`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularExecutionBounds.familyPolynomial`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularFamily.Alphabet`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularFamily.FamilyState`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularFamily.Label`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularFamily.SmallTable`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularFamily.State`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularFamily.cleanupInTime`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularFamily.familyCleanInTime`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularFamily.familyInTime`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularFamily.familyTape`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularFamily.familyView`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularFamily.frame`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularFamily.inputNative`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularFamily.levelNative`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularFamily.levelTape`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularFamily.outputNative`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularFamily.powerNative`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularFamily.powerTape`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularFamily.program`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularFamily.readyState`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularFamily.resultCore`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularFamily.rotor`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularFamily.seedState` and 281 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `UniqueGames_Games_ProductLemmas`, `UniqueGames_Games_ProductSoundness`, `UniqueGames_Games_SubdivisionTarget`, `UniqueGames_Games_UniformTarget`, `UniqueGames_Machines_FinalCNFOutputLemmas`, `UniqueGames_Machines_GraphIterationBoundsLemmas`, `UniqueGames_Machines_MachinePaddedOverlay`, `UniqueGames_Machines_MachinePaddedOverlayRuntimeLemmas`, `UniqueGames_Machines_MachinePaddingRowsLemmas`, `UniqueGames_Machines_MachinePaddingTable`, `UniqueGames_Machines_MachineRegularDummyRow`, `UniqueGames_Machines_MachineRegularFamily`, `UniqueGames_Machines_MachineRegularInternalRow`, `UniqueGames_Machines_MachineRegularMetadata`, `UniqueGames_Machines_MachineRegularOriginalBody`, `UniqueGames_Machines_MachineRegularOriginalBodyBounds`, `UniqueGames_Machines_MachineRegularOriginalClean`, `UniqueGames_Machines_MachineRegularOriginalRow`, `UniqueGames_Machines_MachineRegularOwnerBody`, `UniqueGames_Machines_MachineRegularOwnerBodyBounds`, `UniqueGames_Machines_MachineRegularOwnerCleanup`, `UniqueGames_Machines_MachineRegularOwnerProgram`, `UniqueGames_Machines_MachineRegularTable`, `UniqueGames_Machines_MachineRegularTableBoundsLemmas`, `UniqueGames_Machines_MachineRegularTableTrace`, `UniqueGames_Machines_MachineRegularVertexBlock`, `UniqueGames_Machines_MachineVertexPadding`, `UniqueGames_Machines_PoweringGlobalEnumerationLemmas`, `UniqueGames_Machines_PoweringMachineEqualityField`, `UniqueGames_Machines_PoweringMachineFinish`, `UniqueGames_Machines_PoweringMachineOuterLoopLemmas`, `UniqueGames_Machines_PoweringMachineRelationLemmas`, `UniqueGames_Machines_PoweringMachineRowBody`, `UniqueGames_Machines_PoweringMachineVertex`, `UniqueGames_Machines_PoweringPlanBudget`, `UniqueGames_Machines_PoweringPolynomialBudgetLemmas`, `UniqueGames_PCP_FinalTableFormula`, `UniqueGames_PCP_MachineRawInitialTable`, `UniqueGames_PCP_PreprocessingPaddingWords`, `UniqueGames_PCP_PreprocessingRegularLoopWordsLemmas`, `UniqueGames_PCP_PreprocessingRegularWords`, `UniqueGames_PCP_RawInitialMachineBody`, `UniqueGames_PCP_RawInitialMachineCleanup`, `UniqueGames_PCP_RawInitialMachineFinish`, `UniqueGames_PCP_RawInitialMachineLoop`, `UniqueGames_PCP_RawInitialMachineLoopData`, `UniqueGames_PCP_RawInitialMachinePhases`, `UniqueGames_PCP_RawInitialMachineReadClause`, `UniqueGames_PCP_RawInitialMachineRows`, `UniqueGames_PCP_RawInitialMachineStart`, `UniqueGames_PCP_RawInitialTablesLemmas`, `UniqueGames_PCP_SourceContextClear`, `UniqueGames_PCP_SourceDescriptorEmissionLemmas`, `UniqueGames_PCP_SourceFieldArrayLemmas`, `UniqueGames_PCP_SourceGapLemmas`, `UniqueGames_PCP_SourceHonestLemmas`, `UniqueGames_PCP_SourceQueryLoopLemmas`, `UniqueGames_PCP_SourceQueryOrderLemmas`, `UniqueGames_PCP_SourceSignaturePrepareLemmas`, `UniqueGames_PCP_SourceTupleBody`, `UniqueGames_PCP_TableIteration`, `UniqueGames_Reduction_FinishReduction`, `UniqueGames_Repetition_TensorAlgebraLemmas`.
--
--   **Imports.** It imports the published bundle `Def_UniqueGamesTheorem`; the bundles `OAIQ086U006`, `OAIQ086U007` and `OAIQ086U008` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ086U012`; the statement `OAI_UniqueGamesTheorem_Inverse_KMSMomentTheorem_lifted_fourth_moment_bound`; the proofs of `OAI_UniqueGamesTheorem_Decoder_MatrixGap_parameters_of_inverse` and `OAI_UniqueGamesTheorem_Inverse_KMSMomentTheorem_lifted_fourth_moment_bound`.
-- source:
--   OpenAI, The Unique Games Theorem, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Unique-Games-Theorem-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Std
import Definitions.Def_UniqueGamesTheorem
import Definitions.Def_OAIQ086U006
import Definitions.Def_OAIQ086U007
import Definitions.Def_OAIQ086U008

section
-- module Solutions.OAIQ086_UG.UniqueGames_Games_ProductLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
The independent graph product in the last step of the reduction.

Edges are tuples of actual base edges.  The endpoint maps remain injective,
the edge law is exactly uniform, and the associated game agrees with ordinary
parallel repetition for every pair of local strategies, including strategies
depending on their whole question tuples.  Only the completeness lower bound
uses coordinatewise strategies; no repetition soundness bound is assumed here.
-/

/-!
The actual ordered full-table instance of the final independent product.
Caller-supplied coordinate numberings are used explicitly. Edges are emitted in
increasing mixed-radix address, with division/remainder decoding; the two vertex
blocks and the entire permutation table use the same coordinate convention.
-/

/-!
Machine-friendly product numbering on the common global vertex base.
Both endpoints use the same radix, so the machine needs neither a right-side
subtraction nor a final offset. Mixed-side tuples are isolated vertices. For a
positive repetition count the first coordinate supplies a total bipartition.
-/

namespace UniqueGamesTheorem.Explicit.ProductPaddedOutput

open UniqueGamesTheorem.Foundations
open Target
open MachineOutputContract
open ProductTarget
open scoped BigOperators

variable {q : ℕ} (H : Instance q) (presentation : SimpleBipartite H)

attribute [local instance] OAI.UniqueGamesTheorem.Explicit.ProductPaddedOutput.instNonemptyFinLengthConstraintVerticesConstraints
theorem side_left (t : ℕ) (ht : 0 < t) (x : Fin t → Left H presentation) :
    side H presentation t ht (vertices H presentation t ht (Sum.inl x)) = false := by
  simp only [side, vertices]
  change presentation.side (finFunctionFinEquiv.symm
    (finFunctionFinEquiv (fun i => (x i).val)) ⟨0, ht⟩) = false
  rw [Equiv.symm_apply_apply]
  exact (x ⟨0, ht⟩).property

theorem side_right (t : ℕ) (ht : 0 < t) (y : Fin t → Right H presentation) :
    side H presentation t ht (vertices H presentation t ht (Sum.inr y)) = true := by
  simp only [side, vertices]
  change presentation.side (finFunctionFinEquiv.symm
    (finFunctionFinEquiv (fun i => (y i).val)) ⟨0, ht⟩) = true
  rw [Equiv.symm_apply_apply]
  exact (y ⟨0, ht⟩).property

def simpleBipartite (t : ℕ) (ht : 0 < t) : SimpleBipartite (output H presentation t ht) :=
  Embedded.simpleBipartite _ _ _ _ (side H presentation t ht)
    (side_left H presentation t ht) (side_right H presentation t ht)

theorem output_translations {ell : ℕ}
    (coordinates : Fin q ≃ (Fin ell → ZMod 2))
    (hH : Integration.TranslationTarget.IsTranslationInstance coordinates H)
    (t : ℕ) (ht : 0 < t) :
    Integration.TranslationTarget.IsTranslationInstance (finalCoordinates coordinates t)
      (output H presentation t ht) := by
  classical
  choose offset hoffset using fun e : Fin H.constraints.length =>
    hH H.constraints[e] (List.getElem_mem e.isLt)
  intro constraint hconstraint
  rw [output_constraints] at hconstraint
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hconstraint
  refine ⟨BipartiteGame.binaryProductEquiv ell t
    (fun j => offset (finFunctionFinEquiv.symm i j)), ?_⟩
  intro a
  rw [outputRow_images]
  simp only [finalCoordinates_apply, Equiv.symm_apply_apply]
  rw [← map_add]
  congr 1
  funext j
  exact hoffset _ _

end UniqueGamesTheorem.Explicit.ProductPaddedOutput

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Repetition_TensorAlgebraLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Alphabet-independent repetition of ordinary finite projection games.

The game is the actual finite question distribution and its local acceptance
predicate. The proof bounds nonnegative vector assignments by finite
thresholding and correlated sampling, factors each unrestricted product
strategy through that bound, and iterates the resulting collision contraction.
No repetition bound, decoder certificate, or alphabet-size budget is a premise.

The deterministic-predicate game interface permits arbitrary real question
weights. Distinct hidden constraints on the same question pair are not encoded
by this interface. Both v2 uses have a unique predicate for each question pair:
the distinct-position equation--variable game and the final simple graph.
-/

namespace UniqueGamesTheorem.Repetition
open UniqueGamesTheorem.Foundations.Games
noncomputable section

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [Nonempty A₁] [Nonempty A₂]

/-- The v2 projection-repetition estimate, including the empty product.
The repetition exponent is independent of all question and answer cardinalities. -/
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
end UniqueGamesTheorem.Repetition

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Games_ProductSoundness
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
The final graph product inherits the alphabet-independent repetition estimate
through its proved uniform occurrence law and arbitrary-local-strategy bridge.
The only input soundness premise is the base graph's actual finite maximum.
-/

namespace UniqueGamesTheorem.Explicit.ProductPaddedOutput

open UniqueGamesTheorem.Foundations
open Target
open MachineOutputContract

noncomputable section

variable {q : ℕ} [Nonempty (Fin q)]

/-- Soundness for the actual globally numbered, fully tabulated output. -/
theorem output_soundness_rate (H : Instance q) (presentation : SimpleBipartite H)
    (t : ℕ) (ht : 0 < t)
    (hvalue : Integration.InstanceValue.value H ≤ 1 - (1 : ℝ) / 800) :
    Integration.InstanceValue.value (output H presentation t ht) ≤
      (1 - (1 : ℝ) / 10240000) ^ t := by
  let : Nonempty (Fin H.constraints.length) := ⟨⟨0, H.constraintCount_positive⟩⟩
  rw [output_value_eq_repetition]
  apply UniqueGamesTheorem.Repetition.final_repetition_value
    presentation.toBipartiteGame.toGame presentation.toBipartiteGame.toGame_isProjection
  simpa only [BipartiteGame.toGame_value, presentation.toBipartiteGame_value] using hvalue

theorem output_soundness (H : Instance q) (presentation : SimpleBipartite H)
    (t : ℕ) (ht : 0 < t) {δ : ℝ}
    (hcount : (1 - (1 : ℝ) / 10240000) ^ t ≤ δ)
    (hvalue : Integration.InstanceValue.value H ≤ 1 - (1 : ℝ) / 800) :
    Integration.InstanceValue.value (output H presentation t ht) ≤ δ :=
  (output_soundness_rate H presentation t ht hvalue).trans hcount

end
end UniqueGamesTheorem.Explicit.ProductPaddedOutput

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Games_SubdivisionTarget
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Concrete numbered, full-table output for the four-edge subdivision.
Original vertices keep their names. The new names are `n+e`, `n+Q+2e`,
and `n+Q+2e+1`, and each input occurrence emits four consecutive rows.
-/

namespace UniqueGamesTheorem.Explicit.SubdivisionTarget

open UniqueGamesTheorem.Foundations Target
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

theorem tables_correspond {q : Nat} (H : Instance q)
    (ei : Fin H.constraints.length × Fin 4) :
    permutationEquiv (tables H ei) = (Subdivision.game (ofInstance H)).permutation ei := by
  ext a
  by_cases hi : ei.2 = 3 <;>
    simp [tables, permutationEquiv, Subdivision.game, Subdivision.permutation, ofInstance,
      MachineSubdivisionRows.inverseTable, MachineSubdivisionRows.identityTable, hi]

theorem tables_translation {q s : Nat}
    (coordinates : Fin q ≃ Integration.BinaryLinear.Vector s) (H : Instance q)
    (hH : Integration.TranslationTarget.IsTranslationInstance coordinates H)
    (ei : Fin H.constraints.length × Fin 4) :
    ∃ shift : Integration.BinaryLinear.Vector s, ∀ a : Fin q,
      coordinates ((tables H ei).images[a]) = coordinates a + shift := by
  by_cases hi : ei.2 = 3
  · obtain ⟨shift, hs⟩ := hH H.constraints[ei.1] (List.getElem_mem ei.1.isLt)
    refine ⟨shift, ?_⟩
    intro a
    simp only [tables, hi, ite_eq_left, MachineSubdivisionRows.inverseTable]
    have h := hs (H.constraints[ei.1].permutation.inverseImages[a])
    rw [H.constraints[ei.1].permutation.rightInverse] at h
    have hc := congrArg (fun x => x + shift) h
    simpa only [add_assoc, ZModModule.add_self, add_zero] using hc.symm
  · refine ⟨0, ?_⟩
    intro a
    simp [tables, hi, MachineSubdivisionRows.identityTable]

theorem subdivide_translation {q s : Nat}
    (coordinates : Fin q ≃ Integration.BinaryLinear.Vector s) (H : Instance q)
    (hH : Integration.TranslationTarget.IsTranslationInstance coordinates H) :
    Integration.TranslationTarget.IsTranslationInstance coordinates (subdivide H) := by
  intro c hc
  change c ∈ List.ofFn _ at hc
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
  exact tables_translation coordinates H hH (numericEdgeEquiv H.constraints.length i)

def simpleBipartite {q : Nat} (H : Instance q) : SimpleBipartite (subdivide H) :=
  ProductTarget.render_simpleBipartite _ _ _ _ _

/-- The serialized output has exactly the abstract subdivision value. -/
theorem subdivide_value {q : Nat} (H : Instance q) :
    Integration.InstanceValue.value (subdivide H) =
      (Subdivision.game (ofInstance H)).value :=
  ProductTarget.render_value _ _ _ _ _ (tables_correspond H)

/-- Exact equation (bipartization-value) for the concrete list/table format. -/
theorem value_eq {q : Nat} (H : Instance q) (hq : 0 < q) :
    Integration.InstanceValue.value (subdivide H) =
      1 - (1 - Integration.InstanceValue.value H) / 4 := by
  let : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  let : Nonempty (Fin H.constraints.length) := ⟨⟨0, H.constraintCount_positive⟩⟩
  rw [subdivide_value, Subdivision.value_eq, ofInstance_value]

end UniqueGamesTheorem.Explicit.SubdivisionTarget

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Games_UniformTarget
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Explicit.UniformTarget

open UniqueGamesTheorem.Foundations Target Complexity
open UniqueGamesTheorem.Integration
open MachineUniformCopyOrder

theorem count_append {n q : Nat} (a : Fin n → Fin q)
    (xs ys : List (Constraint n q)) :
    countSatisfied a (xs ++ ys) = countSatisfied a xs + countSatisfied a ys := by
  simp [GapSemantics.countSatisfied_eq_sum]

theorem count_copies {n q : Nat} (C : Nat) (es : List (Constraint n q))
    (a : Fin n → Fin q) :
    countSatisfied a (copyMajor C es) = C * countSatisfied a es := by
  induction C with
  | zero => simp [copyMajor, countSatisfied]
  | succ C ih =>
    change countSatisfied a (es ++ copyMajor C es) = _
    rw [count_append, ih, Nat.add_mul, Nat.one_mul]
    omega

theorem count {q : Nat} (C : Nat) (hC : 0 < C) (g : Instance q)
    (a : Fin g.vertices → Fin q) :
    countSatisfied a (construct C hC g).constraints = C * countSatisfied a g.constraints :=
  count_copies C g.constraints a

theorem maxSatisfied {q : Nat} (C : Nat) (hC : 0 < C) (g : Instance q) (hq : 0 < q) :
    InstanceValue.maxSatisfied (construct C hC g) = C * InstanceValue.maxSatisfied g := by
  classical
  apply Nat.le_antisymm
  · unfold InstanceValue.maxSatisfied
    apply Finset.sup_le
    intro a _
    change countSatisfied a (copyMajor C g.constraints) ≤ C * InstanceValue.maxSatisfied g
    erw [count_copies]
    exact Nat.mul_le_mul_left C (InstanceValue.countSatisfied_le_maxSatisfied g a)
  · obtain ⟨a, ha⟩ := InstanceValue.maxSatisfied_attained g hq
    rw [← ha, ← count C hC g a]
    exact InstanceValue.countSatisfied_le_maxSatisfied (construct C hC g) a

theorem value {q : Nat} (C : Nat) (hC : 0 < C) (g : Instance q) (hq : 0 < q) :
    InstanceValue.value (construct C hC g) = InstanceValue.value g := by
  have hc : (C : ℝ) ≠ 0 := by exact_mod_cast hC.ne'
  have hm : (g.constraints.length : ℝ) ≠ 0 := by
    exact_mod_cast g.constraintCount_positive.ne'
  unfold InstanceValue.value
  rw [maxSatisfied C hC g hq, edge_count]
  push_cast
  field_simp

theorem mem_original {q : Nat} (C : Nat) (hC : 0 < C) (g : Instance q)
    (c : Constraint g.vertices q) (hc : c ∈ (construct C hC g).constraints) :
    c ∈ g.constraints := by
  obtain ⟨es, hes, hc⟩ := List.mem_flatten.mp hc
  have he : es = g.constraints := List.eq_of_mem_replicate hes
  simpa [he] using hc

theorem translations {q s : Nat} (C : Nat) (hC : 0 < C) (g : Instance q)
    (coordinates : Fin q ≃ BinaryLinear.Vector s)
    (hg : TranslationTarget.IsTranslationInstance coordinates g) :
    TranslationTarget.IsTranslationInstance coordinates (construct C hC g) := by
  intro c hc
  exact hg c (mem_original C hC g c hc)

end UniqueGamesTheorem.Explicit.UniformTarget

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceHonestLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Hastad.SourceLocalEquation

open Target SourceContexts SourceOccurrences SourceLocalSignature
open UniqueGamesTheorem.Reduction.CloneGap
open UniqueGamesTheorem.Reduction.FiniteNoise

theorem addressMap_emptyLocalAddress (F : Formula) (u : ℕ)
    (c : ClauseContext F u) (v : VariableContext F u) :
    addressMap F u c v ∘ emptyLocalAddress u = emptyAddress F u v := by
  funext a
  cases a <;> rfl

theorem addressMap_foldedLocalAddress (F : Formula) (u : ℕ)
    (c : ClauseContext F u) (v : VariableContext F u) (valid : J u → Bool)
    (j₀ : {j : J u // valid j = true}) :
    addressMap F u c v ∘ foldedLocalAddress u valid j₀ =
      localAddress (variableEncoding F u) (clauseEncoding F u) (iEncoding u) (jEncoding u)
        v c valid (leftAnchor u) j₀ := by
  funext a
  cases a <;> rfl

/-- A generic factorization first aligns the validity function itself, so no
unproved transport of dependent anchor subtypes is needed. -/
theorem contextEquation_eq_map_equationFor (F : Formula) (u D : ℕ)
    (c : ClauseContext F u) (v : VariableContext F u)
    (t : SourceTape.TestTape (I u) (J u) D) :
    contextEquation F u D c v t =
      mapEquation (addressMap F u c v) (equationFor u D (validJ F c) (pi F c v) t) := by
  unfold contextEquation equationFor rightAnchor
  cases h : firstValid (jEncoding u) (validJ F c) with
  | none =>
    rw [mapEquation_comp, addressMap_emptyLocalAddress]
  | some j₀ =>
    rw [mapEquation_comp, addressMap_foldedLocalAddress]
    rfl

theorem contextEquation_eq_map (F : Formula) (u D : ℕ)
    (c : ClauseContext F u) (s : SlotContext u)
    (t : SourceTape.TestTape (I u) (J u) D) :
    contextEquation F u D c (sampledVariables F c s) t =
      mapEquation (addressMap F u c (sampledVariables F c s))
        (equation u D (ofContext F c s) t) := by
  have hv : signatureValid (ofContext F c s) = validJ F c :=
    funext (signature_validJ F c s)
  have hp : signatureProjection (ofContext F c s) = pi F c (sampledVariables F c s) :=
    funext (signature_pi F c s)
  rw [equation, hv, hp]
  exact contextEquation_eq_map_equationFor F u D c (sampledVariables F c s) t

theorem sourceEquation_eq_map_emit (F : Formula) (u D : ℕ)
    (p : SourceIndex F u D) :
    sourceEquation F u D p =
      mapEquation (addressMap F u p.1.1 (sampledVariables F p.1.1 p.1.2))
        (emit u D (ofContext F p.1.1 p.1.2, p.2)) :=
  contextEquation_eq_map F u D p.1.1 p.1.2 p.2

end UniqueGamesTheorem.Foundations.Hastad.SourceLocalEquation

/-! The actual global addresses use three input-dependent base registers.
Every local query contributes only a fixed finite selector and fixed offset,
so a finite control table can select a base and emit its unary offset. -/

namespace UniqueGamesTheorem.Foundations.Hastad.SourceAddressDescriptors

open Target SourceContexts SourceOccurrences SourceLocalEquation SourceLocalSignature
open SourceAddressArithmetic
open UniqueGamesTheorem.Reduction.CloneGap

/-- Registers zero and one start the selected left and right query blocks;
register two is the single dummy address. -/
def baseValue (F : Formula) (u : ℕ) (c : ClauseContext F u)
    (v : VariableContext F u) (side : Fin 3) : ℕ :=
  if side = 0 then 2 ^ (2 ^ u) * ((variableEncoding F u).code v).val
  else if side = 1 then F.variables ^ u * 2 ^ (2 ^ u) +
    2 ^ (8 ^ u) * ((clauseEncoding F u).code c).val
  else F.variables ^ u * 2 ^ (2 ^ u) + F.clauses.length ^ u * 2 ^ (8 ^ u)

theorem realize_descriptor (F : Formula) (u : ℕ) (c : ClauseContext F u)
    (v : VariableContext F u) (key : LocalKey u) :
    realize (baseValue F u c v) (descriptor u key) = (addressMap F u c v key).val := by
  cases key with
  | inl f =>
      simpa [realize, descriptor, baseValue, addressMap] using
        (left_address F u v f).symm
  | inr key =>
      cases key with
      | inl g =>
          simp [realize, descriptor, baseValue, addressMap, right_address]
          omega
      | inr _dummy =>
          simp only [realize, descriptor, baseValue, show (2 : Fin 3) ≠ 0 by decide,
            show (2 : Fin 3) ≠ 1 by decide, ite_false, Nat.zero_add, addressMap,
            dummy_address]

theorem sourceEquation_words (F : Formula) (u D : ℕ) (p : SourceIndex F u D) :
    UniqueGamesTheorem.Reduction.SourceEncoding.equationWords (sourceEquation F u D p) =
      words (baseValue F u p.1.1 (sampledVariables F p.1.1 p.1.2))
        (mapEquation (descriptor u) (emit u D (ofContext F p.1.1 p.1.2, p.2))) := by
  rw [sourceEquation_eq_map_emit]
  simp only [UniqueGamesTheorem.Reduction.SourceEncoding.equationWords, words, mapEquation]
  rw [realize_descriptor, realize_descriptor, realize_descriptor]
  rfl

theorem baseValue_lt (F : Formula) (u : ℕ) (c : ClauseContext F u)
    (v : VariableContext F u) (side : Fin 3) :
    baseValue F u c v side < nBits F u := by
  have hside : side = 0 ∨ side = 1 ∨ side = 2 := by omega
  rcases hside with rfl | rfl | rfl
  · have h := (addressMap F u c v (.inl (fun _ => false))).isLt
    rw [← realize_descriptor] at h
    change _ + baseValue F u c v 0 < _ at h
    exact (Nat.le_add_left _ _).trans_lt h
  · have h := (addressMap F u c v (.inr (.inl (fun _ => false)))).isLt
    rw [← realize_descriptor] at h
    change _ + baseValue F u c v 1 < _ at h
    exact (Nat.le_add_left _ _).trans_lt h
  · have h := (addressMap F u c v (.inr (.inr ()))).isLt
    rw [← realize_descriptor] at h
    simpa only [realize, descriptor, Nat.zero_add] using h

theorem equation_emit_steps_le (F : Formula) (u : ℕ) (c : ClauseContext F u)
    (v : VariableContext F u) (e : Equation Descriptor) :
    2 * (baseValue F u c v e.first.1 + baseValue F u c v e.second.1 +
      baseValue F u c v e.third.1) + 16 ≤ 6 * nBits F u + 16 := by
  have h₁ := (baseValue_lt F u c v e.first.1).le
  have h₂ := (baseValue_lt F u c v e.second.1).le
  have h₃ := (baseValue_lt F u c v e.third.1).le
  omega

end UniqueGamesTheorem.Foundations.Hastad.SourceAddressDescriptors

/-! Actual fixed-coefficient affine address construction. A finite literal phase
loads the coefficient, the checked width-two Horner machine reads coefficient
and preserved offset with the rank as its radix, then the literal field is
actually consumed. All operands and work stacks are restored. -/

namespace UniqueGamesTheorem.Foundations.Hastad.SourceBasePhase

open Turing Complexity
open Target SourceContexts SourceOccurrences SourceAddressDescriptors
open UniqueGamesTheorem.Reduction.MachineSubstitution

variable {K Λ σ : Type} [DecidableEq K]

/-- Left query-block base from the preserved variable tuple rank and a zero offset field. -/
def leftBaseInTime (F : Formula) (u : Nat) (c : ClauseContext F u) (v : VariableContext F u)
    (slots : Layout ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ label, p (labels label) = statement slots (2 ^ (2 ^ u)) labels exit label)
    (base : K → List Bool)
    (rankWord : base (slots (.inl 0)) = encodeWord (((variableEncoding F u).code v).val))
    (zeroWord : base (slots (.inr 1)) = encodeWord 0)
    (coefficientEmpty : base (slots (.inr 0)) = [])
    (clean : MachineHorner.Clean slots base) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .seed), ((ambient, ()), register), base⟩
      (some ⟨exit, ((ambient, ()), none), MachineHorner.resultTapes slots base (baseValue F u c v 0)⟩)
      ((timePolynomial (2 ^ (2 ^ u))).eval (operandLength (((variableEncoding F u).code v).val) 0)) := by
  have h := affineInPolynomialTime slots (2 ^ (2 ^ u)) labels exit p atLabels base
    (((variableEncoding F u).code v).val) 0 rankWord zeroWord coefficientEmpty clean ambient register
  have hv : 2 ^ (2 ^ u) * (((variableEncoding F u).code v).val) + 0 = baseValue F u c v 0 := by
    simp [baseValue]
  simpa only [hv] using h

/-- Right query-block base using the globally retained left-block size. -/
def rightBaseInTime (F : Formula) (u : Nat) (c : ClauseContext F u) (v : VariableContext F u)
    (slots : Layout ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ label, p (labels label) = statement slots (2 ^ (8 ^ u)) labels exit label)
    (base : K → List Bool)
    (rankWord : base (slots (.inl 0)) = encodeWord (((clauseEncoding F u).code c).val))
    (leftBlockWord : base (slots (.inr 1)) = encodeWord (2 ^ (2 ^ u) * F.variables ^ u))
    (coefficientEmpty : base (slots (.inr 0)) = [])
    (clean : MachineHorner.Clean slots base) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .seed), ((ambient, ()), register), base⟩
      (some ⟨exit, ((ambient, ()), none), MachineHorner.resultTapes slots base (baseValue F u c v 1)⟩)
      ((timePolynomial (2 ^ (8 ^ u))).eval
        (operandLength (((clauseEncoding F u).code c).val) (2 ^ (2 ^ u) * F.variables ^ u))) := by
  have h := affineInPolynomialTime slots (2 ^ (8 ^ u)) labels exit p atLabels base
    (((clauseEncoding F u).code c).val) (2 ^ (2 ^ u) * F.variables ^ u)
    rankWord leftBlockWord coefficientEmpty clean ambient register
  have hv : 2 ^ (8 ^ u) * (((clauseEncoding F u).code c).val) + 2 ^ (2 ^ u) * F.variables ^ u =
      baseValue F u c v 1 := by
    simp [baseValue, Nat.mul_comm, Nat.add_comm]
  simpa only [hv] using h

end UniqueGamesTheorem.Foundations.Hastad.SourceBasePhase

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceFieldArrayLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Hastad.SourceClauseLookup

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineComposition SourceMachine

def outputTapes {n : Nat} (base : Tape → List Bool) (clause : Target.Clause n)
    (indexSuffix suffix : List Bool) : Tape → List Bool :=
  SourceFieldArray.sequenceTapes .work fieldDestination
    (scanTapes base 0 indexSuffix (encodeWords (clauseWords clause) ++ suffix))
    0 (clauseWords clause) suffix

end UniqueGamesTheorem.Foundations.Hastad.SourceClauseLookup

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceDescriptorEmissionLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Emit one fixed descriptor equation from three preserved unary base registers.
The output order is first address, second address, third address, RHS. The actual
stack program emits those fields in reverse order. -/

namespace UniqueGamesTheorem.Foundations.Hastad.SourceProfileBridge

open Target SourceContexts SourceOccurrences SourceLocalSignature
open Complexity

def names (F : Formula) {u : ℕ} (c : ClauseContext F u) :
    Fin (positionEncoding u).size → ℕ :=
  fun i => (occurrenceName F c ((positionEncoding u).code.symm i)).val

def nameWords (F : Formula) {u : ℕ} (c : ClauseContext F u) :
    Fin (positionEncoding u).size → List Bool :=
  fun i => encodeWord (names F c i)

end UniqueGamesTheorem.Foundations.Hastad.SourceProfileBridge

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceSignaturePrepareLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Hastad.SourceSignaturePrepare

open Turing
open Target PCP SourceContexts SourceOccurrences SourceLocalSignature SourceProfileBridge
open UniqueGamesTheorem.Foundations.Complexity

abbrev ProfileLabel (u : ℕ) := MachineFieldProfile.Label (MachineFieldProfile.allPairs (Width u))

inductive Label (u : ℕ)
  | profile (label : ProfileLabel u)
  | commit
  deriving DecidableEq, Fintype

end UniqueGamesTheorem.Foundations.Hastad.SourceSignaturePrepare

namespace UniqueGamesTheorem.Foundations.Hastad.SourceContextPrepare

open Turing UniqueGamesTheorem.Foundations.Complexity
open Target PCP SourceContexts SourceOccurrences SourceLocalSignature SourceProfileBridge

abbrev Label (u : Nat) := SourceContextLoad.Label u ⊕ SourceSignaturePrepare.Label u

variable {u : Nat} {Extra τ : Type}

variable [DecidableEq Extra]

def finalState (F : Formula) (c : ClauseContext F u) (selected : SlotContext u)
    (ambient : τ) : State u τ :=
  (((), none), (MachineFieldProfile.normalState (MachineFieldProfile.equalityProfile (nameWords F c)),
    (ofContext F c selected, ambient)))

end UniqueGamesTheorem.Foundations.Hastad.SourceContextPrepare

/-! The actual numbered equation list has exactly the acceptance bounded by
the private Fourier decoder. Only the repeated base-game value is an input
here; list semantics and all finite sampling laws are supplied. -/

namespace UniqueGamesTheorem.Foundations.Hastad.SourceTestAppend

open Turing Complexity
open Target SourceContexts SourceOccurrences SourceLocalSignature SourceLocalEquation
open SourceAddressDescriptors SourceEquationEmit SourceTestEmit

abbrev State (u D : Nat) := SourceTestEmit.State u D

end UniqueGamesTheorem.Foundations.Hastad.SourceTestAppend

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceQueryLoopLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An actual fixed finite traversal of all query/noise tapes. The finite
control contains one branch for each prescribed tape. The input-dependent
signature and the three address bases remain in registers throughout. -/

namespace UniqueGamesTheorem.Foundations.Hastad.SourceQueryLoop

open Turing Complexity Target SourceContexts SourceOccurrences
open SourceLocalSignature SourceLocalEquation

abbrev State (u D : Nat) := SourceTestAppend.State u D

end UniqueGamesTheorem.Foundations.Hastad.SourceQueryLoop

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceContextClear
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Hastad.SourceContextClear

open Turing Complexity MachineComposition

variable {u : Nat} {Extra : Type}

def fieldAt (i : Fin (u * 6)) : Tape u Extra :=
  .field (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2

def fields : List (Tape u Extra) := List.ofFn fieldAt

@[simp] theorem fields_length : (fields (u := u) (Extra := Extra)).length = 6 * u := by
  simp [fields, Nat.mul_comm]

def outputTapes (base : Tape u Extra → List Bool) : Tape u Extra → List Bool
  | .field _ _ => []
  | p => base p

@[simp] theorem output_field (base : Tape u Extra → List Bool) (j : Fin u) (s : Fin 6) :
    outputTapes base (.field j s) = [] := rfl

end UniqueGamesTheorem.Foundations.Hastad.SourceContextClear

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceQueryOrderLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace UniqueGamesTheorem.Foundations.Hastad.SourceRuntimeModel

open Turing Complexity SourceContexts SourceOccurrences SourceLocalSignature SourceProfileBridge


abbrev Arena (u : Nat) (Extra : Type) := SourceContextLoad.Tape u (BodyExtra Extra)
abbrev QueryState (u D : Nat) := SourceQueryLoop.State u D
abbrev State (u D : Nat) := SourceContextPrepare.State u (QueryState u D × ArithmeticState)
abbrev ArithmeticMetadata (u D : Nat) := SourceContextPrepare.LoadState ×
  (SourceSignaturePrepare.ProfileState u × (Signature u × QueryState u D))

variable {u D : Nat} {Extra : Type}

def workTape (role : BodyWork Extra) : Arena u Extra := .extra (.inr role)
def variableHeader : Arena u Extra := SourceLoopInit.variableHeader
def clauseHeader : Arena u Extra := SourceLoopInit.clauseHeader

def canonicalState (initialQuery : SourceQueryLoop.Query u D) : State u D :=
  SourceContextPrepare.initialState (fun _ _ => false) (canonicalSignature u)
    (((canonicalSignature u, initialQuery), none), (((), ()), none))

def queryStateEquiv (u D : Nat) : QueryState u D × QueryMetadata u ≃ State u D where
  toFun x := (x.2.1, (x.2.2.1, (x.2.2.2.1, (x.1, x.2.2.2.2))))
  invFun x := (x.2.2.2.1, (x.1, (x.2.1, (x.2.2.1, x.2.2.2.2))))
  left_inv _ := rfl
  right_inv _ := rfl

def arithmeticStateEquiv (u D : Nat) : ArithmeticState × ArithmeticMetadata u D ≃ State u D where
  toFun x := (x.2.1, (x.2.2.1, (x.2.2.2.1, (x.2.2.2.2, x.1))))
  invFun x := (x.2.2.2.2, (x.1, (x.2.1, (x.2.2.1, x.2.2.2.1))))
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem initializer_arena :
    SourceLoopInit.Tape u (BodyWork Extra) = Arena u Extra := rfl

end UniqueGamesTheorem.Foundations.Hastad.SourceRuntimeModel



namespace UniqueGamesTheorem.Foundations.Hastad.SourceGeneratorModel

open Turing Complexity SourceRuntimeModel


abbrev Tape (u D : Nat) := SourceRuntimeModel.Arena u (Extra u D)
abbrev State (u D : Nat) := SourceRuntimeModel.State u D

def accumulatorTape (u D : Nat) : Tape u D := workTape .accumulator

abbrev ControlAmbient (u D : Nat) := (Unit × Unit) × ArithmeticMetadata u D

/-- Expose the existing arithmetic head register to the odometer and final
cleanup. This is a static finite-state equivalence, with no machine steps. -/
def controlStateEquiv (u D : Nat) :
    ControlAmbient u D × Option Bool ≃ State u D where
  toFun x := arithmeticStateEquiv u D ((x.1.1, x.2), x.1.2)
  invFun x :=
    let y := (arithmeticStateEquiv u D).symm x
    ((y.1.1, y.2), y.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

def initialQuery (u D : Nat) (hD : 0 < D) : SourceQueryLoop.Query u D :=
  (fun _ => false, fun _ => ⟨0, hD⟩, fun _ => false)

def initialState (u D : Nat) (hD : 0 < D) : State u D :=
  canonicalState (initialQuery u D hD)

def initialAmbient (u D : Nat) (hD : 0 < D) : ControlAmbient u D :=
  ((controlStateEquiv u D).symm (initialState u D hD)).1

end UniqueGamesTheorem.Foundations.Hastad.SourceGeneratorModel



namespace UniqueGamesTheorem.Foundations.Hastad.SourceStartup

open Turing Complexity SourceRuntimeModel SourceGeneratorModel
open MachineComposition


noncomputable section

variable {u D : Nat}

abbrev Tape (u D : Nat) := SourceGeneratorModel.Tape u D

local instance instDecidableEqExtra (u D : Nat) : DecidableEq (SourceGeneratorModel.Extra u D) := Classical.decEq _

def initialTapes (F : Target.Formula) : Tape u D → List Bool :=
  Function.update (fun _ => []) .formula (formulaBits F)

def initializedTapes (F : Target.Formula) : Tape u D → List Bool :=
  SourceLoopInit.outputTapes F (initialTapes F)

def readyTapes (F : Target.Formula) : Tape u D → List Bool
  | .extra (.inr .leftBlock) => encodeWord (SourceHeaderCounts.leftValue u F.variables)
  | .extra (.inr .dummy) => encodeWord (SourceHeaderCounts.dummyValue u F.variables F.clauses.length)
  | .extra (.inr .accumulator) =>
      (encodeWords [SourceOccurrences.nBits F u, (SourceOccurrences.sourceList F u D).length]).reverse
  | p => initializedTapes F p

@[simp] theorem initialized_formula (F : Target.Formula) :
    initializedTapes (u := u) (D := D) F .formula = formulaBits F := by
  simp [initializedTapes, initialTapes]

@[simp] theorem initialized_current (F : Target.Formula) (j : Fin u) :
    initializedTapes (D := D) F (.current j) = encodeWord 0 := by
  simp [initializedTapes]

@[simp] theorem initialized_remaining (F : Target.Formula) (j : Fin u) :
    initializedTapes (D := D) F (.remaining j) = encodeWord (F.clauses.length - 1) := by
  simp [initializedTapes]

@[simp] theorem initialized_variableHeader (F : Target.Formula) :
    initializedTapes (u := u) (D := D) F variableHeader = encodeWord F.variables := by
  change SourceLoopInit.outputTapes F (initialTapes F) SourceLoopInit.variableHeader = _
  rw [SourceLoopInit.output_variableHeader]
  simp [initialTapes, SourceLoopInit.variableHeader]

@[simp] theorem initialized_clauseHeader (F : Target.Formula) :
    initializedTapes (u := u) (D := D) F clauseHeader = encodeWord F.clauses.length := by
  change SourceLoopInit.outputTapes F (initialTapes F) SourceLoopInit.clauseHeader = _
  rw [SourceLoopInit.output_clauseHeader]
  simp [initialTapes, SourceLoopInit.clauseHeader]

@[simp] theorem initialized_work (F : Target.Formula) (role : BodyWork (SourceGeneratorModel.Extra u D)) :
    initializedTapes F (workTape role) = [] := by
  rw [initializedTapes, SourceLoopInit.output_frame F (initialTapes F) (workTape role)
    (by simp [workTape]) (by simp [workTape, SourceLoopInit.variableHeader])
    (by simp [workTape, SourceLoopInit.clauseHeader]) (by simp [workTape]) (by simp [workTape])]
  simp [initialTapes, workTape]

@[simp] theorem initialized_work_raw (F : Target.Formula)
    (role : BodyWork (SourceGeneratorModel.Extra u D)) :
    initializedTapes F (.extra (.inr role)) = [] := initialized_work F role

@[simp] theorem initialized_field (F : Target.Formula) (j : Fin u) (s : Fin 6) :
    initializedTapes (D := D) F (.field j s) = [] := by
  rw [initializedTapes, SourceLoopInit.output_frame F (initialTapes F) (.field j s)
    (by simp) (by simp [SourceLoopInit.variableHeader]) (by simp [SourceLoopInit.clauseHeader])
    (by simp) (by simp)]
  simp [initialTapes]

@[simp] theorem ready_formula (F : Target.Formula) :
    readyTapes (u := u) (D := D) F .formula = formulaBits F := initialized_formula F

@[simp] theorem ready_current (F : Target.Formula) (j : Fin u) :
    readyTapes (D := D) F (.current j) = encodeWord 0 := initialized_current F j

@[simp] theorem ready_remaining (F : Target.Formula) (j : Fin u) :
    readyTapes (D := D) F (.remaining j) = encodeWord (F.clauses.length - 1) := initialized_remaining F j

@[simp] theorem ready_variableHeader (F : Target.Formula) :
    readyTapes (u := u) (D := D) F variableHeader = encodeWord F.variables := initialized_variableHeader F

@[simp] theorem ready_clauseHeader (F : Target.Formula) :
    readyTapes (u := u) (D := D) F clauseHeader = encodeWord F.clauses.length := initialized_clauseHeader F

@[simp] theorem ready_leftBlock (F : Target.Formula) :
    readyTapes (u := u) (D := D) F (workTape .leftBlock) =
      encodeWord (SourceHeaderCounts.leftValue u F.variables) := rfl

@[simp] theorem ready_dummy (F : Target.Formula) :
    readyTapes (u := u) (D := D) F (workTape .dummy) =
      encodeWord (SourceHeaderCounts.dummyValue u F.variables F.clauses.length) := rfl

@[simp] theorem ready_accumulator (F : Target.Formula) :
    readyTapes (u := u) (D := D) F (accumulatorTape u D) =
      (encodeWords [SourceOccurrences.nBits F u, (SourceOccurrences.sourceList F u D).length]).reverse := rfl

@[simp] theorem ready_field (F : Target.Formula) (j : Fin u) (s : Fin 6) :
    readyTapes (D := D) F (.field j s) = [] := initialized_field F j s

@[simp] theorem ready_sharedWork (F : Target.Formula) :
    readyTapes (u := u) (D := D) F .work = [] := by
  simp [readyTapes, initializedTapes]

end

end UniqueGamesTheorem.Foundations.Hastad.SourceStartup



namespace UniqueGamesTheorem.Foundations.Hastad.SourceTupleTape

open Turing Complexity SourceContexts SourceRuntimeModel


variable {u : Nat} {Extra : Type}

def tapes (base : Arena u Extra → List Bool) (s : Snapshot) : Arena u Extra → List Bool
  | .extra (.inr .rank) => s.rank
  | .extra (.inr .rightBase) => s.rightBase
  | .extra (.inr .leftBase) => s.leftBase
  | .extra (.inr .zero) => s.zero
  | .extra (.inr .accumulator) => s.emitted.reverse ++ base (workTape .accumulator)
  | k => base k

@[simp] theorem tapes_rank (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes base s (workTape .rank) = s.rank := rfl
@[simp] theorem tapes_rightBase (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes base s (workTape .rightBase) = s.rightBase := rfl
@[simp] theorem tapes_leftBase (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes base s (workTape .leftBase) = s.leftBase := rfl
@[simp] theorem tapes_zero (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes base s (workTape .zero) = s.zero := rfl
@[simp] theorem tapes_accumulator (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes base s (workTape .accumulator) = s.emitted.reverse ++ base (workTape .accumulator) := rfl
@[simp] theorem tapes_coefficient (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes base s (workTape .coefficient) = base (workTape .coefficient) := rfl
@[simp] theorem tapes_dummy (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes base s (workTape .dummy) = base (workTape .dummy) := rfl
@[simp] theorem tapes_leftBlock (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes base s (workTape .leftBlock) = base (workTape .leftBlock) := rfl
@[simp] theorem tapes_queryTemporary (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes base s (workTape .queryTemporary) = base (workTape .queryTemporary) := rfl
@[simp] theorem tapes_queryScratch (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes base s (workTape .queryScratch) = base (workTape .queryScratch) := rfl
@[simp] theorem tapes_field (base : Arena u Extra → List Bool) (s : Snapshot) (j : Fin u) (k : Fin 6) :
    tapes base s (.field j k) = base (.field j k) := rfl
@[simp] theorem tapes_current (base : Arena u Extra → List Bool) (s : Snapshot) (j : Fin u) :
    tapes base s (.current j) = base (.current j) := rfl
@[simp] theorem tapes_formula (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes base s .formula = base .formula := rfl
@[simp] theorem tapes_index (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes base s .index = base .index := rfl
@[simp] theorem tapes_work (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes base s .work = base .work := rfl
@[simp] theorem tapes_variableHeader (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes base s variableHeader = base variableHeader := rfl
@[simp] theorem tapes_clauseHeader (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes base s clauseHeader = base clauseHeader := rfl

end UniqueGamesTheorem.Foundations.Hastad.SourceTupleTape

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceTupleBody
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.slotFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-! One actual clause-tuple body. Its fixed finite control loads the context,
computes the shared right address base, traverses every selected-slot tuple and
query tape in their declared encoding order, and physically clears its work.
-/

namespace UniqueGamesTheorem.Foundations.Hastad.SourceTupleBody

open Turing Complexity SourceContexts SourceOccurrences SourceLocalSignature
open SourceRuntimeModel SourceTupleTape


abbrev Query (u D : Nat) := SourceQueryLoop.Query u D

variable {u D : Nat} {Extra : Type}

variable [DecidableEq Extra]

/-- Only the chosen-slot/query registers change; the computed context profile
and original signature remain available across all local traversals. -/
def selectState (initialQuery : Query u D) (index : Fin (SlotCount u))
    (state : State u D) : State u D :=
  (state.1, (state.2.1, (state.2.2.1,
    ((({state.2.2.1 with selected := selected index}, initialQuery), none), state.2.2.2.2))))

def contextSignature (F : Target.Formula) (c : ClauseContext F u) : Signature u :=
  ofContext F c (fun _ => .first)

def workingState (F : Target.Formula) (c : ClauseContext F u)
    (signature : Signature u) (query : Query u D) : State u D :=
  SourceContextPrepare.finalState F c (fun _ => .first)
    (((signature, query), none), (((), ()), none))

@[simp] theorem workingState_loader (F : Target.Formula) (c : ClauseContext F u)
    (signature : Signature u) (query : Query u D) :
    (((), none), (workingState F c signature query).2) = workingState F c signature query := rfl

def arithmeticMetadata (F : Target.Formula) (c : ClauseContext F u)
    (signature : Signature u) (query : Query u D) : ArithmeticMetadata u D :=
  (((), none), (MachineFieldProfile.normalState
    (MachineFieldProfile.equalityProfile (SourceProfileBridge.nameWords F c)),
      (contextSignature F c, ((signature, query), none))))

def queryMetadata (F : Target.Formula) (c : ClauseContext F u) : QueryMetadata u :=
  (((), none), (MachineFieldProfile.normalState
    (MachineFieldProfile.equalityProfile (SourceProfileBridge.nameWords F c)),
      (contextSignature F c, (((), ()), none))))

@[simp] theorem arithmeticState_working (F : Target.Formula) (c : ClauseContext F u)
    (signature : Signature u) (query : Query u D) :
    arithmeticStateEquiv u D ((((), ()), none), arithmeticMetadata F c signature query) =
      workingState F c signature query := rfl

@[simp] theorem queryState_working (F : Target.Formula) (c : ClauseContext F u)
    (signature : Signature u) (query : Query u D) :
    queryStateEquiv u D (((signature, query), none), queryMetadata F c) =
      workingState F c signature query := rfl

@[simp] theorem select_workingState (F : Target.Formula) (c : ClauseContext F u)
    (index : Fin (SlotCount u)) (initialQuery query : Query u D) (signature : Signature u) :
    selectState initialQuery index (workingState F c signature query) =
      workingState F c (ofContext F c (selected index)) initialQuery := rfl

omit [DecidableEq Extra] in
@[simp] theorem loaded_extra (F : Target.Formula) (c : ClauseContext F u)
    (base : Arena u Extra → List Bool) (extra : BodyExtra Extra) :
    SourceContextLoad.stageTapes F c base u (.extra extra) = base (.extra extra) :=
  SourceContextLoad.stageTapes_frame F c base u _ (by simp) (by simp) (by simp)

end UniqueGamesTheorem.Foundations.Hastad.SourceTupleBody

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceGapLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace UniqueGamesTheorem.Foundations.Hastad.SourceGeneratorProgram

open Turing Complexity SourceGeneratorModel

noncomputable section


abbrev Ambient (u D : Nat) := SourceGeneratorModel.ControlAmbient u D
abbrev State (u D : Nat) := Ambient u D × Option Bool

local instance instDecidableEqExtra_rcb1e0c_1 (u D : Nat) : DecidableEq (Extra u D) := Classical.decEq _
def sourceStateEquiv (u D : Nat) : SourceRuntimeModel.State u D × Unit ≃ State u D where
  toFun x := (controlStateEquiv u D).symm x.1
  invFun x := (controlStateEquiv u D x, ())
  left_inv x := by cases x with | mk x y => cases y; simp
  right_inv x := by simp

end

end UniqueGamesTheorem.Foundations.Hastad.SourceGeneratorProgram



namespace UniqueGamesTheorem.Foundations.Hastad.SourceGeneratorTraversal

open Turing Complexity SourceContexts SourceOccurrences SourceRuntimeModel
open SourceGeneratorModel SourceGeneratorProgram SourceOdometerSchedule


noncomputable section

variable {u D : Nat}

local instance instDecidableEqExtra (u D : Nat) : DecidableEq (SourceGeneratorModel.Extra u D) := Classical.decEq _

def accumulatorRole (u D : Nat) : BodyExtra (SourceGeneratorModel.Extra u D) :=
  .inr .accumulator

def leafTapes (F : Target.Formula) (c : ClauseContext F u) (output : List Bool) :
    SourceGeneratorModel.Tape u D → List Bool :=
  setDigits F.clauses.length (fun i => (c i).val)
    (setAcc (accumulatorRole u D) (SourceStartup.readyTapes F) output)

@[simp] theorem leaf_accumulator (F : Target.Formula) (c : ClauseContext F u) (output : List Bool) :
    leafTapes (D := D) F c output (accumulatorTape u D) = output := by
  exact setAcc_apply (accumulatorRole u D) (SourceStartup.readyTapes F) output

@[simp] theorem source_initial (hD : 0 < D) :
    sourceStateEquiv u D (canonicalState (initialQuery u D hD), ()) =
      (initialAmbient u D hD, none) := rfl

def traversalOutput (F : Target.Formula) (hD : 0 < D) : SourceGeneratorModel.Tape u D → List Bool :=
  Function.update (SourceStartup.readyTapes F) (accumulatorTape u D)
    (UniqueGamesTheorem.Reduction.SourceEncoding.inputBits (sourceInput F u D hD)).reverse

@[simp] theorem traversalOutput_accumulator (F : Target.Formula) (hD : 0 < D) :
    traversalOutput F hD (accumulatorTape u D) =
      (UniqueGamesTheorem.Reduction.SourceEncoding.inputBits (sourceInput F u D hD)).reverse := by
  simp [traversalOutput]

end

end UniqueGamesTheorem.Foundations.Hastad.SourceGeneratorTraversal



end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_FinalTableFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! The exact table-to-formula converter used by the final CNF machine.
Its semantic count premise is explicit; amplification supplies that premise
elsewhere. The converter chooses no vertex or dart numbering. -/

namespace UniqueGamesTheorem.Foundations.PCP.FinalTableFormula

open Target Complexity

def output (table : GraphTables.Table) : Formula :=
  FinalBooleanVerifier.cnf (FinalCNFPattern.tableGraph table) (Equiv.refl _) (Equiv.refl _)

@[simp] theorem variable_count (table : GraphTables.Table) :
    (output table).variables = table.vertices * 6 + table.darts * 36864 :=
  FinalBooleanVerifier.cnf_variable_count _ (Equiv.refl _) (Equiv.refl _)

@[simp] theorem clause_count (table : GraphTables.Table) :
    (output table).clauses.length = table.darts * 40960 :=
  FinalBooleanVerifier.cnf_clause_count _ (Equiv.refl _) (Equiv.refl _)

theorem formulaBits_length_le_polynomial (table : GraphTables.Table) :
    (formulaBits (output table)).length ≤
      sizePolynomial.eval (GraphTables.tableBits table).length := by
  have hinput := GraphTableComplexity.size_add_two_le_bits table
  have hv : (output table).variables ≤ 36864 * (GraphTables.tableBits table).length := by
    rw [variable_count]
    omega
  have hc : (output table).clauses.length ≤ 40960 * (GraphTables.tableBits table).length := by
    rw [clause_count]
    omega
  have hsum : (output table).variables + (output table).clauses.length + 2 ≤
      77824 * (GraphTables.tableBits table).length + 2 := by omega
  have hproduct := Nat.mul_le_mul hc (Nat.mul_le_mul_left 3 (Nat.add_le_add_right hv 2))
  rw [sizePolynomial_eval]
  exact (formulaBits_length_le (output table)).trans (Nat.add_le_add hsum hproduct)

end UniqueGamesTheorem.Foundations.PCP.FinalTableFormula

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_FinalCNFOutputLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-!
The final machine's complete output stream is the exact serialization of its
actual formula. This identity includes the two size fields, every clause and
literal field, and all unary delimiters. No desired output equality is assumed.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program

open PCP

section Alphabet

open PCP.AlphabetTable


def formulaHeader (table : GraphTables.Table) : List Bool :=
  encodeWords [6 * table.vertices + 36864 * table.darts, 40960 * table.darts]

theorem formulaHeader_eq (table : GraphTables.Table) :
    formulaHeader table = encodeWords [(FinalTableFormula.output table).variables,
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

end Alphabet

/-- The bound specialized to the actual table and actual formula serialization. -/
theorem table_phaseTime_le (table : GraphTables.Table) :
    headerTimePolynomial.eval (GraphTables.tableBits table).length +
      (table.darts * (rowTime rowPlan (GraphTables.tableBits table).length + 1) + 1) +
      ((formulaBits (FinalTableFormula.output table)).length + 1) ≤
        phaseTimePolynomial.eval (GraphTables.tableBits table).length :=
  phaseTime_le (GraphTables.darts_le_tableBits_length table)
    (FinalTableFormula.formulaBits_length_le_polynomial table)

/-!
The complete polynomial-time machine certificate for converting a validated
64-label graph table into its actual 3CNF formula. The proof composes the real
input parser, all row executions, output reversal, and private-tape cleanup.
-/

open Turing


theorem emittedBytes_eq_formulaBits (table : GraphTables.Table) :
    emittedBytes rowPlan table = formulaBits (FinalTableFormula.output table) :=
  header_append_outputStream table

theorem rawBudget_le_phaseTime (table : GraphTables.Table) :
    rawBudget rowPlan table ≤ phaseTimePolynomial.eval (GraphTables.tableBits table).length := by
  unfold rawBudget
  rw [emittedBytes_eq_formulaBits]
  simpa only [Nat.add_assoc] using table_phaseTime_le table

/-- A concrete finite machine computes the complete CNF serialization from
the exact unary graph-table serialization, with a proved polynomial bound. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime GraphTables.tableBits formulaBits FinalTableFormula.output where
  tm := FinalCNFCleanup.completedMachine headerPlan rowPlan
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := finalTimePolynomial (Runtime.programPushBound (machine headerPlan rowPlan))
  outputsFun table := by
    change TM2OutputsInTime (FinalCNFCleanup.completedMachine headerPlan rowPlan)
      ((GraphTables.tableBits table).map id)
      (some ((formulaBits (FinalTableFormula.output table)).map id))
      ((finalTimePolynomial (Runtime.programPushBound (machine headerPlan rowPlan))).eval
        (GraphTables.tableBits table).length)
    have input_eq :
        @List.map ((FinalCNFCleanup.completedMachine headerPlan rowPlan).Γ
            (FinalCNFCleanup.completedMachine headerPlan rowPlan).k₀)
          ((FinalCNFCleanup.completedMachine headerPlan rowPlan).Γ
            (FinalCNFCleanup.completedMachine headerPlan rowPlan).k₀)
          id (GraphTables.tableBits table) = GraphTables.tableBits table := List.map_id _
    have output_eq :
        @List.map ((FinalCNFCleanup.completedMachine headerPlan rowPlan).Γ
            (FinalCNFCleanup.completedMachine headerPlan rowPlan).k₁)
          ((FinalCNFCleanup.completedMachine headerPlan rowPlan).Γ
            (FinalCNFCleanup.completedMachine headerPlan rowPlan).k₁)
          id (formulaBits (FinalTableFormula.output table)) =
          formulaBits (FinalTableFormula.output table) := List.map_id _
    rw [input_eq, output_eq, finalTimePolynomial_eval]
    let raw := rawRun rowPlan table
    let bounded : StateTransition.EvalsToInTime (machine headerPlan rowPlan).step
        (initList (machine headerPlan rowPlan) (GraphTables.tableBits table))
        (some ⟨none, ((raw.finalAmbient, ()), none), raw.finalTapes⟩)
        (phaseTimePolynomial.eval (GraphTables.tableBits table).length) := {
      toEvalsTo := raw.execution.toEvalsTo
      steps_le_m := raw.execution.steps_le_m.trans (rawBudget_le_phaseTime table) }
    have correct : raw.finalTapes .output = formulaBits (FinalTableFormula.output table) :=
      raw.output.trans (emittedBytes_eq_formulaBits table)
    have run := FinalCNFCleanup.outputsInTime headerPlan rowPlan
      (GraphTables.tableBits table) (formulaBits (FinalTableFormula.output table))
      ((raw.finalAmbient, ()), none) raw.finalTapes
      (phaseTimePolynomial.eval (GraphTables.tableBits table).length) bounded correct
    exact run

end UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachinePaddingRowsLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachinePaddingRows

open Turing MachineComposition

theorem bodyTrace (d : Nat) (hd : 0 < d) (v e fuel : Nat) (output : List Bool) :
    (advance (TM2.step (program d hd)))^[MachineDummyRows.steps v e output d]
      (some (cfg d (some (bodyEntry d hd)) v e fuel output)) =
      some (cfg d (some (.inr .bump)) v (e + d) fuel
        (output ++ MachineDummyRows.rowsBits v e d)) := by
  have run := MachineDummyRows.suffixTrace d ⟨0, hd⟩ (by simp)
    v e output () none
  have lifted := liftSuccessfulTrace
    (TM2.step (MachineDummyRows.program d)) (TM2.step (program d hd))
    (MachineEmbedding.configuration (some (.inr .bump)) ()
      (fun _ : Unit => encodeWord fuel))
    (by
      intro a b h
      exact MachineEmbedding.step_simulation (some (.inr Control.bump)) ()
        (fun _ : Unit => encodeWord fuel) (MachineDummyRows.program d) (extra d hd) a b h)
    (MachineDummyRows.steps v e output d) _ _ run
  exact lifted

/-- The entire varying-length padding loop is proved from its actual guards,
actual row bodies and actual vertex increments. -/
theorem loopTrace (d : Nat) (hd : 0 < d) (count v e : Nat) (output : List Bool) :
    (advance (TM2.step (program d hd)))^[steps d v e output count]
      (some (cfg d (some (.inr .guard)) v e count output)) =
      some (cfg d none (v + count) (e + count * d) 0
        (output ++ paddingBits d v e count)) := by
  induction count generalizing v e output with
  | zero => simpa [steps, paddingBits] using guard_zero d hd v e output
  | succ count ih =>
      rw [steps, Nat.add_comm (MachineDummyRows.steps v e output d + 2),
        Function.iterate_add_apply]
      have hb : (advance (TM2.step (program d hd)))^[MachineDummyRows.steps v e output d + 2]
          (some (cfg d (some (.inr .guard)) v e (count + 1) output)) =
          some (cfg d (some (.inr .guard)) (v + 1) (e + d) count
            (output ++ MachineDummyRows.rowsBits v e d)) := by
        rw [show MachineDummyRows.steps v e output d + 2 =
          (MachineDummyRows.steps v e output d + 1) + 1 by omega,
          Function.iterate_succ_apply, advance_some, guard_succ,
          Function.iterate_succ_apply', bodyTrace, advance_some, bump_step]
      rw [hb, ih]
      simp only [paddingBits, List.append_assoc, Nat.succ_mul]
      congr 2 <;> omega

theorem paddingTrace (d : Nat) (hd : 0 < d) (count v e : Nat) (output : List Bool) :
    (advance (TM2.step (program d hd)))^[steps d v e output count + 1]
      (some ⟨some (.inr .initialize_), (((), none), ()), initialTapes v e count output⟩) =
      some (cfg d none (v + count) (e + count * d) 0
        (output ++ paddingBits d v e count)) := by
  rw [Function.iterate_succ_apply, advance_some, initialize_step, loopTrace]

end UniqueGamesTheorem.Foundations.Complexity.MachinePaddingRows

/-! Polynomial bounds for the actual outer padding-loop recurrence. No
execution or cost premise is introduced: the recurrence is the one matched
to the concrete machine by `MachinePaddingRows.loopTrace`. -/

namespace UniqueGamesTheorem.Foundations.Complexity.MachinePaddingBounds

/-- All rows in a fixed block are bounded by its last possible index. -/
theorem rowsBits_length_le (v e count : Nat) :
    (MachineDummyRows.rowsBits v e count).length ≤ count * (v + e + count + 8194) := by
  induction count generalizing e with
  | zero => simp [MachineDummyRows.rowsBits]
  | succ count ih =>
    have hi := ih (e + 1)
    have hb : v + (e + 1) + count + 8194 = v + e + (count + 1) + 8194 := by omega
    rw [hb] at hi
    have hr : v + e + 8194 ≤ v + e + (count + 1) + 8194 := by omega
    simp only [MachineDummyRows.rowsBits, List.length_append, MachineDummyRows.rowBits_length]
    calc
      _ ≤ (v + e + (count + 1) + 8194) +
          count * (v + e + (count + 1) + 8194) := Nat.add_le_add hr hi
      _ = _ := by rw [Nat.add_mul, Nat.one_mul]; omega

/-- The actual outer-loop cost is bounded by the number of vertices times
a uniform bound on its actual row bodies and two control transitions. -/
theorem steps_le_bound (d v e : Nat) (output : List Bool) (count : Nat) :
    MachinePaddingRows.steps d v e output count ≤
      count * (d * (4 * rowBound d v e count +
        2 * (output.length + count * d * rowBound d v e count) + 10) + 2) + 1 := by
  induction count generalizing v e output with
  | zero => simp [MachinePaddingRows.steps]
  | succ count ih =>
    let B := rowBound d v e (count + 1)
    let C := d * (4 * B + 2 * (output.length + (count + 1) * d * B) + 10) + 2
    have hb : rowBound d (v + 1) (e + d) count = B := rowBound_next d v e count
    have hr : v + e + d + 8194 ≤ B := blockRow_le_rowBound d v e count
    have hlen : (MachineDummyRows.rowsBits v e d).length ≤ d * B :=
      (rowsBits_length_le v e d).trans (Nat.mul_le_mul_left d hr)
    have hout : (output ++ MachineDummyRows.rowsBits v e d).length + count * d * B ≤
        output.length + (count + 1) * d * B := by
      rw [List.length_append]
      calc
        _ ≤ output.length + d * B + count * d * B :=
          Nat.add_le_add_right (Nat.add_le_add_left hlen output.length) _
        _ = _ := by simp only [Nat.add_mul, Nat.one_mul]; omega
    have hi := ih (v + 1) (e + d) (output ++ MachineDummyRows.rowsBits v e d)
    rw [hb] at hi
    have hconstant :
        d * (4 * B + 2 * ((output ++ MachineDummyRows.rowsBits v e d).length +
          count * d * B) + 10) + 2 ≤ C := by
      exact Nat.add_le_add_right (Nat.mul_le_mul_left d
        (Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left 2 hout) (4 * B)) 10)) 2
    have hremaining := hi.trans
      (Nat.add_le_add_right (Nat.mul_le_mul_left count hconstant) 1)
    have hcount : d * B ≤ (count + 1) * d * B := by
      simpa only [Nat.one_mul, Nat.mul_assoc] using
        Nat.mul_le_mul_right (d * B) (Nat.succ_le_succ (Nat.zero_le count))
    have hbodyOutput : output.length + d * (v + e + d + 8194) ≤
        output.length + (count + 1) * d * B :=
      Nat.add_le_add_left ((Nat.mul_le_mul_left d hr).trans hcount) output.length
    have hbodyInner : 4 * (v + e + d + 8194) +
        2 * (output.length + d * (v + e + d + 8194)) + 10 ≤
          4 * B + 2 * (output.length + (count + 1) * d * B) + 10 := by
      exact Nat.add_le_add_right (Nat.add_le_add (Nat.mul_le_mul_left 4 hr)
        (Nat.mul_le_mul_left 2 hbodyOutput)) 10
    have hbody : MachineDummyRows.steps v e output d + 2 ≤ C :=
      Nat.add_le_add_right ((MachineDummyRows.steps_le_bound v e output d).trans
        (Nat.mul_le_mul_left d hbodyInner)) 2
    change (MachineDummyRows.steps v e output d + 2) +
      MachinePaddingRows.steps d (v + 1) (e + d)
        (output ++ MachineDummyRows.rowsBits v e d) count ≤ (count + 1) * C + 1
    calc
      _ ≤ C + (count * C + 1) := Nat.add_le_add hbody hremaining
      _ = _ := by rw [Nat.add_mul, Nat.one_mul]; omega

theorem timePolynomial_bounds (d v e count : Nat) (output : List Bool) :
    MachinePaddingRows.steps d v e output count ≤
      (timePolynomial d).eval (inputSize v e count output) := by
  have hc : count ≤ inputSize v e count output := by
    simp only [inputSize, encodeWord_length]
    omega
  have ho : output.length ≤ inputSize v e count output := by
    simp only [inputSize, encodeWord_length]
    omega
  have hb := rowBound_le_cap d v e count output
  have hp := Nat.mul_le_mul (Nat.mul_le_mul_right d hc) hb
  have hout := Nat.add_le_add ho hp
  have hinner := Nat.add_le_add_right
    (Nat.add_le_add (Nat.mul_le_mul_left 4 hb) (Nat.mul_le_mul_left 2 hout)) 10
  have hbody := Nat.add_le_add_right (Nat.mul_le_mul_left d hinner) 2
  have h := (steps_le_bound d v e output count).trans
    (Nat.add_le_add_right (Nat.mul_le_mul hc hbody) 1)
  simpa only [timePolynomial, rowPolynomial, rowCap, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one] using h

end UniqueGamesTheorem.Foundations.Complexity.MachinePaddingBounds

/-! Polynomial-time certificate for the actual varying-length padding loop,
including its one-time relation initialization. The input vertex, reverse
index, fuel, and accumulated output are all measured as physically stored
bits. This is a reusable stage of the graph-table transformation. -/

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_PreprocessingPaddingWords
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Exact serialization of whole-vertex padding

The original dart rows remain in their original order, with every old tail,
reverse index, and relation bit unchanged. The suffix is exactly the bit stream
emitted by the checked dummy-vertex machine, starting at vertex `n` and dart
`n*d`. This is an equality for the actual table codec, with no runtime premise.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingWords

open Complexity PortTables

variable {n m d : Nat}

/-- Recover the original flat row from its exact mixed-radix coordinates. -/
theorem rowBits_flat (table : Table n d) (i : Fin (n * d)) :
    encodeWords (GraphTables.rowWords ((flatRows table)[i])) =
      rowBits table ((rowIndex n d).symm i).1 ((rowIndex n d).symm i).2 := by
  simp only [flatRows, Vector.getElem_ofFn, Fin.getElem_fin,
    MachineTableRows.rowBits_eq, rowBits, Prod.eta, Equiv.apply_symm_apply]

/-- Serializing all rows agrees with grouping their bits by vertex and port. -/
theorem rowsBits_eq_vertices (table : Table n d) :
    rowsBits table = (List.ofFn (fun v : Fin n => vertexBits table v)).flatten := by
  have hflat : (flatRows table).toList =
      List.ofFn (fun i : Fin (n * d) => (flatRows table)[i]) := by
    simp only [flatRows, Vector.toList_ofFn, Vector.getElem_ofFn, Fin.getElem_fin]
  unfold rowsBits
  rw [hflat, encodeWords_flatMap, List.flatMap_def, List.map_ofFn]
  change (List.ofFn (fun i : Fin (n * d) =>
    encodeWords (GraphTables.rowWords ((flatRows table)[i])))).flatten = _
  simp_rw [rowBits_flat]
  simpa only [Equiv.symm_apply_apply, vertexBits] using
    flatten_ofFn_rowIndex (fun i : Fin (n * d) =>
      rowBits table ((rowIndex n d).symm i).1 ((rowIndex n d).symm i).2)

/-- The actual padded row codec is the old row codec followed by the emitted suffix. -/
theorem rowsBits_pad (table : Table n d) (h : n ≤ m) :
    rowsBits (PreprocessingPaddingTables.pad table h) =
      rowsBits table ++ MachinePaddingRows.paddingBits d n (n * d) (m - n) := by
  rw [rowsBits_eq_vertices, ofFn_split h, List.flatten_append]
  simp_rw [vertexBits_pad_old, vertexBits_pad_new]
  rw [← rowsBits_eq_vertices, ← paddingBits_eq_ofFn]

/-- Exact final codec identity used by the machine-output correspondence. -/
theorem tableBits_pad (table : Table n d) (h : n ≤ m) :
    tableBits (PreprocessingPaddingTables.pad table h) =
      encodeWords [m, m * d] ++ rowsBits table ++
        MachinePaddingRows.paddingBits d n (n * d) (m - n) := by
  change encodeWords (PortTables.tableWords (PreprocessingPaddingTables.pad table h)) = _
  rw [tableWords_eq, encodeWords_append]
  change encodeWords [m, m * d] ++ rowsBits (PreprocessingPaddingTables.pad table h) = _
  rw [rowsBits_pad, List.append_assoc]

end UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingWords

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_PreprocessingRegularWords
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Complete serialization of the actual regularized table

Each global vertex emits its internal ports in increasing order, then its
inherited port. Original darts are the first global vertices. Dummy vertices
follow in increasing owner and local-dummy order. These are identities for the
actual stored rows and existing codec, with arbitrary actual cloud tables.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords

open DegreeReplacement PreprocessingCloudIndex PreprocessingRegularTables Complexity
open scoped BigOperators

variable (t : GraphTables.Table) (padding : Fin t.vertices → Nat) {q : Nat}
variable (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding v) q)

/-- Per-row serialization agrees with the generic table codec. -/
theorem actualRow_bits (x : Vertex t padding) (p : Fin q ⊕ Unit) :
    encodeWords (GraphTables.rowWords (actualRow t padding tables x p)) =
      PreprocessingPaddingWords.rowBits (ofCloudTables t padding tables)
        (vertexOrder t padding x) (portOrder q p) := by
  simpa only [actualRow, Equiv.symm_apply_apply] using
    PreprocessingPaddingWords.rowBits_flat (ofCloudTables t padding tables)
      (PortTables.rowIndex _ _ (vertexOrder t padding x, portOrder q p))

/-- Each block uses exactly the port order of the actual stored table. -/
theorem vertexBits_eq (x : Vertex t padding) :
    vertexBits t padding tables x =
      PreprocessingPaddingWords.vertexBits (ofCloudTables t padding tables)
        (vertexOrder t padding x) := by
  unfold vertexBits vertexRows
  rw [List.flatMap_append, encodeWords_append]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [encodeWords_flatMap, List.flatMap_def, List.map_ofFn]
  change (List.ofFn (fun p : Fin q =>
    encodeWords (GraphTables.rowWords (actualRow t padding tables x (.inl p))))).flatten ++
      encodeWords (GraphTables.rowWords (actualRow t padding tables x (.inr ()))) = _
  simp_rw [actualRow_bits]
  unfold PreprocessingPaddingWords.vertexBits
  rw [List.ofFn_succ_last, List.flatten_append]
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
  rfl

/-- The whole actual row stream, split into the two executable outer loops. -/
theorem rowsBits_ofCloudTables :
    PreprocessingPaddingWords.rowsBits (ofCloudTables t padding tables) =
      (List.ofFn (originalVertexBits t padding tables)).flatten ++
        (List.ofFn (fun v : Fin t.vertices =>
          (List.ofFn (dummyVertexBits t padding tables v)).flatten)).flatten := by
  rw [PreprocessingPaddingWords.rowsBits_eq_vertices]
  have hblocks :
      List.ofFn (fun i : Fin (vertexCount t padding) =>
        PreprocessingPaddingWords.vertexBits (ofCloudTables t padding tables) i) =
      List.ofFn (fun i : Fin (vertexCount t padding) =>
        vertexBits t padding tables ((vertexOrder t padding).symm i)) := by
    apply congrArg List.ofFn
    funext i
    rw [vertexBits_eq, Equiv.apply_symm_apply]
  rw [hblocks, vertexOrder_ofFn, List.flatten_append]
  change (List.ofFn (originalVertexBits t padding tables)).flatten ++
      ((paddingList padding).map (fun z => dummyVertexBits t padding tables z.1 z.2)).flatten = _
  rw [← List.flatMap_def, paddingList_flatMap]

/-- Exact complete codec identity: new headers, original blocks, then dummy blocks. -/
theorem tableBits_ofCloudTables :
    PortTables.tableBits (ofCloudTables t padding tables) =
      encodeWords [vertexCount t padding, vertexCount t padding * (q + 1)] ++
        (List.ofFn (originalVertexBits t padding tables)).flatten ++
        (List.ofFn (fun v : Fin t.vertices =>
          (List.ofFn (dummyVertexBits t padding tables v)).flatten)).flatten := by
  change encodeWords (PortTables.tableWords (ofCloudTables t padding tables)) = _
  rw [PortTables.tableWords_eq, encodeWords_append]
  change encodeWords [vertexCount t padding, vertexCount t padding * (q + 1)] ++
    PreprocessingPaddingWords.rowsBits (ofCloudTables t padding tables) = _
  rw [rowsBits_ofCloudTables, List.append_assoc]

end UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_RawInitialTablesLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit structural numberings of the raw 3SAT incidence graph. Unused
declared variable names are retained; their unary input header pays for them.
The graph has one dummy vertex and one tautological loop, even for an empty
formula. No input-dependent choice of a finite enumeration is made. -/

namespace UniqueGamesTheorem.Foundations.PCP.RawInitialTables

open Target GraphTables

theorem table_darts_positive (F : Formula) : 0 < (table F).darts := by
  rw [table_darts]; omega

theorem initial_size (F : Formula) :
    (table F).vertices + (table F).darts = F.variables + 7 * F.clauses.length + 2 := by
  rw [table_vertices, table_darts]
  omega

end UniqueGamesTheorem.Foundations.PCP.RawInitialTables

/-! Polynomial arithmetic for the actual initial-machine phase counts. The
separate execution theorem must connect these counts to the concrete program. -/

namespace UniqueGamesTheorem.Foundations.PCP.RawInitialMachineBudget

open Target Complexity

def nameSum {n : Nat} (clause : Clause n) : Nat :=
  clause[0].variableIndex.val + clause[1].variableIndex.val + clause[2].variableIndex.val

def bodyTime {n : Nat} (i : Nat) (c : Clause n) : Nat :=
  6 * n + 18 * i + 2 * nameSum c +
    2 * (encodeWords (Complexity.clauseWords c)).length + 63

def loopTime {n : Nat} (i : Nat) : List (Clause n) → Nat
  | [] => 1
  | c :: cs => bodyTime i c + loopTime (i + 1) cs

theorem nameSum_le {n : Nat} (clause : Clause n) : nameSum clause ≤ 3 * n := by
  have h0 := clause[0].variableIndex.isLt
  have h1 := clause[1].variableIndex.isLt
  have h2 := clause[2].variableIndex.isLt
  unfold nameSum
  omega

theorem bodyTime_le {n : Nat} (i : Nat) (c : Clause n) :
    bodyTime i c ≤ 18 * n + 18 * i + 81 := by
  have hn := nameSum_le c
  have hb := clauseBits_length_le c
  unfold bodyTime
  omega

theorem loopTime_le {n : Nat} (i : Nat) (cs : List (Clause n)) :
    loopTime i cs ≤ cs.length * (18 * n + 18 * (i + cs.length) + 81) + 1 := by
  induction cs generalizing i with
  | nil => simp [loopTime]
  | cons c cs ih =>
      have hc := bodyTime_le i c
      have ht := ih (i + 1)
      have hbound : bodyTime i c ≤ 18 * n + 18 * (i + (c :: cs).length) + 81 := by
        simp only [List.length_cons]
        omega
      have hsame : 18 * n + 18 * (i + 1 + cs.length) + 81 =
          18 * n + 18 * (i + (c :: cs).length) + 81 := by
        simp only [List.length_cons]
        omega
      rw [hsame] at ht
      rw [loopTime]
      calc
        _ ≤ (18 * n + 18 * (i + (c :: cs).length) + 81) +
            (cs.length * (18 * n + 18 * (i + (c :: cs).length) + 81) + 1) :=
          Nat.add_le_add hbound ht
        _ = _ := by rw [List.length_cons]; ring

theorem input_header_bound (F : Formula) :
    F.variables + F.clauses.length + 2 ≤ (formulaBits F).length := by
  simp only [formulaBits, formulaWords, encodeWords_append, List.length_append,
    encodeWords, encodeWord_length, List.length_nil]
  omega

theorem graph_size_bound (F : Formula) :
    (RawInitialTables.table F).vertices + (RawInitialTables.table F).darts ≤
      7 * (formulaBits F).length := by
  rw [RawInitialTables.initial_size]
  have h := input_header_bound F
  omega

def fullBudget (F : Formula) : Nat :=
  6 * F.variables + 10 * F.clauses.length + 30 + loopTime 0 F.clauses +
    (GraphTables.tableBits (RawInitialTables.table F)).length

theorem timePolynomial_eval (N : Nat) :
    timePolynomial.eval N = 100 * N ^ 2 + 60000 * N + 100 := by
  simp [timePolynomial]

theorem fullBudget_le (F : Formula) :
    fullBudget F ≤ timePolynomial.eval (formulaBits F).length := by
  have hinput := input_header_bound F
  have hloop := loopTime_le 0 F.clauses
  have hout := GraphTableComplexity.bits_le_of_size_le (RawInitialTables.table F)
    (graph_size_bound F)
  rw [GraphTableComplexity.encodingPolynomial_eval] at hout
  simp only [Nat.zero_add] at hloop
  have hm : F.clauses.length ≤ (formulaBits F).length := by omega
  have hcoefficient : 18 * F.variables + 18 * F.clauses.length + 81 ≤
      18 * (formulaBits F).length + 81 := by omega
  have hproduct := Nat.mul_le_mul hm hcoefficient
  rw [timePolynomial_eval]
  unfold fullBudget
  nlinarith

end UniqueGamesTheorem.Foundations.PCP.RawInitialMachineBudget

/-! Explicit finite predicates and numeric row words of the initial incidence table.
Every relation retains all 4096 entries, including repetitions. -/

namespace UniqueGamesTheorem.Foundations.PCP.RawInitialRows

open Target GraphTables RawInitialTables

def clauseSigns {n : Nat} (clause : Clause n) : Signs :=
  (clause[0].positive, clause[1].positive, clause[2].positive)

def clauseNames {n : Nat} (clause : Clause n) : Names :=
  (clause[0].variableIndex.val, clause[1].variableIndex.val, clause[2].variableIndex.val)

def nameWord (names : Names) : Slot → Nat
  | .first => names.1
  | .second => names.2.1
  | .third => names.2.2

def incidencePredicate (signs : Signs) (slot : Slot)
    (clauseLabel variableLabel : InitialGraph.Label) : Bool :=
  InitialGraph.variableValid variableLabel &&
    (((literalValue signs.1 clauseLabel.1 ||
      literalValue signs.2.1 clauseLabel.2.1) ||
      literalValue signs.2.2 clauseLabel.2.2) &&
      decide (answerAt (InitialGraph.toClauseAnswer clauseLabel) slot = variableLabel.1))

def relationPredicate (signs : Signs) (slot : Slot) :
    Bool → GraphTables.Label → GraphTables.Label → Bool
  | false, a, b => incidencePredicate signs slot (decodedLabel a) (decodedLabel b)
  | true, a, b => incidencePredicate signs slot (decodedLabel b) (decodedLabel a)

def relationWordsFor (signs : Signs) (slot : Slot) (orientation : Bool) : List Nat :=
  relationWords (relationOf (relationPredicate signs slot orientation))

@[simp] theorem relationWordsFor_length (signs : Signs) (slot : Slot) (orientation : Bool) :
    (relationWordsFor signs slot orientation).length = 4096 := by
  exact relationWords_length _

def incidenceWords (n i : Nat) (names : Names) (signs : Signs)
    (slot : Slot) (orientation : Bool) : List Nat :=
  [if orientation then nameWord names slot else n + i,
    6 * i + 2 * (slotOrder slot).val + (if orientation then 0 else 1)] ++
      relationWordsFor signs slot orientation

def clauseWords (n i : Nat) (names : Names) (signs : Signs) : List Nat :=
  incidenceWords n i names signs .first false ++
  incidenceWords n i names signs .first true ++
  incidenceWords n i names signs .second false ++
  incidenceWords n i names signs .second true ++
  incidenceWords n i names signs .third false ++
  incidenceWords n i names signs .third true

/-! Exact ordered rows of the initial incidence table. Every relation retains
all 4096 entries, including repetitions; this is a list identity, not a runtime bound. -/

theorem orderedList_prod {α β : Type*} {m n : Nat}
    (e : α ≃ Fin m) (f : β ≃ Fin n) :
    orderedList ((e.prodCongr f).trans finProdFinEquiv) =
      (orderedList e).flatMap (fun a => (orderedList f).map (fun b => (a, b))) := by
  change List.ofFn (fun q : Fin (m * n) =>
    (e.symm (finProdFinEquiv.symm q).1, f.symm (finProdFinEquiv.symm q).2)) = _
  rw [List.ofFn_mul]
  simp only [orderedList, List.flatMap_def, List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  have h : (⟨i.val * n + j.val, by
      calc
        i.val * n + j.val < (i.val + 1) * n :=
          (Nat.add_lt_add_left j.isLt _).trans_eq (by rw [Nat.add_mul, Nat.one_mul])
        _ ≤ m * n := Nat.mul_le_mul_right _ i.isLt⟩ : Fin (m * n)) =
      finProdFinEquiv (i, j) := by
    apply Fin.ext
    simp [finProdFinEquiv, Nat.add_comm, Nat.mul_comm]
  rw [h, Equiv.symm_apply_apply]
  rfl

theorem orderedList_sum {α β : Type*} {m n : Nat}
    (e : α ≃ Fin m) (f : β ≃ Fin n) :
    orderedList ((e.sumCongr f).trans finSumFinEquiv) =
      (orderedList e).map Sum.inl ++ (orderedList f).map Sum.inr := by
  change List.ofFn (fun q : Fin (m + n) =>
    (e.sumCongr f).symm (finSumFinEquiv.symm q)) = _
  rw [List.ofFn_add]
  change (List.ofFn (fun i : Fin m =>
    (e.sumCongr f).symm (finSumFinEquiv.symm (i.castAdd n)))) ++
    (List.ofFn (fun i : Fin n =>
      (e.sumCongr f).symm (finSumFinEquiv.symm (i.natAdd m)))) = _
  simp [orderedList, List.map_ofFn]
  rfl

def clauseDarts (F : Formula) (i : Fin F.clauses.length) : List (InitialGraph.Dart F) :=
  [.inl ((i, .first), false), .inl ((i, .first), true),
   .inl ((i, .second), false), .inl ((i, .second), true),
   .inl ((i, .third), false), .inl ((i, .third), true)]

theorem orderedList_dartOrder (F : Formula) :
    orderedList (dartOrder F) =
      (List.finRange F.clauses.length).flatMap (clauseDarts F) ++ [.inr ()] := by
  rw [dartOrder, orderedList_cast, orderedList_sum, orderedList_prod]
  rw [eventOrder, orderedList_prod]
  have hs : orderedList slotOrder = [.first, .second, .third] := rfl
  have hb : orderedList finTwoEquiv.symm = [false, true] := rfl
  have hu : orderedList unitOrder = [()] := rfl
  rw [hs, hb, hu]
  simp [orderedList, List.finRange, List.flatMap_assoc, List.map_flatMap,
    ]
  rfl

def rowFor (F : Formula) (d : InitialGraph.Dart F) :
    DartRow (F.variables + F.clauses.length + 1) (6 * F.clauses.length + 1) where
  tail := vertexOrder F (InitialGraph.tail F d)
  reverseIndex := dartOrder F (InitialGraph.reverse F d)
  relation := relationOf (fun a b => InitialGraph.predicate F d (decodedLabel a) (decodedLabel b))

theorem rowList_table (F : Formula) :
    rowList (table F) = (orderedList (dartOrder F)).map (rowFor F) := by
  simp only [rowList, table, ofEnumeratedGraph, ofGraph, graphRows, Vector.toList_ofFn,
    orderedList, List.map_ofFn]
  rfl

theorem rowWords_incidence (F : Formula) (i : Fin F.clauses.length)
    (slot : Slot) (orientation : Bool) :
    rowWords (rowFor F (.inl ((i, slot), orientation))) =
      incidenceWords F.variables i.val (clauseNames (clauseAt F i))
        (clauseSigns (clauseAt F i)) slot orientation := by
  have ht : (rowFor F (.inl ((i, slot), orientation))).tail.val =
      if orientation then nameWord (clauseNames (clauseAt F i)) slot else F.variables + i.val := by
    cases orientation <;> cases slot <;> rfl
  have hr : (rowFor F (.inl ((i, slot), orientation))).reverseIndex.val =
      6 * i.val + 2 * (slotOrder slot).val + (if orientation then 0 else 1) := by
    cases orientation <;> cases slot <;>
      simp [rowFor, InitialGraph.reverse, dartOrder, eventOrder, slotOrder, unitOrder,
        finProdFinEquiv, finSumFinEquiv, finTwoEquiv, Nat.mul_add,
        Nat.mul_comm, Nat.mul_left_comm, Nat.add_comm]
  have hp : (rowFor F (.inl ((i, slot), orientation))).relation =
      relationOf (relationPredicate (clauseSigns (clauseAt F i)) slot orientation) := by
    cases orientation <;> rfl
  unfold rowWords incidenceWords relationWordsFor
  rw [ht, hr, hp]

theorem rowWords_dummy (F : Formula) :
    rowWords (rowFor F (.inr ())) = dummyWords F.variables F.clauses.length := by
  have ht : (rowFor F (.inr ())).tail.val = F.variables + F.clauses.length := rfl
  have hr : (rowFor F (.inr ())).reverseIndex.val = 6 * F.clauses.length := by
    simp [rowFor, InitialGraph.reverse, dartOrder, unitOrder, finSumFinEquiv]
  have hp : (rowFor F (.inr ())).relation = relationOf (fun _ _ => true) := rfl
  have hw : relationWords (relationOf (fun _ _ => true)) = List.replicate 4096 1 := by
    unfold relationWords
    rw [relationOf, Vector.toList_ofFn, List.map_ofFn]
    exact List.ofFn_const 4096 1
  unfold rowWords dummyWords
  rw [ht, hr, hp, hw]

theorem clauseDarts_rowWords (F : Formula) (i : Fin F.clauses.length) :
    (clauseDarts F i).flatMap (fun d => rowWords (rowFor F d)) =
      clauseWords F.variables i.val (clauseNames (clauseAt F i))
        (clauseSigns (clauseAt F i)) := by
  simp [clauseDarts, rowWords_incidence, clauseWords, List.append_assoc]

/-- Exact headers and exact clause/slot/orientation order of every emitted word. -/
theorem tableWords_eq (F : Formula) :
    tableWords (table F) =
      [F.variables + F.clauses.length + 1, 6 * F.clauses.length + 1] ++
      (List.finRange F.clauses.length).flatMap (fun i =>
        clauseWords F.variables i.val (clauseNames (clauseAt F i))
          (clauseSigns (clauseAt F i))) ++ dummyWords F.variables F.clauses.length := by
  rw [tableWords, rowList_table, orderedList_dartOrder]
  simp [List.flatMap_map, List.flatMap_append, List.flatMap_assoc, clauseDarts_rowWords,
    rowWords_dummy]

end UniqueGamesTheorem.Foundations.PCP.RawInitialRows

/-! The concrete numbered amplification round, with one fixed base expander.
Every intermediate is an actual stored table, with explicit finite coordinates.
The running-time certificate is a separate theorem about these same functions. -/

namespace UniqueGamesTheorem.Foundations.PCP.RoundTables

def initial (F : Target.Formula) : Input :=
  ⟨RawInitialTables.table F, RawInitialTables.table_darts_positive F⟩

end UniqueGamesTheorem.Foundations.PCP.RoundTables

/-! Gap amplification for the actual numbered table round. The fixed base
expander is the only supplied construction datum with a spectral certificate. -/

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_PreprocessingRegularLoopWordsLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Bounds on the actual output prefixes used by the regularization loops.
The bounds include the stored headers and all earlier original/owner blocks.
They concern actual serialized words; machine executions are proved separately. -/
namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularBounds

open PreprocessingRegularTables PreprocessingRegularWords PreprocessingRegularLoopWords
open UniqueGamesTheorem.Foundations.Complexity
open scoped BigOperators

def header (t : GraphTables.Table) (p : Fin t.vertices → Nat) (q : Nat) : List Bool :=
  encodeWords [vertexCount t p, vertexCount t p * (q + 1)]

def ownerBits (t : GraphTables.Table) (p : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table (PreprocessingCloudIndex.cloudSize t v + p v) q)
    (v : Fin t.vertices) : List Bool :=
  (List.ofFn (dummyVertexBits t p tables v)).flatten

def originalPrefix (t : GraphTables.Table) (p : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table (PreprocessingCloudIndex.cloudSize t v + p v) q)
    (k : Nat) : List Bool :=
  header t p q ++ blocksPrefix (originalVertexBits t p tables) k

def ownerPrefix (t : GraphTables.Table) (p : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table (PreprocessingCloudIndex.cloudSize t v + p v) q)
    (k : Nat) : List Bool :=
  header t p q ++ (List.ofFn (originalVertexBits t p tables)).flatten ++
    blocksPrefix (ownerBits t p tables) k

def dummyPrefix (t : GraphTables.Table) (p : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table (PreprocessingCloudIndex.cloudSize t v + p v) q)
    (v : Fin t.vertices) (k : Nat) : List Bool :=
  ownerPrefix t p tables v.val ++ blocksPrefix (dummyVertexBits t p tables v) k

variable (t : GraphTables.Table) (p : Fin t.vertices → Nat) {q : Nat}
variable (tables : ∀ v, ExpanderTables.Table (PreprocessingCloudIndex.cloudSize t v + p v) q)

theorem originalPrefix_length_le (k : Nat) :
    (originalPrefix t p tables k).length ≤
      (PortTables.tableBits (ofCloudTables t p tables)).length := by
  have h := blocksPrefix_length_le (originalVertexBits t p tables) k
  rw [tableBits_ofCloudTables]
  simp only [originalPrefix, header, List.length_append]
  omega

theorem ownerPrefix_length_le (k : Nat) :
    (ownerPrefix t p tables k).length ≤
      (PortTables.tableBits (ofCloudTables t p tables)).length := by
  have h := blocksPrefix_length_le (ownerBits t p tables) k
  have he : ownerBits t p tables =
      (fun v => (List.ofFn (dummyVertexBits t p tables v)).flatten) := rfl
  rw [tableBits_ofCloudTables]
  simp only [ownerPrefix, header, List.length_append] at *
  simp only [he] at *
  omega

theorem dummyPrefix_length_le (v : Fin t.vertices) (k : Nat) :
    (dummyPrefix t p tables v k).length ≤
      (PortTables.tableBits (ofCloudTables t p tables)).length := by
  have hi := blocksPrefix_length_le (dummyVertexBits t p tables v) k
  have ho := blocksPrefix_length_le (ownerBits t p tables) (v.val + 1)
  rw [blocksPrefix_succ _ _ v.isLt] at ho
  have he : ownerBits t p tables =
      (fun v => (List.ofFn (dummyVertexBits t p tables v)).flatten) := rfl
  simp only [Fin.eta] at ho
  rw [tableBits_ofCloudTables]
  simp only [dummyPrefix, ownerPrefix, header, ownerBits, List.length_append] at *
  simp only [he] at *
  omega

theorem regular_originalPrefix_le (H : BaseTable) (k : Nat) :
    (originalPrefix t (padding t) (familyCloudTable H t) k).length ≤
      PreprocessingMachineBounds.regularPolynomial.eval
        (PreprocessingMachineBounds.inputLength t) :=
  (originalPrefix_length_le t (padding t) (familyCloudTable H t) k).trans
    (PreprocessingMachineBounds.regularBits_le H t)

theorem regular_ownerPrefix_le (H : BaseTable) (k : Nat) :
    (ownerPrefix t (padding t) (familyCloudTable H t) k).length ≤
      PreprocessingMachineBounds.regularPolynomial.eval
        (PreprocessingMachineBounds.inputLength t) :=
  (ownerPrefix_length_le t (padding t) (familyCloudTable H t) k).trans
    (PreprocessingMachineBounds.regularBits_le H t)

theorem regular_dummyPrefix_le (H : BaseTable) (v : Fin t.vertices) (k : Nat) :
    (dummyPrefix t (padding t) (familyCloudTable H t) v k).length ≤
      PreprocessingMachineBounds.regularPolynomial.eval
        (PreprocessingMachineBounds.inputLength t) :=
  (dummyPrefix_length_le t (padding t) (familyCloudTable H t) v k).trans
    (PreprocessingMachineBounds.regularBits_le H t)

end UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularBounds

end

section

namespace UniqueGamesTheorem.Foundations.PCP.RawInitialMachineModel

open Turing Complexity Hastad

def relationOutput (slot : Fin 3) (orientation : Bool) (state : State) : List Bool :=
  (encodeWords (RawInitialRows.relationWordsFor state.1
    (RawInitialTables.slotOrder.symm slot) orientation)).reverse

def program : Label → TM2.Stmt Alphabet Label State
  | .headerStart slot => SourceMachine.fieldStart (headerTape slot) (.headerLoop slot)
  | .headerLoop slot => SourceMachine.fieldLoop .input (headerTape slot) (.headerLoop slot)
      (if slot.val = 0 then some (.headerStart 1) else some .scanN)
  | .scanN => MachineInitialHeaders.prefixScan .variables .scratch .reversed 1 .scanN .restoreN
  | .restoreN => Reduction.MachineTransfer.loopAt .scratch .variables id false .restoreN (some .scanM1)
  | .scanM1 => MachineInitialHeaders.prefixScan .counter .scratch .reversed 1 .scanM1 .restoreM1
  | .restoreM1 => Reduction.MachineTransfer.loopAt .scratch .counter id false .restoreM1 (some .closeFirst)
  | .closeFirst => Reduction.MachineSubstitution.pushWord .reversed [true, false]
      (.goto fun _ => .scanM6)
  | .scanM6 => MachineInitialHeaders.prefixScan .counter .scratch .reversed 6 .scanM6 .restoreM6
  | .restoreM6 => Reduction.MachineTransfer.loopAt .scratch .counter id false .restoreM6 (some .closeSecond)
  | .closeSecond => Reduction.MachineSubstitution.pushWord .reversed [true, false]
      (.goto fun _ => .initializeIndex)
  | .initializeIndex => .push .index (fun _ => false) (.goto fun _ => .guard)
  | .guard => MachineUnaryCounter.guard .counter (.fieldStart 0) (.scan .dummyVariables)
  | .fieldStart slot => SourceMachine.fieldStart (.field slot) (.fieldLoop slot)
  | .fieldLoop slot => SourceMachine.fieldLoop .input (.field slot) (.fieldLoop slot)
      (if h : slot.val + 1 < 6 then some (.fieldStart ⟨slot.val + 1, h⟩)
        else some .loadSigns)
  | .loadSigns =>
      .peek (.field 1) (fun state head => ((head.getD false, state.1.2), state.2))
        (.peek (.field 3) (fun state head => ((state.1.1, head.getD false, state.1.2.2), state.2))
          (.peek (.field 5) (fun state head => ((state.1.1, state.1.2.1, head.getD false), state.2))
            (.load (fun state => (state.1, none)) (.goto fun _ => .scan (.tailVariables 0)))))
  | .scan phase => MachineInitialHeaders.prefixScan (copySource phase) .scratch .reversed
      (copyScale phase) (.scan phase) (.restore phase)
  | .restore phase => Reduction.MachineTransfer.loopAt .scratch (copySource phase) id false
      (.restore phase) (some (copyNext phase))
  | .closeTail slot orientation => .push .reversed (fun _ => false)
      (.goto fun _ => .scan (.reverseIndex slot orientation))
  | .closeReverse slot orientation => Reduction.MachineSubstitution.pushWord .reversed
      (encodeWord (2 * slot.val + if orientation then 0 else 1))
        (.goto fun _ => .relation slot orientation)
  | .relation slot orientation => MachineFiniteTable.emit .reversed
      (relationOutput slot orientation)
      stateKeys (.goto fun _ => relationNext slot orientation)
  | .cleanupField slot => drain (.field slot) (.cleanupField slot)
      (if h : slot.val + 1 < 6 then .cleanupField ⟨slot.val + 1, h⟩ else .incrementIndex)
  | .incrementIndex => .push .index (fun _ => true) (.goto fun _ => .guard)
  | .closeDummyTail => .push .reversed (fun _ => false) (.goto fun _ => .scan .dummyReverse)
  | .closeDummyReverse => .push .reversed (fun _ => false) (.goto fun _ => .dummyRelation)
  | .dummyRelation => Reduction.MachineSubstitution.pushWord .reversed
      (encodeWords (GraphTables.relationWords (GraphTables.relationOf (fun _ _ => true))))
        (.goto fun _ => .cleanupFinal 0)
  | .cleanupFinal slot => drain (finalTape slot) (.cleanupFinal slot)
      (if h : slot.val + 1 < 3 then .cleanupFinal ⟨slot.val + 1, h⟩ else .reset)
  | .reset => .load (fun _ => initialState) (.goto fun _ => .finalReverse)
  | .finalReverse => Reduction.MachineTransfer.loopAt .reversed .output id false .finalReverse none

def machine : FinTM2 where
  K := Tape
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .headerStart 0
  σ := State
  initialState := initialState
  m := program

end UniqueGamesTheorem.Foundations.PCP.RawInitialMachineModel

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_RawInitialMachinePhases
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual execution of the raw initial graph program's reusable phases. -/

namespace UniqueGamesTheorem.Foundations.PCP.RawInitialMachinePhases

open Turing Complexity RawInitialMachineModel

def copyInTime (phase : CopyPhase) (base : Tape → List Bool)
    (n : Nat) (suffix : List Bool)
    (hsource : base (copySource phase) = encodeWord n ++ suffix)
    (hscratch : base .scratch = []) (state : State) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.scan phase), state, base⟩
      (some ⟨some (copyNext phase), (state.1, none),
        Function.update base .reversed
          (List.replicate (copyScale phase * n) true ++ base .reversed)⟩)
      (2 * n + 2) :=
  MachineInitialHeaders.prefixInTime (copySource phase) Tape.scratch Tape.reversed
    (copySource_ne_scratch phase) (copySource_ne_reversed phase) (by decide)
    (copyScale phase) (.scan phase) (.restore phase) (some (copyNext phase))
    program rfl rfl base n suffix hsource hscratch state.1 state.2

def relationInTime (slot : Fin 3) (orientation : Bool)
    (base : Tape → List Bool) (state : State) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.relation slot orientation), state, base⟩
      (some ⟨some (relationNext slot orientation), state,
        Function.update base .reversed
          (relationOutput slot orientation state ++ base .reversed)⟩) 1 :=
  MachineFiniteTable.emitInTime (K := Tape) (Λ := Label) (σ := State) (Γ := Alphabet)
    Tape.reversed
    (relationOutput slot orientation)
    stateKeys stateKeys_complete program (.relation slot orientation)
    (relationNext slot orientation) rfl state base

theorem loadSigns_step (base : Tape → List Bool) (a b c : Bool)
    (ha : base (.field 1) = encodeWord (if a then 1 else 0))
    (hb : base (.field 3) = encodeWord (if b then 1 else 0))
    (hc : base (.field 5) = encodeWord (if c then 1 else 0)) (state : State) :
    (TM2.step program) ⟨some .loadSigns, state, base⟩ =
      some ⟨some (.scan (.tailVariables 0)), ((a, b, c), none), base⟩ := by
  change some (TM2.stepAux (program .loadSigns) state base) = _
  simp only [program, TM2.stepAux, ha, hb, hc, bitWord_head, Option.getD_some]

def cleanupFieldInTime (slot : Fin 6) (base : Tape → List Bool) (state : State) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.cleanupField slot), state, base⟩
      (some ⟨some (if h : slot.val + 1 < 6 then .cleanupField ⟨slot.val + 1, h⟩
        else .incrementIndex), (state.1, none), Function.update base (.field slot) []⟩)
      ((base (.field slot)).length + 1) :=
  MachineDrain.drainInTime (.field slot) (.cleanupField slot) _ program rfl base state.1 state.2

def cleanupFinalInTime (slot : Fin 3) (base : Tape → List Bool) (state : State) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.cleanupFinal slot), state, base⟩
      (some ⟨some (if h : slot.val + 1 < 3 then .cleanupFinal ⟨slot.val + 1, h⟩
        else .reset), (state.1, none), Function.update base (finalTape slot) []⟩)
      ((base (finalTape slot)).length + 1) :=
  MachineDrain.drainInTime (finalTape slot) (.cleanupFinal slot) _ program rfl base state.1 state.2

end UniqueGamesTheorem.Foundations.PCP.RawInitialMachinePhases

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_RawInitialMachineReadClause
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Read exactly one concrete six-field CNF clause in the actual global machine,
then execute its real sign-loading instruction. No extra finish transition
is inserted. Every unrelated tape and the unread input suffix are preserved.
-/

namespace UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause

open Turing Complexity Hastad RawInitialMachineModel

/-- Six actual field routines, stopping directly at the global sign loader. -/
theorem fieldsTrace {n : ℕ} (base : Tape → List Bool) (c : Target.Clause n)
    (suffix : List Bool)
    (hinput : base .input = encodeWords (Complexity.clauseWords c) ++ suffix)
    (hempty : ∀ j, base (.field j) = []) (state : State) :
    (MachineComposition.advance (TM2.step program))^[
        (encodeWords (Complexity.clauseWords c)).length + 6]
      (some ⟨some (.fieldStart 0), state, base⟩) =
      some ⟨some .loadSigns, (state.1, none), recordTapes base c suffix⟩ := by
  let a := fieldValue c 0
  let b := fieldValue c 1
  let d := fieldValue c 2
  let e := fieldValue c 3
  let f := fieldValue c 4
  let g := fieldValue c 5
  have hwords : Complexity.clauseWords c = [a, b, d, e, f, g] := rfl
  have hin : base .input = encodeWord a ++ (encodeWords [b, d, e, f, g] ++ suffix) := by
    rw [hinput, hwords]
    simp only [encodeWords, List.append_assoc]
  let t1 := SourceMachine.afterField .input (.field 0) base a
    (encodeWords [b, d, e, f, g] ++ suffix)
  let t2 := SourceMachine.afterField .input (.field 1) t1 b
    (encodeWords [d, e, f, g] ++ suffix)
  let t3 := SourceMachine.afterField .input (.field 2) t2 d
    (encodeWords [e, f, g] ++ suffix)
  let t4 := SourceMachine.afterField .input (.field 3) t3 e
    (encodeWords [f, g] ++ suffix)
  let t5 := SourceMachine.afterField .input (.field 4) t4 f
    (encodeWords [g] ++ suffix)
  let t6 := SourceMachine.afterField .input (.field 5) t5 g suffix
  have h1 := (SourceMachine.fieldInTime .input (.field 0) (by decide)
    (.fieldStart 0) (.fieldLoop 0) (some (.fieldStart 1)) program rfl rfl
    base a (encodeWords [b, d, e, f, g] ++ suffix) hin state.1 state.2).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[a + 2]
    (some ⟨some (.fieldStart 0), state, base⟩) =
    some ⟨some (.fieldStart 1), (state.1, none), t1⟩ at h1
  have h2 := (SourceMachine.fieldInTime .input (.field 1) (by decide)
    (.fieldStart 1) (.fieldLoop 1) (some (.fieldStart 2)) program rfl rfl
    t1 b (encodeWords [d, e, f, g] ++ suffix)
    (by simp [t1, SourceMachine.afterField, encodeWords, List.append_assoc])
    state.1 none).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[b + 2]
    (some ⟨some (.fieldStart 1), (state.1, none), t1⟩) =
    some ⟨some (.fieldStart 2), (state.1, none), t2⟩ at h2
  have h3 := (SourceMachine.fieldInTime .input (.field 2) (by decide)
    (.fieldStart 2) (.fieldLoop 2) (some (.fieldStart 3)) program rfl rfl
    t2 d (encodeWords [e, f, g] ++ suffix)
    (by simp [t2, SourceMachine.afterField, encodeWords, List.append_assoc])
    state.1 none).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[d + 2]
    (some ⟨some (.fieldStart 2), (state.1, none), t2⟩) =
    some ⟨some (.fieldStart 3), (state.1, none), t3⟩ at h3
  have h4 := (SourceMachine.fieldInTime .input (.field 3) (by decide)
    (.fieldStart 3) (.fieldLoop 3) (some (.fieldStart 4)) program rfl rfl
    t3 e (encodeWords [f, g] ++ suffix)
    (by simp [t3, SourceMachine.afterField, encodeWords, List.append_assoc])
    state.1 none).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[e + 2]
    (some ⟨some (.fieldStart 3), (state.1, none), t3⟩) =
    some ⟨some (.fieldStart 4), (state.1, none), t4⟩ at h4
  have h5 := (SourceMachine.fieldInTime .input (.field 4) (by decide)
    (.fieldStart 4) (.fieldLoop 4) (some (.fieldStart 5)) program rfl rfl
    t4 f (encodeWords [g] ++ suffix)
    (by simp [t4, SourceMachine.afterField, encodeWords, List.append_assoc])
    state.1 none).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[f + 2]
    (some ⟨some (.fieldStart 4), (state.1, none), t4⟩) =
    some ⟨some (.fieldStart 5), (state.1, none), t5⟩ at h5
  have h6 := (SourceMachine.fieldInTime .input (.field 5) (by decide)
    (.fieldStart 5) (.fieldLoop 5) (some .loadSigns) program rfl rfl
    t5 g suffix
    (by simp [t5, SourceMachine.afterField, encodeWords])
    state.1 none).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[g + 2]
    (some ⟨some (.fieldStart 5), (state.1, none), t5⟩) =
    some ⟨some .loadSigns, (state.1, none), t6⟩ at h6
  have total := trace_trans _ (trace_trans _ (trace_trans _
    (trace_trans _ (trace_trans _ h1 h2) h3) h4) h5) h6
  have htime : (((((a + 2) + (b + 2)) + (d + 2)) + (e + 2)) + (f + 2)) + (g + 2) =
      (encodeWords (Complexity.clauseWords c)).length + 6 := by
    rw [hwords, encodeWords_length]
    simp
    omega
  rw [htime] at total
  have frame : t6 = recordTapes base c suffix := by
    funext k
    cases k with
    | field j =>
      fin_cases j <;>
        simp [t6, t5, t4, t3, t2, t1, SourceMachine.afterField, SourceMachine.fieldTapes,
          recordTapes, hempty, a, b, d, e, f, g]
    | _ =>
      simp [t6, t5, t4, t3, t2, t1, SourceMachine.afterField, SourceMachine.fieldTapes,
        recordTapes]
  rw [frame] at total
  exact total

theorem readClauseTrace {n : ℕ} (base : Tape → List Bool) (c : Target.Clause n)
    (suffix : List Bool)
    (hinput : base .input = encodeWords (Complexity.clauseWords c) ++ suffix)
    (hempty : ∀ j, base (.field j) = []) (state : State) :
    (MachineComposition.advance (TM2.step program))^[
        (encodeWords (Complexity.clauseWords c)).length + 7]
      (some ⟨some (.fieldStart 0), state, base⟩) =
      some ⟨some (.scan (.tailVariables 0)), (RawInitialRows.clauseSigns c, none),
        recordTapes base c suffix⟩ := by
  have first := fieldsTrace base c suffix hinput hempty state
  have last := RawInitialMachinePhases.loadSigns_step (recordTapes base c suffix)
    (c)[0].positive (c)[1].positive (c)[2].positive rfl rfl rfl (state.1, none)
  have lastTrace : (MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some .loadSigns, (state.1, none), recordTapes base c suffix⟩) =
      some ⟨some (.scan (.tailVariables 0)), (RawInitialRows.clauseSigns c, none),
        recordTapes base c suffix⟩ := last
  have total := trace_trans _ first lastTrace
  simpa only [show (encodeWords (Complexity.clauseWords c)).length + 6 + 1 =
    (encodeWords (Complexity.clauseWords c)).length + 7 by omega] using total

end UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_RawInitialMachineCleanup
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-!
Actual cleanup of all six clause-field tapes followed by the global unary
index increment. The output accumulator, unread input, and other caller tapes
are preserved, and no additional finish instruction is assumed.
-/

namespace UniqueGamesTheorem.Foundations.PCP.RawInitialMachineCleanup

open Turing Complexity RawInitialMachineModel RawInitialMachineReadClause

/-- The index increment is exactly the one push in the actual global program. -/
theorem incrementIndexTrace (base : Tape → List Bool) (state : State) :
    (MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some .incrementIndex, state, base⟩) =
      some ⟨some .guard, state, Function.update base .index (true :: base .index)⟩ := by
  rfl

/-- Clear six actual field tapes, increment the index, and return to the guard. -/
theorem cleanupTrace {n : ℕ} (base : Tape → List Bool) (c : Target.Clause n)
    (suffix : List Bool) (i : ℕ)
    (hempty : ∀ j, base (.field j) = []) (hindex : base .index = encodeWord i)
    (incoming : State) :
    (MachineComposition.advance (TM2.step program))^[
        (encodeWords (Complexity.clauseWords c)).length + 7]
      (some ⟨some (.cleanupField 0), incoming, recordTapes base c suffix⟩) =
      some ⟨some .guard, (incoming.1, none),
        Function.update (Function.update base .input suffix) .index (encodeWord (i + 1))⟩ := by
  let r := recordTapes base c suffix
  let t1 := Function.update r (.field 0) []
  let t2 := Function.update t1 (.field 1) []
  let t3 := Function.update t2 (.field 2) []
  let t4 := Function.update t3 (.field 3) []
  let t5 := Function.update t4 (.field 4) []
  let t6 := Function.update t5 (.field 5) []
  have h1 := (RawInitialMachinePhases.cleanupFieldInTime 0 r incoming).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[
      (encodeWord (fieldValue c 0)).length + 1]
    (some ⟨some (.cleanupField 0), incoming, r⟩) =
    some ⟨some (.cleanupField 1), (incoming.1, none), t1⟩ at h1
  have h2 := (RawInitialMachinePhases.cleanupFieldInTime 1 t1 (incoming.1, none)).evals_in_steps
  have hf2 : t1 (.field 1) = encodeWord (fieldValue c 1) := by
    simp [t1, r]
  change (MachineComposition.advance (TM2.step program))^[(t1 (.field 1)).length + 1]
    (some ⟨some (.cleanupField 1), (incoming.1, none), t1⟩) =
    some ⟨some (.cleanupField 2), (incoming.1, none), t2⟩ at h2
  rw [hf2] at h2
  have h3 := (RawInitialMachinePhases.cleanupFieldInTime 2 t2 (incoming.1, none)).evals_in_steps
  have hf3 : t2 (.field 2) = encodeWord (fieldValue c 2) := by
    simp [t2, t1, r]
  change (MachineComposition.advance (TM2.step program))^[(t2 (.field 2)).length + 1]
    (some ⟨some (.cleanupField 2), (incoming.1, none), t2⟩) =
    some ⟨some (.cleanupField 3), (incoming.1, none), t3⟩ at h3
  rw [hf3] at h3
  have h4 := (RawInitialMachinePhases.cleanupFieldInTime 3 t3 (incoming.1, none)).evals_in_steps
  have hf4 : t3 (.field 3) = encodeWord (fieldValue c 3) := by
    simp [t3, t2, t1, r]
  change (MachineComposition.advance (TM2.step program))^[(t3 (.field 3)).length + 1]
    (some ⟨some (.cleanupField 3), (incoming.1, none), t3⟩) =
    some ⟨some (.cleanupField 4), (incoming.1, none), t4⟩ at h4
  rw [hf4] at h4
  have h5 := (RawInitialMachinePhases.cleanupFieldInTime 4 t4 (incoming.1, none)).evals_in_steps
  have hf5 : t4 (.field 4) = encodeWord (fieldValue c 4) := by
    simp [t4, t3, t2, t1, r]
  change (MachineComposition.advance (TM2.step program))^[(t4 (.field 4)).length + 1]
    (some ⟨some (.cleanupField 4), (incoming.1, none), t4⟩) =
    some ⟨some (.cleanupField 5), (incoming.1, none), t5⟩ at h5
  rw [hf5] at h5
  have h6 := (RawInitialMachinePhases.cleanupFieldInTime 5 t5 (incoming.1, none)).evals_in_steps
  have hf6 : t5 (.field 5) = encodeWord (fieldValue c 5) := by
    simp [t5, t4, t3, t2, t1, r]
  change (MachineComposition.advance (TM2.step program))^[(t5 (.field 5)).length + 1]
    (some ⟨some (.cleanupField 5), (incoming.1, none), t5⟩) =
    some ⟨some .incrementIndex, (incoming.1, none), t6⟩ at h6
  rw [hf6] at h6
  have last := incrementIndexTrace t6 (incoming.1, none)
  have total := trace_trans _ (trace_trans _ (trace_trans _ (trace_trans _
    (trace_trans _ (trace_trans _ h1 h2) h3) h4) h5) h6) last
  have htime :
      ((((((encodeWord (fieldValue c 0)).length + 1 +
        ((encodeWord (fieldValue c 1)).length + 1)) +
        ((encodeWord (fieldValue c 2)).length + 1)) +
        ((encodeWord (fieldValue c 3)).length + 1)) +
        ((encodeWord (fieldValue c 4)).length + 1)) +
        ((encodeWord (fieldValue c 5)).length + 1)) + 1 =
      (encodeWords (Complexity.clauseWords c)).length + 7 := by
    simp [fieldValue, Complexity.clauseWords, Complexity.literalWords, encodeWords]
    omega
  rw [htime] at total
  have frame : Function.update t6 .index (true :: t6 .index) =
      Function.update (Function.update base .input suffix) .index (encodeWord (i + 1)) := by
    funext k
    cases k with
    | field j =>
      fin_cases j <;> simp [t6, t5, t4, t3, t2, t1, r, recordTapes, hempty]
    | index =>
      simp [t6, t5, t4, t3, t2, t1, r, recordTapes, hindex,
        encodeWord, List.replicate_succ]
    | _ => simp [t6, t5, t4, t3, t2, t1, r, recordTapes]
  rw [frame] at total
  exact total

end UniqueGamesTheorem.Foundations.PCP.RawInitialMachineCleanup

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_RawInitialMachineStart
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-!
Actual execution of the raw initial graph machine from its standard input
configuration to the first clause-loop guard. The unread clause bits are
preserved verbatim, and all tape contents at the boundary are explicit.
-/

namespace UniqueGamesTheorem.Foundations.PCP.RawInitialMachineStart

open Turing Complexity Hastad RawInitialMachineModel

theorem initList_eq (bits : List Bool) :
    initList machine bits =
      ⟨some (.headerStart 0), initialState, inputTapes bits⟩ := by
  unfold initList
  congr 1
  funext k
  change Tape at k
  cases k <;> rfl

/-- The two actual header-field readers reach the prepared counter boundary. -/
theorem readCountersTrace (n m : ℕ) (clauseBits : List Bool) :
    (MachineComposition.advance (TM2.step program))^[n + m + 4]
      (some (initList machine (encodeWords [n, m] ++ clauseBits))) =
      some ⟨some .scanN, initialState, counterTapes n m clauseBits⟩ := by
  let t0 := inputTapes (encodeWords [n, m] ++ clauseBits)
  have first := (SourceMachine.fieldInTime .input .variables (by decide)
    (.headerStart 0) (.headerLoop 0) (some (.headerStart 1)) program rfl rfl
    t0 n (encodeWord m ++ clauseBits)
    (by simp [t0, inputTapes, encodeWords, List.append_assoc])
    (false, false, false) none).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[n + 2]
    (some ⟨some (.headerStart 0), initialState, t0⟩) = _ at first
  have firstFrame : SourceMachine.fieldTapes .input .variables t0
      (encodeWord m ++ clauseBits) (encodeWord n ++ t0 .variables) =
      firstTapes n m clauseBits := by
    funext k
    cases k <;> simp [SourceMachine.fieldTapes, t0, inputTapes, firstTapes]
  rw [firstFrame] at first
  have second := (SourceMachine.fieldInTime .input .counter (by decide)
    (.headerStart 1) (.headerLoop 1) (some .scanN) program rfl rfl
    (firstTapes n m clauseBits) m clauseBits rfl (false, false, false) none).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[m + 2]
    (some ⟨some (.headerStart 1), initialState, firstTapes n m clauseBits⟩) = _ at second
  have secondFrame : SourceMachine.fieldTapes .input .counter (firstTapes n m clauseBits)
      clauseBits (encodeWord m ++ firstTapes n m clauseBits .counter) =
      counterTapes n m clauseBits := by
    funext k
    cases k <;> simp [SourceMachine.fieldTapes, firstTapes, counterTapes]
  rw [secondFrame] at second
  have total := trace_trans _ first second
  rw [show (n + 2) + (m + 2) = n + m + 4 by omega] at total
  simpa only [initList_eq, t0, initialState] using! total

/-- Instantiation of the checked arithmetic phase in the actual global program. -/
theorem headersTrace (n m : ℕ) (clauseBits : List Bool) :
    (MachineComposition.advance (TM2.step program))^[2 * n + 4 * m + 8]
      (some ⟨some .scanN, initialState, counterTapes n m clauseBits⟩) =
      some ⟨some .initializeIndex, initialState, headerTapes n m clauseBits⟩ := by
  have h := MachineInitialHeaders.headerTrace .variables .counter .scratch .reversed
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    .scanN .restoreN .scanM1 .restoreM1 .closeFirst .scanM6 .restoreM6 .closeSecond
    (some .initializeIndex) program rfl rfl rfl rfl rfl rfl rfl rfl
    (counterTapes n m clauseBits) n m [] []
    (by simp [counterTapes]) (by simp [counterTapes]) rfl
    (false, false, false) none
  have frame : Function.update (counterTapes n m clauseBits) .reversed
      ((encodeWords [n + m + 1, 6 * m + 1]).reverse ++
        counterTapes n m clauseBits .reversed) = headerTapes n m clauseBits := by
    funext k
    cases k <;> simp [counterTapes, headerTapes]
  rw [frame] at h
  exact h

theorem initializeIndexTrace (n m : ℕ) (clauseBits : List Bool) :
    (MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some .initializeIndex, initialState, headerTapes n m clauseBits⟩) =
      some ⟨some .guard, initialState, startTapes n m clauseBits⟩ := by
  simp only [Function.iterate_one, MachineComposition.advance_some]
  change some (TM2.stepAux (program .initializeIndex) initialState
    (headerTapes n m clauseBits)) = _
  simp only [program, TM2.stepAux]
  congr 2
  funext k
  cases k <;> simp [headerTapes, startTapes]

/-- Exact startup trace for arbitrary encoded clause-tail data. -/
theorem startTrace (n m : ℕ) (clauseBits : List Bool) :
    (MachineComposition.advance (TM2.step program))^[3 * n + 5 * m + 13]
      (some (initList machine (encodeWords [n, m] ++ clauseBits))) =
      some ⟨some .guard, initialState, startTapes n m clauseBits⟩ := by
  have total := trace_trans _
    (trace_trans _ (readCountersTrace n m clauseBits) (headersTrace n m clauseBits))
    (initializeIndexTrace n m clauseBits)
  simpa only [show (n + m + 4) + (2 * n + 4 * m + 8) + 1 =
    3 * n + 5 * m + 13 by omega] using total

/-- Startup from the actual serialized CNF, with its untouched clause tail. -/
theorem formulaStartTrace (F : Target.Formula) :
    (MachineComposition.advance (TM2.step program))^[
        3 * F.variables + 5 * F.clauses.length + 13]
      (some (initList machine (formulaBits F))) =
      some ⟨some .guard, initialState,
        startTapes F.variables F.clauses.length
          (encodeWords (F.clauses.flatMap clauseWords))⟩ := by
  simpa only [formulaBits, formulaWords, encodeWords_append] using
    startTrace F.variables F.clauses.length (encodeWords (F.clauses.flatMap clauseWords))

end UniqueGamesTheorem.Foundations.PCP.RawInitialMachineStart

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_RawInitialMachineLoopData
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! The exact input and output streams at successive clause-loop iterations.
These tape invariants use the actual word codecs and clause occurrence order. -/

namespace UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData

open Target Complexity RawInitialMachineModel

def clauseInput {n : Nat} (clauses : List (Clause n)) : List Bool :=
  encodeWords (clauses.flatMap Complexity.clauseWords)

@[simp] theorem clauseInput_nil (n : Nat) : clauseInput ([] : List (Clause n)) = [] := rfl

@[simp] theorem clauseInput_cons {n : Nat} (c : Clause n) (cs : List (Clause n)) :
    clauseInput (c :: cs) = encodeWords (Complexity.clauseWords c) ++ clauseInput cs := by
  simp only [clauseInput, List.flatMap_cons, encodeWords_append]

def clauseOutput (n i : Nat) (clauses : List (Clause n)) : List Nat :=
  (clauses.mapIdx fun offset c => RawInitialRows.clauseWords n (i + offset)
    (RawInitialRows.clauseNames c) (RawInitialRows.clauseSigns c)).flatten

theorem mapIdx_ofFn {α β : Type} (xs : List α) (f : Nat → α → β) :
    xs.mapIdx f = List.ofFn (fun i : Fin xs.length => f i.val (xs.get i)) := by
  induction xs generalizing f with
  | nil => simp
  | cons x xs ih => simp [ih]

@[simp] theorem clauseOutput_nil (n i : Nat) : clauseOutput n i [] = [] := rfl

@[simp] theorem clauseOutput_cons (n i : Nat) (c : Clause n) (cs : List (Clause n)) :
    clauseOutput n i (c :: cs) =
      RawInitialRows.clauseWords n i (RawInitialRows.clauseNames c)
        (RawInitialRows.clauseSigns c) ++ clauseOutput n (i + 1) cs := by
  simp only [clauseOutput, List.mapIdx_cons, Nat.add_zero, List.flatten_cons,
    Nat.add_comm, Nat.add_left_comm]

theorem clauseOutput_numbered (F : Formula) :
    clauseOutput F.variables 0 F.clauses =
      (List.finRange F.clauses.length).flatMap (fun i =>
        RawInitialRows.clauseWords F.variables i.val
          (RawInitialRows.clauseNames (clauseAt F i))
          (RawInitialRows.clauseSigns (clauseAt F i))) := by
  simp only [clauseOutput, mapIdx_ofFn, List.ofFn_eq_map,
    Nat.zero_add, clauseAt]
  rfl

theorem tableWords_decomposition (F : Formula) :
    GraphTables.tableWords (RawInitialTables.table F) =
      [F.variables + F.clauses.length + 1, 6 * F.clauses.length + 1] ++
        clauseOutput F.variables 0 F.clauses ++
          RawInitialRows.dummyWords F.variables F.clauses.length := by
  rw [RawInitialRows.tableWords_eq, clauseOutput_numbered]

theorem startTapes_eq (n m : Nat) (input : List Bool) :
    RawInitialMachineStart.startTapes n m input =
      loopTapes n 0 m input (encodeWords [n + m + 1, 6 * m + 1]).reverse := by
  funext tape
  cases tape <;> rfl

end UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_RawInitialMachineRows
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-! The six incidence rows are emitted by the actual finite program, with
their exact order, full relation lists, transition count, and tape frame. -/

namespace UniqueGamesTheorem.Foundations.PCP.RawInitialMachineRows

open Turing Complexity RawInitialMachineModel RawInitialMachinePhases


attribute [local irreducible] relationOutput RawInitialRows.relationWordsFor

abbrev advance := MachineComposition.advance (TM2.step program)

theorem copyTrace (phase : CopyPhase) (base : Tape → List Bool)
    (n : ℕ) (hsource : base (copySource phase) = encodeWord n)
    (hscratch : base .scratch = []) (signs : Signs) :
    advance^[2 * n + 2] (some ⟨some (.scan phase), (signs, none), base⟩) =
      some ⟨some (copyNext phase), (signs, none),
        outputTapes base (List.replicate (copyScale phase * n) true)⟩ :=
  (copyInTime phase base n [] (by simpa using hsource) hscratch (signs, none)).evals_in_steps

theorem closeTailTrace (slot : Fin 3) (orientation : Bool)
    (base : Tape → List Bool) (signs : Signs) :
    advance^[1] (some ⟨some (.closeTail slot orientation), (signs, none), base⟩) =
      some ⟨some (.scan (.reverseIndex slot orientation)), (signs, none),
        outputTapes base [false]⟩ := by
  change some (TM2.stepAux (program (.closeTail slot orientation)) (signs, none) base) = _
  rfl

theorem closeReverseTrace (slot : Fin 3) (orientation : Bool)
    (base : Tape → List Bool) (signs : Signs) :
    advance^[1] (some ⟨some (.closeReverse slot orientation), (signs, none), base⟩) =
      some ⟨some (.relation slot orientation), (signs, none),
        outputTapes base (encodeWord (2 * slot.val + if orientation then 0 else 1)).reverse⟩ :=
  MachineInitialHeaders.literalTrace .reversed
    (encodeWord (2 * slot.val + if orientation then 0 else 1))
    (.closeReverse slot orientation) (some (.relation slot orientation))
    program rfl base signs none

def rowEndBits (slot : Fin 3) (orientation : Bool) (i : ℕ) (signs : Signs) : List Bool :=
  relationOutput slot orientation (signs, none) ++
    (encodeWord (6 * i + 2 * slot.val + if orientation then 0 else 1)).reverse ++ [false]

theorem rowEndTrace (slot : Fin 3) (orientation : Bool) (base : Tape → List Bool)
    (i : ℕ) (hindex : base .index = encodeWord i) (hscratch : base .scratch = [])
    (signs : Signs) :
    advance^[2 * i + 5] (some ⟨some (.closeTail slot orientation), (signs, none), base⟩) =
      some ⟨some (relationNext slot orientation), (signs, none),
        outputTapes base (rowEndBits slot orientation i signs)⟩ := by
  let first := outputTapes base [false]
  let second := outputTapes first (List.replicate (6 * i) true)
  let third := outputTapes second
    (encodeWord (2 * slot.val + if orientation then 0 else 1)).reverse
  have h1 := closeTailTrace slot orientation base signs
  have h2 := copyTrace (.reverseIndex slot orientation) first i
    (by simpa [first, outputTapes, copySource] using hindex)
    (by simpa [first, outputTapes] using hscratch) signs
  change advance^[2 * i + 2]
    (some ⟨some (.scan (.reverseIndex slot orientation)), (signs, none), first⟩) =
    some ⟨some (.closeReverse slot orientation), (signs, none), second⟩ at h2
  have h3 := closeReverseTrace slot orientation second signs
  have h4 := (relationInTime slot orientation third (signs, none)).evals_in_steps
  change advance^[1] (some ⟨some (.relation slot orientation), (signs, none), third⟩) =
    some ⟨some (relationNext slot orientation), (signs, none),
      outputTapes third (relationOutput slot orientation (signs, none))⟩ at h4
  have total := trace_trans _ (trace_trans _ (trace_trans _ h1 h2) h3) h4
  have hout : outputTapes third (relationOutput slot orientation (signs, none)) =
      outputTapes base (rowEndBits slot orientation i signs) := by
    simp only [third, second, first, outputTapes_twice]
    apply congrArg (outputTapes base)
    rw [reverse_encodeWord_add]
    simp only [rowEndBits, Nat.add_assoc, List.append_assoc]
  rw [hout] at total
  simpa only [show 1 + (2 * i + 2) + 1 + 1 = 2 * i + 5 by omega] using total

theorem rowEndBits_append (slot : Fin 3) (orientation : Bool)
    (tail i : ℕ) (signs : Signs) :
    rowEndBits slot orientation i signs ++ List.replicate tail true =
      (encodeWords ([tail, 6 * i + 2 * slot.val + if orientation then 0 else 1] ++
        RawInitialRows.relationWordsFor signs (RawInitialTables.slotOrder.symm slot) orientation)).reverse := by
  simp only [rowEndBits, relationOutput, encodeWords_append, encodeWords,
    List.append_nil, List.reverse_append, encodeWord,
    List.reverse_replicate, List.reverse_singleton, List.append_assoc]

theorem falseRowTrace (slot : Fin 3) (base : Tape → List Bool) (n i : ℕ)
    (names : RawInitialRows.Names) (signs : Signs)
    (hvariables : base .variables = encodeWord n) (hindex : base .index = encodeWord i)
    (hscratch : base .scratch = []) :
    advance^[2 * n + 4 * i + 9]
      (some ⟨some (.scan (.tailVariables slot)), (signs, none), base⟩) =
      some ⟨some (.scan (.variableName slot)), (signs, none),
        outputTapes base (encodeWords (RawInitialRows.incidenceWords n i names signs
          (RawInitialTables.slotOrder.symm slot) false)).reverse⟩ := by
  let first := outputTapes base (List.replicate n true)
  let second := outputTapes first (List.replicate i true)
  have h1 := copyTrace (.tailVariables slot) base n hvariables hscratch signs
  have h2 := copyTrace (.tailIndex slot) first i
    (by simpa [first, outputTapes, copySource] using hindex)
    (by simpa [first, outputTapes] using hscratch) signs
  simp only [copyScale, Nat.one_mul, copyNext] at h1 h2
  change advance^[2 * n + 2]
    (some ⟨some (.scan (.tailVariables slot)), (signs, none), base⟩) =
    some ⟨some (.scan (.tailIndex slot)), (signs, none), first⟩ at h1
  change advance^[2 * i + 2]
    (some ⟨some (.scan (.tailIndex slot)), (signs, none), first⟩) =
    some ⟨some (.closeTail slot false), (signs, none), second⟩ at h2
  have h3 := rowEndTrace slot false second i
    (by simpa [second, first, outputTapes] using hindex)
    (by simpa [second, first, outputTapes] using hscratch) signs
  have total := trace_trans _ (trace_trans _ h1 h2) h3
  have hout : outputTapes second (rowEndBits slot false i signs) =
      outputTapes base (encodeWords (RawInitialRows.incidenceWords n i names signs
        (RawInitialTables.slotOrder.symm slot) false)).reverse := by
    simp only [second, first, outputTapes_twice]
    apply congrArg (outputTapes base)
    rw [← List.replicate_add, Nat.add_comm i n, rowEndBits_append]
    simp only [RawInitialRows.incidenceWords, Bool.false_eq_true, ↓reduceIte,
      Equiv.apply_symm_apply]
  rw [hout] at total
  simpa only [relationNext, Bool.false_eq_true, ↓reduceIte,
    show (2 * n + 2) + (2 * i + 2) + (2 * i + 5) = 2 * n + 4 * i + 9 by omega] using total

theorem trueRowTrace (slot : Fin 3) (base : Tape → List Bool) (n i : ℕ)
    (names : RawInitialRows.Names) (signs : Signs)
    (hname : base (.field (nameField slot)) =
      encodeWord (RawInitialRows.nameWord names (RawInitialTables.slotOrder.symm slot)))
    (hindex : base .index = encodeWord i) (hscratch : base .scratch = []) :
    advance^[2 * RawInitialRows.nameWord names (RawInitialTables.slotOrder.symm slot) + 2 * i + 7]
      (some ⟨some (.scan (.variableName slot)), (signs, none), base⟩) =
      some ⟨some (relationNext slot true), (signs, none),
        outputTapes base (encodeWords (RawInitialRows.incidenceWords n i names signs
          (RawInitialTables.slotOrder.symm slot) true)).reverse⟩ := by
  let value := RawInitialRows.nameWord names (RawInitialTables.slotOrder.symm slot)
  let first := outputTapes base (List.replicate value true)
  have h1 := copyTrace (.variableName slot) base value hname hscratch signs
  simp only [copyScale, Nat.one_mul, copyNext] at h1
  change advance^[2 * value + 2]
    (some ⟨some (.scan (.variableName slot)), (signs, none), base⟩) =
    some ⟨some (.closeTail slot true), (signs, none), first⟩ at h1
  have h2 := rowEndTrace slot true first i
    (by simpa [first, outputTapes] using hindex)
    (by simpa [first, outputTapes] using hscratch) signs
  have total := trace_trans _ h1 h2
  have hout : outputTapes first (rowEndBits slot true i signs) =
      outputTapes base (encodeWords (RawInitialRows.incidenceWords n i names signs
        (RawInitialTables.slotOrder.symm slot) true)).reverse := by
    simp only [first, outputTapes_twice, rowEndBits_append, value,
      RawInitialRows.incidenceWords, ↓reduceIte, Equiv.apply_symm_apply]
  rw [hout] at total
  simpa only [value, show (2 * value + 2) + (2 * i + 5) = 2 * value + 2 * i + 7 by omega] using total

def pairWords (slot : Fin 3) (n i : ℕ) (names : RawInitialRows.Names)
    (signs : Signs) : List ℕ :=
  RawInitialRows.incidenceWords n i names signs (RawInitialTables.slotOrder.symm slot) false ++
    RawInitialRows.incidenceWords n i names signs (RawInitialTables.slotOrder.symm slot) true

theorem pairTrace (slot : Fin 3) (base : Tape → List Bool) (n i : ℕ)
    (names : RawInitialRows.Names) (signs : Signs)
    (hvariables : base .variables = encodeWord n) (hindex : base .index = encodeWord i)
    (hname : base (.field (nameField slot)) =
      encodeWord (RawInitialRows.nameWord names (RawInitialTables.slotOrder.symm slot)))
    (hscratch : base .scratch = []) :
    advance^[2 * n + 6 * i +
      2 * RawInitialRows.nameWord names (RawInitialTables.slotOrder.symm slot) + 16]
      (some ⟨some (.scan (.tailVariables slot)), (signs, none), base⟩) =
      some ⟨some (relationNext slot true), (signs, none),
        outputTapes base (encodeWords (pairWords slot n i names signs)).reverse⟩ := by
  let first := outputTapes base (encodeWords (RawInitialRows.incidenceWords n i names signs
    (RawInitialTables.slotOrder.symm slot) false)).reverse
  have h1 := falseRowTrace slot base n i names signs hvariables hindex hscratch
  have h2 := trueRowTrace slot first n i names signs
    (by simpa [first, outputTapes] using hname)
    (by simpa [first, outputTapes] using hindex)
    (by simpa [first, outputTapes] using hscratch)
  have total := trace_trans _ h1 h2
  simpa only [first, outputTapes_twice, pairWords, encodeWords_append, List.reverse_append,
    show (2 * n + 4 * i + 9) +
      (2 * RawInitialRows.nameWord names (RawInitialTables.slotOrder.symm slot) + 2 * i + 7) =
      2 * n + 6 * i +
        2 * RawInitialRows.nameWord names (RawInitialTables.slotOrder.symm slot) + 16 by omega]
    using total

/-- Exact execution of all six incidence rows. Relation tables stay symbolic;
no entry is discarded and every non-output tape is preserved. -/
theorem rowsTrace (base : Tape → List Bool) (n i : ℕ)
    (names : RawInitialRows.Names) (signs : Signs)
    (hvariables : base .variables = encodeWord n) (hindex : base .index = encodeWord i)
    (hname0 : base (.field 0) = encodeWord names.1)
    (hname2 : base (.field 2) = encodeWord names.2.1)
    (hname4 : base (.field 4) = encodeWord names.2.2)
    (hscratch : base .scratch = []) :
    advance^[6 * n + 18 * i + 2 * (names.1 + names.2.1 + names.2.2) + 48]
      (some ⟨some (.scan (.tailVariables 0)), (signs, none), base⟩) =
      some ⟨some (.cleanupField 0), (signs, none),
        outputTapes base (encodeWords (RawInitialRows.clauseWords n i names signs)).reverse⟩ := by
  let first := outputTapes base (encodeWords (pairWords 0 n i names signs)).reverse
  let second := outputTapes first (encodeWords (pairWords 1 n i names signs)).reverse
  have h0 := pairTrace 0 base n i names signs hvariables hindex hname0 hscratch
  have h1 := pairTrace 1 first n i names signs
    (by simpa [first, outputTapes] using hvariables)
    (by simpa [first, outputTapes] using hindex)
    (by simpa [first, outputTapes, nameField, RawInitialRows.nameWord,
      RawInitialTables.slotOrder] using hname2)
    (by simpa [first, outputTapes] using hscratch)
  have h2 := pairTrace 2 second n i names signs
    (by simpa [second, first, outputTapes] using hvariables)
    (by simpa [second, first, outputTapes] using hindex)
    (by simpa [second, first, outputTapes, nameField, RawInitialRows.nameWord,
      RawInitialTables.slotOrder] using hname4)
    (by simpa [second, first, outputTapes] using hscratch)
  change advance^[2 * n + 6 * i + 2 * names.1 + 16]
    (some ⟨some (.scan (.tailVariables 0)), (signs, none), base⟩) =
    some ⟨some (.scan (.tailVariables 1)), (signs, none), first⟩ at h0
  change advance^[2 * n + 6 * i + 2 * names.2.1 + 16]
    (some ⟨some (.scan (.tailVariables 1)), (signs, none), first⟩) =
    some ⟨some (.scan (.tailVariables 2)), (signs, none), second⟩ at h1
  change advance^[2 * n + 6 * i + 2 * names.2.2 + 16]
    (some ⟨some (.scan (.tailVariables 2)), (signs, none), second⟩) =
    some ⟨some (.cleanupField 0), (signs, none),
      outputTapes second (encodeWords (pairWords 2 n i names signs)).reverse⟩ at h2
  have total := trace_trans _ (trace_trans _ h0 h1) h2
  have hout : outputTapes second (encodeWords (pairWords 2 n i names signs)).reverse =
      outputTapes base (encodeWords (RawInitialRows.clauseWords n i names signs)).reverse := by
    simp only [second, first, outputTapes_twice, RawInitialRows.clauseWords,
      encodeWords_append, List.reverse_append, pairWords, List.append_assoc]
    rfl
  rw [hout] at total
  simpa only [show (2 * n + 6 * i + 2 * names.1 + 16) +
    (2 * n + 6 * i + 2 * names.2.1 + 16) + (2 * n + 6 * i + 2 * names.2.2 + 16) =
      6 * n + 18 * i + 2 * (names.1 + names.2.1 + names.2.2) + 48 by omega] using total

end UniqueGamesTheorem.Foundations.PCP.RawInitialMachineRows

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_RawInitialMachineBody
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! One complete clause iteration of the actual initial graph machine. -/

namespace UniqueGamesTheorem.Foundations.PCP.RawInitialMachineBody

open Turing Target Complexity RawInitialMachineModel RawInitialMachineLoopData
open RawInitialMachineReadClause RawInitialMachineRows RawInitialMachineBudget

theorem guardTrace_succ (n i remaining : Nat) (input reversed : List Bool)
    (state : State) :
    (MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some .guard, state, loopTapes n i (remaining + 1) input reversed⟩) =
      some ⟨some (.fieldStart 0), (state.1, none),
        loopTapes n i remaining input reversed⟩ := by
  have h := MachineUnaryCounter.guardTrace_succ Tape.counter Label.guard
    (.fieldStart 0) (.scan .dummyVariables) program rfl
    (loopTapes n i remaining input reversed) remaining [] state.1 state.2
  have heq (r : Nat) : MachineUnaryCounter.counterTapes Tape.counter
      (loopTapes n i remaining input reversed) r [] = loopTapes n i r input reversed := by
    funext tape
    cases tape <;> simp [MachineUnaryCounter.counterTapes, loopTapes]
  simpa only [heq, Prod.mk.eta] using h

theorem guardTrace_zero (n i : Nat) (input reversed : List Bool) (state : State) :
    (MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some .guard, state, loopTapes n i 0 input reversed⟩) =
      some ⟨some (.scan .dummyVariables), (state.1, none),
        loopTapes n i 0 input reversed⟩ := by
  have h := MachineUnaryCounter.guardTrace_zero Tape.counter Label.guard
    (.fieldStart 0) (.scan .dummyVariables) program rfl
    (loopTapes n i 0 input reversed) [] state.1 state.2
  have heq : MachineUnaryCounter.counterTapes Tape.counter
      (loopTapes n i 0 input reversed) 0 [] = loopTapes n i 0 input reversed := by
    funext tape
    cases tape <;> simp [MachineUnaryCounter.counterTapes, loopTapes]
  simpa only [heq, Prod.mk.eta] using h

theorem bodyTrace {n : Nat} (i remaining : Nat) (c : Clause n)
    (suffix reversed : List Bool) (state : State) :
    (MachineComposition.advance (TM2.step program))^[bodyTime i c]
      (some ⟨some .guard, state,
        loopTapes n i (remaining + 1)
          (encodeWords (Complexity.clauseWords c) ++ suffix) reversed⟩) =
      some ⟨some .guard, (RawInitialRows.clauseSigns c, none),
        loopTapes n (i + 1) remaining suffix
          ((encodeWords (RawInitialRows.clauseWords n i
            (RawInitialRows.clauseNames c) (RawInitialRows.clauseSigns c))).reverse ++ reversed)⟩ := by
  let input := encodeWords (Complexity.clauseWords c) ++ suffix
  let base := loopTapes n i remaining input reversed
  let chunk := (encodeWords (RawInitialRows.clauseWords n i
    (RawInitialRows.clauseNames c) (RawInitialRows.clauseSigns c))).reverse
  let emitted := loopTapes n i remaining input (chunk ++ reversed)
  have first := guardTrace_succ n i remaining input reversed state
  have read := readClauseTrace base c suffix rfl (fun _ => rfl) (state.1, none)
  have rows := rowsTrace (recordTapes base c suffix) n i
    (RawInitialRows.clauseNames c) (RawInitialRows.clauseSigns c)
    rfl rfl rfl rfl rfl rfl
  have frame : outputTapes (recordTapes base c suffix) chunk =
      recordTapes emitted c suffix := by
    funext tape
    cases tape <;> simp [outputTapes, recordTapes, emitted, base, loopTapes]
  change (MachineComposition.advance (TM2.step program))^[6 * n + 18 * i +
      2 * nameSum c + 48]
    (some ⟨some (.scan (.tailVariables 0)), (RawInitialRows.clauseSigns c, none),
      recordTapes base c suffix⟩) =
    some ⟨some (.cleanupField 0), (RawInitialRows.clauseSigns c, none),
    outputTapes (recordTapes base c suffix) chunk⟩ at rows
  rw [frame] at rows
  have cleanup := RawInitialMachineCleanup.cleanupTrace emitted c suffix i
    (fun _ => rfl) rfl (RawInitialRows.clauseSigns c, none)
  have finalFrame : Function.update (Function.update emitted .input suffix)
      .index (encodeWord (i + 1)) =
      loopTapes n (i + 1) remaining suffix (chunk ++ reversed) := by
    funext tape
    cases tape <;> simp [emitted, loopTapes]
  rw [finalFrame] at cleanup
  have total := trace_trans _ (trace_trans _ (trace_trans _ first read) rows) cleanup
  have time : 1 + ((encodeWords (Complexity.clauseWords c)).length + 7) +
      (6 * n + 18 * i + 2 * nameSum c + 48) +
      ((encodeWords (Complexity.clauseWords c)).length + 7) = bodyTime i c := by
    simp only [bodyTime, nameSum]
    omega
  simpa only [time] using total

end UniqueGamesTheorem.Foundations.PCP.RawInitialMachineBody

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_RawInitialMachineFinish
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Exact execution of the dummy-row and final cleanup/reversal phases. -/

namespace UniqueGamesTheorem.Foundations.PCP.RawInitialMachineFinish

open Turing Complexity RawInitialMachineModel RawInitialMachinePhases

theorem cleanupTrace (n m : Nat) (rev : List Bool) (state : State) :
    (MachineComposition.advance (TM2.step program))^[n + m + 6]
      (some ⟨some (.cleanupFinal 0), state, finishTapes n m rev⟩) =
      some ⟨some .reset, (state.1, none), tapes [] [] [] rev []⟩ := by
  have h0 := (cleanupFinalInTime 0 (finishTapes n m rev) state).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[(encodeWord n).length + 1]
    (some ⟨some (.cleanupFinal 0), state, finishTapes n m rev⟩) = _ at h0
  rw [encodeWord_length] at h0
  have f0 : Function.update (finishTapes n m rev) .variables [] =
      tapes [] [false] (encodeWord m) rev [] := by
    funext k
    cases k <;> simp [finishTapes, tapes]
  change (MachineComposition.advance (TM2.step program))^[n + 2]
    (some ⟨some (.cleanupFinal 0), state, finishTapes n m rev⟩) =
    some ⟨some (.cleanupFinal 1), (state.1, none),
      Function.update (finishTapes n m rev) .variables []⟩ at h0
  rw [f0] at h0
  have h1 := (cleanupFinalInTime 1 (tapes [] [false] (encodeWord m) rev [])
    (state.1, none)).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[2]
    (some ⟨some (.cleanupFinal 1), (state.1, none),
      tapes [] [false] (encodeWord m) rev []⟩) = _ at h1
  have f1 : Function.update (tapes [] [false] (encodeWord m) rev []) .counter [] =
      tapes [] [] (encodeWord m) rev [] := by
    funext k
    cases k <;> simp [tapes]
  change (MachineComposition.advance (TM2.step program))^[2]
    (some ⟨some (.cleanupFinal 1), (state.1, none), tapes [] [false] (encodeWord m) rev []⟩) =
    some ⟨some (.cleanupFinal 2), (state.1, none),
      Function.update (tapes [] [false] (encodeWord m) rev []) .counter []⟩ at h1
  rw [f1] at h1
  have h2 := (cleanupFinalInTime 2 (tapes [] [] (encodeWord m) rev [])
    (state.1, none)).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[(encodeWord m).length + 1]
    (some ⟨some (.cleanupFinal 2), (state.1, none),
      tapes [] [] (encodeWord m) rev []⟩) = _ at h2
  rw [encodeWord_length] at h2
  have f2 : Function.update (tapes [] [] (encodeWord m) rev []) .index [] =
      tapes [] [] [] rev [] := by
    funext k
    cases k <;> simp [tapes]
  change (MachineComposition.advance (TM2.step program))^[m + 2]
    (some ⟨some (.cleanupFinal 2), (state.1, none), tapes [] [] (encodeWord m) rev []⟩) =
    some ⟨some .reset, (state.1, none),
      Function.update (tapes [] [] (encodeWord m) rev []) .index []⟩ at h2
  rw [f2] at h2
  have total := trace_trans _ (trace_trans _ h0 h1) h2
  simpa only [show (n + 2) + 2 + (m + 2) = n + m + 6 by omega] using total

theorem resetReverseTrace (rev : List Bool) (state : State) :
    (MachineComposition.advance (TM2.step program))^[rev.length + 2]
      (some ⟨some .reset, state, tapes [] [] [] rev []⟩) =
      some (haltList machine rev.reverse) := by
  have reset : (MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some .reset, state, tapes [] [] [] rev []⟩) =
      some ⟨some .finalReverse, initialState, tapes [] [] [] rev []⟩ := rfl
  have transfer := (Reduction.MachineTransfer.transferAtInTime
    .reversed .output (by decide) id false .finalReverse none program rfl
    (tapes [] [] [] rev []) (false, false, false) none).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[rev.length + 1]
    (some ⟨some .finalReverse, initialState, tapes [] [] [] rev []⟩) = _ at transfer
  have frame : Reduction.MachineTransfer.tapesAt .reversed .output
      (tapes [] [] [] rev []) [] (rev.reverse.map id ++ []) =
      (haltList machine rev.reverse).stk := by
    funext k
    change Tape at k
    cases k <;> simp [Reduction.MachineTransfer.tapesAt, tapes, haltList, machine]
    rfl
  change (MachineComposition.advance (TM2.step program))^[rev.length + 1]
    (some ⟨some .finalReverse, initialState, tapes [] [] [] rev []⟩) =
    some ⟨none, initialState, Reduction.MachineTransfer.tapesAt .reversed .output
      (tapes [] [] [] rev []) [] (rev.reverse.map id ++ [])⟩ at transfer
  rw [frame] at transfer
  have total := trace_trans _ reset transfer
  rw [show 1 + (rev.length + 1) = rev.length + 2 by omega] at total
  change (MachineComposition.advance (TM2.step program))^[rev.length + 2]
    (some ⟨some .reset, state, tapes [] [] [] rev []⟩) =
    some ⟨none, initialState, (haltList machine rev.reverse).stk⟩
  exact total

theorem copyFinishTrace (n m r : Nat) (rev : List Bool) (phase : CopyPhase)
    (hsource : finishTapes n m rev (copySource phase) = encodeWord r) (state : State) :
    (MachineComposition.advance (TM2.step program))^[2 * r + 2]
      (some ⟨some (.scan phase), state, finishTapes n m rev⟩) =
      some ⟨some (copyNext phase), (state.1, none),
        finishTapes n m (List.replicate (copyScale phase * r) true ++ rev)⟩ := by
  have h := (copyInTime phase (finishTapes n m rev) r []
    (by simpa only [List.append_nil] using hsource) rfl state).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[2 * r + 2]
    (some ⟨some (.scan phase), state, finishTapes n m rev⟩) =
    some ⟨some (copyNext phase), (state.1, none),
      Function.update (finishTapes n m rev) .reversed
        (List.replicate (copyScale phase * r) true ++ rev)⟩ at h
  rw [update_finish] at h
  exact h

theorem closeDummyTailTrace (n m : Nat) (rev : List Bool) (state : State) :
    (MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some .closeDummyTail, state, finishTapes n m rev⟩) =
      some ⟨some (.scan .dummyReverse), state, finishTapes n m (false :: rev)⟩ := by
  change some (TM2.stepAux (program .closeDummyTail) state (finishTapes n m rev)) = _
  simp only [program, TM2.stepAux]
  congr 2
  exact update_finish _ _ _ _

theorem closeDummyReverseTrace (n m : Nat) (rev : List Bool) (state : State) :
    (MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some .closeDummyReverse, state, finishTapes n m rev⟩) =
      some ⟨some .dummyRelation, state, finishTapes n m (false :: rev)⟩ := by
  change some (TM2.stepAux (program .closeDummyReverse) state (finishTapes n m rev)) = _
  simp only [program, TM2.stepAux]
  congr 2
  exact update_finish _ _ _ _

theorem dummyRelationTrace (n m : Nat) (rev : List Bool) (state : State) :
    (MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some .dummyRelation, state, finishTapes n m rev⟩) =
      some ⟨some (.cleanupFinal 0), state,
        finishTapes n m ((encodeWords (List.replicate 4096 1)).reverse ++ rev)⟩ := by
  change some (TM2.stepAux (program .dummyRelation) state (finishTapes n m rev)) = _
  rw [program, Reduction.MachineSubstitution.stepAux_pushWord, trueRelationWords]
  simp only [TM2.stepAux]
  congr 2
  exact update_finish _ _ _ _

/-- The three actual prefix scans and three emitting transitions append the complete dummy row. -/
theorem dummyTrace (n m : Nat) (rev : List Bool) (state : State) :
    (MachineComposition.advance (TM2.step program))^[2 * n + 4 * m + 9]
      (some ⟨some (.scan .dummyVariables), state, finishTapes n m rev⟩) =
      some ⟨some (.cleanupFinal 0), (state.1, none),
        finishTapes n m ((encodeWords (RawInitialRows.dummyWords n m)).reverse ++ rev)⟩ := by
  let a := List.replicate n true ++ rev
  let b := List.replicate m true ++ a
  let c := false :: b
  let d := List.replicate (6 * m) true ++ c
  let e := false :: d
  have h0 := copyFinishTrace n m n rev .dummyVariables rfl state
  simp only [copyScale, copyNext, Nat.one_mul] at h0
  have h1 := copyFinishTrace n m m a .dummyIndex rfl (state.1, none)
  simp only [copyScale, copyNext, Nat.one_mul] at h1
  have h2 := closeDummyTailTrace n m b (state.1, none)
  have h3 := copyFinishTrace n m m c .dummyReverse rfl (state.1, none)
  simp only [copyScale, copyNext] at h3
  have h4 := closeDummyReverseTrace n m d (state.1, none)
  have h5 := dummyRelationTrace n m e (state.1, none)
  have total := trace_trans _ (trace_trans _ (trace_trans _
    (trace_trans _ (trace_trans _ h0 h1) h2) h3) h4) h5
  have output : (encodeWords (List.replicate 4096 1)).reverse ++ e =
      (encodeWords (RawInitialRows.dummyWords n m)).reverse ++ rev := by
    have rep : List.replicate m true ++ (List.replicate n true ++ rev) =
        List.replicate (n + m) true ++ rev := by
      rw [← List.append_assoc, ← List.replicate_add, Nat.add_comm m n]
    simp only [RawInitialRows.dummyWords, encodeWords_append, encodeWords,
      List.append_nil, List.reverse_append,
      encodeWord, List.reverse_cons,
      List.reverse_replicate, List.append_assoc, List.singleton_append,
      a, b, c, d, e]
    rw [rep]
    simp only [List.reverse_nil, List.nil_append, List.cons_append]
  rw [output] at total
  simpa only [show (((((2 * n + 2) + (2 * m + 2)) + 1) + (2 * m + 2)) + 1) + 1 =
    2 * n + 4 * m + 9 by omega] using total

/-- Exact final execution, including all tape cleanup and the canonical halt state. -/
theorem finishTrace (n m : Nat) (rev : List Bool) (state : State) :
    (MachineComposition.advance (TM2.step program))^[
        3 * n + 5 * m + 17 + (encodeWords (RawInitialRows.dummyWords n m)).length + rev.length]
      (some ⟨some (.scan .dummyVariables), state, finishTapes n m rev⟩) =
      some (haltList machine (rev.reverse ++ encodeWords (RawInitialRows.dummyWords n m))) := by
  let emitted := (encodeWords (RawInitialRows.dummyWords n m)).reverse ++ rev
  have total := trace_trans _ (trace_trans _ (dummyTrace n m rev state)
    (cleanupTrace n m emitted (state.1, none)))
    (resetReverseTrace emitted (state.1, none))
  have hout : emitted.reverse = rev.reverse ++ encodeWords (RawInitialRows.dummyWords n m) := by
    simp only [emitted, List.reverse_append, List.reverse_reverse]
  rw [hout] at total
  have htime : (2 * n + 4 * m + 9) + (n + m + 6) + (emitted.length + 2) =
      3 * n + 5 * m + 17 + (encodeWords (RawInitialRows.dummyWords n m)).length + rev.length := by
    simp only [emitted, List.length_append, List.length_reverse]
    omega
  rwa [htime] at total

end UniqueGamesTheorem.Foundations.PCP.RawInitialMachineFinish

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_RawInitialMachineLoop
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Exact execution of the clause loop, in the original occurrence order. -/

namespace UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoop

open Turing Target Complexity RawInitialMachineModel RawInitialMachineLoopData
open RawInitialMachineBudget RawInitialMachineBody RawInitialMachineFinish

def finalSigns {n : Nat} (incoming : RawInitialMachineModel.Signs) :
    List (Clause n) → RawInitialMachineModel.Signs
  | [] => incoming
  | c :: cs => finalSigns (RawInitialRows.clauseSigns c) cs

theorem empty_loopTapes (n i : Nat) (rev : List Bool) :
    loopTapes n i 0 [] rev = finishTapes n i rev := by
  funext tape
  cases tape <;> rfl

/-- The complete actual loop: every clause is read once, emits six rows, and
leaves clean field tapes before the next guard. The final zero guard is included. -/
theorem loopTrace {n : Nat} (i : Nat) (cs : List (Clause n))
    (rev : List Bool) (state : State) :
    (MachineComposition.advance (TM2.step program))^[loopTime i cs]
      (some ⟨some .guard, state, loopTapes n i cs.length (clauseInput cs) rev⟩) =
      some ⟨some (.scan .dummyVariables), (finalSigns state.1 cs, none),
        finishTapes n (i + cs.length) ((encodeWords (clauseOutput n i cs)).reverse ++ rev)⟩ := by
  induction cs generalizing i rev state with
  | nil =>
      have h := RawInitialMachineBody.guardTrace_zero n i [] rev state
      rw [empty_loopTapes] at h
      simpa only [loopTime, List.length_nil, clauseInput_nil, clauseOutput_nil,
        finalSigns, encodeWords, List.reverse_nil, List.nil_append, Nat.add_zero,
        empty_loopTapes] using h
  | cons c cs ih =>
      have first := bodyTrace i cs.length c (clauseInput cs) rev state
      have rest := ih (i + 1)
        ((encodeWords (RawInitialRows.clauseWords n i
          (RawInitialRows.clauseNames c) (RawInitialRows.clauseSigns c))).reverse ++ rev)
        (RawInitialRows.clauseSigns c, none)
      have total := trace_trans _ first rest
      have hi : i + 1 + cs.length = i + (cs.length + 1) := by omega
      simpa only [loopTime, List.length_cons, clauseInput_cons, clauseOutput_cons,
        encodeWords_append, List.reverse_append, List.append_assoc, finalSigns, hi] using total

end UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoop

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_MachineRawInitialTable
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! The actual finite machine computing the initial graph's full serialized
table. The runtime bound counts every parse, row, cleanup and output reversal. -/

namespace UniqueGamesTheorem.Foundations.PCP.MachineRawInitialTable

open Turing Target Complexity RawInitialMachineModel RawInitialMachineLoopData
open RawInitialMachineBudget RawInitialMachineLoop

def prefixBits (F : Formula) : List Bool :=
  encodeWords ([F.variables + F.clauses.length + 1, 6 * F.clauses.length + 1] ++
    clauseOutput F.variables 0 F.clauses)

theorem outputBits (F : Formula) :
    GraphTables.tableBits (RawInitialTables.table F) = prefixBits F ++
      encodeWords (RawInitialRows.dummyWords F.variables F.clauses.length) := by
  change encodeWords (GraphTables.tableWords (RawInitialTables.table F)) = _
  rw [tableWords_decomposition, encodeWords_append]
  rfl

theorem machineTrace (F : Formula) :
    (MachineComposition.advance (TM2.step program))^[fullBudget F]
      (some (initList machine (formulaBits F))) =
      some (haltList machine (GraphTables.tableBits (RawInitialTables.table F))) := by
  have startup := RawInitialMachineStart.formulaStartTrace F
  rw [startTapes_eq] at startup
  have loop := loopTrace 0 F.clauses
    (encodeWords [F.variables + F.clauses.length + 1, 6 * F.clauses.length + 1]).reverse
    initialState
  have hprefix : (encodeWords (clauseOutput F.variables 0 F.clauses)).reverse ++
      (encodeWords [F.variables + F.clauses.length + 1, 6 * F.clauses.length + 1]).reverse =
      (prefixBits F).reverse := by
    simp only [prefixBits, encodeWords_append, List.reverse_append]
  rw [hprefix, Nat.zero_add] at loop
  have finish := RawInitialMachineFinish.finishTrace F.variables F.clauses.length
    (prefixBits F).reverse (finalSigns initialState.1 F.clauses, none)
  rw [List.reverse_reverse, ← outputBits F] at finish
  have total := trace_trans _ (trace_trans _ startup loop) finish
  have time : (3 * F.variables + 5 * F.clauses.length + 13 + loopTime 0 F.clauses) +
      (3 * F.variables + 5 * F.clauses.length + 17 +
        (encodeWords (RawInitialRows.dummyWords F.variables F.clauses.length)).length +
        (prefixBits F).reverse.length) = fullBudget F := by
    rw [fullBudget, outputBits, List.length_append, List.length_reverse]
    omega
  simpa only [time] using total

def outputsInTime (F : Formula) :
    TM2OutputsInTime machine (formulaBits F)
      (some (GraphTables.tableBits (RawInitialTables.table F)))
      (timePolynomial.eval (formulaBits F).length) where
  steps := fullBudget F
  evals_in_steps := machineTrace F
  steps_le_m := fullBudget_le F

noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime formulaEncoding.encode GraphTables.encoding.encode
      RawInitialTables.table where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := timePolynomial
  outputsFun F := by
    change TM2OutputsInTime machine ((formulaBits F).map id)
      (some ((GraphTables.tableBits (RawInitialTables.table F)).map id))
      (timePolynomial.eval (formulaBits F).length)
    have hi := @List.map_id (machine.Γ machine.k₀) (formulaBits F)
    have ho := @List.map_id (machine.Γ machine.k₁)
      (GraphTables.tableBits (RawInitialTables.table F))
    rw [hi, ho]
    exact outputsInTime F

end UniqueGamesTheorem.Foundations.PCP.MachineRawInitialTable

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_TableIteration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Iteration of the concrete stored-table round, with the original formula's
actual initial graph size controlling the number of rounds. -/

namespace UniqueGamesTheorem.Foundations.PCP.TableIteration

open RoundTables
open Target Complexity

/-- The same data computation on all validated tables; positivity is an invariant,
and is erased from the runtime path. -/
def runTables (H : BaseTable) : Nat → GraphTables.Table → GraphTables.Table :=
  AmplificationIteration.run (build H)

theorem run_val (H : BaseTable) (n : Nat) (input : Input) :
    (run H n input).val = runTables H n input.val := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change build H (run H n input).val = build H (runTables H n input.val)
      rw [ih]

def iterationCount (F : Formula) : Nat := AmplificationIteration.rounds (size (initial F))

def outputTable (H : BaseTable) (F : Formula) : GraphTables.Table :=
  runTables H (iterationCount F) (RawInitialTables.table F)

def gapMap (H : BaseTable) (F : Formula) : Formula := FinalTableFormula.output (outputTable H F)

end UniqueGamesTheorem.Foundations.PCP.TableIteration

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_GraphIterationBoundsLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-! One polynomial bounds every actual intermediate encoding in the concrete
logarithmic graph iteration. The linear recurrence is on graph size. -/

namespace UniqueGamesTheorem.Foundations.Complexity.GraphIterationBounds

open PCP RoundTables

def inputBits (input : Input) : List Bool := GraphTables.tableBits input.val

def countedBits (input : Input) : List Bool := GraphCounterPrefix.output input.val

def words (H : BaseTable) (input : Input) (i : Nat) : List Bool :=
  GraphTables.tableBits (TableIteration.runTables H i input.val)

def count (input : Input) : Nat := GraphCounterPrefix.count input.val

theorem inputBits_le_countedBits (input : Input) : (inputBits input).length ≤ (countedBits input).length := by
  simp only [inputBits, countedBits, GraphCounterPrefix.output, List.length_append]
  omega

theorem size_le_inputBits (input : Input) : size input ≤ (inputBits input).length := by
  have h := GraphTableComplexity.size_add_two_le_bits input.val
  unfold size inputBits
  omega

theorem count_le (input : Input) : count input ≤ (countedBits input).length + 1 :=
  (PCPIterationMachine.rounds_le (size input)).trans
    (Nat.add_le_add_right ((size_le_inputBits input).trans (inputBits_le_countedBits input)) 1)

theorem intermediate_size (H : BaseTable) (input : Input) (i : Nat) (hi : i ≤ count input) :
    size (TableIteration.run H i input) ≤ PCPIterationMachine.sizeEnvelope sizeFactor (size input) := by
  apply PCPIterationMachine.semanticSize_bound
    (fun j => size (TableIteration.run H j input)) sizeFactor (size input)
    sizeFactor_positive (Nat.le_succ _) _ i hi
  intro j _
  exact step_size H (TableIteration.run H j input)

theorem intermediate_bits (H : BaseTable) (input : Input) (i : Nat) (hi : i ≤ count input) :
    (words H input i).length ≤ lengthPolynomial.eval (countedBits input).length := by
  have hsize := intermediate_size H input i hi
  have hinput := (size_le_inputBits input).trans (inputBits_le_countedBits input)
  have heval := MachineComposition.natPolynomial_eval_mono
    (PCPIterationMachine.sizePolynomial sizeFactor) hinput
  rw [PCPIterationMachine.sizePolynomial_eval, PCPIterationMachine.sizePolynomial_eval] at heval
  have hs := hsize.trans heval
  have htable : (TableIteration.runTables H i input.val).vertices +
      (TableIteration.runTables H i input.val).darts ≤
        PCPIterationMachine.sizeEnvelope sizeFactor (countedBits input).length := by
    rw [← TableIteration.run_val]
    exact hs
  rw [lengthPolynomial, Polynomial.eval_comp, PCPIterationMachine.sizePolynomial_eval]
  exact GraphTableComplexity.bits_le_of_size_le _ htable

end UniqueGamesTheorem.Foundations.Complexity.GraphIterationBounds



/-! Actual polynomial-time iteration of the concrete graph-table round. A
certificate for that one body is the only supplied machine input. Counter
preparation, repeated calls, tape handoffs, and final cleanup are all proved. -/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineTableIteration

open Turing PCP RoundTables GraphIterationBounds


def finalTable (H : BaseTable) (input : Input) : GraphTables.Table :=
  TableIteration.runTables H (count input) input.val

noncomputable def counterCertificate : TM2ComputableInPolyTime inputBits countedBits (id : Input → Input) where
  toTM2ComputableAux := GraphCounterPrefix.computableInPolyTime.toTM2ComputableAux
  time := GraphCounterPrefix.computableInPolyTime.time
  outputsFun input := GraphCounterPrefix.computableInPolyTime.outputsFun input.val

variable (H : BaseTable)
  (body : TM2ComputableInPolyTime GraphTables.tableBits GraphTables.tableBits (build H))

/-- The generic repeat machine executes only the actual successive graph words.
Its polynomial bound uses the proved linear growth of their semantic sizes. -/
noncomputable def countedCertificate :
    TM2ComputableInPolyTime countedBits GraphTables.tableBits (finalTable H) where
  tm := MachineRepeat.machine body.tm body.inputAlphabet body.outputAlphabet
  inputAlphabet := body.inputAlphabet
  outputAlphabet := body.inputAlphabet
  time := runtimePolynomial body.time
  outputsFun input := by
    let budgets := fun i => body.time.eval (words H input i).length
    have runs (i : Nat) (_hi : i < count input) :
        TM2OutputsInTime body.tm ((words H input i).map body.inputAlphabet.symm)
          (some ((words H input (i + 1)).map body.outputAlphabet.symm)) (budgets i) := by
      exact body.outputsFun (TableIteration.runTables H i input.val)
    let run := MachineRepeat.executeSequence body.tm body.inputAlphabet body.outputAlphabet
      (count input) (words H input) budgets runs
    have start : encodeWord (count input) ++ words H input 0 = countedBits input := rfl
    have finish : words H input (count input) = GraphTables.tableBits (finalTable H input) := rfl
    rw [start, finish] at run
    refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
    let N := (countedBits input).length
    let L := lengthPolynomial.eval N
    let B := body.time.eval L
    have hl (i : Nat) (hi : i ≤ count input) : (words H input i).length ≤ L :=
      intermediate_bits H input i hi
    have hb (i : Nat) (hi : i < count input) : budgets i ≤ B :=
      MachineComposition.natPolynomial_eval_mono body.time (hl i hi.le)
    have hloop := MachineRepeat.loopBudget_le (count input) (words H input) budgets B L hb hl
    have hc : count input ≤ N + 1 := count_le input
    rw [runtimePolynomial_eval]
    calc
      run.steps ≤ count input + 1 + MachineRepeat.loopBudget (count input) (words H input) budgets :=
        run.steps_le_m
      _ ≤ count input + 1 + (count input * (B + 2 * L + 3) + 2 * L + 3) :=
        Nat.add_le_add_left hloop _
      _ = count input * (B + 2 * L + 4) + 2 * L + 4 := by ring
      _ ≤ (N + 1) * (B + 2 * L + 4) + 2 * L + 4 :=
        Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul_right _ hc) _) _

/-- One actual finite machine computes the complete logarithmic iteration. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime inputBits GraphTables.tableBits (finalTable H) :=
  MachineSequential.composeBits counterCertificate (countedCertificate H body)

noncomputable def initialCertificate :
    TM2ComputableInPolyTime formulaBits inputBits initial where
  toTM2ComputableAux := MachineRawInitialTable.computableInPolyTime.toTM2ComputableAux
  time := MachineRawInitialTable.computableInPolyTime.time
  outputsFun F := MachineRawInitialTable.computableInPolyTime.outputsFun F

/-- The initial graph and entire repeated table transformation have concrete
finite-machine executions with the same formula and table encodings. -/
noncomputable def tableCertificate :
    TM2ComputableInPolyTime formulaBits GraphTables.tableBits (TableIteration.outputTable H) := by
  change TM2ComputableInPolyTime formulaBits GraphTables.tableBits
    (fun F => finalTable H (initial F))
  exact MachineSequential.composeBits (f := initial) (g := finalTable H)
    initialCertificate (computableInPolyTime H body)

/-- Actual 3SAT gap-map runtime follows from the one concrete round certificate;
initialization, variable repetition, and the final CNF converter are supplied. -/
noncomputable def gapMapCertificate :
    TM2ComputableInPolyTime formulaBits formulaBits (TableIteration.gapMap H) :=
  MachineSequential.composeBits (f := TableIteration.outputTable H) (g := FinalTableFormula.output)
    (tableCertificate H body)
    FinalCNFMachine.Program.computableInPolyTime

end UniqueGamesTheorem.Foundations.Complexity.MachineTableIteration



namespace UniqueGamesTheorem.Foundations.Complexity.TableIterationFiniteAlphabet

open PCP MachineFiniteAlphabet

theorem initial : FiniteAlphabet MachineRawInitialTable.computableInPolyTime.tm := by
  intro k
  change Finite Bool
  infer_instance

theorem finalCNF : FiniteAlphabet FinalCNFMachine.Program.computableInPolyTime.tm := by
  intro k
  change Finite Bool
  infer_instance

theorem counter : FiniteAlphabet MachineTableIteration.counterCertificate.tm := by
  intro k
  change Finite Bool
  infer_instance

variable (H : RoundTables.BaseTable)
  (body : Turing.TM2ComputableInPolyTime GraphTables.tableBits GraphTables.tableBits
    (RoundTables.build H))
  (finiteBody : FiniteAlphabet body.tm)

include finiteBody

theorem counted : FiniteAlphabet (MachineTableIteration.countedCertificate H body).tm :=
  repeat_machine body.tm body.inputAlphabet body.outputAlphabet finiteBody

theorem iteration : FiniteAlphabet (MachineTableIteration.computableInPolyTime H body).tm :=
  composeBits MachineTableIteration.counterCertificate
    (MachineTableIteration.countedCertificate H body) counter (counted H body finiteBody)

theorem table : FiniteAlphabet (MachineTableIteration.tableCertificate H body).tm :=
  composeBits MachineTableIteration.initialCertificate
    (MachineTableIteration.computableInPolyTime H body) initial (iteration H body finiteBody)

theorem gapMap : FiniteAlphabet (MachineTableIteration.gapMapCertificate H body).tm :=
  composeBits (MachineTableIteration.tableCertificate H body)
    FinalCNFMachine.Program.computableInPolyTime (table H body finiteBody) finalCNF

end UniqueGamesTheorem.Foundations.Complexity.TableIterationFiniteAlphabet

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineRegularOriginalRow
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq
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

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularOriginalRow

open Turing MachineComposition
open PCP PCP.GraphTables PCP.PreprocessingRegularTables

/-! ## The actual stored row and its input word boundaries -/

/-! ## One fixed finite program -/

/-! ## Physical intermediate tape states -/

theorem affined_fields (q : Nat) (t : Table) (e : Fin t.darts)
    (base : Tape → List Bool) (input : Input t e base) :
    MachineTableRows.fieldBits fields (affined q t e base) = encodeWords (emittedWords q t e) := by
  have htail := affined_other q t e base 0 (by decide) (by decide) (by decide)
    (by decide) (by decide)
  simp only [MachineTableRows.fieldBits, fields_zero, fields_one, fields_two,
    htail, input.indexWord, affined_reverse, input.computedEmpty,
    affined_relation, input.relationEmpty, List.append_nil,
    emittedWords, encodeWords, List.append_assoc]

section Execution

variable {Λ σ : Type}

theorem emitTrace (q : Nat) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Alphabet Λ (State σ))
    (code : ∀ l, program (labels l) = instruction q labels exit l)
    (t : Table) (e : Fin t.darts) (base : Tape → List Bool) (input : Input t e base)
    (ambient : σ) :
    (advance (TM2.step program))^[rowSteps q t e base]
      (some ⟨some (labels (.emit .relationRead)), ((ambient, zeroBuffer), none), affined q t e base⟩) =
      some ⟨exit, ((ambient, zeroBuffer), none), finalTapes q t e base⟩ := by
  have hrow : affined q t e base 8 = [] := by
    rw [affined_other q t e base 8 (by decide) (by decide) (by decide) (by decide)
      (by decide), input.rowEmpty]
  have hscratch : affined q t e base 5 = [] := by
    rw [affined_other q t e base 5 (by decide) (by decide) (by decide) (by decide)
      (by decide), input.scratchEmpty]
  have hout := affined_other q t e base 9 (by decide) (by decide) (by decide)
    (by decide) (by decide)
  have hfields := affined_fields q t e base input
  have hsize : MachineTableRows.fieldSize fields (affined q t e base) =
      (encodeWords (emittedWords q t e)).length := by
    rw [← MachineTableRows.fieldBits_length, hfields]
  have run := MachineTableRows.appendTrace fields (8 : Tape) 9 5 fields_separate
    (by decide) (by decide) (by decide) (fun l => labels (.emit l)) exit program
    (fun l => code (.emit l)) (affined q t e base) hrow hscratch (ambient, zeroBuffer) none
  rw [hsize, hout, hfields] at run
  exact run

/-- All four phases are derived from their concrete instructions. -/
theorem traceAt (q : Nat) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Alphabet Λ (State σ))
    (code : ∀ l, program (labels l) = instruction q labels exit l)
    (t : Table) (e : Fin t.darts) (base : Tape → List Bool) (input : Input t e base)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[steps q t e base]
      (some ⟨some (labels (.lookup .seed)), ((ambient, zeroBuffer), register), base⟩) =
      some ⟨exit, ((ambient, zeroBuffer), none), finalTapes q t e base⟩ := by
  have hlookup := lookupTrace q labels exit program code t e base input ambient register
  have hcopy := copyTrace q labels exit program code t e base ambient
  have haffine := affineTrace q labels exit program code t e base input ambient
  have hemit := emitTrace q labels exit program code t e base input ambient
  exact join_trace (join_trace (join_trace hlookup hcopy) haffine) hemit

end Execution

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularOriginalRow

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachinePaddingTable
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Exact table-codec endpoint of the polynomial padding-row routine.
The caller supplies the physical unary counters and copied old-row buffer
with the updated headers. This theorem executes every added row and proves
that the resulting output is exactly the existing full table encoding. -/

namespace UniqueGamesTheorem.Foundations.Complexity.MachinePaddingTable

open PCP MachinePaddingRows

def execution {n d m : Nat} (table : PortTables.Table n d) (h : n ≤ m) (hd : 0 < d) :
    StateTransition.EvalsToInTime (machine d hd).step
      ⟨some (.inr .initialize_), (((), none), ()),
        initialTapes n (n * d) (m - n) (initialOutput (m := m) table)⟩
      (some (cfg d none m (m * d) 0
        (PortTables.tableBits (PreprocessingPaddingTables.pad table h))))
      ((MachinePaddingCertificate.timePolynomial d).eval
        (MachinePaddingBounds.inputSize n (n * d) (m - n) (initialOutput (m := m) table))) where
  steps := steps d n (n * d) (initialOutput (m := m) table) (m - n) + 1
  evals_in_steps := by
    have run := paddingTrace d hd (m - n) n (n * d) (initialOutput (m := m) table)
    have hv : n + (m - n) = m := Nat.add_sub_of_le h
    have he : n * d + (m - n) * d = m * d := by rw [← Nat.add_mul, hv]
    have hout : initialOutput (m := m) table ++ paddingBits d n (n * d) (m - n) =
        PortTables.tableBits (PreprocessingPaddingTables.pad table h) := by
      rw [PreprocessingPaddingWords.tableBits_pad]
      rfl
    rw [hv, he, hout] at run
    convert run using 1
    all_goals try with_reducible_and_instances rfl
    rfl
  steps_le_m := by
    simp only [MachinePaddingCertificate.timePolynomial, Polynomial.eval_add, Polynomial.eval_one]
    exact Nat.add_le_add_right
      (MachinePaddingBounds.timePolynomial_bounds d n (n * d) (m - n) (initialOutput (m := m) table)) 1

end UniqueGamesTheorem.Foundations.Complexity.MachinePaddingTable

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineVertexPadding
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Vertex padding from the original serialized port graph

Header counters, the geometric padding count, and the initial row buffer
are generated by physical tape operations before the checked row emitter.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineVertexPadding

open Turing MachineComposition
open UniqueGamesTheorem.Foundations.PCP
open MachineCloudPadding

theorem splitTrace {σ : Type} {n d : Nat} (hd : 0 < d) (t : PortTables.Table n d)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program d hd)))^[MachineTableSplit.exactSteps n (n * d)
      (PreprocessingPaddingWords.rowsBits t)]
      (some ⟨some (.splitCode .copyFirst), ((ambient, false), register),
        memory (PortTables.tableBits t) [] [] [] [] [] [] []⟩) =
      some ⟨some (.powerCode .init), ((ambient, false), none),
        memory (PortTables.tableBits t) (PreprocessingPaddingWords.rowsBits t)
          (encodeWord n) (encodeWord (n * d)) [] [] [] []⟩ := by
  have h := Placement.trace splitTape splitView splitView_left splitView_right
    (Label.splitCode (d := d)) (some (.powerCode .init)) (fun _ => [])
    (MachineTableSplit.program (σ := σ × Bool)) (program d hd) (fun _ => rfl) _ _ _
    (MachineTableSplit.splitTrace n (n * d) (PreprocessingPaddingWords.rowsBits t)
      (ambient, false) register)
  simpa only [Placement.configuration, Placement.label, splitInitialTapes, splitResultTapes,
    ← tableBits_split] using h

theorem powerTrace {σ : Type} (d : Nat) (hd : 0 < d)
    (input output edge : List Bool) (n : Nat) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program d hd)))^[MachineCeilingPower.totalTime ExpanderFamily.growth n]
      (some ⟨some (.powerCode .init), ((ambient, false), register),
        memory input output (encodeWord n) edge [] [] [] []⟩) =
      some ⟨some .dartSeed, ((ambient, false), none),
        memory input output (encodeWord n) edge (encodeWord (PreprocessingLevels.paddedSize n))
          (encodeWord (PreprocessingLevels.boundedLevel n)) [] []⟩ := by
  have h := Placement.trace powerTape powerView powerView_left powerView_right
    (Label.powerCode (d := d)) (some .dartSeed) (memory input output [] edge [] [] [] [])
    (MachineCeilingPower.program ExpanderFamily.growth (σ := σ)) (program d hd)
    (fun _ => rfl) _ _ _ (MachineCeilingPower.paddingTrace n ambient register)
  simpa only [Placement.configuration, Placement.label, powerTapes] using h

theorem affineOutputTrace {σ : Type} (d : Nat) (hd : 0 < d)
    (coefficient : Nat) (seed scan restore : Label d) (exit : Option (Label d))
    (atSeed : program (σ := σ) d hd seed = MachineUnaryAffineAt.seed (σ := σ × Bool) .output 0 scan)
    (atScan : program (σ := σ) d hd scan = MachineUnaryAffineAt.scan (σ := σ × Bool) .power .scratch .output
      coefficient scan restore)
    (atRestore : program (σ := σ) d hd restore = Reduction.MachineTransfer.loopAt (σ := σ × Bool)
      .scratch .power id false restore exit)
    (input output vertex edge level fuel relation : List Bool) (m : Nat)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program d hd)))^[1 + 2 * (m + 1)]
      (some ⟨some seed, ((ambient, false), register),
        memory input output vertex edge (encodeWord m) level fuel relation⟩) =
      some ⟨exit, ((ambient, false), none),
        memory input (encodeWord (coefficient * m) ++ output) vertex edge
          (encodeWord m) level fuel relation⟩ := by
  have hs : (advance (TM2.step (program d hd)))^[1]
      (some ⟨some seed, ((ambient, false), register),
        memory input output vertex edge (encodeWord m) level fuel relation⟩) =
      some ⟨some scan, ((ambient, false), register),
        memory input (encodeWord 0 ++ output) vertex edge (encodeWord m) level fuel relation⟩ := by
    change some (TM2.stepAux (program d hd seed) _ _) = _
    rw [atSeed]
    simp [MachineUnaryAffineAt.seed, Reduction.MachineSubstitution.stepAux_pushWord,
      TM2.stepAux, encodeWord, memory]
  let base := memory input output vertex edge (encodeWord m) level fuel relation
  have ht := MachineUnaryAffineAt.affineTrace Tape.power Tape.scratch Tape.output
    (by decide) (by decide) (by decide) coefficient scan restore exit (program d hd)
    atScan atRestore base m 0 [] output (ambient, false) register
  have hstart : MachineUnaryAffineAt.tapes Tape.power Tape.scratch Tape.output base
      (encodeWord m ++ []) [] (encodeWord 0 ++ output) =
      memory input (encodeWord 0 ++ output) vertex edge (encodeWord m) level fuel relation := by
    funext k
    cases k <;> simp [MachineUnaryAffineAt.tapes, MachineCopy.forkTapes, base, memory]
  have hfinish : MachineUnaryAffineAt.tapes Tape.power Tape.scratch Tape.output base
      (encodeWord m ++ []) [] (encodeWord (coefficient * m + 0) ++ output) =
      memory input (encodeWord (coefficient * m) ++ output) vertex edge
        (encodeWord m) level fuel relation := by
    funext k
    cases k <;> simp [MachineUnaryAffineAt.tapes, MachineCopy.forkTapes, base, memory]
  rw [hstart, hfinish] at ht
  exact appendTrace _ hs ht

theorem headersTrace {σ : Type} (d : Nat) (hd : 0 < d)
    (input output vertex edge level : List Bool) (m : Nat) (ambient : σ)
    (register : Option Bool) :
    (advance (TM2.step (program d hd)))^[4 * (m + 1) + 2]
      (some ⟨some .dartSeed, ((ambient, false), register),
        memory input output vertex edge (encodeWord m) level [] []⟩) =
      some ⟨some .copyFirst, ((ambient, false), none),
        memory input (encodeWords [m, m * d] ++ output) vertex edge (encodeWord m) level [] []⟩ := by
  have h₁ := affineOutputTrace d hd d .dartSeed .dartScan .dartRestore (some .vertexSeed)
    rfl rfl rfl input output vertex edge level [] [] m ambient register
  have h₂ := affineOutputTrace d hd 1 .vertexSeed .vertexScan .vertexRestore (some .copyFirst)
    rfl rfl rfl input (encodeWord (d * m) ++ output) vertex edge level [] [] m ambient none
  have h := appendTrace _ h₁ h₂
  simpa only [Nat.one_mul, Nat.mul_comm d m, encodeWords, List.append_nil, List.append_assoc,
    show (1 + 2 * (m + 1)) + (1 + 2 * (m + 1)) = 4 * (m + 1) + 2 by omega] using h

theorem copyPowerTrace {σ : Type} (d : Nat) (hd : 0 < d)
    (input output vertex edge level : List Bool) (m : Nat) (ambient : σ)
    (register : Option Bool) :
    (advance (TM2.step (program d hd)))^[2 * (m + 2)]
      (some ⟨some .copyFirst, ((ambient, false), register),
        memory input output vertex edge (encodeWord m) level [] []⟩) =
      some ⟨some (.subtractCode .subtract), ((ambient, false), none),
        memory input output vertex edge (encodeWord m) level (encodeWord m) []⟩ := by
  have h := MachineCopy.copyTrace Tape.power Tape.fuel Tape.scratch
    (by decide) (by decide) (by decide) false (Label.copyFirst (d := d)) .copySecond
    (some (.subtractCode .subtract)) (program d hd) rfl rfl
    (memory input output vertex edge (encodeWord m) level [] []) rfl (ambient, false) register
  simpa only [memory, encodeWord_length, List.append_nil, update_fuel] using h

theorem subtractTrace {σ : Type} (d : Nat) (hd : 0 < d)
    (input output edge power level : List Bool) (n m : Nat) (hnm : n ≤ m)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program d hd)))^[2 * n + 2]
      (some ⟨some (.subtractCode .subtract), ((ambient, false), register),
        memory input output (encodeWord n) edge power level (encodeWord m) []⟩) =
      some ⟨some (.rowsCode (.inr .initialize_)), ((ambient, false), none),
        memory input output (encodeWord n) edge power level (encodeWord (m - n)) []⟩ := by
  have h := Placement.trace subtractTape subtractView subtractView_left subtractView_right
    (Label.subtractCode (d := d)) (some (.rowsCode (.inr .initialize_)))
    (memory [] [] [] edge power [] [] [])
    (MachineCloudPadding.program (σ := σ)) (program d hd) (fun _ => rfl) _ _ _
    (MachineCloudPadding.subtractTrace input output level n m hnm ambient register)
  simpa only [Placement.configuration, Placement.label, subtractTapes] using h

/-- The checked padding-row machine is transported through alphabet/state
equalities and a static tape placement. No row execution is assumed. -/
theorem rowsTrace {σ : Type} {n d m : Nat} (hd : 0 < d) (t : PortTables.Table n d)
    (hnm : n ≤ m) (input power level : List Bool) (ambient : σ) :
    (advance (TM2.step (program d hd)))^[rowTime (m := m) t]
      (some ⟨some (.rowsCode (.inr .initialize_)), ((ambient, false), none),
        memory input (MachinePaddingTable.initialOutput (m := m) t)
          (encodeWord n) (encodeWord (n * d)) power level (encodeWord (m - n)) []⟩) =
      some ⟨some .cleanVertex, ((ambient, false), none),
        memory input (PortTables.tableBits (PreprocessingPaddingTables.pad t hnm))
          (encodeWord m) (encodeWord (m * d)) power level (encodeWord 0)
          MachineDummyRows.trueBits⟩ := by
  have hraw := (MachinePaddingTable.execution t hnm hd).evals_in_steps
  change (advance (TM2.step (MachinePaddingRows.program d hd)))^[rowTime (m := m) t]
    (some ⟨some (.inr .initialize_), (((), none), ()),
      MachinePaddingRows.initialTapes n (n * d) (m - n)
        (MachinePaddingTable.initialOutput (m := m) t)⟩) =
    some (MachinePaddingRows.cfg d none m (m * d) 0
      (PortTables.tableBits (PreprocessingPaddingTables.pad t hnm))) at hraw
  have hb := MachineAlphabetTransport.successfulTrace rowAlphabet_eq
    (MachinePaddingRows.program d hd) _ _ _ hraw
  have hf := frameTrace
    (MachineAlphabetTransport.program rowAlphabet_eq (MachinePaddingRows.program d hd))
    (ambient, false) _ _ _ hb
  have hs := MachineStateEquiv.trace (rowStateEquiv σ)
    (MachineStateFrame.frameProgram
      (MachineAlphabetTransport.program rowAlphabet_eq (MachinePaddingRows.program d hd)))
    _ _ _ hf
  have hp := Placement.trace rowTape rowView rowView_left rowView_right
    (Label.rowsCode (d := d)) (some .cleanVertex) (memory input [] [] [] power level [] [])
    (rowProgram d hd (σ := σ)) (program d hd) (fun _ => rfl) _ _ _ hs
  simpa only [Placement.configuration, Placement.label, MachineStateEquiv.configuration,
    MachineStateFrame.frameConfiguration, MachineAlphabetTransport.configuration_mk,
    rowCastTapes, MachinePaddingRows.cfg, rowStateEquiv, Equiv.coe_fn_mk,
    rowInitialTapes, rowFinalTapes] using hp

theorem cleanupTrace {σ : Type} (d : Nat) (hd : 0 < d)
    (input output level : List Bool) (m : Nat) (ambient : σ) :
    (advance (TM2.step (program d hd)))^[cleanupTime d m]
      (some ⟨some .cleanVertex, ((ambient, false), none),
        memory input output (encodeWord m) (encodeWord (m * d)) (encodeWord m) level
          (encodeWord 0) MachineDummyRows.trueBits⟩) =
      some ⟨none, ((ambient, false), none), memory input output [] [] [] level [] []⟩ := by
  have h₁ := (MachineDrain.drainInTime Tape.vertex (Label.cleanVertex (d := d)) (some .cleanEdge)
    (program d hd) rfl
    (memory input output (encodeWord m) (encodeWord (m * d)) (encodeWord m) level
      (encodeWord 0) MachineDummyRows.trueBits) (ambient, false) none).evals_in_steps
  have h₂ := (MachineDrain.drainInTime Tape.edge (Label.cleanEdge (d := d)) (some .cleanPower)
    (program d hd) rfl
    (memory input output [] (encodeWord (m * d)) (encodeWord m) level
      (encodeWord 0) MachineDummyRows.trueBits) (ambient, false) none).evals_in_steps
  have h₃ := (MachineDrain.drainInTime Tape.power (Label.cleanPower (d := d)) (some .cleanRelation)
    (program d hd) rfl
    (memory input output [] [] (encodeWord m) level (encodeWord 0) MachineDummyRows.trueBits)
    (ambient, false) none).evals_in_steps
  have h₄ := (MachineDrain.drainInTime Tape.relation (Label.cleanRelation (d := d)) (some .cleanFuel)
    (program d hd) rfl
    (memory input output [] [] [] level (encodeWord 0) MachineDummyRows.trueBits)
    (ambient, false) none).evals_in_steps
  have h₅ := (MachineDrain.drainInTime Tape.fuel (Label.cleanFuel (d := d)) none
    (program d hd) rfl (memory input output [] [] [] level (encodeWord 0) [])
    (ambient, false) none).evals_in_steps
  simp only [MachineDrain.drainInTime, memory, encodeWord_length, MachineDummyRows.trueBits_length,
    update_vertex, update_edge, update_power, update_relation, update_fuel] at h₁ h₂ h₃ h₄ h₅
  have h := appendTrace _ (appendTrace _ (appendTrace _ (appendTrace _ h₁ h₂) h₃) h₄) h₅
  have ht : cleanupTime d m = (((m + 2 + (m * d + 2)) + (m + 2)) + 8193) + 2 := by
    unfold cleanupTime
    omega
  rw [ht]
  exact h

/-- The whole table transformation begins with only its original encoding.
Every row-emitter counter and the updated prefix are produced by this run. -/
theorem vertexPaddingTrace {σ : Type} {n d : Nat} (hd : 0 < d) (t : PortTables.Table n d)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program d hd)))^[totalTime t]
      (some ⟨some (.splitCode .copyFirst), ((ambient, false), register),
        memory (PortTables.tableBits t) [] [] [] [] [] [] []⟩) =
      some ⟨none, ((ambient, false), none),
        memory (PortTables.tableBits t)
          (PortTables.tableBits (PreprocessingPaddingTables.pad t (PreprocessingLevels.le_paddedSize n)))
          [] [] [] (encodeWord (PreprocessingLevels.boundedLevel n)) [] []⟩ := by
  let m := PreprocessingLevels.paddedSize n
  let level := encodeWord (PreprocessingLevels.boundedLevel n)
  let input := PortTables.tableBits t
  let rows := PreprocessingPaddingWords.rowsBits t
  let initialOutput := MachinePaddingTable.initialOutput (m := m) t
  have h₁ := splitTrace hd t ambient register
  have h₂ := powerTrace d hd input rows (encodeWord (n * d)) n ambient none
  have h₃ := headersTrace d hd input rows (encodeWord n) (encodeWord (n * d)) level m ambient none
  have h₄ := copyPowerTrace d hd input initialOutput (encodeWord n) (encodeWord (n * d))
    level m ambient none
  have h₅ := subtractTrace d hd input initialOutput (encodeWord (n * d)) (encodeWord m)
    level n m (PreprocessingLevels.le_paddedSize n) ambient none
  have h₆ := rowsTrace hd t (PreprocessingLevels.le_paddedSize n) input (encodeWord m) level ambient
  have h₇ := cleanupTrace d hd input
    (PortTables.tableBits (PreprocessingPaddingTables.pad t (PreprocessingLevels.le_paddedSize n)))
    level m ambient
  have h := appendTrace _ (appendTrace _ (appendTrace _ (appendTrace _
    (appendTrace _ (appendTrace _ h₁ h₂) h₃) h₄) h₅) h₆) h₇
  have ht : totalTime t =
      (((((MachineTableSplit.exactSteps n (n * d) rows +
        MachineCeilingPower.totalTime ExpanderFamily.growth n) + (4 * (m + 1) + 2)) +
        (2 * (m + 2))) + (2 * n + 2)) + rowTime (m := m) t) + cleanupTime d m := by
    dsimp only [totalTime, otherTime, m, rows]
    omega
  rw [ht]
  exact h

theorem totalTime_le {n d : Nat} (hd : 0 < d) (t : PortTables.Table n d) :
    totalTime t ≤ (timePolynomial d).eval (PortTables.tableBits t).length := by
  have hrow := (MachinePaddingTable.execution t (PreprocessingLevels.le_paddedSize n) hd).steps_le_m
  change rowTime (m := PreprocessingLevels.paddedSize n) t ≤
    (MachinePaddingCertificate.timePolynomial d).eval
      (MachinePaddingBounds.inputSize n (n * d) (PreprocessingLevels.paddedSize n - n)
        (MachinePaddingTable.initialOutput (m := PreprocessingLevels.paddedSize n) t)) at hrow
  have hmono := natPolynomial_eval_mono (MachinePaddingCertificate.timePolynomial d) (intermediate_bound t)
  have h := Nat.add_le_add (otherTime_le t) (hrow.trans hmono)
  simpa only [totalTime, timePolynomial, Polynomial.eval_add, Polynomial.eval_comp] using h

/-- Complete runtime certificate from the original input alone, with an
explicit clean final frame and an actual polynomial in its encoded length. -/
def vertexPaddingInTime {σ : Type} {n d : Nat} (hd : 0 < d) (t : PortTables.Table n d)
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step (program d hd))
      ⟨some (.splitCode .copyFirst), ((ambient, false), register),
        memory (PortTables.tableBits t) [] [] [] [] [] [] []⟩
      (some ⟨none, ((ambient, false), none),
        memory (PortTables.tableBits t)
          (PortTables.tableBits (PreprocessingPaddingTables.pad t (PreprocessingLevels.le_paddedSize n)))
          [] [] [] (encodeWord (PreprocessingLevels.boundedLevel n)) [] []⟩)
      ((timePolynomial d).eval (PortTables.tableBits t).length) where
  steps := totalTime t
  evals_in_steps := vertexPaddingTrace hd t ambient register
  steps_le_m := totalTime_le hd t

end UniqueGamesTheorem.Foundations.Complexity.MachineVertexPadding

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachinePaddedOverlay
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq
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

namespace UniqueGamesTheorem.Foundations.Complexity.MachinePaddedOverlay

open Turing MachineComposition MachineCloudPadding
open PCP

variable {d : Nat}

/-- The actual padding execution stops at the family entry on the same
physical level stack, and preserves both inactive finite states. -/
noncomputable def paddingInTime (H : BaseTable) {n d : Nat} (hd : 0 < d) (t : PortTables.Table n d) :
    StateTransition.EvalsToInTime (TM2.step (program H d hd))
      ⟨some main, clean H d hd, initialTapes t⟩
      (some ⟨some familyEntry, clean H d hd, paddedTapes t⟩)
      ((MachineVertexPadding.timePolynomial d).eval (PortTables.tableBits t).length) := by
  let ambient := (MachineExpanderFamily.initialState MachineExpanderFamily.baseDegree_positive H (),
    MachineOverlayTable.clean d overlayDegree hd overlayDegree_positive ())
  have run := placeExecution paddingTape paddingView paddingView_left paddingView_right
    paddingLabel (some familyEntry) (fun _ => []) (MachineVertexPadding.program d hd) (program H d hd)
    (fun _ => rfl) (MachineVertexPadding.vertexPaddingInTime hd t ambient none)
  simpa only [Placement.configuration, Placement.label, padding_initial_memory,
    padding_final_memory, initialTapes, paddedTapes, padded, main, clean, ambient] using run

/-- The complete three-phase program executes from the original serialized
input alone, with a polynomial bound in that input's full unary length. -/
noncomputable def execution (H : BaseTable) {n d : Nat} (hd : 0 < d)
    (t : PortTables.Table n d) :
    StateTransition.EvalsToInTime (TM2.step (program H d hd))
      ⟨some main, clean H d hd, initialTapes t⟩
      (some ⟨none, clean H d hd, finalTapes H t⟩)
      ((timePolynomial d).eval (PortTables.tableBits t).length) := by
  let first := paddingInTime H hd t
  let second := familyInTime H hd t
  let third := overlayInTime H hd t
  let firstTwo := StateTransition.EvalsToInTime.trans (TM2.step (program H d hd))
    _ _ _ _ _ first second
  let all := StateTransition.EvalsToInTime.trans (TM2.step (program H d hd))
    _ _ _ _ _ firstTwo third
  refine { toEvalsTo := all.toEvalsTo, steps_le_m := all.steps_le_m.trans ?_ }
  have hn := PortTables.vertices_le_tableBits_length t
  have hf := Nat.mul_le_mul_left MachineExpanderFamilyBounds.inputCoefficient
    (Nat.pow_le_pow_left (Nat.add_le_add_right hn 1) 5)
  have ho := natPolynomial_eval_mono (MachineOverlayTable.timePolynomial d overlayDegree)
    (archive_length_le H t)
  have h := Nat.add_le_add
    (Nat.add_le_add (Nat.le_refl ((MachineVertexPadding.timePolynomial d).eval
      (PortTables.tableBits t).length)) hf) ho
  simpa only [timePolynomial, familyPolynomial, Polynomial.eval_add, Polynomial.eval_comp,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

def machine (H : BaseTable) (d : Nat) (hd : 0 < d) : FinTM2 where
  K := Tape
  k₀ := .inl .original
  k₁ := .inr (.inr MachineOverlayTable.output)
  Γ := Alphabet
  Λ := Label d
  main := main
  σ := State d
  initialState := clean H d hd
  m := program H d hd

theorem initial_configuration (H : BaseTable) {n d : Nat} (hd : 0 < d)
    (t : PortTables.Table n d) :
    initList (machine H d hd) (PortTables.tableBits t) =
      ⟨some main, clean H d hd, initialTapes t⟩ := by
  have ht : (initList (machine H d hd) (PortTables.tableBits t)).stk = initialTapes t := by
    funext k
    rcases k with k | k
    · cases k <;> simp [initList, machine, initialTapes, memory, MachineVertexPadding.memory]
      rfl
    · rcases k with k | k
      · rcases k with k | k
        · rcases k with k | k <;> cases k <;>
            simp [initList, machine, initialTapes, memory]
        · cases k <;> simp [initList, machine, initialTapes, memory]
      · simp [initList, machine, initialTapes, memory]
  exact congrArg (TM2.Cfg.mk _ _) ht

theorem final_output (H : BaseTable) {n d : Nat} (hd : 0 < d)
    (t : PortTables.Table n d) :
    finalTapes H t (machine H d hd).k₁ =
      PortTables.inputBits (PreprocessingStageMaps.paddedOverlay H d ⟨n, t⟩) := by
  simp [finalTapes, machine, memory, PortTables.inputBits]

end UniqueGamesTheorem.Foundations.Complexity.MachinePaddedOverlay

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineRegularInternalRow
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.legalDecidable _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq
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

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularInternalRow

open Turing MachineComposition
open PCP
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)

variable {K Λ σ : Type} [DecidableEq K]

theorem emittedBits_eq_row (t : GraphTables.Table) (padding : Fin t.vertices → Nat)
    {q : Nat} (tables : ∀ v, ExpanderTables.Table
      (PreprocessingCloudIndex.cloudSize t v + padding v) q)
    (v : Fin t.vertices) (x : PreprocessingCloudIndex.PaddedCloud t padding v) (p : Fin q) :
    emittedBits q (PreprocessingRegularTables.vertexOrder t padding x.val).val
      (PreprocessingInternalRows.selectedIndex t padding v
        (PreprocessingInternalRows.localStep t padding tables v x p).1)
      (PreprocessingInternalRows.localStep t padding tables v x p).2.val =
        encodeWords (GraphTables.rowWords
          (PreprocessingInternalRows.row t padding tables v x p)) := by
  rw [MachineTableRows.rowBits_eq, PreprocessingInternalRows.row_tail,
    PreprocessingInternalRows.row_reverse_selectedIndex, PreprocessingInternalRows.row_relation]
  rfl

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
    fin_cases i
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
  exact joinTrace (joinTrace (joinTrace (joinTrace (joinTrace
    copyRun affineRun) initRun) rowRun) reverseRun) equalityRun

/-- The shared cloud-selector trace is preserved exactly by static tape,
register and alphabet transport. These transports add no transition. -/
theorem selectCloudTrace (t : GraphTables.Table) (v : Fin t.vertices)
    (i : Fin (PreprocessingCloudIndex.cloudSize t v))
    (extra : SelectExtraTape → List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step selectProgram))^[MachineCloudSelect.cloudSelectSteps t v i []]
      (some ⟨some (.inl (.inr .initialize_)), selectCleanState ambient register,
        selectToBoolTapes (MachineEmbedding.tapes
          (MachineCloudSelect.memory (GraphTables.tableBits t) []
            (MachineCloudSelect.queryWord v.val i.val []) [] [] [] []) extra)⟩) =
      some ⟨some (.inr (.cleanup 0)), selectCleanState ambient none,
        selectToBoolTapes (MachineEmbedding.tapes
          (MachineCloudSelect.memory (GraphTables.tableBits t) []
            (MachineCloudSelect.queryWord v.val i.val []) [] [] []
            (encodeWord (PreprocessingCloudIndex.cloudSelect t v i).val.val)) extra)⟩ := by
  let source := MachineCloudSelect.program (σ := σ)
  let more := fun c => MachineStateEquiv.statement (selectStateEquiv σ).symm
    (MachineAlphabetTransport.statement selectAlphabet_eq.symm (selectControl (σ := σ) c))
  let caller := MachineEmbedding.program (some (.inr (.cleanup 0))) source more
  let embed := MachineEmbedding.configuration (K := MachineCloudSelect.Tape)
    (Γ := MachineCloudSelect.Alphabet) (σ := MachineCloudSelect.State σ)
    (some (Sum.inr (SelectControl.cleanup 0)) : Option SelectLabel) () extra
  have sourceRun := MachineCloudSelect.cloudSelectTrace t v i [] [] ambient register
  have lifted := liftSuccessfulTrace (TM2.step source) (TM2.step caller) embed
    (MachineEmbedding.step_simulation (some (.inr (.cleanup 0))) () extra source more)
    _ _ _ sourceRun
  have transported := MachineStateEquiv.trace (selectStateEquiv σ) caller _ _ _ lifted
  have boolean := MachineAlphabetTransport.successfulTrace selectAlphabet_eq
    (MachineStateEquiv.program (selectStateEquiv σ) caller) _ _ _ transported
  simp only [embed, MachineCloudSelect.cfg, MachineStateEquiv.configuration, MachineEmbedding.configuration,
    MachineEmbedding.label, selectStateEquiv, List.append_nil,
    MachineAlphabetTransport.configuration_mk, ← selectToBoolTapes_eq] at boolean
  convert boolean using 1 <;> rfl

theorem selectOldTrace (t : GraphTables.Table) (v : Fin t.vertices)
    (i : Fin (PreprocessingCloudIndex.cloudSize t v)) (o : Nat) (ambient : σ) :
    (advance (TM2.step selectProgram))^[oldSelectSteps t v i]
      (some ⟨some (.inr (.copy .oldLocal .seed)), selectCleanState ambient none,
        selectMemory (GraphTables.tableBits t) i.val v.val
          (PreprocessingCloudIndex.cloudSize t v) o t.darts [] [] [] [] [] []⟩) =
      some ⟨none, selectCleanState ambient none,
        selectMemory (GraphTables.tableBits t) i.val v.val
          (PreprocessingCloudIndex.cloudSize t v) o t.darts []
          (encodeWord (PreprocessingCloudIndex.cloudSelect t v i).val.val) [] [] [] []⟩ := by
  let graph := GraphTables.tableBits t
  let k := PreprocessingCloudIndex.cloudSize t v
  have hi := selectCopyTrace .oldLocal
    (selectMemory graph i.val v.val k o t.darts [] [] [] [] [] [])
    i.val rfl rfl ambient none
  simp only [copyDestination, afterCopy, selectMemory_query, update_selectMemory_query, List.append_nil] at hi
  have hv := selectCopyTrace .oldOwner
    (selectMemory graph i.val v.val k o t.darts (encodeWord i.val) [] [] [] [] [])
    v.val rfl rfl ambient none
  simp only [copyDestination, afterCopy, selectMemory_query, update_selectMemory_query] at hv
  have hc := selectCloudTrace t v i (selectExtraMemory i.val v.val k o t.darts [] [] [] [])
    ambient none
  have hq : MachineCloudSelect.queryWord v.val i.val [] =
      encodeWord v.val ++ encodeWord i.val := by
    simp only [MachineCloudSelect.queryWord, MachineCloudRank.queryWord, List.append_nil]
  change (advance (TM2.step selectProgram))^[MachineCloudSelect.cloudSelectSteps t v i []]
    (some ⟨some (.inl (.inr .initialize_)), selectCleanState ambient none,
      selectMemory graph i.val v.val k o t.darts
        (MachineCloudSelect.queryWord v.val i.val []) [] [] [] [] []⟩) =
    some ⟨some (.inr (.cleanup 0)), selectCleanState ambient none,
      selectMemory graph i.val v.val k o t.darts
        (MachineCloudSelect.queryWord v.val i.val [])
        (encodeWord (PreprocessingCloudIndex.cloudSelect t v i).val.val) [] [] [] []⟩ at hc
  rw [hq] at hc
  have hd := selectCleanupTrace graph i.val v.val k o t.darts
    (encodeWord v.val ++ encodeWord i.val)
    (encodeWord (PreprocessingCloudIndex.cloudSelect t v i).val.val) [] [] [] [] ambient
  have hn : (encodeWord v.val ++ encodeWord i.val).length + ([] : List Bool).length + ([] : List Bool).length +
      ([] : List Bool).length + ([] : List Bool).length + 5 = v.val + i.val + 7 := by
    simp only [List.length_append, encodeWord_length, List.length_nil]
    omega
  rw [hn] at hd
  exact joinTrace (joinTrace (joinTrace hi hv) hc) hd

/-- The entire actual selector program, with both runtime branches and the
same clean final frame. Metadata values are premises about physical tapes. -/
theorem selectionTrace (t : GraphTables.Table) (padding : Fin t.vertices → Nat)
    (v : Fin t.vertices) (i : Fin (PreprocessingCloudIndex.cloudSize t v + padding v))
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step selectProgram))^[selectionSteps t padding v i]
      (some ⟨some (.inr (.compare .scan)), selectCleanState ambient register,
        selectMemory (GraphTables.tableBits t) i.val v.val
          (PreprocessingCloudIndex.cloudSize t v)
          (PreprocessingPaddingOffsets.offset padding v.val) t.darts [] [] [] [] [] []⟩) =
      some ⟨none, selectCleanState ambient none,
        selectMemory (GraphTables.tableBits t) i.val v.val
          (PreprocessingCloudIndex.cloudSize t v)
          (PreprocessingPaddingOffsets.offset padding v.val) t.darts []
          (encodeWord (PreprocessingInternalRows.selectedIndex t padding v i)) [] [] [] []⟩ := by
  have hc := selectComparisonTrace
    (selectMemory (GraphTables.tableBits t) i.val v.val
      (PreprocessingCloudIndex.cloudSize t v)
      (PreprocessingPaddingOffsets.offset padding v.val) t.darts [] [] [] [] [] [])
    i.val (PreprocessingCloudIndex.cloudSize t v) rfl rfl rfl rfl ambient register
  by_cases hi : i.val < PreprocessingCloudIndex.cloudSize t v
  · simp only [ite_eq_left hi] at hc
    have hb := selectOldTrace t v ⟨i.val, hi⟩
      (PreprocessingPaddingOffsets.offset padding v.val) ambient
    simpa only [selectionSteps, dite_eq_left hi,
      PreprocessingInternalRows.selectedIndex_old t padding v i hi] using joinTrace hc hb
  · simp only [ite_eq_right hi] at hc
    have hb := selectDummyTrace (GraphTables.tableBits t) i.val v.val
      (PreprocessingCloudIndex.cloudSize t v)
      (PreprocessingPaddingOffsets.offset padding v.val) t.darts (Nat.le_of_not_gt hi) ambient
    simpa only [selectionSteps, dite_eq_right hi,
      PreprocessingInternalRows.selectedIndex_dummy t padding v i (Nat.le_of_not_gt hi)]
      using joinTrace hc hb

theorem coreSelectionTrace (q : Nat) (positive : 0 < q) (p : Fin q)
    (labels : CoreLabel q → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : CoreTape => Bool) Λ (CoreState σ q))
    (code : ∀ l, program (labels l) = coreInstruction q positive p labels exit l)
    (t : GraphTables.Table) (padding : Fin t.vertices → Nat) (v : Fin t.vertices)
    (j : Fin (PreprocessingCloudIndex.cloudSize t v + padding v))
    (x i : Nat) (rotor output query scan flat returnPort : List Bool) (ambient : σ) :
    (advance (TM2.step program))^[selectionSteps t padding v j]
      (some ⟨some (labels (.select (.inr (.compare .scan)))), coreInitialState q positive ambient,
        coreMemory (GraphTables.tableBits t) x v.val i (PreprocessingCloudIndex.cloudSize t v)
          (PreprocessingPaddingOffsets.offset padding v.val) t.darts rotor output query scan flat
          (encodeWord j.val) returnPort []⟩) =
      some ⟨some (labels (.finish .seedReturn)), coreInitialState q positive ambient,
        coreMemory (GraphTables.tableBits t) x v.val i (PreprocessingCloudIndex.cloudSize t v)
          (PreprocessingPaddingOffsets.offset padding v.val) t.darts rotor output query scan flat
          (encodeWord j.val) returnPort
          (encodeWord (PreprocessingInternalRows.selectedIndex t padding v j))⟩ := by
  let e := coreSelectStateEquiv σ q
  let state := (ambient, (MachineFixedBlockMap.emptyBuffer 4096,
    MachineFixedDivMod.residue q positive 0))
  have sourceRun := selectionTrace t padding v j state none
  have moved := MachineStateEquiv.trace e selectProgram _ _ _ sourceRun
  let base := coreMemory (GraphTables.tableBits t) x v.val i
    (PreprocessingCloudIndex.cloudSize t v)
    (PreprocessingPaddingOffsets.offset padding v.val) t.darts rotor output query scan flat
    (encodeWord j.val) returnPort []
  have placed := MachineCloudPadding.Placement.trace coreSelectTape coreSelectView
    coreSelectView_left coreSelectView_right (fun l => labels (.select l))
    (some (labels (.finish .seedReturn))) base
    (MachineStateEquiv.program e selectProgram) program (fun l => code (.select l))
    _ _ _ moved
  simp only [MachineCloudPadding.Placement.configuration, MachineCloudPadding.Placement.label,
    MachineStateEquiv.configuration, base, coreSelectFrame] at placed
  convert placed using 1 <;> rfl

theorem coreFinishTrace (q : Nat) (positive : 0 < q) (p : Fin q)
    (labels : CoreLabel q → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : CoreTape => Bool) Λ (CoreState σ q))
    (code : ∀ l, program (labels l) = coreInstruction q positive p labels exit l)
    (graph : List Bool) (x v i k o m j r z : Nat)
    (rotor output query scan flat : List Bool) (ambient : σ) :
    (advance (TM2.step program))^[finishSteps q x z r output.length]
      (some ⟨some (labels (.finish .seedReturn)), coreInitialState q positive ambient,
        coreMemory graph x v i k o m rotor output query scan flat
          (encodeWord j) (encodeWord r) (encodeWord z)⟩) =
      some ⟨some (labels (.cleanup 0)), coreInitialState q positive ambient,
        coreMemory graph x v i k o m rotor (output ++ emittedBits q x z r) query scan flat
          (encodeWord j) (encodeWord r) (encodeWord z)⟩ := by
  have h := finishTrace q coreFinishTapes coreFinishTapes_injective
    (fun l => labels (.finish l)) (some (labels (.cleanup 0))) program
    (fun l => code (.finish l))
    (coreMemory graph x v i k o m rotor output query scan flat
      (encodeWord j) (encodeWord r) (encodeWord z))
    x z r rfl rfl rfl rfl rfl rfl rfl
    (ambient, (MachineFixedBlockMap.emptyBuffer 4096,
      (MachineFixedDivMod.residue q positive 0, (false, MachineCloudSelect.Phase.checking)))) none
  change (advance (TM2.step program))^[finishSteps q x z r output.length]
    (some ⟨some (labels (.finish .seedReturn)), coreInitialState q positive ambient,
      coreMemory graph x v i k o m rotor output query scan flat
        (encodeWord j) (encodeWord r) (encodeWord z)⟩) =
    some ⟨some (labels (.cleanup 0)), coreInitialState q positive ambient,
      Function.update (coreMemory graph x v i k o m rotor output query scan flat
        (encodeWord j) (encodeWord r) (encodeWord z)) (8 : CoreTape)
        (output ++ emittedBits q x z r)⟩ at h
  rw [coreMemory_update_output] at h
  exact h

/-- One full actual internal row of the serialized regularization, including
the physical rotor lookup, both destination cases, full equality predicate,
row append and complete reusable cleanup frame. -/
theorem coreTrace (q : Nat) (positive : 0 < q) (p : Fin q)
    (labels : CoreLabel q → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : CoreTape => Bool) Λ (CoreState σ q))
    (code : ∀ l, program (labels l) = coreInstruction q positive p labels exit l)
    (t : GraphTables.Table) (padding : Fin t.vertices → Nat)
    (tables : ∀ v, ExpanderTables.Table (PreprocessingCloudIndex.cloudSize t v + padding v) q)
    (v : Fin t.vertices) (x : PreprocessingCloudIndex.PaddedCloud t padding v)
    (output : List Bool) (ambient : σ) :
    (advance (TM2.step program))^[coreSteps t padding tables v x p output.length]
      (some ⟨some (labels (coreEntry q)), coreInitialState q positive ambient,
        coreInputTapes t padding tables v x output⟩) =
      some ⟨exit, coreInitialState q positive ambient,
        coreInputTapes t padding tables v x
          (output ++ encodeWords (GraphTables.rowWords
            (PreprocessingInternalRows.row t padding tables v x p)))⟩ := by
  let rank := PreprocessingCloudIndex.paddedCloudRank t padding v x
  let step := ExpanderTables.lookup (tables v) (rank, p)
  let z := PreprocessingInternalRows.selectedIndex t padding v step.1
  let X := (PreprocessingRegularTables.vertexOrder t padding x.val).val
  let o := PreprocessingPaddingOffsets.offset padding v.val
  let bits := encodeWords (ExpanderTableWords.rotationWords (tables v))
  let tailBits := encodeWords ((ExpanderTableWords.rotationWords (tables v)).drop
    (q * rank.val + p.val + 1))
  let graph := GraphTables.tableBits t
  let k := PreprocessingCloudIndex.cloudSize t v
  have hr := coreRotorTrace positive (tables v) rank p labels exit program code
    graph X v.val k o t.darts output ambient
  have hs := coreSelectionTrace q positive p labels exit program code t padding v step.1
    X rank.val bits output (encodeWord 0) tailBits (encodeWord 0) (encodeWord step.2.val) ambient
  have hf := coreFinishTrace q positive p labels exit program code
    graph X v.val rank.val k o t.darts step.1.val step.2.val z bits output
    (encodeWord 0) tailBits (encodeWord 0) ambient
  have hc := coreCleanupTrace q positive p labels exit program code
    (coreMemory graph X v.val rank.val k o t.darts bits
      (output ++ emittedBits q X z step.2.val)
      (encodeWord 0) tailBits (encodeWord 0) (encodeWord step.1.val)
      (encodeWord step.2.val) (encodeWord z))
    (ambient, (MachineFixedBlockMap.emptyBuffer 4096,
      (MachineFixedDivMod.residue q positive 0, (false, MachineCloudSelect.Phase.checking))))
  rw [coreCleanupSteps_memory, coreCleaned_memory] at hc
  have h := joinTrace (joinTrace (joinTrace hr hs) hf) hc
  have hbits : emittedBits q X z step.2.val =
      encodeWords (GraphTables.rowWords (PreprocessingInternalRows.row t padding tables v x p)) :=
    emittedBits_eq_row t padding tables v x p
  rw [hbits] at h
  exact h

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularInternalRow

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineRegularMetadata
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.legalDecidable _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual metadata preparation for an original regularized vertex. The
shared 27-tape row interface is preserved, with two explicit extra outputs
for padding count and geometric level. Family generation is a subsequent
stage and owns the rotor tape. -/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularMetadata

open Turing MachineComposition
open UniqueGamesTheorem.Foundations.PCP

variable {σ : Type}

/-- Fixed finite code. Original graph/global-index inputs are never replaced
by specification values; owner and rank queries are produced on the tapes. -/
def program : Label → TM2.Stmt Alphabet Label (State σ)
  | .owner l => MachineAffineLookup.instruction (.inl 1) ownerTapes 4098 2
      Label.owner (some .ownerClearQuery) l
  | .ownerClearQuery => MachineDrain.drain (.inl 9) .ownerClearQuery (some .ownerClearWork)
  | .ownerClearWork => MachineDrain.drain (.inl 10) .ownerClearWork (some .copyXFirst)
  | .copyXFirst => Reduction.MachineTransfer.loopAt (.inl 1) (.inl 10) id false
      .copyXFirst (some .copyXSecond)
  | .copyXSecond => MachineCopy.forkLoop (.inl 10) (.inl 1) (.inl 9) false
      .copyXSecond (some .copyOwnerFirst)
  | .copyOwnerFirst => Reduction.MachineTransfer.loopAt (.inl 2) (.inl 10) id false
      .copyOwnerFirst (some .copyOwnerSecond)
  | .copyOwnerSecond => MachineCopy.forkLoop (.inl 10) (.inl 2) (.inl 9) false
      .copyOwnerSecond (some .rankInit)
  | .rankInit => .push (.inl 3) (fun _ => false) (.goto fun _ => .rank .queryFirst)
  | .rank l => MachineCloudPadding.Placement.statement rankTape Label.rank
      (some .rankClearQuery) (MachineCloudRank.rankProgram l)
  | .rankClearQuery => MachineDrain.drain (.inl 9) .rankClearQuery (some .rankClearWork)
  | .rankClearWork => MachineDrain.drain (.inl 10) .rankClearWork (some .rankClearFuel)
  | .rankClearFuel => MachineDrain.drain (.inl 12) .rankClearFuel (some (.prefixCode .init))
  | .prefixCode l => MachineCloudPadding.Placement.statement prefixTape Label.prefixCode
      (some .prefixClearQuery) (MachineCloudPrefix.program l)
  | .prefixClearQuery => MachineDrain.drain (.inl 9) .prefixClearQuery (some .prefixClearFuel)
  | .prefixClearFuel => MachineDrain.drain (.inl 18) .prefixClearFuel (some (.cloud .init))
  | .cloud l => MachineCloudPadding.Placement.statement cloudTape Label.cloud none
      (MachineCloudPadding.program l)

/-- Common owner-based stage for original and dummy vertices. The count,
padding, and level are actual outputs of the checked physical cloud scan. -/
theorem cloudTrace (t : GraphTables.Table) (v : Fin t.vertices) (data : Data)
    (htable : data.table = GraphTables.tableBits t) (howner : data.owner = encodeWord v.val)
    (hcount : data.count = []) (hpadding : data.padding = []) (hlevel : data.level = [])
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[MachineCloudPadding.totalTime t v]
      (some (cfg (some (.cloud .init)) data ambient register)) =
      some (cfg none (cloudData t v data) ambient none) := by
  have raw := MachineCloudPadding.cloudPaddingTrace t v [] ambient register
  simp only [List.append_nil] at raw
  have placed := MachineCloudPadding.Placement.trace cloudTape cloudView cloudView_left cloudView_right
    Label.cloud none (frame data) MachineCloudPadding.program program (fun _ => rfl)
    (MachineCloudPadding.totalTime t v) _ _ raw
  have hstart : MachineCloudPadding.Placement.tapes cloudView
      (MachineCloudPadding.memory (GraphTables.tableBits t) (encodeWord v.val)
        [] [] [] [] [] [] [] []) (frame data) = frame data := by
    funext j
    cases j with
    | inl j => fin_cases j <;>
        simp_all [MachineCloudPadding.Placement.tapes, cloudView, frame, MachineCloudPadding.memory]
    | inr j => cases j <;>
        simp_all [MachineCloudPadding.Placement.tapes, cloudView, frame, MachineCloudPadding.memory]
  have hfinish : MachineCloudPadding.Placement.tapes cloudView
      (MachineCloudPadding.memory (GraphTables.tableBits t) (encodeWord v.val)
        (encodeWord (PreprocessingCloudIndex.cloudSize t v)) [] [] []
        (encodeWord (MachineCloudPadding.padding (PreprocessingCloudIndex.cloudSize t v)))
        (encodeWord (PreprocessingLevels.boundedLevel (PreprocessingCloudIndex.cloudSize t v))) [] [])
      (frame data) = frame (cloudData t v data) := by
    funext j
    cases j with
    | inl j => fin_cases j <;>
        simp_all [MachineCloudPadding.Placement.tapes, cloudView, frame, cloudData, MachineCloudPadding.memory]
    | inr j => cases j <;>
        simp_all [MachineCloudPadding.Placement.tapes, cloudView, frame, cloudData, MachineCloudPadding.memory]
  simpa only [MachineCloudPadding.Placement.configuration, MachineCloudPadding.Placement.label,
    hstart, hfinish, cfg] using placed

theorem drainAt (source : Tape) (again : Label) (exit : Option Label)
    (code : program (σ := σ) again = MachineDrain.drain source again exit)
    (base : Tape → List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[(base source).length + 1]
      (some ⟨some again, ((ambient, false), register), base⟩) =
      some ⟨exit, ((ambient, false), none), Function.update base source []⟩ := by
  simpa only [Function.update_eq_self] using
    MachineDrain.drainTrace source again exit program code base (base source)
      (ambient, false) register

def prefixSteps (t : GraphTables.Table) (v : Fin t.vertices) : Nat :=
  MachineCloudPrefix.totalTime t v.val [] + (v.val + 2) + 2

/-- The actual padding-prefix scan, followed by removal of its copied query
and exhausted fuel. Every other core field is preserved. -/
theorem prefixTrace (t : GraphTables.Table) (v : Fin t.vertices) (data : Data)
    (htable : data.table = GraphTables.tableBits t) (howner : data.owner = encodeWord v.val)
    (hoffset : data.offset = []) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[prefixSteps t v]
      (some (cfg (some (.prefixCode .init)) data ambient register)) =
      some (cfg (some (.cloud .init)) (prefixData t v data) ambient none) := by
  have raw := MachineCloudPrefix.prefixTrace t v.val v.isLt.le [] ambient register
  simp only [List.append_nil] at raw
  let mid := MachineCloudPadding.Placement.tapes prefixView
    (MachineCloudPrefix.frame (GraphTables.tableBits t) (encodeWord v.val) [] [] []
      (encodeWord v.val) (encodeWord 0)
      (encodeWord (PreprocessingPaddingOffsets.offset
        (PreprocessingRegularTables.padding t) v.val))) (frame data)
  have placed := MachineCloudPadding.Placement.trace prefixTape prefixView prefixView_left
    prefixView_right Label.prefixCode (some .prefixClearQuery) (frame data)
    MachineCloudPrefix.program program (fun _ => rfl)
    (MachineCloudPrefix.totalTime t v.val []) _ _ raw
  have hstart : MachineCloudPadding.Placement.tapes prefixView
      (MachineCloudPrefix.frame (GraphTables.tableBits t) [] [] [] [] (encodeWord v.val) [] [])
      (frame data) = frame data := by
    funext j
    cases j with
    | inl j => fin_cases j <;>
        simp [htable, howner, hoffset, MachineCloudPadding.Placement.tapes, prefixView, frame,
          MachineCloudPrefix.frame, MachineCloudPrefix.memory, MachineCloudPadding.memory]
    | inr j => cases j <;> rfl
  have phase : (advance (TM2.step program))^[MachineCloudPrefix.totalTime t v.val []]
      (some (cfg (some (.prefixCode .init)) data ambient register)) =
      some ⟨some .prefixClearQuery, ((ambient, false), none), mid⟩ := by
    simpa only [MachineCloudPadding.Placement.configuration,
      MachineCloudPadding.Placement.label, hstart, cfg, mid] using placed
  have first := drainAt (.inl 9) .prefixClearQuery (some .prefixClearFuel) rfl mid ambient none
  have second := drainAt (.inl 18) .prefixClearFuel (some (.cloud .init)) rfl
    (Function.update mid (.inl 9) []) ambient none
  have hquery : (mid (.inl 9)).length + 1 = v.val + 2 := by
    simp [mid, MachineCloudPadding.Placement.tapes, prefixView, MachineCloudPrefix.frame, MachineCloudPrefix.memory,
      MachineCloudPadding.memory, encodeWord_length]
  have hfuel : ((Function.update mid (.inl 9) []) (.inl 18)).length + 1 = 2 := by
    simp [mid, MachineCloudPadding.Placement.tapes, prefixView, MachineCloudPrefix.frame, MachineCloudPrefix.memory,
      encodeWord_length]
  have hfinish : Function.update (Function.update mid (.inl 9) []) (.inl 18) [] =
      frame (prefixData t v data) := by
    funext j
    cases j with
    | inl j => fin_cases j <;>
        simp [htable, howner, mid, MachineCloudPadding.Placement.tapes, prefixView, frame, prefixData,
          MachineCloudPrefix.frame, MachineCloudPrefix.memory, MachineCloudPadding.memory]
    | inr j => cases j <;> rfl
  rw [hquery] at first
  rw [hfuel, hfinish] at second
  exact join_trace (join_trace phase first) second

/-- The owner is read from its actual field at `4098*x+2`; arithmetic, table
copy, lookup, and cleanup all execute in the finite machine. -/
theorem ownerTrace (t : GraphTables.Table) (e : Fin t.darts) (data : Data)
    (htable : data.table = GraphTables.tableBits t)
    (hindex : data.globalIndex = encodeWord e.val) (howner : data.owner = [])
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[ownerSteps t e]
      (some (cfg (some (.owner .seed)) data ambient register)) =
      some (cfg (some .copyXFirst) (ownerData t e data) ambient none) := by
  have distinct : Function.Injective ownerTapes := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [ownerTapes]
  have outside : ∀ i, (.inl 1 : Tape) ≠ ownerTapes i := by
    intro i
    fin_cases i <;> decide
  let mid := MachineAffineLookup.finalTapes ownerTapes (frame data)
    (GraphTables.tableWords t) (4098 * e.val + 2) t.rows[e].tail.val
  have phase : (advance (TM2.step program))^[
      MachineAffineLookup.steps (GraphTables.tableWords t) e.val 4098 2]
      (some (cfg (some (.owner .seed)) data ambient register)) =
      some ⟨some .ownerClearQuery, ((ambient, false), none), mid⟩ := by
    exact MachineAffineLookup.affineLookupTrace (.inl 1) ownerTapes distinct outside 4098 2
      Label.owner (some .ownerClearQuery) program (fun _ => rfl) (frame data)
      (GraphTables.tableWords t) htable rfl e.val []
      (by change data.globalIndex = encodeWord e.val ++ [];
          simpa only [List.append_nil] using hindex)
      t.rows[e].tail.val (selected_owner t e) (ambient, false) register
  have first := drainAt (.inl 9) .ownerClearQuery (some .ownerClearWork) rfl mid ambient none
  have second := drainAt (.inl 10) .ownerClearWork (some .copyXFirst) rfl
    (Function.update mid (.inl 9) []) ambient none
  have hquery : (mid (.inl 9)).length + 1 = 2 := by
    simp [mid, MachineAffineLookup.finalTapes, MachinePreservingLookup.finalTapes,
      MachineLookup.tapes, ownerTapes, frame, encodeWord_length]
  have hwork : (Function.update mid (.inl 9) []) (.inl 10) = ownerRemainder t e := by
    simp [mid, MachineAffineLookup.finalTapes, MachinePreservingLookup.finalTapes,
      MachineLookup.tapes, ownerTapes, frame, ownerRemainder]
  have hfinish : Function.update (Function.update mid (.inl 9) []) (.inl 10) [] =
      frame (ownerData t e data) := by
    funext j
    cases j with
    | inl j => fin_cases j <;>
        simp [howner, mid, MachineAffineLookup.finalTapes, MachinePreservingLookup.finalTapes,
          MachineLookup.tapes, ownerTapes, frame, ownerData]
    | inr j => cases j <;> rfl
  rw [hquery] at first
  rw [hwork, hfinish] at second
  exact join_trace (join_trace phase first) second

/-- Two preserving copy loops physically create `[owner,x]`; a transition
then initializes the unary result counter. -/
theorem queryTrace (data : Data) (v x : Nat)
    (howner : data.owner = encodeWord v) (hindex : data.globalIndex = encodeWord x)
    (hrank : data.localRank = []) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[querySteps v x]
      (some (cfg (some .copyXFirst) data ambient register)) =
      some ⟨some (.rank .queryFirst), ((ambient, false), none), queryFrame data v x⟩ := by
  let first := Function.update (frame data) (.inl 9) data.globalIndex
  let second := Function.update first (.inl 9) (data.owner ++ data.globalIndex)
  have copyX := MachineCopy.copyTrace (.inl 1 : Tape) (.inl 9) (.inl 10)
    (by decide) (by decide) (by decide) false Label.copyXFirst Label.copyXSecond
    (some .copyOwnerFirst) program rfl rfl (frame data) rfl (ambient, false) register
  have copyOwner := MachineCopy.copyTrace (.inl 2 : Tape) (.inl 9) (.inl 10)
    (by decide) (by decide) (by decide) false Label.copyOwnerFirst Label.copyOwnerSecond
    (some .rankInit) program rfl rfl first (by simp [first, frame]) (ambient, false) none
  have firstRun : (advance (TM2.step program))^[2 * (x + 2)]
      (some (cfg (some .copyXFirst) data ambient register)) =
      some ⟨some .copyOwnerFirst, ((ambient, false), none), first⟩ := by
    simpa only [frame_index, frame_query_empty, hindex, encodeWord_length,
      List.append_nil, cfg, first] using copyX
  have secondRun : (advance (TM2.step program))^[2 * (v + 2)]
      (some ⟨some .copyOwnerFirst, ((ambient, false), none), first⟩) =
      some ⟨some .rankInit, ((ambient, false), none), second⟩ := by
    simpa [first, frame, howner, encodeWord_length, second] using copyOwner
  have init : (advance (TM2.step program))^[1]
      (some ⟨some .rankInit, ((ambient, false), none), second⟩) =
      some ⟨some (.rank .queryFirst), ((ambient, false), none), queryFrame data v x⟩ := by
    have ht : Function.update second (.inl 3) (false :: second (.inl 3)) =
        queryFrame data v x := by
      funext j
      cases j with
      | inl j => fin_cases j <;>
          simp_all [queryFrame, second, first, frame, rankQuery,
            MachineCloudRank.queryWord, encodeWord]
      | inr j => cases j <;> rfl
    simp only [Function.iterate_one, advance_some, TM2.step, program, TM2.stepAux, ht]
  exact join_trace (join_trace firstRun secondRun) init

/-- Rank is computed by physically scanning earlier original rows, with the
fresh query and copied scan/fuel all removed before the next phase. -/
theorem rankTrace (t : GraphTables.Table) (v : Fin t.vertices)
    (e : DegreeReplacement.Cloud (GraphTables.semantics t) v) (data : Data)
    (htable : data.table = GraphTables.tableBits t)
    (howner : data.owner = encodeWord v.val) (hindex : data.globalIndex = encodeWord e.val.val)
    (hrank : data.localRank = []) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[rankSteps t v e]
      (some (cfg (some .copyXFirst) data ambient register)) =
      some (cfg (some (.prefixCode .init)) (rankData t v e data) ambient none) := by
  have query := queryTrace data v.val e.val.val howner hindex hrank ambient register
  have raw := MachineCloudRank.cloudRankTrace t v e [] [] ambient none
  simp only [List.append_nil] at raw
  let mid := MachineCloudPadding.Placement.tapes rankView
    (MachineCloudCount.memory (GraphTables.tableBits t) (rankRemainder t v e)
      (rankQuery v.val e.val.val) []
      (encodeWord (PreprocessingCloudIndex.cloudRank t v e).val) (encodeWord 0)) (frame data)
  have placed := MachineCloudPadding.Placement.trace rankTape rankView rankView_left
    rankView_right Label.rank (some .rankClearQuery) (frame data)
    MachineCloudRank.rankProgram program (fun _ => rfl)
    (MachineCloudRank.rankSteps t.vertices t.darts v.val e.val.val (MachineCloudCount.tableRows t) [])
    _ _ raw
  have hstart : MachineCloudPadding.Placement.tapes rankView
      (MachineCloudCount.memory (GraphTables.tableBits t) []
        (rankQuery v.val e.val.val) [] (encodeWord 0) []) (frame data) =
      queryFrame data v.val e.val.val := by
    funext j
    cases j with
    | inl j => fin_cases j <;>
        simp_all [MachineCloudPadding.Placement.tapes, rankView, frame,
          queryFrame, MachineCloudCount.memory]
    | inr j => cases j <;> rfl
  simp only [rankQuery] at hstart
  have phase : (advance (TM2.step program))^[
      MachineCloudRank.rankSteps t.vertices t.darts v.val e.val.val (MachineCloudCount.tableRows t) []]
      (some ⟨some (.rank .queryFirst), ((ambient, false), none), queryFrame data v.val e.val.val⟩) =
      some ⟨some .rankClearQuery, ((ambient, false), none), mid⟩ := by
    simpa only [MachineCloudPadding.Placement.configuration, MachineCloudPadding.Placement.label,
      hstart, mid, rankQuery, rankRemainder] using placed
  have first := drainAt (.inl 9) .rankClearQuery (some .rankClearWork) rfl mid ambient none
  have second := drainAt (.inl 10) .rankClearWork (some .rankClearFuel) rfl
    (Function.update mid (.inl 9) []) ambient none
  have third := drainAt (.inl 12) .rankClearFuel (some (.prefixCode .init)) rfl
    (Function.update (Function.update mid (.inl 9) []) (.inl 10) []) ambient none
  have hquery : mid (.inl 9) = rankQuery v.val e.val.val := rfl
  have hwork : Function.update mid (.inl 9) [] (.inl 10) = rankRemainder t v e := by
    simp [mid, MachineCloudPadding.Placement.tapes, rankView, MachineCloudCount.memory]
  have hfuel : ((Function.update (Function.update mid (.inl 9) []) (.inl 10) [])
      (.inl 12)).length + 1 = 2 := by
    simp [mid, MachineCloudPadding.Placement.tapes, rankView, MachineCloudCount.memory,
      encodeWord_length]
  have hfinish : Function.update
      (Function.update (Function.update mid (.inl 9) []) (.inl 10) []) (.inl 12) [] =
      frame (rankData t v e data) := by
    funext j
    cases j with
    | inl j => fin_cases j <;>
        simp [mid, MachineCloudPadding.Placement.tapes, rankView, frame, rankData,
          MachineCloudCount.memory, htable]
    | inr j => cases j <;> rfl
  rw [hquery] at first
  rw [hwork] at second
  rw [hfuel, hfinish] at third
  exact join_trace (join_trace (join_trace (join_trace query phase) first) second) third

def totalTime (t : GraphTables.Table) (e : Fin t.darts) : Nat :=
  ownerSteps t e + rankSteps t t.rows[e].tail (originalMember t e) +
    prefixSteps t t.rows[e].tail + MachineCloudPadding.totalTime t t.rows[e].tail

/-- Full original-vertex metadata preparation. Inputs and all row/output
fields are preserved, results occupy their agreed physical tapes, and every
one of the eighteen core work tapes is empty at return. -/
theorem originalTrace (t : GraphTables.Table) (e : Fin t.darts) (data : Data)
    (htable : data.table = GraphTables.tableBits t)
    (hindex : data.globalIndex = encodeWord e.val)
    (howner : data.owner = []) (hrank : data.localRank = []) (hcount : data.count = [])
    (hoffset : data.offset = []) (hpadding : data.padding = []) (hlevel : data.level = [])
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[totalTime t e]
      (some (cfg (some (.owner .seed)) data ambient register)) =
      some (cfg none (originalData t e data) ambient none) := by
  have own := ownerTrace t e data htable hindex howner ambient register
  have rank := rankTrace t t.rows[e].tail (originalMember t e) (ownerData t e data)
    htable rfl hindex hrank ambient none
  have pref := prefixTrace t t.rows[e].tail
    (rankData t t.rows[e].tail (originalMember t e) (ownerData t e data))
    htable rfl hoffset ambient none
  have cloud := cloudTrace t t.rows[e].tail
    (prefixData t t.rows[e].tail
      (rankData t t.rows[e].tail (originalMember t e) (ownerData t e data)))
    htable rfl hcount hpadding hlevel ambient none
  exact join_trace (join_trace (join_trace own rank) pref) cloud

theorem totalTime_le (t : GraphTables.Table) (e : Fin t.darts) :
    totalTime t e ≤ timePolynomial.eval (GraphTables.tableBits t).length := by
  let v := t.rows[e].tail
  let c := originalMember t e
  let N := (GraphTables.tableBits t).length
  have hn := GraphTables.vertices_le_tableBits_length t
  have hm := GraphTables.darts_le_tableBits_length t
  have hv : v.val < N := lt_of_lt_of_le v.isLt hn
  have hx : e.val ≤ N := e.isLt.le.trans hm
  have ownerBound := MachineAffineLookup.steps_le (GraphTables.tableWords t)
    e.val 4098 2 t.rows[e].tail.val (selected_owner t e)
  have ownerRest := ownerRemainder_length_le t e
  have rankBound := MachineCloudRank.rankSteps_le t.vertices t.darts v.val e.val
    (MachineCloudCount.tableRows t) []
  rw [MachineCloudCount.tableRows_input] at rankBound
  have rankRest := rankRemainder_length_le t v c
  have hpIn : MachineCloudPrefix.inputLength t v.val [] ≤ 2*N := by
    simp only [MachineCloudPrefix.inputLength, List.append_nil, encodeWord_length]
    omega
  have hcIn : MachineCloudPadding.inputLength t v [] ≤ 2*N := by
    simp only [MachineCloudPadding.inputLength, List.append_nil, encodeWord_length]
    omega
  have hp := (MachineCloudPrefix.totalTime_le t v.val v.isLt.le []).trans
    (natPolynomial_eval_mono MachineCloudPrefix.timePolynomial hpIn)
  have hc := (MachineCloudPadding.totalTime_le t v []).trans
    (natPolynomial_eval_mono MachineCloudPadding.timePolynomial hcIn)
  have ho := overhead_le N e.val v.val hx hv.le
  have hsmall : ownerSteps t e + rankSteps t v c + (v.val+2) + 2 ≤
      overhead N e.val v.val := by
    simp only [MachineCloudRank.queryWord, List.length_append, encodeWord_length,
      List.length_nil] at rankBound
    simp only [ownerSteps, rankSteps, querySteps, rankQuery, MachineCloudRank.queryWord,
      List.length_append, encodeWord_length, List.length_nil, overhead]
    change _ ≤ _ at ownerBound
    dsimp only [c, originalMember] at rankRest ⊢
    change MachineAffineLookup.steps (GraphTables.tableWords t) e.val 4098 2 ≤
      2*e.val+5*N+6 at ownerBound
    omega
  have htotal : totalTime t e = ownerSteps t e + rankSteps t v c +
      MachineCloudPrefix.totalTime t v.val [] + (v.val+2) + 2 +
        MachineCloudPadding.totalTime t v := by
    simp only [totalTime, prefixSteps, v, c]
    omega
  rw [htotal]
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_comp,
    Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X, Polynomial.eval_one]
  change _ ≤ MachineCloudPrefix.timePolynomial.eval (2*N) +
    MachineCloudPadding.timePolynomial.eval (2*N) + 40*(N+1)
  omega

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularMetadata

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachinePaddedOverlayRuntimeLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachinePaddedOverlayRuntime

open Turing
open PCP
open MachinePaddedOverlay (BaseTable Tape Label State)

def rawProgram (H : BaseTable) (d : Nat) (hd : 0 < d) :
    MachineCanonicalOutput.Program Tape (Label d) (State d) where
  input := .inl .original
  output := .inr (.inr MachineOverlayTable.output)
  main := MachinePaddedOverlay.main
  initial := MachinePaddedOverlay.clean H d hd
  code := MachinePaddedOverlay.program H d hd

/-- A fixed finite list of every non-output stack. This includes both
retained archives, the original input, and the physically consumed level. -/
noncomputable def cleanupTapes : List Tape :=
  (Finset.univ.erase (.inr (.inr MachineOverlayTable.output) : Tape)).toList

theorem cleanup_complete (H : BaseTable) (d : Nat) (hd : 0 < d) (k : Tape) :
    k ∈ cleanupTapes ↔ k ≠ (rawProgram H d hd).output := by
  simp [cleanupTapes, rawProgram]

theorem initial_configuration (H : BaseTable) (d : Nat) (hd : 0 < d)
    (a : PortTables.Input d) :
    initList (MachineCanonicalOutput.sourceMachine (rawProgram H d hd))
        (PortTables.inputBits a) =
      ⟨some MachinePaddedOverlay.main, MachinePaddedOverlay.clean H d hd,
        MachinePaddedOverlay.initialTapes a.2⟩ := by
  change initList (MachinePaddedOverlay.machine H d hd) (PortTables.tableBits a.2) = _
  exact MachinePaddedOverlay.initial_configuration H hd a.2

/-- The raw terminal witness is the actual three-phase execution. No phase
trace, output-size bound, or complexity assertion is an input hypothesis. -/
noncomputable def terminalRun (H : BaseTable) (d : Nat) (hd : 0 < d)
    (a : PortTables.Input d) :
    MachineCanonicalOutput.TerminalRun (rawProgram H d hd) (PortTables.inputBits a)
      (PortTables.inputBits (PreprocessingStageMaps.paddedOverlay H d a))
      ((MachinePaddedOverlay.timePolynomial d).eval (PortTables.inputBits a).length) where
  state := MachinePaddedOverlay.clean H d hd
  tapes := MachinePaddedOverlay.finalTapes H a.2
  execution := by
    rw [initial_configuration]
    exact MachinePaddedOverlay.execution H hd a.2
  output_eq := MachinePaddedOverlay.final_output H hd a.2

/-- A concrete machine reaches the canonical `haltList` encoding of the
existing executable preprocessing map in polynomial time. -/
noncomputable def computableInPolyTime (H : BaseTable) (d : Nat) (hd : 0 < d) :
    TM2ComputableInPolyTime (PortTables.inputBits (ports := d))
      (PortTables.inputBits (ports := d + MachinePaddedOverlay.overlayDegree))
      (PreprocessingStageMaps.paddedOverlay H d) :=
  MachineCanonicalOutput.computableInPolyTime (rawProgram H d hd) cleanupTapes
    (cleanup_complete H d hd) PortTables.inputBits PortTables.inputBits
    (PreprocessingStageMaps.paddedOverlay H d) (MachinePaddedOverlay.timePolynomial d)
    (terminalRun H d hd)

/-- Finiteness belongs to the exact machine stored in the certificate above. -/
theorem finite_alphabet (H : BaseTable) (d : Nat) (hd : 0 < d) :
    ∀ k, Finite ((computableInPolyTime H d hd).tm.Γ k) :=
  MachineCanonicalOutput.computableInPolyTime_finite_alphabet (rawProgram H d hd) cleanupTapes
    (cleanup_complete H d hd) PortTables.inputBits PortTables.inputBits
    (PreprocessingStageMaps.paddedOverlay H d) (MachinePaddedOverlay.timePolynomial d)
    (terminalRun H d hd)

end UniqueGamesTheorem.Foundations.Complexity.MachinePaddedOverlayRuntime

/-! Polynomial bounds for the actual regularization subcalls. These lemmas
bound the established step counts; they do not assume any machine execution. -/
namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularExecutionBounds

open Turing MachineComposition PCP PCP.PreprocessingRegularTables PCP.PreprocessingCloudIndex
open PCP.PreprocessingMachineBounds MachineRegularInternalRow

noncomputable def familyPolynomial : Polynomial Nat :=
  MachinePaddedExpanderFamilyBounds.timePolynomial.comp (Polynomial.X + 1) +
    Polynomial.C (2 * ExpanderFamily.growth) * (Polynomial.X + 1) + 7

/-- The completed reusable family call includes the three actual drains. -/
theorem family_budget_le (t : GraphTables.Table) (v : Fin t.vertices) :
    MachinePaddedExpanderFamilyBounds.timePolynomial.eval (cloudSize t v + 1) +
      2 * ExpanderFamily.growth * (cloudSize t v + 1) + 7 ≤
        familyPolynomial.eval (inputLength t) := by
  have h := Nat.add_le_add_right (cloudSize_le_input t v) 1
  have hp := natPolynomial_eval_mono MachinePaddedExpanderFamilyBounds.timePolynomial h
  have hm := Nat.mul_le_mul_left (2 * ExpanderFamily.growth) h
  simp only [familyPolynomial, Polynomial.eval_add, Polynomial.eval_comp,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one,
    Polynomial.eval_ofNat]
  omega

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularExecutionBounds

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineRegularDummyRow
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual inherited-row emission for a dummy vertex

The fixed program preserves the physical unary vertex index on tape zero,
computes its inherited reverse index on tape one, invokes the actual one-port
dummy-row emitter, and drains the computed index and fixed true relation.
Tape four accumulates output. Tapes one, two, three, and five are empty at both
boundaries. The degree is fixed program data, not an input-dependent control
parameter.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularDummyRow

open Turing MachineComposition PCP.GraphTables

/-- The existing one-port emitter executes under the caller's actual labels. -/
theorem rowTraceAt {σ Λ : Type} (q : Nat) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Alphabet Λ (State σ))
    (code : ∀ l, program (labels l) = instruction q labels exit l)
    (x e : Nat) (output : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[MachineDummyRows.steps x e output 1 + 1]
      (some ⟨some (labels (.row (MachineDummyRows.start 1))), (ambient, register),
        MachineDummyRows.initialTapes x e output⟩) =
      some ⟨some (labels .reverse), (ambient, none),
        MachineDummyRows.fieldTapes x (e + 1) (output ++ MachineDummyRows.rowBits x e)⟩ := by
  have run := MachineDummyRows.allTrace 1 x e output ambient register
  have placed := MachineCloudPadding.Placement.trace (id : Tape → Tape) (fun k => some k)
    (fun _ => rfl) (fun _ _ h => (Option.some.inj h).symm)
    (fun l => labels (.row l)) (some (labels .reverse)) (fun _ => [])
    (MachineDummyRows.program 1) program
    (fun l => code (.row l)) _ _ _ run
  have identityTapes (source : Tape → List Bool) :
      MachineCloudPadding.Placement.tapes (fun k : Tape => some k) source
        (fun _ : Tape => []) = source := rfl
  simpa only [MachineCloudPadding.Placement.configuration,
    MachineCloudPadding.Placement.label, identityTapes,
    MachineDummyRows.rowsBits, List.append_nil] using placed

/-- Exact physical execution; only the accumulated output changes at the boundary. -/
theorem traceAt {σ Λ : Type} (q : Nat) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Alphabet Λ (State σ))
    (code : ∀ l, program (labels l) = instruction q labels exit l)
    (x : Nat) (base : Tape → List Bool) (input : Input x base)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[steps q x (base 4)]
      (some ⟨some (labels (.affine .seed)), (ambient, register), base⟩) =
      some ⟨exit, (ambient, none), Function.update base 4 (base 4 ++ emittedBits q x)⟩ := by
  have affine := MachineUnaryAffineAt.seededAffineTrace (0 : Tape) 3 1
    (by decide) (by decide) (by decide) (q + 1) q
    (labels (.affine .seed)) (labels (.affine .scan)) (labels (.affine .restore))
    (some (labels (.row (MachineDummyRows.start 1)))) program
    (code (.affine .seed)) (code (.affine .scan)) (code (.affine .restore))
    base x [] (by simpa only [List.append_nil] using input.source)
    input.scratchEmpty ambient register
  simp only [input.reverseEmpty, List.append_nil] at affine
  change (advance (TM2.step program))^[2 * (x + 1) + 1]
    (some ⟨some (labels (.affine .seed)), (ambient, register), base⟩) =
      some ⟨some (labels (.row (MachineDummyRows.start 1))), (ambient, none),
        Function.update base 1 (encodeWord (reverseIndex q x))⟩ at affine
  rw [affine_frame x (reverseIndex q x) base input] at affine
  have row := rowTraceAt q labels exit program code x (reverseIndex q x) (base 4) ambient none
  have clean := cleanupTraceAt q labels exit program code x (reverseIndex q x + 1)
    (base 4 ++ MachineDummyRows.rowBits x (reverseIndex q x)) ambient none
  rw [cleanup_frame x (reverseIndex q x + 1) _ base input] at clean
  exact join_trace (join_trace affine row) clean

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularDummyRow

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineRegularFamily
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Materializing a cloud rotor inside the regularization machine

Core tape 4 contains the unary cloud size and core tape 7 receives the complete
forward rotor table. The actual family computation runs on private tapes;
three retained unary words are then physically drained. All other core tapes
are preserved and all private tapes are empty on return.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularFamily

open Turing MachineComposition
open MachineCloudPadding

abbrev Alphabet (_ : Tape) := Bool
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

/-- Unused private shadows of the two public roles remain empty. -/
def familyTape (t : NativeTape) : Tape :=
  if t = inputNative then .inl 4 else if t = outputNative then .inl 7 else .inr t

def familyView : Tape → Option NativeTape
  | .inl i => if i = 4 then some inputNative else if i = 7 then some outputNative else none
  | .inr t => if t = inputNative then none else if t = outputNative then none else some t

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

def stateEquiv : MachinePaddedExpanderFamily.State Unit ≃ State :=
  (Equiv.prodAssoc FamilyState Bool (Option Bool)).symm

def seedState (H : SmallTable) : FamilyState :=
  MachineExpanderFamily.initialState MachineExpanderFamily.baseDegree_positive H ()

def readyState (H : SmallTable) : State := ((seedState H, false), none)

def sourceProgram (H : SmallTable) : MachinePaddedExpanderFamily.Label →
    TM2.Stmt (fun _ : NativeTape => Bool) MachinePaddedExpanderFamily.Label State :=
  MachineStateEquiv.program stateEquiv (MachinePaddedExpanderFamily.program (ρ := Unit) H)

inductive Label
  | start
  | family (label : MachinePaddedExpanderFamily.Label)
  | drainPower | drainSize | drainLevel
  deriving DecidableEq, Fintype

/-- Every size-dependent operation is performed by the checked native program.
The entry load only resets the finite control state. -/
def program (H : SmallTable) : Label → TM2.Stmt Alphabet Label State
  | .start => .load (fun _ => readyState H) (.goto fun _ => .family MachinePaddedExpanderFamily.main)
  | .family l => Placement.statement familyTape Label.family (some .drainPower) (sourceProgram H l)
  | .drainPower => MachineDrain.drain powerTape .drainPower (some .drainSize)
  | .drainSize => MachineDrain.drain sizeTape .drainSize (some .drainLevel)
  | .drainLevel => MachineDrain.drain levelTape .drainLevel none

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

@[simp] theorem working_empty (core : CoreTape → List Bool) :
    working core [] [] [] = frame core := by
  funext t; cases t <;> simp [working, frame]

theorem initial_other (k : Nat) (t : NativeTape) (h : t ≠ inputNative) :
    MachinePaddedExpanderFamily.initialTapes k t = [] := by
  cases t with
  | inl t => rfl
  | inr t => cases t <;> simp_all [MachinePaddedExpanderFamily.initialTapes, inputNative]

/-- The only retained native work words are the two sizes and the exhausted level. -/
theorem final_other (H : SmallTable) (k : Nat) (t : NativeTape)
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
      · simp [Placement.tapes, familyView, frame, hi, ho, initial_other k t hi]

theorem final_placement (H : SmallTable) (k : Nat) (core : CoreTape → List Bool)
    (hinput : core 4 = encodeWord k) :
    Placement.tapes familyView (MachinePaddedExpanderFamily.finalTapes H k) (frame core) =
      working (resultCore H k core)
        (encodeWord (PCP.PreprocessingLevels.paddedSize k))
        (encodeWord (PCP.PreprocessingLevels.paddedSize k)) (encodeWord 0) := by
  funext t
  cases t with
  | inl i =>
    by_cases hi : i = 4
    · subst i
      simp [Placement.tapes, familyView, working, resultCore, inputNative, hinput]
    · by_cases ho : i = 7
      · subst i
        simp [Placement.tapes, familyView, working, resultCore, outputNative,
          rotor, MachinePaddedExpanderFamilyBounds.outputWord]
        change MachinePaddedExpanderFamily.finalTapes H k
          (MachinePaddedExpanderFamily.familyTape MachineExpanderFamily.tableTape) = _
        exact MachinePaddedExpanderFamily.finalTapes_table H k
      · simp [Placement.tapes, familyView, working, resultCore, frame, hi, ho]
  | inr t =>
    by_cases hi : t = inputNative
    · subst t
      simp [Placement.tapes, familyView, working, frame,
        inputNative, powerNative, sizeNative, levelNative]
    · by_cases ho : t = outputNative
      · subst t
        simp [Placement.tapes, familyView, working, frame,
          outputNative, MachineExpanderFamily.tableTape, inputNative,
          powerNative, sizeNative, levelNative]
      · by_cases hp : t = powerNative
        · subst t
          simp [Placement.tapes, familyView, working, powerNative, inputNative, outputNative]
        · by_cases hs : t = sizeNative
          · subst t
            simpa [Placement.tapes, familyView, working, sizeNative,
              powerNative, inputNative, outputNative, MachineExpanderFamily.tableTape,
              MachinePaddedExpanderFamily.familyTape] using
              MachinePaddedExpanderFamily.finalTapes_currentSize H k
          · by_cases hl : t = levelNative
            · subst t
              simpa [Placement.tapes, familyView, working, levelNative,
                sizeNative, powerNative, inputNative, outputNative,
                MachineExpanderFamily.tableTape, MachinePaddedExpanderFamily.ceilingTape] using
                MachinePaddedExpanderFamily.finalTapes_remainingLevel H k
            · simp [Placement.tapes, familyView, working, hi, ho, hp, hs, hl,
                final_other H k t hi ho hp hs hl]

@[simp] theorem source_initial_state (H : SmallTable) :
    stateEquiv (MachinePaddedExpanderFamily.initialState (seedState H) none) =
      readyState H := rfl

@[simp] theorem source_final_state (H : SmallTable) :
    stateEquiv (MachinePaddedExpanderFamily.finalState H (seedState H)) =
      readyState H := by
  simp [stateEquiv, MachinePaddedExpanderFamily.finalState, readyState, seedState]

/-- The actual native family run, including geometric-level computation. -/
noncomputable def familyInTime (H : SmallTable) (k : Nat) (core : CoreTape → List Bool)
    (hinput : core 4 = encodeWord k) (houtput : core 7 = []) :
    StateTransition.EvalsToInTime (TM2.step (program H))
      ⟨some (.family MachinePaddedExpanderFamily.main), readyState H, frame core⟩
      (some ⟨some .drainPower, readyState H,
        working (resultCore H k core)
          (encodeWord (PCP.PreprocessingLevels.paddedSize k))
          (encodeWord (PCP.PreprocessingLevels.paddedSize k)) (encodeWord 0)⟩)
      (MachinePaddedExpanderFamilyBounds.timePolynomial.eval (encodeWord k).length) := by
  let raw := MachinePaddedExpanderFamily.paddedInTime H k (seedState H) none
  let renamed := MachineStateEquiv.execution stateEquiv
    (MachinePaddedExpanderFamily.program (ρ := Unit) H) raw
  let placed := liftExecutionInTime (TM2.step (sourceProgram H)) (TM2.step (program H))
    (Placement.configuration familyView Label.family (some .drainPower) (frame core))
    (Placement.step_simulation familyTape familyView familyView_left familyView_right
      Label.family (some .drainPower) (frame core) (sourceProgram H) (program H)
      (fun _ => rfl)) renamed
  simpa only [MachineStateEquiv.configuration, Placement.configuration, Placement.label,
    source_initial_state, source_final_state, initial_placement k core hinput houtput,
    final_placement H k core hinput] using placed

/-- Every retained private symbol is physically popped. -/
theorem cleanupTrace (H : SmallTable) (m : Nat) (core : CoreTape → List Bool) :
    (advance (TM2.step (program H)))^[2*m+6]
      (some ⟨some .drainPower, readyState H,
        working core (encodeWord m) (encodeWord m) (encodeWord 0)⟩) =
      some ⟨none, readyState H, frame core⟩ := by
  have first := (MachineDrain.drainInTime powerTape .drainPower (some .drainSize)
    (program H) rfl (working core (encodeWord m) (encodeWord m) (encodeWord 0))
    (seedState H, false) none).evals_in_steps
  have second := (MachineDrain.drainInTime sizeTape .drainSize (some .drainLevel)
    (program H) rfl (working core [] (encodeWord m) (encodeWord 0))
    (seedState H, false) none).evals_in_steps
  have third := (MachineDrain.drainInTime levelTape .drainLevel none
    (program H) rfl (working core [] [] (encodeWord 0))
    (seedState H, false) none).evals_in_steps
  simp only [MachineDrain.drainInTime, working_power, working_size, working_level,
    encodeWord_length, update_working_power, update_working_size,
    update_working_level, working_empty] at first second third
  have all := appendTrace _ (appendTrace _ first second) third
  have count : 2*m+6 = (m+1+1)+(m+1+1)+(0+1+1) := by omega
  rw [count]
  exact all

def cleanupInTime (H : SmallTable) (m : Nat) (core : CoreTape → List Bool) :
    StateTransition.EvalsToInTime (TM2.step (program H))
      ⟨some .drainPower, readyState H,
        working core (encodeWord m) (encodeWord m) (encodeWord 0)⟩
      (some ⟨none, readyState H, frame core⟩) (2*m+6) where
  steps := 2*m+6
  evals_in_steps := cleanupTrace H m core
  steps_le_m := le_rfl

def startInTime (H : SmallTable) (core : CoreTape → List Bool) (state : State) :
    StateTransition.EvalsToInTime (TM2.step (program H))
      ⟨some .start, state, frame core⟩
      (some ⟨some (.family MachinePaddedExpanderFamily.main), readyState H, frame core⟩) 1 where
  steps := 1
  evals_in_steps := by
    change some (TM2.stepAux (program H .start) state (frame core)) = _
    rfl
  steps_le_m := le_rfl

noncomputable def timePolynomial : Polynomial Nat :=
  MachinePaddedExpanderFamilyBounds.timePolynomial +
    Polynomial.C (2 * PCP.ExpanderFamily.growth) * Polynomial.X + 7

theorem totalBudget_le (k : Nat) :
    1 + MachinePaddedExpanderFamilyBounds.timePolynomial.eval (encodeWord k).length +
        (2 * PCP.PreprocessingLevels.paddedSize k + 6) ≤
      timePolynomial.eval (encodeWord k).length := by
  have hs := MachineExpanderFamilyBounds.paddedSize_le_succ_input k
  have hm := Nat.mul_le_mul_left 2 hs
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat, encodeWord_length]
  simp only [Nat.mul_assoc] at hm ⊢
  omega

/-- Complete clean-frame execution, from the caller's actual unary request.
No callback, table-construction premise, or caller-supplied runtime is assumed. -/
noncomputable def familyCleanInTime (H : SmallTable) (k : Nat)
    (core : CoreTape → List Bool) (hinput : core 4 = encodeWord k)
    (houtput : core 7 = []) (state : State) :
    StateTransition.EvalsToInTime (TM2.step (program H))
      ⟨some .start, state, frame core⟩
      (some ⟨none, readyState H, frame (resultCore H k core)⟩)
      (timePolynomial.eval (encodeWord k).length) := by
  let first := startInTime H core state
  let second := familyInTime H k core hinput houtput
  let third := cleanupInTime H (PCP.PreprocessingLevels.paddedSize k) (resultCore H k core)
  let pair := StateTransition.EvalsToInTime.trans (TM2.step (program H)) _ _ _ _ _ first second
  let all := StateTransition.EvalsToInTime.trans (TM2.step (program H)) _ _ _ _ _ pair third
  refine { toEvalsTo := all.toEvalsTo, steps_le_m := ?_ }
  exact all.steps_le_m.trans
    (by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using totalBudget_le k)

@[simp] theorem result_output (H : SmallTable) (k : Nat) (core : CoreTape → List Bool) :
    frame (resultCore H k core) (.inl 7) = rotor H k := by simp [frame, resultCore]

@[simp] theorem result_private_empty (H : SmallTable) (k : Nat)
    (core : CoreTape → List Bool) (t : NativeTape) :
    frame (resultCore H k core) (.inr t) = [] := rfl

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularFamily

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineRegularOriginalClean
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Reusable inherited-row execution with actual cleanup

Five concrete drain loops remove the query delimiter, unread scan suffix,
raw reverse field, computed reverse field, and copied relation. With initially
empty work tapes, the only final tape change is the appended output row. The
index on tape zero and input table on tape one are both preserved.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularOriginalClean

open Turing MachineComposition PCP PCP.GraphTables PCP.PreprocessingRegularTables

theorem traceAt {σ Λ : Type} (q : Nat) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Alphabet Λ (State σ))
    (code : ∀ l, program (labels l) = instruction q labels exit l)
    (t : Table) (e : Fin t.darts) (base : Tape → List Bool) (input : Input t e base)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[steps q t e base]
      (some ⟨some (labels (.row (.lookup .seed))),
        ((ambient, MachineRegularOriginalRow.zeroBuffer), register), base⟩) =
      some ⟨exit, ((ambient, MachineRegularOriginalRow.zeroBuffer), none),
        Function.update base 9
          (base 9 ++ encodeWords (MachineRegularOriginalRow.emittedWords q t e))⟩ := by
  have row := MachineRegularOriginalRow.traceAt q (fun l => labels (.row l))
    (some (labels .query)) program (fun l => code (.row l)) t e base input.toInput ambient register
  have clean := cleanupTraceAt q labels exit program code
    (MachineRegularOriginalRow.finalTapes q t e base)
    ((ambient, MachineRegularOriginalRow.zeroBuffer), none)
  rw [cleanup_frame q t e base input] at clean
  exact join_trace row clean

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularOriginalClean

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineRegularVertexBlock
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.legalDecidable _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual regularized vertex-block execution

The finite internal-port loop invokes the checked row machine for every port in
order. Each invocation restores the shared 27-tape frame. Inherited-row stages
use fixed tape placements and finite state permutations.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularVertexBlock

open Turing MachineComposition PCP MachineRegularInternalRow
open PreprocessingCloudIndex PreprocessingRegularTables

variable {σ Λ : Type}

/-- Every body is an actual invocation of `coreTrace`; the code hypothesis only
states the fixed placement into the caller's program. -/
theorem portPrefixTrace (q : Nat) (positive : 0 < q)
    (labels : PortLabel q → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : CoreTape => Bool) Λ (CoreState σ q))
    (code : ∀ l, program (labels l) = portInstruction q positive labels exit l)
    (t : GraphTables.Table) (padding : Fin t.vertices → Nat)
    (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding v) q)
    (v : Fin t.vertices) (x : PaddedCloud t padding v) (output : List Bool) (ambient : σ)
    (k : Nat) (hk : k ≤ q) :
    (advance (TM2.step program))^[portSteps t padding tables v x output.length k]
      (some ⟨portEntry q labels exit 0, coreInitialState q positive ambient,
        coreInputTapes t padding tables v x output⟩) =
      some ⟨portEntry q labels exit k, coreInitialState q positive ambient,
        coreInputTapes t padding tables v x
          (output ++ portBits (rowBits t padding tables v x) k)⟩ := by
  induction k with
  | zero => simp only [portSteps, portBits, List.append_nil, Function.iterate_zero, id_eq]
  | succ k ih =>
    have h : k < q := by omega
    have first := ih (by omega)
    have second := coreTrace q positive ⟨k, h⟩ (fun s => labels (⟨k, h⟩, s))
      (portEntry q labels exit (k + 1)) program (fun s => code (⟨k, h⟩, s))
      t padding tables v x (output ++ portBits (rowBits t padding tables v x) k) ambient
    have he : portEntry q labels exit k = some (labels (⟨k, h⟩, coreEntry q)) := by
      simp only [portEntry, dite_eq_left h]
    rw [he] at first
    have total := joinTrace first second
    simpa only [portSteps, dite_eq_left h, List.length_append, portBits, rowBits,
      List.append_assoc] using total

theorem portTrace (q : Nat) (positive : 0 < q)
    (labels : PortLabel q → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : CoreTape => Bool) Λ (CoreState σ q))
    (code : ∀ l, program (labels l) = portInstruction q positive labels exit l)
    (t : GraphTables.Table) (padding : Fin t.vertices → Nat)
    (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding v) q)
    (v : Fin t.vertices) (x : PaddedCloud t padding v) (output : List Bool) (ambient : σ) :
    (advance (TM2.step program))^[portSteps t padding tables v x output.length q]
      (some ⟨portEntry q labels exit 0, coreInitialState q positive ambient,
        coreInputTapes t padding tables v x output⟩) =
      some ⟨exit, coreInitialState q positive ambient,
        coreInputTapes t padding tables v x
          (output ++ (List.ofFn (rowBits t padding tables v x)).flatten)⟩ := by
  simpa only [portEntry, lt_self_iff_false, dite_false, portBits_all] using
    portPrefixTrace q positive labels exit program code t padding tables v x output ambient q le_rfl

/-- The inherited old relation is physically copied by the checked original-row
machine, with a static tape placement and state permutation. -/
theorem originalCoreTrace (q : Nat) (positive : 0 < q)
    (labels : MachineRegularOriginalClean.Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : CoreTape => Bool) Λ (CoreState σ q))
    (code : ∀ l, program (labels l) = originalCoreInstruction q labels exit l)
    (t : GraphTables.Table) (e : Fin t.darts) (v i k o m : Nat)
    (rotor output : List Bool) (ambient : σ) :
    (advance (TM2.step program))^[MachineRegularOriginalClean.steps q t e
        (originalMemory (GraphTables.tableBits t) e.val output)]
      (some ⟨some (labels (.row (.lookup .seed))), coreInitialState q positive ambient,
        coreMemory (GraphTables.tableBits t) e.val v i k o m rotor output [] [] [] [] [] []⟩) =
      some ⟨exit, coreInitialState q positive ambient,
        coreMemory (GraphTables.tableBits t) e.val v i k o m rotor
          (output ++ encodeWords (MachineRegularOriginalRow.emittedWords q t e))
          [] [] [] [] [] []⟩ := by
  let state := (ambient, (MachineFixedDivMod.residue q positive 0,
    (false, MachineCloudSelect.Phase.checking)))
  have run := MachineRegularOriginalClean.traceAt q id none
    (MachineRegularOriginalClean.instruction q id none) (fun _ => rfl) t e
    (originalMemory (GraphTables.tableBits t) e.val output)
    (originalMemory_input t e output) state none
  rw [originalMemory_update] at run
  have moved := MachineStateEquiv.trace (originalStateEquiv σ q)
    (MachineRegularOriginalClean.instruction q id none) _ _ _ run
  have placed := MachineCloudPadding.Placement.trace originalTapes originalView
    originalView_left originalView_right labels exit
    (coreMemory (GraphTables.tableBits t) e.val v i k o m rotor output [] [] [] [] [] [])
    (MachineStateEquiv.program (originalStateEquiv σ q)
      (MachineRegularOriginalClean.instruction q id none)) program code _ _ _ moved
  simp only [MachineCloudPadding.Placement.configuration, MachineCloudPadding.Placement.label,
    MachineStateEquiv.configuration, originalFrame] at placed
  convert placed using 1 <;> rfl

theorem dummyCoreTrace (q : Nat) (positive : 0 < q)
    (labels : MachineRegularDummyRow.Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : CoreTape => Bool) Λ (CoreState σ q))
    (code : ∀ l, program (labels l) = dummyCoreInstruction q labels exit l)
    (graph : List Bool) (x v i k o m : Nat) (rotor output : List Bool) (ambient : σ) :
    (advance (TM2.step program))^[MachineRegularDummyRow.timeBound q x output.length]
      (some ⟨some (labels (.affine .seed)), coreInitialState q positive ambient,
        coreMemory graph x v i k o m rotor output [] [] [] [] [] []⟩) =
      some ⟨exit, coreInitialState q positive ambient,
        coreMemory graph x v i k o m rotor
          (output ++ MachineRegularDummyRow.emittedBits q x) [] [] [] [] [] []⟩ := by
  let state := (ambient, (MachineFixedBlockMap.emptyBuffer 4096,
    (MachineFixedDivMod.residue q positive 0, (false, MachineCloudSelect.Phase.checking))))
  have run := MachineRegularDummyRow.traceAt q id none
    (MachineRegularDummyRow.instruction q id none) (fun _ => rfl) x
    (MachineRegularDummyRow.memory x output) (MachineRegularDummyRow.memory_input x output) state none
  rw [dummyMemory_update] at run
  have placed := MachineCloudPadding.Placement.trace dummyTapes dummyView
    dummyView_left dummyView_right labels exit
    (coreMemory graph x v i k o m rotor output [] [] [] [] [] [])
    (MachineRegularDummyRow.instruction q id none) program code _ _ _ run
  simp only [MachineCloudPadding.Placement.configuration, MachineCloudPadding.Placement.label,
    dummyFrame] at placed
  have hs : MachineRegularDummyRow.steps q x output =
      MachineRegularDummyRow.timeBound q x output.length := MachineRegularDummyRow.steps_eq q x output
  change (advance (TM2.step program))^[MachineRegularDummyRow.steps q x output] _ = _ at placed
  rw [hs] at placed
  exact placed

/-- The full old-vertex block uses every internal port, then physically copies
the original relation and reverse index. The output is the actual table block. -/
theorem originalTraceAt (q : Nat) (positive : 0 < q)
    (labels : Label q → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : CoreTape => Bool) Λ (CoreState σ q))
    (code : ∀ l, program (labels l) = instruction q positive labels exit l)
    (t : GraphTables.Table) (padding : Fin t.vertices → Nat)
    (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding v) q)
    (e : Fin t.darts) (output : List Bool) (ambient : σ) :
    (advance (TM2.step program))^[originalSteps t padding tables e output.length]
      (some ⟨some (labels (originalEntry q positive)), coreInitialState q positive ambient,
        coreInputTapes t padding tables t.rows[e].tail (oldCloud t padding e) output⟩) =
      some ⟨exit, coreInitialState q positive ambient,
        coreInputTapes t padding tables t.rows[e].tail (oldCloud t padding e)
          (output ++ PreprocessingRegularWords.originalVertexBits t padding tables e)⟩ := by
  let x := oldCloud t padding e
  let bits := (List.ofFn (rowBits t padding tables t.rows[e].tail x)).flatten
  have ports := portTrace q positive (fun l => labels (.originalPort l))
    (some (labels (.original (.row (.lookup .seed))))) program
    (fun l => code (.originalPort l)) t padding tables t.rows[e].tail x output ambient
  have inherited := originalCoreTrace q positive (fun l => labels (.original l)) exit program
    (fun l => code (.original l)) t e t.rows[e].tail.val
    (paddedCloudRank t padding t.rows[e].tail x).val (cloudSize t t.rows[e].tail)
    (PreprocessingPaddingOffsets.offset padding t.rows[e].tail.val) t.darts
    (encodeWords (ExpanderTableWords.rotationWords (tables t.rows[e].tail))) (output ++ bits) ambient
  rw [originalRowSteps_eq] at inherited
  change (advance (TM2.step program))^[originalRowSteps q t e (output ++ bits).length]
    (some ⟨some (labels (.original (.row (.lookup .seed)))), coreInitialState q positive ambient,
      coreInputTapes t padding tables t.rows[e].tail x (output ++ bits)⟩) =
    some ⟨exit, coreInitialState q positive ambient,
      coreInputTapes t padding tables t.rows[e].tail x
        ((output ++ bits) ++ encodeWords (MachineRegularOriginalRow.emittedWords q t e))⟩ at inherited
  have total := joinTrace ports inherited
  have hbits : PreprocessingRegularWords.originalVertexBits t padding tables e =
      bits ++ encodeWords (MachineRegularOriginalRow.emittedWords q t e) := by
    have h := vertexBits_split t padding tables t.rows[e].tail x
    change PreprocessingRegularWords.originalVertexBits t padding tables e =
      bits ++ encodeWords (GraphTables.rowWords
        (PreprocessingRegularWords.actualRow t padding tables (.inl e) (.inr ()))) at h
    rw [PreprocessingRegularWords.inherited_original_words] at h
    exact h
  rw [hbits]
  simpa only [originalSteps, portEntry, dite_eq_left positive, originalEntry,
    List.length_append, List.append_assoc, x, bits] using total

theorem dummyTraceAt (q : Nat) (positive : 0 < q)
    (labels : Label q → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : CoreTape => Bool) Λ (CoreState σ q))
    (code : ∀ l, program (labels l) = instruction q positive labels exit l)
    (t : GraphTables.Table) (padding : Fin t.vertices → Nat)
    (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding v) q)
    (v : Fin t.vertices) (j : Fin (padding v)) (output : List Bool) (ambient : σ) :
    (advance (TM2.step program))^[dummySteps t padding tables v j output.length]
      (some ⟨some (labels (dummyEntry q positive)), coreInitialState q positive ambient,
        coreInputTapes t padding tables v (paddedNew t padding v j) output⟩) =
      some ⟨exit, coreInitialState q positive ambient,
        coreInputTapes t padding tables v (paddedNew t padding v j)
          (output ++ PreprocessingRegularWords.dummyVertexBits t padding tables v j)⟩ := by
  let x := paddedNew t padding v j
  let bits := (List.ofFn (rowBits t padding tables v x)).flatten
  have ports := portTrace q positive (fun l => labels (.dummyPort l))
    (some (labels (.dummy (.affine .seed)))) program
    (fun l => code (.dummyPort l)) t padding tables v x output ambient
  have inherited := dummyCoreTrace q positive (fun l => labels (.dummy l)) exit program
    (fun l => code (.dummy l)) (GraphTables.tableBits t) (vertexOrder t padding x.val).val v.val
    (paddedCloudRank t padding v x).val (cloudSize t v)
    (PreprocessingPaddingOffsets.offset padding v.val) t.darts
    (encodeWords (ExpanderTableWords.rotationWords (tables v))) (output ++ bits) ambient
  have total := joinTrace ports inherited
  have hbits : PreprocessingRegularWords.dummyVertexBits t padding tables v j =
      bits ++ MachineRegularDummyRow.emittedBits q (vertexOrder t padding x.val).val := by
    have h := vertexBits_split t padding tables v x
    change PreprocessingRegularWords.dummyVertexBits t padding tables v j =
      bits ++ encodeWords (GraphTables.rowWords
        (PreprocessingRegularWords.actualRow t padding tables (.inr ⟨v, j⟩) (.inr ()))) at h
    rw [PreprocessingRegularWords.inherited_dummy_words] at h
    rw [encodeWords_pair] at h
    rw [show (vertexOrder t padding x.val).val =
      t.darts + PreprocessingPaddingOffsets.offset padding v.val + j.val from
      PreprocessingPaddingOffsets.vertexOrder_dummy_val t padding v j]
    simpa only [MachineRegularDummyRow.emittedBits, MachineRegularDummyRow.reverseIndex,
      MachineDummyRows.rowBits, MachineDummyRows.trueBits, List.append_assoc] using h
  rw [hbits]
  simp only [dummySteps, portEntry, dite_eq_left positive, dummyEntry,
    List.length_append, List.append_assoc, x, bits] at total ⊢
  convert total using 1 <;> rfl

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularVertexBlock

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineRegularOriginalBody
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# One actual original-vertex body of regularization

The finite code composes physical metadata preparation, expander-family
materialization, all vertex rows, and seven metadata drain loops. The outer
loop owns the global vertex counter and keeps it unchanged during this body.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularOriginalBody

open Turing MachineComposition PCP
open PreprocessingCloudIndex PreprocessingRegularTables
open MachineRegularTable

abbrev Tape := Fin 27 ⊕ (MachineRegularMetadata.Extra ⊕ MachinePaddedExpanderFamily.Tape)
abbrev Alphabet (_ : Tape) := Bool
abbrev FamilyState := MachineRegularFamily.State
abbrev State := (CoreState × MetaState) × FamilyState

theorem degree_positive : 0 < internalDegree :=
  Nat.mul_pos MachineExpanderFamily.baseDegree_positive MachineExpanderFamily.baseDegree_positive

def readyState (H : BaseTable) : State :=
  ((MachineRegularInternalRow.coreInitialState internalDegree degree_positive (),
    (((), false), none)), MachineRegularFamily.readyState H)

def metadataTape : MachineRegularMetadata.Tape → Tape
  | .inl i => .inl i
  | .inr e => .inr (.inl e)

def metadataView : Tape → Option MachineRegularMetadata.Tape
  | .inl i => some (.inl i)
  | .inr (.inl e) => some (.inr e)
  | .inr (.inr _) => none

def familyTape : MachineRegularFamily.Tape → Tape
  | .inl i => .inl i
  | .inr e => .inr (.inr e)

def familyView : Tape → Option MachineRegularFamily.Tape
  | .inl i => some (.inl i)
  | .inr (.inl _) => none
  | .inr (.inr e) => some (.inr e)

def vertexView : Tape → Option (Fin 27)
  | .inl i => some i
  | .inr _ => none

theorem metadataView_left (k : MachineRegularMetadata.Tape) :
    metadataView (metadataTape k) = some k := by cases k <;> rfl

theorem metadataView_right (j : Tape) (k : MachineRegularMetadata.Tape)
    (h : metadataView j = some k) : metadataTape k = j := by
  cases j with
  | inl i => cases h; rfl
  | inr j => cases j with
    | inl e => cases h; rfl
    | inr e => cases h

theorem familyView_left (k : MachineRegularFamily.Tape) :
    familyView (familyTape k) = some k := by cases k <;> rfl

theorem familyView_right (j : Tape) (k : MachineRegularFamily.Tape)
    (h : familyView j = some k) : familyTape k = j := by
  cases j with
  | inl i => cases h; rfl
  | inr j => cases j with
    | inl e => cases h
    | inr e => cases h; rfl

theorem vertexView_left (k : Fin 27) : vertexView (.inl k) = some k := rfl

theorem vertexView_right (j : Tape) (k : Fin 27)
    (h : vertexView j = some k) : Sum.inl k = j := by
  cases j with
  | inl i => cases h; rfl
  | inr e => cases h

def metadataStates : (MetaState × (CoreState × FamilyState)) ≃ State where
  toFun p := ((p.2.1, p.1), p.2.2)
  invFun p := (p.1.2, (p.1.1, p.2))
  left_inv _ := rfl
  right_inv _ := rfl

def familyStates : (FamilyState × (CoreState × MetaState)) ≃ State := Equiv.prodComm _ _
def vertexStates : (CoreState × (MetaState × FamilyState)) ≃ State :=
  (Equiv.prodAssoc _ _ _).symm

inductive Label
  | metadata (l : MachineRegularMetadata.Label)
  | family (l : MachineRegularFamily.Label)
  | vertex (l : MachineRegularVertexBlock.Label internalDegree)
  | clear (i : Fin 7)
  deriving DecidableEq, Fintype

def entry : Label := .metadata (.owner .seed)

def clearTape : Fin 7 → Tape :=
  ![.inl 2, .inl 3, .inl 4, .inl 5, .inl 7,
    .inr (.inl .padding), .inr (.inl .level)]

def clearEntry (k : Nat) : Option Label :=
  if h : k < 7 then some (.clear ⟨k, h⟩) else none

def clearSource (source : Tape) : Unit → TM2.Stmt Alphabet Unit MetaState :=
  fun _ => MachineDrain.drain source () none

def vertexSource : MachineRegularVertexBlock.Label internalDegree →
    TM2.Stmt (fun _ : Fin 27 => Bool) (MachineRegularVertexBlock.Label internalDegree) CoreState :=
  MachineRegularVertexBlock.instruction internalDegree degree_positive id none

def program (H : BaseTable) : Label → TM2.Stmt Alphabet Label State
  | .metadata l => Lift.statement metadataTape Label.metadata (some (.family .start))
      metadataStates (MachineRegularMetadata.program l)
  | .family l => Lift.statement familyTape Label.family
      (some (.vertex (MachineRegularVertexBlock.originalEntry internalDegree degree_positive)))
      familyStates (MachineRegularFamily.program H l)
  | .vertex l => Lift.statement Sum.inl Label.vertex (clearEntry 0)
      vertexStates (vertexSource l)
  | .clear i => Lift.statement id (fun _ : Unit => .clear i) (clearEntry (i.val + 1))
      metadataStates (clearSource (clearTape i) ())

def frame (data : Data) : Tape → List Bool
  | .inl i => MachineRegularMetadata.frame data (.inl i)
  | .inr (.inl e) => MachineRegularMetadata.frame data (.inr e)
  | .inr (.inr _) => []

def cfg (H : BaseTable) (label : Option Label) (data : Data) : TM2.Cfg Alphabet Label State :=
  ⟨label, readyState H, frame data⟩

def initialData (t : GraphTables.Table) (e : Fin t.darts) (output : List Bool) : Data where
  table := GraphTables.tableBits t
  globalIndex := encodeWord e.val
  owner := []
  localRank := []
  count := []
  offset := []
  darts := encodeWord t.darts
  rotor := []
  output := output
  padding := []
  level := []

def metadataData (t : GraphTables.Table) (e : Fin t.darts) (output : List Bool) : Data :=
  MachineRegularMetadata.originalData t e (initialData t e output)

def familyData (H : BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) : Data :=
  { metadataData t e output with
    rotor := MachineRegularFamily.rotor H (cloudSize t t.rows[e].tail) }

def emittedBits (H : BaseTable) (t : GraphTables.Table) (e : Fin t.darts) : List Bool :=
  PreprocessingRegularWords.originalVertexBits t (padding t) (familyCloudTable H t) e

def emittedData (H : BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) : Data :=
  { familyData H t e output with output := output ++ emittedBits H t e }

theorem metadataPlacement (data extra : Data) :
    MachineCloudPadding.Placement.tapes metadataView (MachineRegularMetadata.frame data)
      (frame extra) = frame data := by
  funext j
  cases j with
  | inl i => rfl
  | inr j => cases j <;> rfl

/-- Genuine metadata trace transported with all other finite registers and
private family tapes preserved. -/
theorem metadataTrace (H : BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) :
    (advance (TM2.step (program H)))^[MachineRegularMetadata.totalTime t e]
      (some (cfg H (some entry) (initialData t e output))) =
      some (cfg H (some (.family .start)) (metadataData t e output)) := by
  have raw := MachineRegularMetadata.originalTrace t e (initialData t e output)
    rfl rfl rfl rfl rfl rfl rfl rfl () none
  have placed := Lift.trace metadataTape metadataView metadataView_left metadataView_right
    Label.metadata (some (.family .start)) metadataStates
    (MachineRegularInternalRow.coreInitialState internalDegree degree_positive (),
      MachineRegularFamily.readyState H) (frame (initialData t e output))
    MachineRegularMetadata.program (program H) (fun _ => rfl) _ _ _ raw
  simpa only [Lift.configuration, MachineCloudPadding.Placement.label,
    metadataPlacement, MachineRegularMetadata.cfg, metadataData, cfg, readyState,
    metadataStates, Equiv.coe_fn_mk, entry] using placed

theorem familyPlacement (data : Data) :
    MachineCloudPadding.Placement.tapes familyView (MachineRegularFamily.frame (coreFrame data))
      (frame data) = frame data := by
  funext j
  cases j with
  | inl i => rfl
  | inr j => cases j <;> rfl

theorem familyResultPlacement (H : BaseTable) (k : Nat) (data : Data) :
    MachineCloudPadding.Placement.tapes familyView
      (MachineRegularFamily.frame (MachineRegularFamily.resultCore H k (coreFrame data)))
      (frame data) = frame { data with rotor := MachineRegularFamily.rotor H k } := by
  funext j
  cases j with
  | inl i => fin_cases i <;>
      simp [MachineCloudPadding.Placement.tapes, familyView, MachineRegularFamily.frame,
        MachineRegularFamily.resultCore, coreFrame, frame, MachineRegularMetadata.frame]
  | inr j => cases j with
    | inl e => cases e <;> rfl
    | inr e => rfl

noncomputable def familyExecution (H : BaseTable) (t : GraphTables.Table)
    (e : Fin t.darts) (output : List Bool) :=
  MachineRegularFamily.familyCleanInTime H (cloudSize t t.rows[e].tail)
    (coreFrame (metadataData t e output)) rfl rfl (MachineRegularFamily.readyState H)

noncomputable def familySteps (H : BaseTable) (t : GraphTables.Table)
    (e : Fin t.darts) (output : List Bool) : Nat :=
  (familyExecution H t e output).steps

/-- Family work is performed on its physical tapes and produces the rotor
from the previously computed unary cloud size. -/
theorem familyTrace (H : BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) :
    (advance (TM2.step (program H)))^[familySteps H t e output]
      (some (cfg H (some (.family .start)) (metadataData t e output))) =
      some (cfg H (some (.vertex (MachineRegularVertexBlock.originalEntry
        internalDegree degree_positive))) (familyData H t e output)) := by
  have raw := (familyExecution H t e output).evals_in_steps
  have placed := Lift.trace familyTape familyView familyView_left familyView_right
    Label.family (some (.vertex (MachineRegularVertexBlock.originalEntry internalDegree degree_positive)))
    familyStates
    (MachineRegularInternalRow.coreInitialState internalDegree degree_positive (),
      ((((), false), none) : MetaState)) (frame (metadataData t e output))
    (MachineRegularFamily.program H) (program H) (fun _ => rfl) _ _ _ raw
  simpa only [Lift.configuration, MachineCloudPadding.Placement.label,
    familyPlacement, familyResultPlacement, familyData, familySteps, cfg, readyState,
    familyStates, Equiv.prodComm_apply, Prod.swap_prod_mk] using placed

/-- Seven real drain loops, including the complete materialized rotor. -/
def clearMemory (base : Tape → List Bool) : Nat → Tape → List Bool
  | 0 => base
  | k + 1 => if h : k < 7 then
      Function.update (clearMemory base k) (clearTape ⟨k, h⟩) [] else clearMemory base k

def clearSteps (base : Tape → List Bool) : Nat → Nat
  | 0 => 0
  | k + 1 => clearSteps base k + if h : k < 7 then
      ((clearMemory base k) (clearTape ⟨k, h⟩)).length + 1 else 0

theorem identityPlacement (base extra : Tape → List Bool) :
    MachineCloudPadding.Placement.tapes some base extra = base := rfl

theorem drainTrace (H : BaseTable) (i : Fin 7) (base : Tape → List Bool) :
    (advance (TM2.step (program H)))^[(base (clearTape i)).length + 1]
      (some ⟨some (.clear i), readyState H, base⟩) =
      some ⟨clearEntry (i.val + 1), readyState H, Function.update base (clearTape i) []⟩ := by
  have raw := MachineDrain.drainTrace (clearTape i) () none (clearSource (clearTape i)) rfl
    base (base (clearTape i)) ((), false) none
  simp only [Function.update_eq_self] at raw
  have placed := Lift.trace id some (fun _ => rfl)
    (fun j k h => (Option.some.inj h).symm)
    (fun _ : Unit => Label.clear i) (clearEntry (i.val + 1)) metadataStates
    (MachineRegularInternalRow.coreInitialState internalDegree degree_positive (),
      MachineRegularFamily.readyState H) base (clearSource (clearTape i)) (program H)
    (fun _ => rfl) _ _ _ raw
  simpa only [Lift.configuration, MachineCloudPadding.Placement.label,
    identityPlacement, metadataStates, Equiv.coe_fn_mk, readyState] using placed

theorem clearPrefixTrace (H : BaseTable) (base : Tape → List Bool)
    (k : Nat) (hk : k ≤ 7) :
    (advance (TM2.step (program H)))^[clearSteps base k]
      (some ⟨clearEntry 0, readyState H, base⟩) =
      some ⟨clearEntry k, readyState H, clearMemory base k⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h : k < 7 := by omega
    have first := ih (by omega)
    have second := drainTrace H ⟨k, h⟩ (clearMemory base k)
    have atEntry : clearEntry k = some (.clear ⟨k, h⟩) := by simp only [clearEntry, dite_eq_left h]
    rw [atEntry] at first
    simpa only [clearSteps, clearMemory, dite_eq_left h] using joinTrace first second

theorem clearTrace (H : BaseTable) (base : Tape → List Bool) :
    (advance (TM2.step (program H)))^[clearSteps base 7]
      (some ⟨clearEntry 0, readyState H, base⟩) =
      some ⟨none, readyState H, clearMemory base 7⟩ := by
  simpa only [clearEntry, lt_self_iff_false, dite_false] using clearPrefixTrace H base 7 le_rfl

theorem clearFrame (data : Data) : clearMemory (frame data) 7 =
    frame { data with
      owner := []
      localRank := []
      count := []
      offset := []
      rotor := []
      padding := []
      level := [] } := by
  funext j
  cases j with
  | inl i => fin_cases i <;>
      simp [clearMemory, clearTape, frame, MachineRegularMetadata.frame]
  | inr j => cases j with
    | inl e => cases e <;>
        simp [clearMemory, clearTape, frame, MachineRegularMetadata.frame]
    | inr e => simp [clearMemory, clearTape, frame]

theorem coreFrame_eq (H : BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) :
    coreFrame (familyData H t e output) =
      MachineRegularInternalRow.coreInputTapes t (padding t) (familyCloudTable H t)
        t.rows[e].tail (MachineRegularVertexBlock.oldCloud t (padding t) e) output := by
  have rotor : MachineRegularFamily.rotor H (cloudSize t t.rows[e].tail) =
      encodeWords (ExpanderTableWords.rotationWords (familyCloudTable H t t.rows[e].tail)) :=
    PreprocessingFamilyBridge.familyRotor_eq_familyCloudTable H t t.rows[e].tail
      (PreprocessingFamilyBridge.cloudSize_pos_of_dart t e)
  funext i
  fin_cases i <;>
    simp [coreFrame, familyData, metadataData, MachineRegularMetadata.originalData,
      MachineRegularMetadata.cloudData, MachineRegularMetadata.prefixData,
      MachineRegularMetadata.rankData, MachineRegularMetadata.ownerData,
      MachineRegularMetadata.frame, initialData,
      MachineRegularInternalRow.coreInputTapes, MachineRegularInternalRow.coreMemory,
      MachineRegularVertexBlock.oldCloud, paddedOld,
      MachineRegularMetadata.originalMember]
  all_goals first | exact rotor | rfl

theorem emittedData_eq (H : BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) : emittedData H t e output =
      familyData H t e (output ++ emittedBits H t e) := rfl

theorem vertexPlacement (H : BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output output' : List Bool) :
    MachineCloudPadding.Placement.tapes vertexView (coreFrame (familyData H t e output'))
      (frame (familyData H t e output)) = frame (familyData H t e output') := by
  funext j
  cases j with
  | inl i => rfl
  | inr j => cases j with
    | inl e => cases e <;> rfl
    | inr e => rfl

def vertexSteps (H : BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) : Nat :=
  MachineRegularVertexBlock.originalSteps t (padding t) (familyCloudTable H t) e output.length

/-- Every internal port and the inherited original row are emitted by their
actual checked row machines, using the rotor just materialized on tape 7. -/
theorem vertexTrace (H : BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) :
    (advance (TM2.step (program H)))^[vertexSteps H t e output]
      (some (cfg H (some (.vertex (MachineRegularVertexBlock.originalEntry
        internalDegree degree_positive))) (familyData H t e output))) =
      some (cfg H (clearEntry 0) (emittedData H t e output)) := by
  have raw := MachineRegularVertexBlock.originalTraceAt internalDegree degree_positive id none
    vertexSource (fun _ => rfl) t (padding t) (familyCloudTable H t) e output ()
  have finished := coreFrame_eq H t e (output ++ emittedBits H t e)
  simp only [emittedBits] at finished
  rw [← coreFrame_eq H t e output, ← finished] at raw
  have placed := Lift.trace Sum.inl vertexView vertexView_left vertexView_right
    Label.vertex (clearEntry 0) vertexStates
    (((((), false), none) : MetaState), MachineRegularFamily.readyState H)
    (frame (familyData H t e output)) vertexSource (program H) (fun _ => rfl) _ _ _ raw
  simpa only [Lift.configuration, MachineCloudPadding.Placement.label, vertexPlacement,
    emittedData_eq, cfg, readyState, vertexStates, Equiv.prodAssoc_symm_apply,
    vertexSteps, emittedBits, id_eq] using placed

noncomputable def totalSteps (H : BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) : Nat :=
  MachineRegularMetadata.totalTime t e + familySteps H t e output + vertexSteps H t e output +
    clearSteps (frame (emittedData H t e output)) 7

/-- Complete execution of one original-vertex iteration, including physical
cleanup of all seven retained metadata fields. The global index is preserved. -/
theorem originalTrace (H : BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) :
    (advance (TM2.step (program H)))^[totalSteps H t e output]
      (some (cfg H (some entry) (initialData t e output))) =
      some (cfg H none (initialData t e (output ++ emittedBits H t e))) := by
  have metadata := metadataTrace H t e output
  have family := familyTrace H t e output
  have vertex := vertexTrace H t e output
  have cleanup := clearTrace H (frame (emittedData H t e output))
  have final : clearMemory (frame (emittedData H t e output)) 7 =
      frame (initialData t e (output ++ emittedBits H t e)) := by
    rw [clearFrame]
    rfl
  rw [final] at cleanup
  exact joinTrace (joinTrace (joinTrace metadata family) vertex) cleanup

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularOriginalBody

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineRegularOriginalBodyBounds
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Polynomial runtime for the actual original-vertex body. The size parameter
includes the already accumulated output, so no output-prefix premise is used. -/
namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularOriginalBodyBounds

open Turing MachineComposition PCP PreprocessingCloudIndex PreprocessingRegularTables
open PreprocessingMachineBounds MachineRegularOriginalBody

noncomputable def timePolynomial : Polynomial Nat :=
  MachineRegularMetadata.timePolynomial + MachineRegularExecutionBounds.familyPolynomial +
    blockPolynomial internalDegree + cleanupPolynomial internalDegree

def bodySize (t : GraphTables.Table) (output : List Bool) : Nat :=
  inputLength t + output.length

theorem wide_le (t : GraphTables.Table) (output : List Bool) :
    inputLength t ≤ (ExpanderFamily.growth+1)*bodySize t output ∧
    ExpanderFamily.growth*inputLength t ≤ (ExpanderFamily.growth+1)*bodySize t output ∧
    output.length ≤ (ExpanderFamily.growth+1)*bodySize t output := by
  have hN : inputLength t ≤ bodySize t output := Nat.le_add_right _ _
  have hO : output.length ≤ bodySize t output := Nat.le_add_left _ _
  have hg := Nat.mul_le_mul_left ExpanderFamily.growth hN
  rw [Nat.add_mul, Nat.one_mul]
  omega

theorem vertexSteps_le (H : PreprocessingRegularTables.BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) :
    MachineRegularOriginalBody.vertexSteps H t e output ≤
      (blockPolynomial internalDegree).eval (bodySize t output) := by
  let v := t.rows[e].tail
  let W := (ExpanderFamily.growth+1)*bodySize t output
  have bounds := wide_le t output
  have hx := e.isLt.le.trans (GraphTables.darts_le_tableBits_length t)
  have hv := v.isLt.le.trans (GraphTables.vertices_le_tableBits_length t)
  have hk := cloudSize_le_input t v
  have hi := (cloudRank t v (MachineRegularMetadata.originalMember t e)).isLt.le.trans hk
  have hm := GraphTables.darts_le_tableBits_length t
  have ho := prefix_le_input t v.val
  have hV := regularVertices_le_input t
  have hR := (cloudRotorBits_le t v (familyCloudTable H t v)).trans
    (natPolynomial_eval_mono (rotorPolynomial internalDegree)
      (Nat.le_add_right (inputLength t) output.length))
  have raw := MachineRegularVertexBlock.originalSteps_le internalDegree degree_positive
    t (padding t) (familyCloudTable H t) e output.length
  have bound := originalTimeBound_le internalDegree _ _ _ _ _ _ _ _ _ _ W _
    bounds.1 hR (hx.trans bounds.1) (hv.trans bounds.1) (hi.trans bounds.1)
    (hk.trans bounds.1) (ho.trans bounds.2.1) (hm.trans bounds.1) bounds.2.2
    (hV.trans bounds.2.1)
  rw [blockPolynomial_eval]
  exact raw.trans bound

theorem clearSteps_frame (data : Data) :
    clearSteps (frame data) 7 = data.owner.length + data.localRank.length +
      data.count.length + data.offset.length + data.rotor.length + data.padding.length +
      data.level.length + 7 := by
  simp [clearSteps, clearMemory, clearTape, frame, MachineRegularMetadata.frame]
  omega

theorem cleanupSteps_le (H : PreprocessingRegularTables.BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) :
    clearSteps (frame (emittedData H t e output)) 7 ≤
      (cleanupPolynomial internalDegree).eval (bodySize t output) := by
  let v := t.rows[e].tail
  have bounds := wide_le t output
  have hv := v.isLt.le.trans (GraphTables.vertices_le_tableBits_length t)
  have hk := cloudSize_le_input t v
  have hi := (cloudRank t v (MachineRegularMetadata.originalMember t e)).isLt.le.trans hk
  have ho := prefix_le_input t v.val
  have hp := cloudTotal_le_input t v
  have hl := level_le_input t v
  have hrotor := PreprocessingFamilyBridge.familyRotor_eq_familyCloudTable H t v
    (PreprocessingFamilyBridge.cloudSize_pos_of_dart t e)
  change MachineRegularFamily.rotor H (cloudSize t v) = _ at hrotor
  have hR := (cloudRotorBits_le t v (familyCloudTable H t v)).trans
    (natPolynomial_eval_mono (rotorPolynomial internalDegree)
      (Nat.le_add_right (inputLength t) output.length))
  rw [← hrotor] at hR
  rw [clearSteps_frame]
  simp only [emittedData, familyData, metadataData, MachineRegularMetadata.originalData,
    MachineRegularMetadata.cloudData, MachineRegularMetadata.prefixData,
    MachineRegularMetadata.rankData, MachineRegularMetadata.ownerData, initialData,
    encodeWord_length, cleanupPolynomial, wide, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat]
  change _ ≤ 6*((ExpanderFamily.growth+1)*bodySize t output) +
    (rotorPolynomial internalDegree).eval (bodySize t output)+13
  change cloudSize t v + MachineCloudPadding.padding (cloudSize t v) ≤ _ at hp
  dsimp only [v, bodySize, inputLength] at *
  omega

theorem totalSteps_le (H : PreprocessingRegularTables.BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) :
    totalSteps H t e output ≤ timePolynomial.eval (bodySize t output) := by
  have hsize : inputLength t ≤ bodySize t output := Nat.le_add_right _ _
  have hm := (MachineRegularMetadata.totalTime_le t e).trans
    (natPolynomial_eval_mono MachineRegularMetadata.timePolynomial hsize)
  have hf := (familyExecution H t e output).steps_le_m
  have hfb := MachineRegularExecutionBounds.family_budget_le t t.rows[e].tail
  simp only [MachineRegularFamily.timePolynomial, encodeWord_length,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_ofNat] at hf
  have hf' := (hf.trans hfb).trans
    (natPolynomial_eval_mono MachineRegularExecutionBounds.familyPolynomial hsize)
  have hv := vertexSteps_le H t e output
  have hc := cleanupSteps_le H t e output
  simp only [totalSteps, familySteps, timePolynomial, Polynomial.eval_add]
  omega

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularOriginalBodyBounds

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineRegularOwnerCleanup
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup

open Turing MachineComposition

abbrev Tape := MachineRegularOriginalBody.Tape ⊕ Fin 2
abbrev State := MachineRegularOriginalBody.State × Option Bool
abbrev Alphabet (_ : Tape) := Bool

/-- Every equality decision is explicitly assembled from fixed finite leaves.
There is no classical decision or recursive typeclass search on the tape sum. -/
instance tapeDecidableEq : DecidableEq Tape :=
  sumDecidableEq
    (sumDecidableEq (inferInstanceAs (DecidableEq (Fin 27)))
      (sumDecidableEq (inferInstanceAs (DecidableEq MachineRegularMetadata.Extra))
        (sumDecidableEq
          (sumDecidableEq
            (sumDecidableEq (inferInstanceAs (DecidableEq MachineExpanderRow.Tape))
              (inferInstanceAs (DecidableEq MachineExpanderTable.ExtraTape)))
            (inferInstanceAs (DecidableEq MachineExpanderFamily.ExtraTape)))
          (inferInstanceAs (DecidableEq MachineCeilingPower.Tape)))))
    (inferInstanceAs (DecidableEq (Fin 2)))

/-- List membership uses Boolean equality. These instances are
the explicit Boolean view of the executable equality procedure above. -/
instance tapeBEq : BEq Tape where
  beq a b := decide (a = b)

instance tapeLawfulBEq : LawfulBEq Tape where
  eq_of_beq := of_decide_eq_true
  rfl := of_decide_eq_self_eq_true _

instance tapeFintype : Fintype Tape := by
  change Fintype
    ((Fin 27 ⊕ (MachineRegularMetadata.Extra ⊕
      (((MachineExpanderRow.Tape ⊕ MachineExpanderTable.ExtraTape) ⊕
        MachineExpanderFamily.ExtraTape) ⊕ MachineCeilingPower.Tape))) ⊕ Fin 2)
  infer_instance

def core (k : Fin 27) : Tape := .inl (.inl k)
def localRank : Tape := core 3
def count : Tape := core 4
def prefixTape : Tape := core 5
def rotor : Tape := core 7
def padding : Tape := .inl (.inr (.inl .padding))
def level : Tape := .inl (.inr (.inl .level))
def dummyFuel : Tape := .inr 0
def scratch : Tape := .inr 1

/-- Every name is distinct, so the exact drain cost uses the entry lengths. -/
def cleanupTapes : List Tape := [localRank, count, rotor, padding, level, dummyFuel]

inductive Label
  | scan
  | restore
  | drain (l : MachineDrainMany.Label cleanupTapes)
  deriving DecidableEq, Fintype

def entry : Label := .scan

variable {Λ : Type}

def cleanupEntry (labels : Label → Λ) (exit : Option Λ) : Option Λ :=
  MachineDrainMany.entry cleanupTapes (fun l => labels (.drain l)) exit

/-- Coefficient one, no seed: the destination already contains its offset. -/
def instruction (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt Alphabet Λ State
  | .scan => MachineUnaryAffineAt.scan padding scratch prefixTape 1
      (labels .scan) (labels .restore)
  | .restore => Reduction.MachineTransfer.loopAt scratch padding id false
      (labels .restore) (cleanupEntry labels exit)
  | .drain l => MachineDrainMany.instruction cleanupTapes
      (fun l => labels (.drain l)) exit l

def afterAddition (base : Tape → List Bool) (d o : Nat) : Tape → List Bool :=
  Function.update base prefixTape (encodeWord (d + o))

def finalTapes (base : Tape → List Bool) (d o : Nat) : Tape → List Bool :=
  MachineDrainMany.finalTapes cleanupTapes (afterAddition base d o)

def steps (base : Tape → List Bool) (d : Nat) : Nat :=
  2 * (d + 1) + (cleanupTapes.map (fun k => (base k).length + 1)).sum

theorem finalTapes_apply (base : Tape → List Bool) (d o : Nat) (k : Tape) :
    finalTapes base d o k =
      if k ∈ cleanupTapes then []
      else if k = prefixTape then encodeWord (d + o) else base k := by
  simp only [finalTapes, MachineDrainMany.finalTapes_apply, afterAddition,
    Function.update_apply]

@[simp] theorem finalTapes_prefix (base : Tape → List Bool) (d o : Nat) :
    finalTapes base d o prefixTape = encodeWord (d + o) := by
  simp [finalTapes_apply, cleanupTapes, prefixTape, localRank, count, rotor,
    padding, level, dummyFuel, core]

theorem drainSteps_eq (base : Tape → List Bool) (d o : Nat) :
    MachineDrainMany.steps cleanupTapes (afterAddition base d o) =
      (cleanupTapes.map (fun k => (base k).length + 1)).sum := by
  simp [MachineDrainMany.steps, cleanupTapes, afterAddition, prefixTape,
    localRank, count, rotor, padding, level, dummyFuel, core]

theorem additionTraceAt (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Alphabet Λ State)
    (code : ∀ l, program (labels l) = instruction labels exit l)
    (base : Tape → List Bool) (d o : Nat)
    (paddingWord : base padding = encodeWord d)
    (prefixWord : base prefixTape = encodeWord o)
    (scratchEmpty : base scratch = [])
    (ambient : MachineRegularOriginalBody.State) (register : Option Bool) :
    (advance (TM2.step program))^[2 * (d + 1)]
      (some ⟨some (labels entry), (ambient, register), base⟩) =
      some ⟨cleanupEntry labels exit, (ambient, none), afterAddition base d o⟩ := by
  have frame (word : List Bool) :
      MachineUnaryAffineAt.tapes padding scratch prefixTape base (encodeWord d) [] word =
        Function.update base prefixTape word := by
    rw [← paddingWord, ← scratchEmpty]
    simp only [MachineUnaryAffineAt.tapes, MachineCopy.forkTapes, Function.update_eq_self]
  have initial : MachineUnaryAffineAt.tapes padding scratch prefixTape base
      (encodeWord d) [] (encodeWord o) = base := by
    rw [frame, ← prefixWord, Function.update_eq_self]
  have run := MachineUnaryAffineAt.affineTrace padding scratch prefixTape
    (by decide) (by decide) (by decide) 1 (labels .scan) (labels .restore)
    (cleanupEntry labels exit) program (code .scan) (code .restore)
    base d o [] [] ambient register
  simpa only [List.append_nil, Nat.one_mul, initial, frame, entry, afterAddition] using run

/-- Complete physical addition followed by the six exact drain loops.
No phase run or precomputed sum word is supplied as a hypothesis. -/
theorem traceAt (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Alphabet Λ State)
    (code : ∀ l, program (labels l) = instruction labels exit l)
    (base : Tape → List Bool) (d o : Nat)
    (paddingWord : base padding = encodeWord d)
    (prefixWord : base prefixTape = encodeWord o)
    (scratchEmpty : base scratch = [])
    (ambient : MachineRegularOriginalBody.State) (register : Option Bool) :
    (advance (TM2.step program))^[steps base d]
      (some ⟨some (labels entry), (ambient, register), base⟩) =
      some ⟨exit, (ambient, none), finalTapes base d o⟩ := by
  have first := additionTraceAt labels exit program code base d o
    paddingWord prefixWord scratchEmpty ambient register
  have second := MachineDrainMany.trace cleanupTapes (fun l => labels (.drain l)) exit
    program (fun l => code (.drain l)) (afterAddition base d o) ambient none
  simp only [MachineDrainMany.finalRegister_none, drainSteps_eq] at second
  unfold steps
  rw [Nat.add_comm, Function.iterate_add_apply, first]
  exact second

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineRegularOwnerProgram
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual dummy-owner body of regularization

The owner is a physically stored unary index. The code computes its cloud
metadata, initializes local index and fuel, skips the family computation when
padding is zero, and otherwise generates one rotor for all dummy vertices of
this owner. Each vertex iteration consumes one fuel bit and increments both
physical vertex indices. The final checked addition and cleanup leave only the
updated global index, prefix, and accumulated output.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody

open Turing MachineComposition PCP
open PreprocessingCloudIndex PreprocessingRegularTables
open MachineRegularTable
open PreprocessingRegularLoopWords

abbrev Tape := MachineRegularOriginalBody.Tape ⊕ Fin 2
abbrev Alphabet (_ : Tape) := Bool
abbrev State := MachineRegularOriginalBody.State × Option Bool
abbrev FamilyState := MachineRegularOriginalBody.FamilyState

instance instDecidableEqTape : DecidableEq Tape := MachineRegularOwnerCleanup.tapeDecidableEq
instance instFintypeTape : Fintype Tape := MachineRegularOwnerCleanup.tapeFintype

def core (k : Fin 27) : Tape := .inl (.inl k)
def paddingTape : Tape := .inl (.inr (.inl .padding))
def dummyFuel : Tape := .inr 0
def scratch : Tape := .inr 1

def readyState (H : BaseTable) : State := (MachineRegularOriginalBody.readyState H, none)

def metadataTape (k : MachineRegularMetadata.Tape) : Tape :=
  .inl (MachineRegularOriginalBody.metadataTape k)

def metadataView : Tape → Option MachineRegularMetadata.Tape
  | .inl k => MachineRegularOriginalBody.metadataView k
  | .inr _ => none

def familyTape (k : MachineRegularFamily.Tape) : Tape :=
  .inl (MachineRegularOriginalBody.familyTape k)

def familyView : Tape → Option MachineRegularFamily.Tape
  | .inl k => MachineRegularOriginalBody.familyView k
  | .inr _ => none

def vertexView : Tape → Option (Fin 27)
  | .inl k => MachineRegularOriginalBody.vertexView k
  | .inr _ => none

theorem metadataView_left (k : MachineRegularMetadata.Tape) :
    metadataView (metadataTape k) = some k := MachineRegularOriginalBody.metadataView_left k

theorem metadataView_right (j : Tape) (k : MachineRegularMetadata.Tape)
    (h : metadataView j = some k) : metadataTape k = j := by
  cases j with
  | inl j => exact congrArg Sum.inl (MachineRegularOriginalBody.metadataView_right j k h)
  | inr j => cases h

theorem familyView_left (k : MachineRegularFamily.Tape) :
    familyView (familyTape k) = some k := MachineRegularOriginalBody.familyView_left k

theorem familyView_right (j : Tape) (k : MachineRegularFamily.Tape)
    (h : familyView j = some k) : familyTape k = j := by
  cases j with
  | inl j => exact congrArg Sum.inl (MachineRegularOriginalBody.familyView_right j k h)
  | inr j => cases h

theorem vertexView_left (k : Fin 27) : vertexView (core k) = some k := rfl

theorem vertexView_right (j : Tape) (k : Fin 27)
    (h : vertexView j = some k) : core k = j := by
  cases j with
  | inl j => exact congrArg Sum.inl (MachineRegularOriginalBody.vertexView_right j k h)
  | inr j => cases h

def metadataStates : (MetaState × ((CoreState × FamilyState) × Option Bool)) ≃ State where
  toFun p := (((p.2.1.1, p.1), p.2.1.2), p.2.2)
  invFun p := (p.1.1.2, ((p.1.1.1, p.1.2), p.2))
  left_inv _ := rfl
  right_inv _ := rfl

def familyStates : (FamilyState × ((CoreState × MetaState) × Option Bool)) ≃ State where
  toFun p := ((p.2.1, p.1), p.2.2)
  invFun p := (p.1.2, (p.1.1, p.2))
  left_inv _ := rfl
  right_inv _ := rfl

def vertexStates : (CoreState × ((MetaState × FamilyState) × Option Bool)) ≃ State where
  toFun p := (((p.1, p.2.1.1), p.2.1.2), p.2.2)
  invFun p := (p.1.1.1, ((p.1.1.2, p.1.2), p.2))
  left_inv _ := rfl
  right_inv _ := rfl

inductive Label
  | metadata (l : MachineRegularMetadata.Label)
  | copyCount (l : MachineUnaryAffineAt.Label)
  | copyFuel (l : MachineUnaryAffineAt.Label)
  | guard
  | family (l : MachineRegularFamily.Label)
  | loop
  | vertex (l : MachineRegularVertexBlock.Label internalDegree)
  | bump
  | cleanup (l : MachineRegularOwnerCleanup.Label)
  deriving DecidableEq, Fintype

def entry : Label := .metadata (.cloud .init)

def program (H : BaseTable) : Label → TM2.Stmt Alphabet Label State
  | .metadata l => Lift.statement metadataTape Label.metadata (some (.copyCount .seed))
      metadataStates (MachineRegularMetadata.program l)
  | .copyCount .seed => MachineUnaryAffineAt.seed (core 3) 0 (.copyCount .scan)
  | .copyCount .scan => MachineUnaryAffineAt.scan (core 4) scratch (core 3) 1
      (.copyCount .scan) (.copyCount .restore)
  | .copyCount .restore => Reduction.MachineTransfer.loopAt scratch (core 4) id false
      (.copyCount .restore) (some (.copyFuel .seed))
  | .copyFuel .seed => MachineUnaryAffineAt.seed dummyFuel 0 (.copyFuel .scan)
  | .copyFuel .scan => MachineUnaryAffineAt.scan paddingTape scratch dummyFuel 1
      (.copyFuel .scan) (.copyFuel .restore)
  | .copyFuel .restore => Reduction.MachineTransfer.loopAt scratch paddingTape id false
      (.copyFuel .restore) (some .guard)
  | .guard => .peek dummyFuel (fun state head => (state.1, head))
      (.branch (fun state => state.2.getD false)
        (.load (fun state => (state.1, none)) (.goto fun _ => .family .start))
        (.load (fun state => (state.1, none))
          (.goto fun _ => .cleanup MachineRegularOwnerCleanup.entry)))
  | .family l => Lift.statement familyTape Label.family (some .loop)
      familyStates (MachineRegularFamily.program H l)
  | .loop => .peek dummyFuel (fun state head => (state.1, head))
      (.branch (fun state => state.2.getD false)
        (.pop dummyFuel (fun state _ => (state.1, none))
          (.goto fun _ => .vertex (MachineRegularVertexBlock.dummyEntry internalDegree
            MachineRegularOriginalBody.degree_positive)))
        (.load (fun state => (state.1, none))
          (.goto fun _ => .cleanup MachineRegularOwnerCleanup.entry)))
  | .vertex l => Lift.statement core Label.vertex (some .bump)
      vertexStates (MachineRegularOriginalBody.vertexSource l)
  | .bump => .push (core 1) (fun _ => true)
      (.push (core 3) (fun _ => true) (.goto fun _ => .loop))
  | .cleanup l => MachineRegularOwnerCleanup.instruction Label.cleanup none l

def working (data : Data) (fuel saved : List Bool) : Tape → List Bool
  | .inl k => MachineRegularOriginalBody.frame data k
  | .inr i => if i = 0 then fuel else saved

def frame (data : Data) : Tape → List Bool := working data [] []

def cfg (H : BaseTable) (label : Option Label) (data : Data) : TM2.Cfg Alphabet Label State :=
  ⟨label, readyState H, frame data⟩

def initialData (t : GraphTables.Table) (v : Fin t.vertices) (output : List Bool) : Data where
  table := GraphTables.tableBits t
  globalIndex := encodeWord (t.darts + PreprocessingPaddingOffsets.offset (padding t) v.val)
  owner := encodeWord v.val
  localRank := []
  count := []
  offset := encodeWord (PreprocessingPaddingOffsets.offset (padding t) v.val)
  darts := encodeWord t.darts
  rotor := []
  output := output
  padding := []
  level := []

def metadataData (t : GraphTables.Table) (v : Fin t.vertices) (output : List Bool) : Data :=
  MachineRegularMetadata.cloudData t v (initialData t v output)

def seededData (t : GraphTables.Table) (v : Fin t.vertices) (output : List Bool) : Data :=
  { metadataData t v output with localRank := encodeWord (cloudSize t v) }

def ownerBits (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices) : List Bool :=
  (List.ofFn (PreprocessingRegularWords.dummyVertexBits t (padding t) (familyCloudTable H t) v)).flatten

def finalData (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) : Data :=
  { initialData t v output with
    globalIndex := encodeWord (t.darts + PreprocessingPaddingOffsets.offset (padding t) v.val + padding t v)
    offset := encodeWord (PreprocessingPaddingOffsets.offset (padding t) v.val + padding t v)
    output := output ++ ownerBits H t v }

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineRegularOwnerBody
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual execution and exact runtime of the fixed dummy-owner program. -/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody

open Turing MachineComposition PCP
open PreprocessingCloudIndex PreprocessingRegularTables
open MachineRegularTable PreprocessingRegularLoopWords

theorem metadataPlacement (data extra : Data) :
    MachineCloudPadding.Placement.tapes metadataView (MachineRegularMetadata.frame data)
      (frame extra) = frame data := by
  funext j
  cases j with
  | inl j => cases j with
    | inl i => rfl
    | inr j => cases j <;> rfl
  | inr i => rfl

/-- Actual cloud metadata, with every outer register and tape preserved. -/
theorem metadataTrace (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) :
    (advance (TM2.step (program H)))^[MachineCloudPadding.totalTime t v]
      (some (cfg H (some entry) (initialData t v output))) =
      some (cfg H (some (.copyCount .seed)) (metadataData t v output)) := by
  have raw := MachineRegularMetadata.cloudTrace t v (initialData t v output)
    rfl rfl rfl rfl rfl () none
  have placed := Lift.trace metadataTape metadataView metadataView_left metadataView_right
    Label.metadata (some (.copyCount .seed)) metadataStates
    ((MachineRegularInternalRow.coreInitialState internalDegree
      MachineRegularOriginalBody.degree_positive (), MachineRegularFamily.readyState H), none)
    (frame (initialData t v output)) MachineRegularMetadata.program (program H)
    (fun _ => rfl) _ _ _ raw
  simpa only [Lift.configuration, MachineCloudPadding.Placement.label,
    metadataPlacement, MachineRegularMetadata.cfg, metadataData, cfg, readyState,
    MachineRegularOriginalBody.readyState, metadataStates, Equiv.coe_fn_mk, entry] using placed

theorem working_update_local (data : Data) (fuel saved word : List Bool) :
    Function.update (working data fuel saved) (core 3) word =
      working { data with localRank := word } fuel saved := by
  funext j
  cases j with
  | inl j => cases j with
    | inl i => fin_cases i <;>
        simp [working, core, MachineRegularOriginalBody.frame, MachineRegularMetadata.frame]
    | inr j => cases j with
      | inl e => cases e <;>
          simp [working, core, MachineRegularOriginalBody.frame, MachineRegularMetadata.frame]
      | inr e => simp [working, core, MachineRegularOriginalBody.frame]
  | inr i => simp [working, core]

theorem working_update_fuel (data : Data) (fuel saved word : List Bool) :
    Function.update (working data fuel saved) dummyFuel word = working data word saved := by
  funext j
  cases j with
  | inl j => simp [working, dummyFuel]
  | inr i => fin_cases i <;> simp [working, dummyFuel]

theorem working_update_global (data : Data) (fuel saved word : List Bool) :
    Function.update (working data fuel saved) (core 1) word =
      working { data with globalIndex := word } fuel saved := by
  funext j
  cases j with
  | inl j => cases j with
    | inl i => fin_cases i <;>
        simp [working, core, MachineRegularOriginalBody.frame, MachineRegularMetadata.frame]
    | inr j => cases j with
      | inl e => cases e <;>
          simp [working, core, MachineRegularOriginalBody.frame, MachineRegularMetadata.frame]
      | inr e => simp [working, core, MachineRegularOriginalBody.frame]
  | inr i => simp [working, core]

/-- The local rank starts at the actual cloud size, copied from its physical tape. -/
theorem copyCountTrace (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) :
    (advance (TM2.step (program H)))^[2 * (cloudSize t v + 1) + 1]
      (some (cfg H (some (.copyCount .seed)) (metadataData t v output))) =
      some (cfg H (some (.copyFuel .seed)) (seededData t v output)) := by
  have run := MachineUnaryAffineAt.seededAffineTrace (core 4) scratch (core 3)
    (by decide) (by decide) (by decide) 1 0
    (.copyCount .seed) (.copyCount .scan) (.copyCount .restore) (some (.copyFuel .seed))
    (program H) rfl rfl rfl (frame (metadataData t v output)) (cloudSize t v) []
    (by simp only [List.append_nil]; rfl) rfl
    (MachineRegularOriginalBody.readyState H) none
  have hempty : frame (metadataData t v output) (core 3) = [] := rfl
  rw [hempty, List.append_nil] at run
  simpa only [Nat.one_mul, Nat.add_zero, List.append_nil, cfg, readyState,
    frame, working_update_local, seededData] using run

/-- Padding fuel is another preserved unary copy; it is never a control parameter. -/
theorem copyFuelTrace (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) :
    (advance (TM2.step (program H)))^[2 * (padding t v + 1) + 1]
      (some (cfg H (some (.copyFuel .seed)) (seededData t v output))) =
      some ⟨some .guard, readyState H,
        working (seededData t v output) (encodeWord (padding t v)) []⟩ := by
  have run := MachineUnaryAffineAt.seededAffineTrace paddingTape scratch dummyFuel
    (by decide) (by decide) (by decide) 1 0
    (.copyFuel .seed) (.copyFuel .scan) (.copyFuel .restore) (some .guard)
    (program H) rfl rfl rfl (frame (seededData t v output)) (padding t v) []
    (by simp only [List.append_nil]; rfl) rfl
    (MachineRegularOriginalBody.readyState H) none
  have hempty : frame (seededData t v output) dummyFuel = [] := rfl
  rw [hempty, List.append_nil] at run
  simpa only [Nat.one_mul, Nat.add_zero, List.append_nil, cfg, readyState,
    frame, working_update_fuel] using run

theorem guardZeroStep (H : BaseTable) (data : Data) :
    TM2.step (program H) ⟨some .guard, readyState H, working data (encodeWord 0) []⟩ =
      some ⟨some (.cleanup MachineRegularOwnerCleanup.entry), readyState H,
        working data (encodeWord 0) []⟩ := by
  rfl

theorem guardPositiveStep (H : BaseTable) (data : Data) (d : Nat) (hd : 0 < d) :
    TM2.step (program H) ⟨some .guard, readyState H, working data (encodeWord d) []⟩ =
      some ⟨some (.family .start), readyState H, working data (encodeWord d) []⟩ := by
  cases d with
  | zero => omega
  | succ d =>
      simp [TM2.step, program, TM2.stepAux, working, dummyFuel, encodeWord,
        List.replicate_succ, readyState]

def dummyBits (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices) :
    Fin (padding t v) → List Bool :=
  PreprocessingRegularWords.dummyVertexBits t (padding t) (familyCloudTable H t) v

def vertexData (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (n : Nat) (output : List Bool) : Data :=
  { seededData t v output with
    globalIndex := encodeWord (t.darts + PreprocessingPaddingOffsets.offset (padding t) v.val + n)
    localRank := encodeWord (cloudSize t v + n)
    rotor := MachineRegularFamily.rotor H (cloudSize t v) }

def loopData (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) (n : Nat) : Data :=
  vertexData H t v n (output ++ blocksPrefix (dummyBits H t v) n)

def loopFrame (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) (n : Nat) : Tape → List Bool :=
  working (loopData H t v output n) (encodeWord (padding t v - n)) []

def preSteps (t : GraphTables.Table) (v : Fin t.vertices) : Nat :=
  MachineCloudPadding.totalTime t v + (2 * (cloudSize t v + 1) + 1) +
    (2 * (padding t v + 1) + 1)

def loopSteps (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) : (n : Nat) → n ≤ padding t v → Nat
  | 0, _ => 0
  | n + 1, hn => loopSteps H t v output n (by omega) +
      (1 + MachineRegularVertexBlock.dummySteps t (padding t) (familyCloudTable H t)
        v ⟨n, by omega⟩ (output ++ blocksPrefix (dummyBits H t v) n).length + 1)

def cleanupCost (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) : Nat :=
  if padding t v = 0 then
    MachineRegularOwnerCleanup.steps (working (seededData t v output) (encodeWord 0) []) (padding t v)
  else MachineRegularOwnerCleanup.steps (loopFrame H t v output (padding t v)) (padding t v)

noncomputable def ownerTime (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) : Nat :=
  preSteps t v + 1 + (if padding t v = 0 then 0 else
    MachineRegularFamily.timePolynomial.eval (encodeWord (cloudSize t v)).length +
      loopSteps H t v output (padding t v) le_rfl + 1) + cleanupCost H t v output

theorem familyPlacement (data : Data) (fuel saved : List Bool) :
    MachineCloudPadding.Placement.tapes familyView
      (MachineRegularFamily.frame (MachineRegularOriginalBody.coreFrame data))
      (working data fuel saved) = working data fuel saved := by
  funext j
  cases j with
  | inl j => exact congrFun (MachineRegularOriginalBody.familyPlacement data) j
  | inr i => rfl

theorem familyResultPlacement (H : BaseTable) (k : Nat) (data : Data) (fuel saved : List Bool) :
    MachineCloudPadding.Placement.tapes familyView
      (MachineRegularFamily.frame (MachineRegularFamily.resultCore H k
        (MachineRegularOriginalBody.coreFrame data)))
      (working data fuel saved) =
      working { data with rotor := MachineRegularFamily.rotor H k } fuel saved := by
  funext j
  cases j with
  | inl j => exact congrFun (MachineRegularOriginalBody.familyResultPlacement H k data) j
  | inr i => rfl

noncomputable def familyExecution (H : BaseTable) (t : GraphTables.Table)
    (v : Fin t.vertices) (output : List Bool) :=
  MachineRegularFamily.familyCleanInTime H (cloudSize t v)
    (MachineRegularOriginalBody.coreFrame (seededData t v output)) rfl rfl
    (MachineRegularFamily.readyState H)

noncomputable def familySteps (H : BaseTable) (t : GraphTables.Table)
    (v : Fin t.vertices) (output : List Bool) : Nat :=
  (familyExecution H t v output).steps

theorem familyTrace (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) :
    (advance (TM2.step (program H)))^[familySteps H t v output]
      (some ⟨some (.family .start), readyState H,
        working (seededData t v output) (encodeWord (padding t v)) []⟩) =
      some ⟨some .loop, readyState H, loopFrame H t v output 0⟩ := by
  have raw := (familyExecution H t v output).evals_in_steps
  have placed := Lift.trace familyTape familyView familyView_left familyView_right
    Label.family (some .loop) familyStates
    ((MachineRegularInternalRow.coreInitialState internalDegree
      MachineRegularOriginalBody.degree_positive (), ((((), false), none) : MetaState)), none)
    (working (seededData t v output) (encodeWord (padding t v)) [])
    (MachineRegularFamily.program H) (program H) (fun _ => rfl) _ _ _ raw
  simpa only [Lift.configuration, MachineCloudPadding.Placement.label,
    familyPlacement, familyResultPlacement, familySteps, readyState,
    MachineRegularOriginalBody.readyState, familyStates, Equiv.coe_fn_mk,
    loopFrame, loopData, vertexData, blocksPrefix_zero, List.append_nil, Nat.sub_zero,
    Nat.add_zero, seededData, metadataData, MachineRegularMetadata.cloudData,
    initialData] using placed

theorem coreFrame_eq (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (j : Fin (padding t v)) (output : List Bool) :
    MachineRegularOriginalBody.coreFrame (vertexData H t v j.val output) =
      MachineRegularInternalRow.coreInputTapes t (padding t) (familyCloudTable H t)
        v (paddedNew t (padding t) v j) output := by
  have rotor : MachineRegularFamily.rotor H (cloudSize t v) =
      encodeWords (ExpanderTableWords.rotationWords (familyCloudTable H t v)) :=
    PreprocessingFamilyBridge.familyRotor_eq_familyCloudTable H t v
      (PreprocessingFamilyBridge.cloudSize_pos_of_dummy t v j)
  funext i
  fin_cases i <;>
    simp [MachineRegularOriginalBody.coreFrame, vertexData, seededData, metadataData,
      MachineRegularMetadata.cloudData, MachineRegularMetadata.frame, initialData,
      MachineRegularInternalRow.coreInputTapes, MachineRegularInternalRow.coreMemory,
      paddedNew,
      PreprocessingPaddingOffsets.paddingOrder_val, Nat.add_assoc]
  all_goals first | exact rotor | rfl

theorem vertexPlacement (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (n : Nat) (output output' fuel : List Bool) :
    MachineCloudPadding.Placement.tapes vertexView
      (MachineRegularOriginalBody.coreFrame (vertexData H t v n output'))
      (working (vertexData H t v n output) fuel []) =
      working (vertexData H t v n output') fuel [] := by
  funext j
  cases j with
  | inl j => cases j with
    | inl i => rfl
    | inr j => cases j with
      | inl e => cases e <;> rfl
      | inr e => rfl
  | inr i => rfl

/-- A complete actual dummy vertex block, with the owner's fuel left untouched. -/
theorem vertexTrace (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (j : Fin (padding t v)) (output fuel : List Bool) :
    (advance (TM2.step (program H)))^[
        MachineRegularVertexBlock.dummySteps t (padding t) (familyCloudTable H t) v j output.length]
      (some ⟨some (.vertex (MachineRegularVertexBlock.dummyEntry internalDegree
        MachineRegularOriginalBody.degree_positive)), readyState H,
        working (vertexData H t v j.val output) fuel []⟩) =
      some ⟨some .bump, readyState H,
        working (vertexData H t v j.val (output ++ dummyBits H t v j)) fuel []⟩ := by
  have raw := MachineRegularVertexBlock.dummyTraceAt internalDegree
    MachineRegularOriginalBody.degree_positive id none MachineRegularOriginalBody.vertexSource
    (fun _ => rfl) t (padding t) (familyCloudTable H t) v j output ()
  have finished := coreFrame_eq H t v j (output ++ dummyBits H t v j)
  simp only [dummyBits] at finished
  rw [← coreFrame_eq H t v j output, ← finished] at raw
  have placed := Lift.trace core vertexView vertexView_left vertexView_right
    Label.vertex (some .bump) vertexStates
    ((((((), false), none) : MetaState), MachineRegularFamily.readyState H), none)
    (working (vertexData H t v j.val output) fuel [])
    MachineRegularOriginalBody.vertexSource (program H) (fun _ => rfl) _ _ _ raw
  simpa only [Lift.configuration, MachineCloudPadding.Placement.label, vertexPlacement,
    readyState, MachineRegularOriginalBody.readyState, vertexStates, Equiv.coe_fn_mk,
    dummyBits, id_eq] using placed

@[simp] theorem working_fuel (data : Data) (fuel saved : List Bool) :
    working data fuel saved dummyFuel = fuel := rfl

@[simp] theorem working_scratch (data : Data) (fuel saved : List Bool) :
    working data fuel saved scratch = saved := rfl

theorem loopPositiveStep (H : BaseTable) (data : Data) (d : Nat) :
    TM2.step (program H) ⟨some .loop, readyState H, working data (encodeWord (d + 1)) []⟩ =
      some ⟨some (.vertex (MachineRegularVertexBlock.dummyEntry internalDegree
        MachineRegularOriginalBody.degree_positive)), readyState H,
        working data (encodeWord d) []⟩ := by
  change some (TM2.stepAux (program H .loop) _ _) = _
  simp only [program, TM2.stepAux, working_fuel, encodeWord, List.replicate_succ,
    List.cons_append, List.head?_cons, Option.getD_some, Bool.cond_true,
    List.tail_cons, working_update_fuel]
  rfl

theorem loopZeroStep (H : BaseTable) (data : Data) :
    TM2.step (program H) ⟨some .loop, readyState H, working data (encodeWord 0) []⟩ =
      some ⟨some (.cleanup MachineRegularOwnerCleanup.entry), readyState H,
        working data (encodeWord 0) []⟩ := by rfl

theorem bumpStep (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (n : Nat) (output fuel : List Bool) :
    TM2.step (program H) ⟨some .bump, readyState H, working (vertexData H t v n output) fuel []⟩ =
      some ⟨some .loop, readyState H, working (vertexData H t v (n + 1) output) fuel []⟩ := by
  change some (TM2.stepAux (program H .bump) _ _) = _
  simp only [program, TM2.stepAux,
    Function.update_of_ne (by decide : core 3 ≠ core 1),
    working_update_global, working_update_local]
  congr 2

theorem loopPrefixTrace (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) (n : Nat) (hn : n ≤ padding t v) :
    (advance (TM2.step (program H)))^[loopSteps H t v output n hn]
      (some ⟨some .loop, readyState H, loopFrame H t v output 0⟩) =
      some ⟨some .loop, readyState H, loopFrame H t v output n⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have h : n < padding t v := by omega
      have first := ih (by omega)
      have hremaining : padding t v - n = (padding t v - (n + 1)) + 1 := by omega
      have guard := loopPositiveStep H (loopData H t v output n) (padding t v - (n + 1))
      rw [← hremaining] at guard
      have guardRun : (advance (TM2.step (program H)))^[1]
          (some ⟨some .loop, readyState H, loopFrame H t v output n⟩) =
          some ⟨some (.vertex (MachineRegularVertexBlock.dummyEntry internalDegree
            MachineRegularOriginalBody.degree_positive)), readyState H,
            working (loopData H t v output n) (encodeWord (padding t v - (n + 1))) []⟩ := oneStep guard
      have vertex := vertexTrace H t v ⟨n, h⟩
        (output ++ blocksPrefix (dummyBits H t v) n) (encodeWord (padding t v - (n + 1)))
      have bump := bumpStep H t v n
        ((output ++ blocksPrefix (dummyBits H t v) n) ++ dummyBits H t v ⟨n, h⟩)
        (encodeWord (padding t v - (n + 1)))
      have bumpRun := oneStep bump
      have all := joinTrace (joinTrace (joinTrace first guardRun) vertex) bumpRun
      simpa only [loopSteps, loopFrame, loopData, blocksPrefix_succ _ n h,
        List.append_assoc, Nat.add_assoc] using all

theorem preparationTrace (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) :
    (advance (TM2.step (program H)))^[preSteps t v]
      (some (cfg H (some entry) (initialData t v output))) =
      some ⟨some .guard, readyState H,
        working (seededData t v output) (encodeWord (padding t v)) []⟩ :=
  joinTrace (joinTrace (metadataTrace H t v output) (copyCountTrace H t v output))
    (copyFuelTrace H t v output)

theorem cleanupFrame (data : Data) (fuel : List Bool) (d o : Nat) :
    MachineRegularOwnerCleanup.finalTapes (working data fuel []) d o =
      frame { data with
        localRank := []
        count := []
        rotor := []
        padding := []
        level := []
        offset := encodeWord (d + o) } := by
  funext j
  rw [MachineRegularOwnerCleanup.finalTapes_apply]
  cases j with
  | inl j => cases j with
    | inl i => fin_cases i <;>
        simp [MachineRegularOwnerCleanup.cleanupTapes, MachineRegularOwnerCleanup.localRank,
          MachineRegularOwnerCleanup.count, MachineRegularOwnerCleanup.rotor,
          MachineRegularOwnerCleanup.padding, MachineRegularOwnerCleanup.level,
          MachineRegularOwnerCleanup.dummyFuel, MachineRegularOwnerCleanup.prefixTape,
          MachineRegularOwnerCleanup.core, frame, working, MachineRegularOriginalBody.frame,
          MachineRegularMetadata.frame]
    | inr j => cases j with
      | inl e => cases e <;>
          simp [MachineRegularOwnerCleanup.cleanupTapes, MachineRegularOwnerCleanup.localRank,
            MachineRegularOwnerCleanup.count, MachineRegularOwnerCleanup.rotor,
            MachineRegularOwnerCleanup.padding, MachineRegularOwnerCleanup.level,
            MachineRegularOwnerCleanup.dummyFuel,
            MachineRegularOwnerCleanup.core, frame, working, MachineRegularOriginalBody.frame,
            MachineRegularMetadata.frame]
      | inr e =>
          simp [MachineRegularOwnerCleanup.cleanupTapes, MachineRegularOwnerCleanup.localRank,
            MachineRegularOwnerCleanup.count, MachineRegularOwnerCleanup.rotor,
            MachineRegularOwnerCleanup.padding, MachineRegularOwnerCleanup.level,
            MachineRegularOwnerCleanup.dummyFuel, MachineRegularOwnerCleanup.prefixTape,
            MachineRegularOwnerCleanup.core, frame, working, MachineRegularOriginalBody.frame]
  | inr i => fin_cases i <;>
      simp [MachineRegularOwnerCleanup.cleanupTapes, MachineRegularOwnerCleanup.localRank,
        MachineRegularOwnerCleanup.count, MachineRegularOwnerCleanup.rotor,
        MachineRegularOwnerCleanup.padding, MachineRegularOwnerCleanup.level,
        MachineRegularOwnerCleanup.dummyFuel, MachineRegularOwnerCleanup.prefixTape,
        MachineRegularOwnerCleanup.core, frame, working]

theorem ownerBits_zero (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (hp : padding t v = 0) : ownerBits H t v = [] := by
  have hnil : List.ofFn (dummyBits H t v) = [] := by
    apply List.length_eq_zero_iff.mp
    simpa only [List.length_ofFn] using hp
  exact congrArg List.flatten hnil

theorem cleanupZeroFrame (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) (hp : padding t v = 0) :
    MachineRegularOwnerCleanup.finalTapes
      (working (seededData t v output) (encodeWord 0) []) (padding t v)
      (PreprocessingPaddingOffsets.offset (padding t) v.val) = frame (finalData H t v output) := by
  rw [cleanupFrame]
  apply congrArg frame
  simp only [seededData, metadataData, MachineRegularMetadata.cloudData, initialData,
    finalData, hp, ownerBits_zero H t v hp, List.append_nil, Nat.add_zero, Nat.zero_add]

theorem cleanupLoopFrame (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) :
    MachineRegularOwnerCleanup.finalTapes (loopFrame H t v output (padding t v))
      (padding t v) (PreprocessingPaddingOffsets.offset (padding t) v.val) =
        frame (finalData H t v output) := by
  rw [loopFrame, cleanupFrame]
  apply congrArg frame
  simp only [loopData, vertexData, seededData, metadataData, MachineRegularMetadata.cloudData,
    initialData, finalData, blocksPrefix_all, dummyBits, ownerBits,
    Nat.add_comm (padding t v) (PreprocessingPaddingOffsets.offset (padding t) v.val)]

theorem cleanupZeroTrace (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) (hp : padding t v = 0) :
    (advance (TM2.step (program H)))^[MachineRegularOwnerCleanup.steps
        (working (seededData t v output) (encodeWord 0) []) (padding t v)]
      (some ⟨some (.cleanup MachineRegularOwnerCleanup.entry), readyState H,
        working (seededData t v output) (encodeWord 0) []⟩) =
      some (cfg H none (finalData H t v output)) := by
  have run := MachineRegularOwnerCleanup.traceAt Label.cleanup none (program H) (fun _ => rfl)
    (working (seededData t v output) (encodeWord 0) []) (padding t v)
    (PreprocessingPaddingOffsets.offset (padding t) v.val) rfl rfl rfl
    (MachineRegularOriginalBody.readyState H) none
  rw [cleanupZeroFrame H t v output hp] at run
  exact run

theorem cleanupLoopTrace (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) :
    (advance (TM2.step (program H)))^[MachineRegularOwnerCleanup.steps
        (loopFrame H t v output (padding t v)) (padding t v)]
      (some ⟨some (.cleanup MachineRegularOwnerCleanup.entry), readyState H,
        loopFrame H t v output (padding t v)⟩) =
      some (cfg H none (finalData H t v output)) := by
  have run := MachineRegularOwnerCleanup.traceAt Label.cleanup none (program H) (fun _ => rfl)
    (loopFrame H t v output (padding t v)) (padding t v)
    (PreprocessingPaddingOffsets.offset (padding t) v.val) rfl rfl rfl
    (MachineRegularOriginalBody.readyState H) none
  rw [cleanupLoopFrame] at run
  exact run

theorem loopTrace (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) :
    (advance (TM2.step (program H)))^[loopSteps H t v output (padding t v) le_rfl + 1]
      (some ⟨some .loop, readyState H, loopFrame H t v output 0⟩) =
      some ⟨some (.cleanup MachineRegularOwnerCleanup.entry), readyState H,
        loopFrame H t v output (padding t v)⟩ := by
  have first := loopPrefixTrace H t v output (padding t v) le_rfl
  have last : (advance (TM2.step (program H)))^[1]
      (some ⟨some .loop, readyState H, loopFrame H t v output (padding t v)⟩) =
      some ⟨some (.cleanup MachineRegularOwnerCleanup.entry), readyState H,
        loopFrame H t v output (padding t v)⟩ := by
    simpa only [loopFrame, Nat.sub_self] using
      oneStep (loopZeroStep H (loopData H t v output (padding t v)))
  exact joinTrace first last

/-- Actual complete owner execution, including the genuinely empty padding case.
The bound is assembled from proven component bounds; its family term is not
used as an exact number of transitions. -/
noncomputable def ownerInTime (H : BaseTable) (t : GraphTables.Table)
    (v : Fin t.vertices) (output : List Bool) :
    StateTransition.EvalsToInTime (TM2.step (program H))
      (cfg H (some entry) (initialData t v output))
      (some (cfg H none (finalData H t v output))) (ownerTime H t v output) := by
  have prepared := preparationTrace H t v output
  by_cases hp : padding t v = 0
  · have gate : (advance (TM2.step (program H)))^[1]
        (some ⟨some .guard, readyState H,
          working (seededData t v output) (encodeWord (padding t v)) []⟩) =
        some ⟨some (.cleanup MachineRegularOwnerCleanup.entry), readyState H,
          working (seededData t v output) (encodeWord 0) []⟩ := by
      simpa only [hp] using oneStep (guardZeroStep H (seededData t v output))
    have all := joinTrace (joinTrace prepared gate) (cleanupZeroTrace H t v output hp)
    refine { steps := _, evals_in_steps := all, steps_le_m := ?_ }
    simp only [ownerTime, cleanupCost, ite_eq_left hp, Nat.add_zero, le_refl]
  · have gate : (advance (TM2.step (program H)))^[1]
        (some ⟨some .guard, readyState H,
          working (seededData t v output) (encodeWord (padding t v)) []⟩) =
        some ⟨some (.family .start), readyState H,
          working (seededData t v output) (encodeWord (padding t v)) []⟩ :=
      oneStep (guardPositiveStep H (seededData t v output) (padding t v) (Nat.pos_of_ne_zero hp))
    have all := joinTrace
      (joinTrace (joinTrace (joinTrace prepared gate) (familyTrace H t v output))
        (loopTrace H t v output)) (cleanupLoopTrace H t v output)
    refine { steps := _, evals_in_steps := all, steps_le_m := ?_ }
    have hb : familySteps H t v output ≤
        MachineRegularFamily.timePolynomial.eval (encodeWord (cloudSize t v)).length :=
      (familyExecution H t v output).steps_le_m
    simp only [ownerTime, cleanupCost, ite_eq_right hp]
    omega

noncomputable def totalSteps (H : BaseTable) (t : GraphTables.Table)
    (v : Fin t.vertices) (output : List Bool) : Nat := (ownerInTime H t v output).steps

theorem ownerTrace (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) :
    (advance (TM2.step (program H)))^[totalSteps H t v output]
      (some (cfg H (some entry) (initialData t v output))) =
      some (cfg H none (finalData H t v output)) := (ownerInTime H t v output).evals_in_steps

theorem totalSteps_le (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) : totalSteps H t v output ≤ ownerTime H t v output :=
  (ownerInTime H t v output).steps_le_m

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineRegularOwnerBodyBounds
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Bounds for actual dummy-owner execution

The size parameter includes the old output length. During the owner loop,
newly emitted dummy blocks are bounded by the actual complete regularized
table codec. No hypothesis about a machine body's execution supplies a bound.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBodyBounds

open Turing MachineComposition PCP PreprocessingCloudIndex PreprocessingRegularTables
open PreprocessingMachineBounds PreprocessingRegularLoopWords

def bodySize (t : GraphTables.Table) (output : List Bool) : Nat :=
  inputLength t + output.length

theorem wide_le (t : GraphTables.Table) (output : List Bool) :
    inputLength t ≤ (ExpanderFamily.growth+1)*bodySize t output ∧
    ExpanderFamily.growth*inputLength t ≤ (ExpanderFamily.growth+1)*bodySize t output ∧
    output.length ≤ (ExpanderFamily.growth+1)*bodySize t output := by
  have hN : inputLength t ≤ bodySize t output := Nat.le_add_right _ _
  have hO : output.length ≤ bodySize t output := Nat.le_add_left _ _
  have hg := Nat.mul_le_mul_left ExpanderFamily.growth hN
  rw [Nat.add_mul, Nat.one_mul]
  omega

/-- Any finite prefix inside this owner is a part of the actual output table,
including when the supplied prefix length is larger than the number of blocks. -/
theorem ownerPrefix_length_le (H : BaseTable) (t : GraphTables.Table)
    (v : Fin t.vertices) (n : Nat) :
    (blocksPrefix (PreprocessingRegularWords.dummyVertexBits t (padding t)
      (familyCloudTable H t) v) n).length ≤ regularPolynomial.eval (inputLength t) := by
  have h := PreprocessingRegularBounds.regular_dummyPrefix_le t H v n
  simp only [PreprocessingRegularBounds.dummyPrefix, List.length_append] at h
  omega

theorem growingOutput_length_le (H : BaseTable) (t : GraphTables.Table)
    (v : Fin t.vertices) (n : Nat) (output : List Bool) :
    (output ++ blocksPrefix (PreprocessingRegularWords.dummyVertexBits t (padding t)
      (familyCloudTable H t) v) n).length ≤
      (ExpanderFamily.growth+1)*bodySize t output + regularPolynomial.eval (bodySize t output) := by
  have h := (ownerPrefix_length_le H t v n).trans
    (natPolynomial_eval_mono regularPolynomial (Nat.le_add_right (inputLength t) output.length))
  have hO := (wide_le t output).2.2
  rw [List.length_append]
  exact Nat.add_le_add hO h

/-- One actual dummy block has a uniform polynomial cost at every prefix of
the owner loop. The only inputs are the real table, indices, and old output. -/
theorem dummySteps_le (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (j : Fin (padding t v)) (n : Nat) (output : List Bool) :
    MachineRegularVertexBlock.dummySteps t (padding t) (familyCloudTable H t) v j
      (output ++ blocksPrefix (PreprocessingRegularWords.dummyVertexBits t (padding t)
        (familyCloudTable H t) v) n).length ≤
      (blockPolynomial internalDegree).eval (bodySize t output) := by
  let x := paddedNew t (padding t) v j
  let W := (ExpanderFamily.growth+1)*bodySize t output
  have bounds := wide_le t output
  have hx := (vertexOrder t (padding t) x.val).isLt.le.trans (regularVertices_le_input t)
  have hv := v.isLt.le.trans (GraphTables.vertices_le_tableBits_length t)
  have hi := (paddedCloudRank t (padding t) v x).isLt.le.trans (cloudTotal_le_input t v)
  have hk := cloudSize_le_input t v
  have hm := GraphTables.darts_le_tableBits_length t
  have ho := prefix_le_input t v.val
  have hV := regularVertices_le_input t
  have hR := (cloudRotorBits_le t v (familyCloudTable H t v)).trans
    (natPolynomial_eval_mono (rotorPolynomial internalDegree)
      (Nat.le_add_right (inputLength t) output.length))
  have hO := growingOutput_length_le H t v n output
  have raw := MachineRegularVertexBlock.dummySteps_le internalDegree
    MachineRegularOriginalBody.degree_positive t (padding t) (familyCloudTable H t) v j
      (output ++ blocksPrefix (PreprocessingRegularWords.dummyVertexBits t (padding t)
        (familyCloudTable H t) v) n).length
  have bound := dummyTimeBound_le internalDegree _ _ _ _ _ _ _ _ _ _ W _ _
    bounds.1 hR (hx.trans bounds.2.1) (hv.trans bounds.1) (hi.trans bounds.2.1)
    (hk.trans bounds.1) (ho.trans bounds.2.1) (hm.trans bounds.1) hO
    (hV.trans bounds.2.1)
  rw [blockPolynomial_eval]
  exact raw.trans bound

noncomputable def timePolynomial : Polynomial Nat :=
  prePolynomial + MachineRegularExecutionBounds.familyPolynomial + loopPolynomial +
    cleanupPolynomial + 2

theorem preSteps_le (t : GraphTables.Table) (v : Fin t.vertices) (output : List Bool) :
    MachineRegularOwnerBody.preSteps t v ≤ prePolynomial.eval (bodySize t output) := by
  have bounds := wide_le t output
  have hk := cloudSize_le_input t v
  have hd := cloudTotal_le_input t v
  have hv := v.isLt.le.trans (GraphTables.vertices_le_tableBits_length t)
  change v.val ≤ inputLength t at hv
  have hN : inputLength t ≤ bodySize t output := Nat.le_add_right _ _
  have hinput : MachineCloudPadding.inputLength t v [] ≤ 2*bodySize t output+1 := by
    simp only [MachineCloudPadding.inputLength, List.append_nil, encodeWord_length]
    change inputLength t + (v.val+1) ≤ _
    omega
  have hm := (MachineCloudPadding.totalTime_le t v []).trans
    (natPolynomial_eval_mono MachineCloudPadding.timePolynomial hinput)
  simp only [MachineRegularOwnerBody.preSteps, prePolynomial, wide, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_ofNat, Polynomial.eval_one]
  omega

theorem loopSteps_le (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) (n : Nat) (hn : n ≤ padding t v) :
    MachineRegularOwnerBody.loopSteps H t v output n hn ≤
      n * ((blockPolynomial internalDegree).eval (bodySize t output) + 2) := by
  induction n with
  | zero => simp only [MachineRegularOwnerBody.loopSteps, Nat.zero_mul, le_refl]
  | succ n ih =>
    have h : n < padding t v := by omega
    have first := ih (by omega)
    have second := dummySteps_le H t v ⟨n, h⟩ n output
    rw [MachineRegularOwnerBody.loopSteps, Nat.succ_mul]
    change MachineRegularOwnerBody.loopSteps H t v output n _ +
      (1 + MachineRegularVertexBlock.dummySteps t (padding t) (familyCloudTable H t) v ⟨n, h⟩
        (output ++ blocksPrefix (PreprocessingRegularWords.dummyVertexBits t (padding t)
          (familyCloudTable H t) v) n).length + 1) ≤ _
    omega

theorem allLoopSteps_le (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) :
    MachineRegularOwnerBody.loopSteps H t v output (padding t v) le_rfl ≤
      loopPolynomial.eval (bodySize t output) := by
  have hd := (cloudTotal_le_input t v).trans (wide_le t output).2.1
  have hp : padding t v ≤ (ExpanderFamily.growth+1)*bodySize t output := by omega
  have h := (loopSteps_le H t v output (padding t v) le_rfl).trans
    (Nat.mul_le_mul_right _ hp)
  simpa only [loopPolynomial, wide, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat] using h

/-- Exact cost of the six physical drain loops and the prefix addition,
expressed through the actual entry stack lengths. -/
theorem cleanupSteps_working (data : MachineRegularOwnerBody.Data)
    (fuel saved : List Bool) (d : Nat) :
    MachineRegularOwnerCleanup.steps (MachineRegularOwnerBody.working data fuel saved) d =
      2*(d+1) + data.localRank.length + data.count.length + data.rotor.length +
        data.padding.length + data.level.length + fuel.length + 6 := by
  change 2*(d+1) + ((data.localRank.length+1) + ((data.count.length+1) +
    ((data.rotor.length+1) + ((data.padding.length+1) + ((data.level.length+1) +
      ((fuel.length+1)+0)))))) = _
  omega

theorem cleanupCost_le (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) :
    MachineRegularOwnerBody.cleanupCost H t v output ≤
      cleanupPolynomial.eval (bodySize t output) := by
  have bounds := wide_le t output
  have hk := (cloudSize_le_input t v).trans bounds.1
  have htotal := (cloudTotal_le_input t v).trans bounds.2.1
  have hl := (level_le_input t v).trans bounds.1
  have hp : MachineCloudPadding.padding (cloudSize t v) = padding t v := rfl
  by_cases hd : padding t v = 0
  · rw [MachineRegularOwnerBody.cleanupCost, ite_eq_left hd, cleanupSteps_working]
    simp only [MachineRegularOwnerBody.seededData, MachineRegularOwnerBody.metadataData,
      MachineRegularMetadata.cloudData, MachineRegularOwnerBody.initialData,
      hp, encodeWord_length, List.length_nil, cleanupPolynomial, wide,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      Polynomial.eval_ofNat]
    omega
  · have hpositive : 0 < padding t v := by omega
    have hkpos := PreprocessingFamilyBridge.cloudSize_pos_of_dummy t v ⟨0, hpositive⟩
    have hrotor := PreprocessingFamilyBridge.familyRotor_eq_familyCloudTable H t v hkpos
    change MachineRegularFamily.rotor H (cloudSize t v) = _ at hrotor
    have hR := (cloudRotorBits_le t v (familyCloudTable H t v)).trans
      (natPolynomial_eval_mono (rotorPolynomial internalDegree)
        (Nat.le_add_right (inputLength t) output.length))
    rw [← hrotor] at hR
    change (MachineRegularFamily.rotor H (cloudSize t v)).length ≤
      (rotorPolynomial internalDegree).eval (bodySize t output) at hR
    rw [MachineRegularOwnerBody.cleanupCost, ite_eq_right hd,
      MachineRegularOwnerBody.loopFrame, cleanupSteps_working]
    simp only [MachineRegularOwnerBody.loopData, MachineRegularOwnerBody.vertexData,
      MachineRegularOwnerBody.seededData, MachineRegularOwnerBody.metadataData,
      MachineRegularMetadata.cloudData, MachineRegularOwnerBody.initialData,
      hp, encodeWord_length, Nat.sub_self, cleanupPolynomial, wide,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      Polynomial.eval_ofNat]
    omega

/-- The whole owner budget follows from the real recurrence and its separately
proved stage bounds. The zero-padding branch performs no family or vertex work. -/
theorem ownerTime_le (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) :
    MachineRegularOwnerBody.ownerTime H t v output ≤ timePolynomial.eval (bodySize t output) := by
  have hp := preSteps_le t v output
  have hc := cleanupCost_le H t v output
  have hl := allLoopSteps_le H t v output
  have hf := (MachineRegularExecutionBounds.family_budget_le t v).trans
    (natPolynomial_eval_mono MachineRegularExecutionBounds.familyPolynomial
      (Nat.le_add_right (inputLength t) output.length))
  have hfamily : MachineRegularFamily.timePolynomial.eval (encodeWord (cloudSize t v)).length ≤
      MachineRegularExecutionBounds.familyPolynomial.eval (bodySize t output) := by
    simpa only [bodySize, MachineRegularFamily.timePolynomial, encodeWord_length, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat] using hf
  simp only [MachineRegularOwnerBody.ownerTime, timePolynomial, Polynomial.eval_add,
    Polynomial.eval_ofNat]
  split_ifs <;> omega

theorem totalSteps_le (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) :
    MachineRegularOwnerBody.totalSteps H t v output ≤ timePolynomial.eval (bodySize t output) :=
  (MachineRegularOwnerBody.totalSteps_le H t v output).trans (ownerTime_le H t v output)

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBodyBounds

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineRegularTable
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual regular-table construction

The header subroutine reads the two original graph headers, computes the
padding total by the actual prefix machine, performs unary addition and
constant multiplication, and appends both resulting header fields. The
outer vertex routines are assembled from actual metadata and row programs.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable

open Turing MachineComposition
open UniqueGamesTheorem.Foundations.PCP

namespace Header

@[simp] theorem frame_table (t n v f s m i w a N R e o : List Bool) :
    frame t n v f s m i w a N R e o tableTape = t := rfl
@[simp] theorem frame_n (t n v f s m i w a N R e o : List Bool) :
    frame t n v f s m i w a N R e o nTape = n := rfl
@[simp] theorem frame_query (t n v f s m i w a N R e o : List Bool) :
    frame t n v f s m i w a N R e o queryTape = v := rfl
@[simp] theorem frame_fuel (t n v f s m i w a N R e o : List Bool) :
    frame t n v f s m i w a N R e o fuelTape = f := rfl
@[simp] theorem frame_sum (t n v f s m i w a N R e o : List Bool) :
    frame t n v f s m i w a N R e o sumTape = s := rfl
@[simp] theorem frame_m (t n v f s m i w a N R e o : List Bool) :
    frame t n v f s m i w a N R e o mTape = m := rfl
@[simp] theorem frame_index (t n v f s m i w a N R e o : List Bool) :
    frame t n v f s m i w a N R e o indexTape = i := rfl
@[simp] theorem frame_work (t n v f s m i w a N R e o : List Bool) :
    frame t n v f s m i w a N R e o workTape = w := rfl
@[simp] theorem frame_scratch (t n v f s m i w a N R e o : List Bool) :
    frame t n v f s m i w a N R e o scratchTape = a := rfl
@[simp] theorem frame_vertices (t n v f s m i w a N R e o : List Bool) :
    frame t n v f s m i w a N R e o verticesTape = N := rfl
@[simp] theorem frame_darts (t n v f s m i w a N R e o : List Bool) :
    frame t n v f s m i w a N R e o dartsTape = R := rfl
@[simp] theorem frame_emit (t n v f s m i w a N R e o : List Bool) :
    frame t n v f s m i w a N R e o emitTape = e := rfl
@[simp] theorem frame_output (t n v f s m i w a N R e o : List Bool) :
    frame t n v f s m i w a N R e o outputTape = o := rfl

@[simp] theorem update_frame_table (t n v f s m i w a N R e o x : List Bool) :
    Function.update (frame t n v f s m i w a N R e o) tableTape x =
      frame x n v f s m i w a N R e o := by
  funext k
  cases k with
  | inl k =>
      cases k with
      | inner j => cases j <;> rfl
      | bound => rfl
      | remaining => rfl
      | total => rfl
  | inr j => cases j <;> rfl

@[simp] theorem update_frame_n (t n v f s m i w a N R e o x : List Bool) :
    Function.update (frame t n v f s m i w a N R e o) nTape x =
      frame t x v f s m i w a N R e o := by
  funext k
  cases k with
  | inl k =>
      cases k with
      | inner j => cases j <;> rfl
      | bound => rfl
      | remaining => rfl
      | total => rfl
  | inr j => cases j <;> rfl

@[simp] theorem update_frame_query (t n v f s m i w a N R e o x : List Bool) :
    Function.update (frame t n v f s m i w a N R e o) queryTape x =
      frame t n x f s m i w a N R e o := by
  funext k
  cases k with
  | inl k =>
      cases k with
      | inner j => cases j <;> rfl
      | bound => rfl
      | remaining => rfl
      | total => rfl
  | inr j => cases j <;> rfl

@[simp] theorem update_frame_fuel (t n v f s m i w a N R e o x : List Bool) :
    Function.update (frame t n v f s m i w a N R e o) fuelTape x =
      frame t n v x s m i w a N R e o := by
  funext k
  cases k with
  | inl k =>
      cases k with
      | inner j => cases j <;> rfl
      | bound => rfl
      | remaining => rfl
      | total => rfl
  | inr j => cases j <;> rfl

@[simp] theorem update_frame_sum (t n v f s m i w a N R e o x : List Bool) :
    Function.update (frame t n v f s m i w a N R e o) sumTape x =
      frame t n v f x m i w a N R e o := by
  funext k
  cases k with
  | inl k =>
      cases k with
      | inner j => cases j <;> rfl
      | bound => rfl
      | remaining => rfl
      | total => rfl
  | inr j => cases j <;> rfl

@[simp] theorem update_frame_m (t n v f s m i w a N R e o x : List Bool) :
    Function.update (frame t n v f s m i w a N R e o) mTape x =
      frame t n v f s x i w a N R e o := by
  funext k
  cases k with
  | inl k =>
      cases k with
      | inner j => cases j <;> rfl
      | bound => rfl
      | remaining => rfl
      | total => rfl
  | inr j => cases j <;> rfl

@[simp] theorem update_frame_index (t n v f s m i w a N R e o x : List Bool) :
    Function.update (frame t n v f s m i w a N R e o) indexTape x =
      frame t n v f s m x w a N R e o := by
  funext k
  cases k with
  | inl k =>
      cases k with
      | inner j => cases j <;> rfl
      | bound => rfl
      | remaining => rfl
      | total => rfl
  | inr j => cases j <;> rfl

@[simp] theorem update_frame_work (t n v f s m i w a N R e o x : List Bool) :
    Function.update (frame t n v f s m i w a N R e o) workTape x =
      frame t n v f s m i x a N R e o := by
  funext k
  cases k with
  | inl k =>
      cases k with
      | inner j => cases j <;> rfl
      | bound => rfl
      | remaining => rfl
      | total => rfl
  | inr j => cases j <;> rfl

@[simp] theorem update_frame_scratch (t n v f s m i w a N R e o x : List Bool) :
    Function.update (frame t n v f s m i w a N R e o) scratchTape x =
      frame t n v f s m i w x N R e o := by
  funext k
  cases k with
  | inl k =>
      cases k with
      | inner j => cases j <;> rfl
      | bound => rfl
      | remaining => rfl
      | total => rfl
  | inr j => cases j <;> rfl

@[simp] theorem update_frame_vertices (t n v f s m i w a N R e o x : List Bool) :
    Function.update (frame t n v f s m i w a N R e o) verticesTape x =
      frame t n v f s m i w a x R e o := by
  funext k
  cases k with
  | inl k =>
      cases k with
      | inner j => cases j <;> rfl
      | bound => rfl
      | remaining => rfl
      | total => rfl
  | inr j => cases j <;> rfl

@[simp] theorem update_frame_darts (t n v f s m i w a N R e o x : List Bool) :
    Function.update (frame t n v f s m i w a N R e o) dartsTape x =
      frame t n v f s m i w a N x e o := by
  funext k
  cases k with
  | inl k =>
      cases k with
      | inner j => cases j <;> rfl
      | bound => rfl
      | remaining => rfl
      | total => rfl
  | inr j => cases j <;> rfl

@[simp] theorem update_frame_emit (t n v f s m i w a N R e o x : List Bool) :
    Function.update (frame t n v f s m i w a N R e o) emitTape x =
      frame t n v f s m i w a N R x o := by
  funext k
  cases k with
  | inl k =>
      cases k with
      | inner j => cases j <;> rfl
      | bound => rfl
      | remaining => rfl
      | total => rfl
  | inr j => cases j <;> rfl

@[simp] theorem update_frame_output (t n v f s m i w a N R e o x : List Bool) :
    Function.update (frame t n v f s m i w a N R e o) outputTape x =
      frame t n v f s m i w a N R e x := by
  funext k
  cases k with
  | inl k =>
      cases k with
      | inner j => cases j <;> rfl
      | bound => rfl
      | remaining => rfl
      | total => rfl
  | inr j => cases j <;> rfl

inductive Label
  | init | seedM | clearIndex
  | lookup (field : Field) (label : MachinePreservingLookupClean.Label)
  | prefix (label : MachineCloudPrefix.Label)
  | copyFirst (phase : CopyPhase) | copySecond (phase : CopyPhase)
  | add | scaleSeed | scaleScan | scaleRestore
  | appendFirst | appendSecond | appendThird
  | cleanupZeros | clearQuery | done
  deriving DecidableEq, Fintype

def fieldTape : Field → Tape
  | .vertices => nTape
  | .darts => mTape

def fieldExit : Field → Label
  | .vertices => .seedM
  | .darts => .clearIndex

def lookupSlots (field : Field) : Fin 5 → Tape :=
  ![tableTape, indexTape, workTape, fieldTape field, scratchTape]

theorem lookupSlots_injective (field : Field) : Function.Injective (lookupSlots field) := by
  intro i j h
  cases field <;> fin_cases i <;> fin_cases j <;>
    simp_all [lookupSlots, fieldTape, tableTape, indexTape, workTape, nTape, mTape, scratchTape]

def copySource : CopyPhase → Tape
  | .count => mTape
  | .rEmit => dartsTape
  | .nEmit => verticesTape

def copyDestination : CopyPhase → Tape
  | .count => verticesTape
  | .rEmit | .nEmit => emitTape

def copyExit : CopyPhase → Label
  | .count => .add
  | .rEmit => .copyFirst .nEmit
  | .nEmit => .appendFirst

def prefixView : Tape → Option MachineCloudPrefix.Tape
  | .inl k => some k
  | .inr _ => none

theorem prefixView_left (k : MachineCloudPrefix.Tape) : prefixView (.inl k) = some k := rfl

theorem prefixView_right (j : Tape) (k : MachineCloudPrefix.Tape)
    (h : prefixView j = some k) : Sum.inl k = j := by
  cases j <;> simp_all [prefixView]

theorem prefixTapes (inner : MachineCloudPrefix.Tape → List Bool) (extra : Tape → List Bool) :
    MachineCloudPadding.Placement.tapes prefixView inner extra =
      memory inner (extra mTape) (extra indexTape) (extra workTape) (extra scratchTape)
        (extra verticesTape) (extra dartsTape) (extra emitTape) (extra outputTape) := by
  funext j
  cases j with
  | inl k => rfl
  | inr k => cases k <;> rfl

variable {σ : Type}

def program (q : Nat) : Label → TM2.Stmt Alphabet Label (State σ)
  | .init => .push indexTape (fun _ => false) (.goto fun _ => .lookup .vertices (.run .copyFirst))
  | .seedM => .push indexTape (fun _ => true) (.goto fun _ => .lookup .darts (.run .copyFirst))
  | .clearIndex => .pop indexTape (fun state _ => (state.1, none))
      (.goto fun _ => .prefix .init)
  | .lookup field l => MachinePreservingLookupClean.statement (lookupSlots field)
      (Label.lookup field) (some (fieldExit field)) l
  | .prefix l => MachineCloudPadding.Placement.statement Sum.inl Label.prefix
      (some (.copyFirst .count)) (MachineCloudPrefix.program l)
  | .copyFirst phase => Reduction.MachineTransfer.loopAt (copySource phase) scratchTape
      id false (.copyFirst phase) (some (.copySecond phase))
  | .copySecond phase => MachineCopy.forkLoop scratchTape (copySource phase) (copyDestination phase)
      false (.copySecond phase) (some (copyExit phase))
  | .add => MachineUnaryAddAt.loop sumTape verticesTape .add (some .scaleSeed)
  | .scaleSeed => MachineUnaryAffineAt.seed dartsTape 0 .scaleScan
  | .scaleScan => MachineUnaryAffineAt.scan verticesTape scratchTape dartsTape (q + 1)
      .scaleScan .scaleRestore
  | .scaleRestore => Reduction.MachineTransfer.loopAt scratchTape verticesTape id false
      .scaleRestore (some (.copyFirst .rEmit))
  | .appendFirst => Reduction.MachineTransfer.loopAt outputTape scratchTape id false
      .appendFirst (some .appendSecond)
  | .appendSecond => Reduction.MachineTransfer.loopAt emitTape scratchTape id false
      .appendSecond (some .appendThird)
  | .appendThird => Reduction.MachineTransfer.loopAt scratchTape outputTape id false
      .appendThird (some .cleanupZeros)
  | .cleanupZeros => .pop sumTape (fun state _ => (state.1, none))
      (.pop fuelTape (fun state _ => (state.1, none)) (.goto fun _ => .clearQuery))
  | .clearQuery => MachineLookup.discard queryTape .clearQuery .done
  | .done => .halt

def paddingTotal (t : GraphTables.Table) : Nat :=
  PreprocessingPaddingOffsets.offset (PreprocessingRegularTables.padding t) t.vertices

def vertexTotal (t : GraphTables.Table) : Nat :=
  PreprocessingRegularTables.vertexCount t (PreprocessingRegularTables.padding t)

def dartTotal (q : Nat) (t : GraphTables.Table) : Nat := vertexTotal t * (q + 1)

theorem vertexTotal_eq (t : GraphTables.Table) :
    vertexTotal t = t.darts + paddingTotal t := by
  unfold vertexTotal PreprocessingRegularTables.vertexCount paddingTotal
  rw [PreprocessingPaddingOffsets.offset_all]

theorem initStep (q : Nat) (table output : List Bool) (ambient : σ)
    (register : Option Bool) :
    TM2.step (program q)
      ⟨some .init, ((ambient, false), register),
        frame table [] [] [] [] [] [] [] [] [] [] [] output⟩ =
      some ⟨some (.lookup .vertices (.run .copyFirst)), ((ambient, false), register),
        frame table [] [] [] [] [] (encodeWord 0) [] [] [] [] [] output⟩ := by
  simp [TM2.step, program, TM2.stepAux, encodeWord]

theorem seedMStep (q : Nat) (table n output : List Bool) (ambient : σ)
    (register : Option Bool) :
    TM2.step (program q)
      ⟨some .seedM, ((ambient, false), register),
        frame table n [] [] [] [] (encodeWord 0) [] [] [] [] [] output⟩ =
      some ⟨some (.lookup .darts (.run .copyFirst)), ((ambient, false), register),
        frame table n [] [] [] [] (encodeWord 1) [] [] [] [] [] output⟩ := by
  simp [TM2.step, program, TM2.stepAux, encodeWord]

theorem clearIndexStep (q : Nat) (table n m output : List Bool) (ambient : σ)
    (register : Option Bool) :
    TM2.step (program q)
      ⟨some .clearIndex, ((ambient, false), register),
        frame table n [] [] [] m (encodeWord 0) [] [] [] [] [] output⟩ =
      some ⟨some (.prefix .init), ((ambient, false), none),
        frame table n [] [] [] m [] [] [] [] [] [] output⟩ := by
  simp [TM2.step, program, TM2.stepAux, encodeWord]

def readTime (t : GraphTables.Table) : Nat :=
  1 + MachinePreservingLookupClean.steps (GraphTables.tableWords t) 0 + 1 +
    MachinePreservingLookupClean.steps (GraphTables.tableWords t) 1 + 1

/-- Both original header numbers are produced by physical preserving lookups. -/
theorem readTrace (q : Nat) (t : GraphTables.Table) (output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program q)))^[readTime t]
      (some ⟨some .init, ((ambient, false), register),
        frame (GraphTables.tableBits t) [] [] [] [] [] [] [] [] [] [] [] output⟩) =
      some ⟨some (.prefix .init), ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) [] [] []
          (encodeWord t.darts) [] [] [] [] [] [] output⟩ := by
  have hi : (advance (TM2.step (program q)))^[1]
      (some ⟨some .init, ((ambient, false), register),
        frame (GraphTables.tableBits t) [] [] [] [] [] [] [] [] [] [] [] output⟩) =
      some ⟨some (.lookup .vertices (.run .copyFirst)), ((ambient, false), register),
        frame (GraphTables.tableBits t) [] [] [] [] [] (encodeWord 0) [] [] [] [] [] output⟩ :=
    initStep q _ _ ambient register
  have hn := MachinePreservingLookupClean.traceAt_fromTapes (lookupSlots .vertices)
    (lookupSlots_injective .vertices) (Label.lookup .vertices) (some Label.seedM)
    (program q) (fun _ => rfl)
    (frame (GraphTables.tableBits t) [] [] [] [] [] (encodeWord 0) [] [] [] [] [] output)
    (GraphTables.tableWords t) rfl rfl 0 t.vertices (by simp [GraphTables.tableWords]) []
    (by simp [lookupSlots]) (by simp [lookupSlots]) (ambient, false) register
  simp [MachinePreservingLookup.initialTapes, MachineLookup.tapes, lookupSlots, fieldTape] at hn
  have hs : (advance (TM2.step (program q)))^[1]
      (some ⟨some .seedM, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) [] [] [] []
          (encodeWord 0) [] [] [] [] [] output⟩) =
      some ⟨some (.lookup .darts (.run .copyFirst)), ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) [] [] [] []
          (encodeWord 1) [] [] [] [] [] output⟩ :=
    seedMStep q _ _ _ ambient none
  have hm := MachinePreservingLookupClean.traceAt_fromTapes (lookupSlots .darts)
    (lookupSlots_injective .darts) (Label.lookup .darts) (some Label.clearIndex)
    (program q) (fun _ => rfl)
    (frame (GraphTables.tableBits t) (encodeWord t.vertices) [] [] [] []
      (encodeWord 1) [] [] [] [] [] output)
    (GraphTables.tableWords t) rfl rfl 1 t.darts (by simp [GraphTables.tableWords]) []
    (by simp [lookupSlots]) (by simp [lookupSlots]) (ambient, false) none
  simp [MachinePreservingLookup.initialTapes, MachineLookup.tapes, lookupSlots, fieldTape] at hm
  have hc : (advance (TM2.step (program q)))^[1]
      (some ⟨some .clearIndex, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) [] [] []
          (encodeWord t.darts) (encodeWord 0) [] [] [] [] [] output⟩) =
      some ⟨some (.prefix .init), ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) [] [] []
          (encodeWord t.darts) [] [] [] [] [] [] output⟩ :=
    clearIndexStep q _ _ _ _ ambient none
  exact appendTrace _ (appendTrace _ (appendTrace _ (appendTrace _ hi hn) hs) hm) hc

/-- The original vertex count is the physical bound supplied to the checked
padding-prefix machine. Its complement tapes preserve the original dart count. -/
theorem prefixTrace (q : Nat) (t : GraphTables.Table) (output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program q)))^[MachineCloudPrefix.totalTime t t.vertices []]
      (some ⟨some (.prefix .init), ((ambient, false), register),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) [] [] []
          (encodeWord t.darts) [] [] [] [] [] [] output⟩) =
      some ⟨some (.copyFirst .count), ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
          (encodeWord 0) (encodeWord (paddingTotal t)) (encodeWord t.darts)
          [] [] [] [] [] [] output⟩ := by
  have h := MachineCloudPadding.Placement.trace Sum.inl prefixView prefixView_left prefixView_right
    Label.prefix (some (Label.copyFirst .count))
    (frame [] [] [] [] [] (encodeWord t.darts) [] [] [] [] [] [] output)
    (MachineCloudPrefix.program (σ := σ)) (program q) (fun _ => rfl) _ _ _
    (MachineCloudPrefix.prefixTrace t t.vertices (Nat.le_refl _) [] ambient register)
  simpa only [MachineCloudPadding.Placement.configuration, MachineCloudPadding.Placement.label,
    prefixTapes, frame_m, frame_index, frame_work, frame_scratch, frame_vertices, frame_darts,
    frame_emit, frame_output, List.append_nil, paddingTotal, frame, memory,
    mTape, indexTape, workTape, scratchTape, verticesTape, dartsTape, emitTape, outputTape] using h

def computeTime (t : GraphTables.Table) : Nat :=
  (2 * (t.darts + 2) + (paddingTotal t + 1)) + (2 * (vertexTotal t + 1) + 1)

theorem computeTrace (q : Nat) (t : GraphTables.Table) (output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program q)))^[computeTime t]
      (some ⟨some (.copyFirst .count), ((ambient, false), register),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
          (encodeWord 0) (encodeWord (paddingTotal t)) (encodeWord t.darts)
          [] [] [] [] [] [] output⟩) =
      some ⟨some (.copyFirst .rEmit), ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
          (encodeWord 0) (encodeWord 0) (encodeWord t.darts)
          [] [] [] (encodeWord (vertexTotal t)) (encodeWord (dartTotal q t)) [] output⟩ := by
  have hc := MachineCopy.copyTrace mTape verticesTape scratchTape (by decide) (by decide)
    (by decide) false (Label.copyFirst .count) (Label.copySecond .count) (some Label.add)
    (program q) rfl rfl
    (frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
      (encodeWord 0) (encodeWord (paddingTotal t)) (encodeWord t.darts)
      [] [] [] [] [] [] output) rfl (ambient, false) register
  simp only [frame_m, frame_vertices, encodeWord_length, List.append_nil, update_frame_vertices] at hc
  have ha := MachineUnaryAddAt.addFromTapes sumTape verticesTape (by decide)
    Label.add (some Label.scaleSeed) (program q) rfl
    (frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
      (encodeWord 0) (encodeWord (paddingTotal t)) (encodeWord t.darts)
      [] [] [] (encodeWord t.darts) [] [] output)
    (paddingTotal t) t.darts [] [] (by simp) (by simp) (ambient, false) none
  simp only [MachineUnaryAddAt.unaryTapes, Reduction.MachineTransfer.tapesAt,
    List.append_nil, update_frame_sum, update_frame_vertices] at ha
  rw [show paddingTotal t + t.darts = vertexTotal t by rw [vertexTotal_eq]; omega] at ha
  have hm := MachineUnaryAffineAt.seededAffineTrace verticesTape scratchTape dartsTape
    (by decide) (by decide) (by decide) (q + 1) 0 Label.scaleSeed Label.scaleScan
    Label.scaleRestore (some (Label.copyFirst .rEmit)) (program q) rfl rfl rfl
    (frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
      (encodeWord 0) (encodeWord 0) (encodeWord t.darts)
      [] [] [] (encodeWord (vertexTotal t)) [] [] output)
    (vertexTotal t) [] (by simp) rfl (ambient, false) none
  simp only [frame_darts, List.append_nil, Nat.add_zero, update_frame_darts] at hm
  rw [show (q + 1) * vertexTotal t = dartTotal q t by unfold dartTotal; ac_rfl] at hm
  exact appendTrace _ (appendTrace _ hc ha) hm

def headerBits (q : Nat) (t : GraphTables.Table) : List Bool :=
  encodeWords [vertexTotal t, dartTotal q t]

theorem headerBits_eq (q : Nat) (t : GraphTables.Table) :
    headerBits q t = encodeWord (vertexTotal t) ++ encodeWord (dartTotal q t) := by
  simp only [headerBits, encodeWords, List.append_nil]

theorem headerBits_length (q : Nat) (t : GraphTables.Table) :
    (headerBits q t).length = vertexTotal t + dartTotal q t + 2 := by
  rw [headerBits_eq]
  simp only [List.length_append, encodeWord_length]
  omega

theorem cleanupZerosStep (q : Nat) (table n m N R output : List Bool) (ambient : σ)
    (register : Option Bool) :
    TM2.step (program q)
      ⟨some .cleanupZeros, ((ambient, false), register),
        frame table n n (encodeWord 0) (encodeWord 0) m [] [] [] N R [] output⟩ =
      some ⟨some .clearQuery, ((ambient, false), none),
        frame table n n [] [] m [] [] [] N R [] output⟩ := by
  simp [TM2.step, program, TM2.stepAux, encodeWord]

def emitTime (q : Nat) (t : GraphTables.Table) (output : List Bool) : Nat :=
  (((2 * (dartTotal q t + 2) + 2 * (vertexTotal t + 2)) +
    (2 * ((headerBits q t).length + output.length) + 3)) + 1) + (t.vertices + 1) + 1

theorem emitTrace (q : Nat) (t : GraphTables.Table) (output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program q)))^[emitTime q t output]
      (some ⟨some (.copyFirst .rEmit), ((ambient, false), register),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
          (encodeWord 0) (encodeWord 0) (encodeWord t.darts)
          [] [] [] (encodeWord (vertexTotal t)) (encodeWord (dartTotal q t)) [] output⟩) =
      some ⟨none, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) [] [] [] (encodeWord t.darts)
          [] [] [] (encodeWord (vertexTotal t)) (encodeWord (dartTotal q t)) []
          (output ++ headerBits q t)⟩ := by
  have hr := MachineCopy.copyTrace dartsTape emitTape scratchTape (by decide) (by decide)
    (by decide) false (Label.copyFirst .rEmit) (Label.copySecond .rEmit)
    (some (Label.copyFirst .nEmit)) (program q) rfl rfl
    (frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
      (encodeWord 0) (encodeWord 0) (encodeWord t.darts) [] [] []
      (encodeWord (vertexTotal t)) (encodeWord (dartTotal q t)) [] output)
    rfl (ambient, false) register
  simp only [frame_darts, frame_emit, encodeWord_length, List.append_nil, update_frame_emit] at hr
  have hn := MachineCopy.copyTrace verticesTape emitTape scratchTape (by decide) (by decide)
    (by decide) false (Label.copyFirst .nEmit) (Label.copySecond .nEmit)
    (some Label.appendFirst) (program q) rfl rfl
    (frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
      (encodeWord 0) (encodeWord 0) (encodeWord t.darts) [] [] []
      (encodeWord (vertexTotal t)) (encodeWord (dartTotal q t)) (encodeWord (dartTotal q t)) output)
    rfl (ambient, false) none
  simp only [frame_vertices, frame_emit, encodeWord_length, update_frame_emit, ← headerBits_eq] at hn
  have ha := MachineAppendAt.appendTrace emitTape outputTape scratchTape
    (by decide) (by decide) (by decide) false Label.appendFirst Label.appendSecond Label.appendThird
    (some Label.cleanupZeros) (program q) rfl rfl rfl
    (frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
      (encodeWord 0) (encodeWord 0) (encodeWord t.darts) [] [] []
      (encodeWord (vertexTotal t)) (encodeWord (dartTotal q t)) (headerBits q t) output)
    rfl (ambient, false) none
  simp only [frame_emit, frame_output, MachineAppendAt.appendTapes,
    Reduction.MachineTransfer.tapesAt, update_frame_emit, update_frame_output] at ha
  have hz : (advance (TM2.step (program q)))^[1]
      (some ⟨some .cleanupZeros, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
          (encodeWord 0) (encodeWord 0) (encodeWord t.darts) [] [] []
          (encodeWord (vertexTotal t)) (encodeWord (dartTotal q t)) [] (output ++ headerBits q t)⟩) =
      some ⟨some .clearQuery, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
          [] [] (encodeWord t.darts) [] [] [] (encodeWord (vertexTotal t))
          (encodeWord (dartTotal q t)) [] (output ++ headerBits q t)⟩ :=
    cleanupZerosStep q _ _ _ _ _ _ ambient none
  have hc := MachineLookup.discardTrace queryTape Label.clearQuery Label.done (program q) rfl
    (frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
      [] [] (encodeWord t.darts) [] [] [] (encodeWord (vertexTotal t))
      (encodeWord (dartTotal q t)) [] (output ++ headerBits q t))
    t.vertices [] (by simp) (ambient, false) none
  simp only [update_frame_query] at hc
  have hd : (advance (TM2.step (program q)))^[1]
      (some ⟨some .done, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) [] [] [] (encodeWord t.darts)
          [] [] [] (encodeWord (vertexTotal t)) (encodeWord (dartTotal q t)) []
          (output ++ headerBits q t)⟩) =
      some ⟨none, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) [] [] [] (encodeWord t.darts)
          [] [] [] (encodeWord (vertexTotal t)) (encodeWord (dartTotal q t)) []
          (output ++ headerBits q t)⟩ := rfl
  exact appendTrace _ (appendTrace _ (appendTrace _ (appendTrace _ (appendTrace _ hr hn) ha) hz) hc) hd

def totalTime (q : Nat) (t : GraphTables.Table) (output : List Bool) : Nat :=
  ((readTime t + MachineCloudPrefix.totalTime t t.vertices []) + computeTime t) + emitTime q t output

theorem trace (q : Nat) (t : GraphTables.Table) (output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program q)))^[totalTime q t output]
      (some ⟨some .init, ((ambient, false), register),
        frame (GraphTables.tableBits t) [] [] [] [] [] [] [] [] [] [] [] output⟩) =
      some ⟨none, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) [] [] [] (encodeWord t.darts)
          [] [] [] (encodeWord (vertexTotal t)) (encodeWord (dartTotal q t)) []
          (output ++ headerBits q t)⟩ :=
  appendTrace _ (appendTrace _ (appendTrace _ (readTrace q t output ambient register)
    (prefixTrace q t output ambient none)) (computeTrace q t output ambient none))
      (emitTrace q t output ambient none)

theorem totalTime_le (q : Nat) (t : GraphTables.Table) (output : List Bool) :
    totalTime q t output ≤ (timePolynomial q).eval ((GraphTables.tableBits t).length + output.length) := by
  let L := (GraphTables.tableBits t).length + output.length
  have hT : (GraphTables.tableBits t).length ≤ L := by unfold L; omega
  have hO : output.length ≤ L := by unfold L; omega
  have hn := (GraphTables.vertices_le_tableBits_length t).trans hT
  have hm := (GraphTables.darts_le_tableBits_length t).trans hT
  have hN : vertexTotal t ≤ ExpanderFamily.growth * L :=
    (PreprocessingMachineBounds.regularVertices_le_input t).trans
      (Nat.mul_le_mul_left ExpanderFamily.growth hT)
  have hS : paddingTotal t ≤ ExpanderFamily.growth * L :=
    (PreprocessingMachineBounds.prefix_le_input t t.vertices).trans
      (Nat.mul_le_mul_left ExpanderFamily.growth hT)
  have hR : dartTotal q t ≤ (ExpanderFamily.growth * (q + 1)) * L := by
    calc
      _ ≤ (ExpanderFamily.growth * L) * (q + 1) := Nat.mul_le_mul_right (q + 1) hN
      _ = _ := by ac_rfl
  have hr0 := MachinePreservingLookupClean.steps_le (GraphTables.tableWords t) 0 t.vertices
    (by simp [GraphTables.tableWords])
  have hr1 := MachinePreservingLookupClean.steps_le (GraphTables.tableWords t) 1 t.darts
    (by simp [GraphTables.tableWords])
  have hread : readTime t ≤ 12 * L + 11 := by
    change _ ≤ 6 * (GraphTables.tableBits t).length + 4 at hr0 hr1
    unfold readTime
    omega
  have hprefixInput : MachineCloudPrefix.inputLength t t.vertices [] ≤ 2 * L + 1 := by
    simp only [MachineCloudPrefix.inputLength, List.append_nil, encodeWord_length]
    omega
  have hp := (MachineCloudPrefix.totalTime_le t t.vertices (Nat.le_refl _) []).trans
    (natPolynomial_eval_mono MachineCloudPrefix.timePolynomial hprefixInput)
  have harith : readTime t + computeTime t + emitTime q t output ≤
      (arithmeticPolynomial q).eval L := by
    simp only [arithmeticPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat, Polynomial.eval_one]
    unfold computeTime emitTime
    rw [headerBits_length]
    omega
  have htotal := Nat.add_le_add hp harith
  simpa only [totalTime, timePolynomial, Polynomial.eval_add, Polynomial.eval_comp,
    Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X, Polynomial.eval_one,
    L, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htotal

end Header

namespace Top

abbrev Body := MachineRegularOriginalBody.Tape
abbrev Tape := Body ⊕ (Header.Tape ⊕ Fin 4)
abbrev Alphabet (_ : Tape) := Bool
abbrev State := MachineRegularOriginalBody.State × Option Bool

instance tapeDecidableEq : DecidableEq Tape :=
  sumDecidableEq
    (sumDecidableEq (inferInstanceAs (DecidableEq (Fin 27)))
      (sumDecidableEq (inferInstanceAs (DecidableEq MachineRegularMetadata.Extra))
        (sumDecidableEq
          (sumDecidableEq
            (sumDecidableEq (inferInstanceAs (DecidableEq MachineExpanderRow.Tape))
              (inferInstanceAs (DecidableEq MachineExpanderTable.ExtraTape)))
            (inferInstanceAs (DecidableEq MachineExpanderFamily.ExtraTape)))
          (inferInstanceAs (DecidableEq MachineCeilingPower.Tape)))))
    (sumDecidableEq
      (sumDecidableEq (inferInstanceAs (DecidableEq MachineCloudPrefix.Tape))
        (inferInstanceAs (DecidableEq Header.Extra)))
      (inferInstanceAs (DecidableEq (Fin 4))))

instance tapeBEq : BEq Tape where
  beq a b := decide (a = b)

instance tapeLawfulBEq : LawfulBEq Tape where
  eq_of_beq := of_decide_eq_true
  rfl := of_decide_eq_self_eq_true _

instance tapeFintype : Fintype Tape := by
  change Fintype
    ((Fin 27 ⊕ (MachineRegularMetadata.Extra ⊕
      (((MachineExpanderRow.Tape ⊕ MachineExpanderTable.ExtraTape) ⊕
        MachineExpanderFamily.ExtraTape) ⊕ MachineCeilingPower.Tape))) ⊕
      ((MachineCloudPrefix.Tape ⊕ Header.Extra) ⊕ Fin 4))
  infer_instance

def coreTape (i : Fin 27) : Tape := .inl (.inl i)
def oldFuel : Tape := .inr (.inr 0)
def ownerFuel : Tape := .inr (.inr 1)
def dummyFuel : Tape := .inr (.inr 2)
def scratch : Tape := .inr (.inr 3)

def headerTape (k : Header.Tape) : Tape :=
  if k = Header.tableTape then coreTape 0
  else if k = Header.mTape then coreTape 6
  else if k = Header.outputTape then coreTape 8
  else .inr (.inl k)

def headerView : Tape → Option Header.Tape
  | .inl (.inl i) => match i.val with
    | 0 => some Header.tableTape
    | 6 => some Header.mTape
    | 8 => some Header.outputTape
    | _ => none
  | .inl (.inr _) => none
  | .inr (.inl k) =>
      if k = Header.tableTape ∨ k = Header.mTape ∨ k = Header.outputTape then none else some k
  | .inr (.inr _) => none

theorem headerView_left (k : Header.Tape) : headerView (headerTape k) = some k := by
  by_cases ht : k = Header.tableTape
  · subst k; rfl
  by_cases hm : k = Header.mTape
  · subst k; rfl
  by_cases ho : k = Header.outputTape
  · subst k; rfl
  simp [headerTape, headerView, ht, hm, ho]

theorem headerView_right (j : Tape) (k : Header.Tape)
    (h : headerView j = some k) : headerTape k = j := by
  cases j with
  | inl j =>
    cases j with
    | inl i =>
      fin_cases i <;> simp_all [headerView] <;> subst k <;> rfl
    | inr e => cases h
  | inr j =>
    cases j with
    | inl i =>
      by_cases hi : i = Header.tableTape ∨ i = Header.mTape ∨ i = Header.outputTape
      · simp [headerView, hi] at h
      · have hik : i = k := by simpa [headerView, hi] using h
        subst k
        simp only [not_or] at hi
        simp [headerTape, hi.1, hi.2.1, hi.2.2]
    | inr i => cases h

def bodyView : Tape → Option Body
  | .inl k => some k
  | .inr _ => none

theorem bodyView_left (k : Body) : bodyView (.inl k) = some k := rfl
theorem bodyView_right (j : Tape) (k : Body)
    (h : bodyView j = some k) : Sum.inl k = j := by
  cases j with
  | inl j => cases h; rfl
  | inr j => cases h

def ownerTape : MachineRegularOwnerBody.Tape → Tape
  | .inl k => .inl k
  | .inr i => if i.val = 0 then dummyFuel else scratch

def ownerView : Tape → Option MachineRegularOwnerBody.Tape
  | .inl k => some (.inl k)
  | .inr (.inl _) => none
  | .inr (.inr i) => match i.val with
    | 2 => some (.inr 0)
    | 3 => some (.inr 1)
    | _ => none

theorem ownerView_left (k : MachineRegularOwnerBody.Tape) :
    ownerView (ownerTape k) = some k := by
  cases k with
  | inl k => rfl
  | inr i => fin_cases i <;> rfl

theorem ownerView_right (j : Tape) (k : MachineRegularOwnerBody.Tape)
    (h : ownerView j = some k) : ownerTape k = j := by
  cases j with
  | inl j => cases h; rfl
  | inr j =>
    cases j with
    | inl j => cases h
    | inr i => fin_cases i <;> simp_all [ownerView] <;> subst k <;> rfl

def headerStates :
    (Header.State Unit × (MachineRegularOriginalBody.CoreState ×
      (MachineRegularOriginalBody.FamilyState × Option Bool))) ≃ State where
  toFun p := (((p.2.1, p.1), p.2.2.1), p.2.2.2)
  invFun p := (p.1.1.2, (p.1.1.1, (p.1.2, p.2)))
  left_inv _ := rfl
  right_inv _ := rfl

def readyState (H : BaseTable) : State := (MachineRegularOriginalBody.readyState H, none)

def copySource : CopyPhase → Tape
  | .old => coreTape 6
  | .owner => headerTape Header.nTape
def copyTarget : CopyPhase → Tape
  | .old => oldFuel
  | .owner => ownerFuel

inductive Label
  | header (l : Header.Label)
  | oldSeed
  | copyFirst (phase : CopyPhase)
  | copySecond (phase : CopyPhase)
  | oldGuard
  | oldBody (l : MachineRegularOriginalBody.Label)
  | oldIncrement
  | ownerSeed
  | ownerGuard
  | ownerBody (l : MachineRegularOwnerBody.Label)
  | ownerIncrement
  | clear (i : Fin 7)
  deriving DecidableEq, Fintype

def copyExit : CopyPhase → Label
  | .old => .oldGuard
  | .owner => .ownerGuard

def clearTape : Fin 7 → Tape :=
  ![coreTape 1, coreTape 2, coreTape 5, coreTape 6,
    headerTape Header.nTape, headerTape Header.verticesTape, headerTape Header.dartsTape]

def clearEntry (k : Nat) : Option Label :=
  if h : k < 7 then some (.clear ⟨k, h⟩) else none

/-- All graph-dependent loop counts remain on tapes. The code contains only
the fixed expander base and the finite subprogram labels. -/
def program (H : BaseTable) : Label → TM2.Stmt Alphabet Label State
  | .header l => Lift.statement headerTape Label.header (some .oldSeed) headerStates
      (Header.program PreprocessingRegularTables.internalDegree l)
  | .oldSeed => .push (coreTape 1) (fun _ => false) (.goto fun _ => Label.copyFirst CopyPhase.old)
  | .copyFirst phase => Reduction.MachineTransfer.loopAt (copySource phase) scratch id false
      (.copyFirst phase) (some (.copySecond phase))
  | .copySecond phase => MachineCopy.forkLoop scratch (copySource phase) (copyTarget phase) false
      (.copySecond phase) (some (copyExit phase))
  | .oldGuard => Fuel.guard oldFuel (Label.oldBody MachineRegularOriginalBody.entry) (some Label.ownerSeed)
  | .oldBody l => Lift.statement Sum.inl Label.oldBody (some .oldIncrement) (Equiv.refl _)
      (MachineRegularOriginalBody.program H l)
  | .oldIncrement => Fuel.increment (coreTape 1) Label.oldGuard
  | .ownerSeed => .push (coreTape 2) (fun _ => false)
      (.push (coreTape 5) (fun _ => false) (.goto fun _ => Label.copyFirst CopyPhase.owner))
  | .ownerGuard => Fuel.guard ownerFuel (.ownerBody MachineRegularOwnerBody.entry) (clearEntry 0)
  | .ownerBody l => MachineCloudPadding.Placement.statement ownerTape Label.ownerBody
      (some .ownerIncrement) (MachineRegularOwnerBody.program H l)
  | .ownerIncrement => Fuel.increment (coreTape 2) Label.ownerGuard
  | .clear i => MachineDrain.drain (clearTape i) (.clear i) (clearEntry (i.val + 1))

def machine (H : BaseTable) : FinTM2 where
  K := Tape
  k₀ := coreTape 0
  k₁ := coreTape 8
  Γ _ := Bool
  Λ := Label
  main := .header .init
  σ := State
  initialState := readyState H
  m := program H

/-- These are mathematical descriptions of the physical stacks at loop
boundaries. They are never loaded into the machine's finite control. -/
def frame (data : Data) (header : Header.Tape → List Bool) (counters : Fin 4 → List Bool) :
    Tape → List Bool
  | .inl k => MachineRegularOriginalBody.frame data k
  | .inr (.inl k) => header k
  | .inr (.inr i) => counters i

def cfg (H : BaseTable) (label : Option Label) (data : Data)
    (header : Header.Tape → List Bool) (counters : Fin 4 → List Bool) :
    TM2.Cfg Alphabet Label State :=
  ⟨label, readyState H, frame data header counters⟩

@[simp] theorem frame_core (data : Data) (header : Header.Tape → List Bool)
    (counters : Fin 4 → List Bool) (i : Fin 27) :
    frame data header counters (coreTape i) = MachineRegularMetadata.frame data (.inl i) := rfl

theorem bodyPlacement (data extra : Data) (header : Header.Tape → List Bool)
    (counters : Fin 4 → List Bool) :
    MachineCloudPadding.Placement.tapes bodyView (MachineRegularOriginalBody.frame data)
      (frame extra header counters) = frame data header counters := by
  funext j
  cases j with
  | inl j => rfl
  | inr j => cases j <;> rfl

def headerAux (n N R : List Bool) : Header.Tape → List Bool := fun k =>
  if k = Header.nTape then n
  else if k = Header.verticesTape then N
  else if k = Header.dartsTape then R
  else []

@[simp] theorem headerAux_empty : headerAux [] [] [] = (fun _ => []) := by
  funext k
  simp [headerAux]

theorem headerPlacement (data : Data) (t n m N R output : List Bool)
    (counters : Fin 4 → List Bool) :
    MachineCloudPadding.Placement.tapes headerView
      (Header.frame t n [] [] [] m [] [] [] N R [] output)
      (frame data (fun _ => []) counters) =
      frame { data with table := t, darts := m, output := output } (headerAux n N R) counters := by
  funext j
  cases j with
  | inl j =>
    cases j with
    | inl i => fin_cases i <;> rfl
    | inr e => cases e with
      | inl e => cases e <;> rfl
      | inr e => rfl
  | inr j =>
    cases j with
    | inl k =>
      cases k with
      | inl k =>
        cases k with
        | inner k => cases k <;> rfl
        | bound => rfl
        | remaining => rfl
        | total => rfl
      | inr k => cases k <;> rfl
    | inr i => rfl

def inputData (t : GraphTables.Table) (output : List Bool) : Data where
  table := GraphTables.tableBits t
  globalIndex := []
  owner := []
  localRank := []
  count := []
  offset := []
  darts := []
  rotor := []
  output := output
  padding := []
  level := []

def headerData (t : GraphTables.Table) (output : List Bool) : Data :=
  { inputData t output with darts := encodeWord t.darts }

def headerStacks (t : GraphTables.Table) : Header.Tape → List Bool :=
  headerAux (encodeWord t.vertices) (encodeWord (Header.vertexTotal t))
    (encodeWord (Header.dartTotal PreprocessingRegularTables.internalDegree t))

theorem headerTrace (H : BaseTable) (t : GraphTables.Table) (output : List Bool)
    (counters : Fin 4 → List Bool) :
    (advance (TM2.step (program H)))^[Header.totalTime PreprocessingRegularTables.internalDegree t output]
      (some (cfg H (some (.header .init)) (inputData t output) (fun _ => []) counters)) =
      some (cfg H (some .oldSeed)
        (headerData t (output ++ Header.headerBits PreprocessingRegularTables.internalDegree t))
        (headerStacks t) counters) := by
  have raw := Header.trace PreprocessingRegularTables.internalDegree t output () none
  have placed := Lift.trace headerTape headerView headerView_left headerView_right
    Label.header (some .oldSeed) headerStates
    (MachineRegularInternalRow.coreInitialState PreprocessingRegularTables.internalDegree
      MachineRegularOriginalBody.degree_positive (), (MachineRegularFamily.readyState H, none))
    (frame (inputData t output) (fun _ => []) counters)
    (Header.program PreprocessingRegularTables.internalDegree) (program H) (fun _ => rfl)
    _ _ _ raw
  simpa only [Lift.configuration, MachineCloudPadding.Placement.label, headerPlacement,
    headerAux_empty, cfg, readyState, MachineRegularOriginalBody.readyState, headerStates,
    Equiv.coe_fn_mk, headerData, inputData, headerStacks] using placed

def oldData (t : GraphTables.Table) (index : Nat) (output : List Bool) : Data :=
  { headerData t output with globalIndex := encodeWord index }

theorem originalData_eq (t : GraphTables.Table) (e : Fin t.darts) (output : List Bool) :
    MachineRegularOriginalBody.initialData t e output = oldData t e.val output := rfl

/-- The actual old-vertex body is transported with all outer counters and
header words untouched. No body-execution hypothesis occurs in this lemma. -/
theorem oldBodyTrace (H : BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) (header : Header.Tape → List Bool) (counters : Fin 4 → List Bool) :
    (advance (TM2.step (program H)))^[MachineRegularOriginalBody.totalSteps H t e output]
      (some (cfg H (some (Label.oldBody MachineRegularOriginalBody.entry))
        (oldData t e.val output) header counters)) =
      some (cfg H (some .oldIncrement)
        (oldData t e.val (output ++ MachineRegularOriginalBody.emittedBits H t e)) header counters) := by
  have raw := MachineRegularOriginalBody.originalTrace H t e output
  have placed := Lift.trace Sum.inl bodyView bodyView_left bodyView_right Label.oldBody
    (some .oldIncrement) (Equiv.refl _) none
    (frame (oldData t e.val output) header counters)
    (MachineRegularOriginalBody.program H) (program H) (fun _ => rfl) _ _ _ raw
  simpa only [Lift.configuration, MachineCloudPadding.Placement.label, bodyPlacement,
    MachineRegularOriginalBody.cfg, originalData_eq, cfg, readyState, Equiv.refl_apply] using placed

@[simp] theorem frame_oldFuel (data : Data) (header : Header.Tape → List Bool)
    (old owners dummy work : List Bool) :
    frame data header (counterStacks old owners dummy work) oldFuel = old := rfl

@[simp] theorem frame_ownerFuel (data : Data) (header : Header.Tape → List Bool)
    (old owners dummy work : List Bool) :
    frame data header (counterStacks old owners dummy work) ownerFuel = owners := rfl

@[simp] theorem update_frame_oldFuel (data : Data) (header : Header.Tape → List Bool)
    (old owners dummy work replacement : List Bool) :
    Function.update (frame data header (counterStacks old owners dummy work)) oldFuel replacement =
      frame data header (counterStacks replacement owners dummy work) := by
  funext j
  cases j with
  | inl j => rfl
  | inr j => cases j with
    | inl j => rfl
    | inr i => fin_cases i <;> rfl

@[simp] theorem update_frame_ownerFuel (data : Data) (header : Header.Tape → List Bool)
    (old owners dummy work replacement : List Bool) :
    Function.update (frame data header (counterStacks old owners dummy work)) ownerFuel replacement =
      frame data header (counterStacks old replacement dummy work) := by
  funext j
  cases j with
  | inl j => rfl
  | inr j => cases j with
    | inl j => rfl
    | inr i => fin_cases i <;> rfl

@[simp] theorem update_frame_global (data : Data) (header : Header.Tape → List Bool)
    (counters : Fin 4 → List Bool) (replacement : List Bool) :
    Function.update (frame data header counters) (coreTape 1) replacement =
      frame { data with globalIndex := replacement } header counters := by
  funext j
  cases j with
  | inl j => cases j with
    | inl i => fin_cases i <;> rfl
    | inr e => cases e with
      | inl e => cases e <;> rfl
      | inr e => rfl
  | inr j => cases j <;> rfl

@[simp] theorem update_frame_owner (data : Data) (header : Header.Tape → List Bool)
    (counters : Fin 4 → List Bool) (replacement : List Bool) :
    Function.update (frame data header counters) (coreTape 2) replacement =
      frame { data with owner := replacement } header counters := by
  funext j
  cases j with
  | inl j => cases j with
    | inl i => fin_cases i <;> rfl
    | inr e => cases e with
      | inl e => cases e <;> rfl
      | inr e => rfl
  | inr j => cases j <;> rfl

theorem oldGuardStep (H : BaseTable) (data : Data) (header : Header.Tape → List Bool)
    (remaining : Nat) :
    (advance (TM2.step (program H)))^[1]
      (some (cfg H (some .oldGuard) data header
        (counterStacks (encodeWord (remaining + 1)) [] [] []))) =
      some (cfg H (some (Label.oldBody MachineRegularOriginalBody.entry)) data header
        (counterStacks (encodeWord remaining) [] [] [])) := by
  change some (TM2.stepAux (Fuel.guard oldFuel (Label.oldBody MachineRegularOriginalBody.entry)
    (some Label.ownerSeed)) (readyState H) _) = _
  simp only [Fuel.guard, TM2.stepAux, frame_oldFuel, encodeWord, List.replicate_succ,
    List.cons_append, List.head?_cons, List.tail_cons, Option.getD_some,
    Bool.cond_true, update_frame_oldFuel]
  rfl

theorem oldGuardExit (H : BaseTable) (data : Data) (header : Header.Tape → List Bool) :
    (advance (TM2.step (program H)))^[1]
      (some (cfg H (some .oldGuard) data header (counterStacks (encodeWord 0) [] [] []))) =
      some (cfg H (some Label.ownerSeed) data header (counterStacks [] [] [] [])) := by
  change some (TM2.stepAux (Fuel.guard oldFuel (Label.oldBody MachineRegularOriginalBody.entry)
    (some Label.ownerSeed)) (readyState H) _) = _
  simp only [Fuel.guard, TM2.stepAux, frame_oldFuel, encodeWord, List.replicate_zero,
    List.nil_append, List.head?_cons, List.tail_cons, Option.getD_some,
    Bool.cond_false, update_frame_oldFuel]
  rfl

theorem oldIncrementStep (H : BaseTable) (t : GraphTables.Table) (index : Nat)
    (output : List Bool) (header : Header.Tape → List Bool) (counters : Fin 4 → List Bool) :
    (advance (TM2.step (program H)))^[1]
      (some (cfg H (some .oldIncrement) (oldData t index output) header counters)) =
      some (cfg H (some .oldGuard) (oldData t (index + 1) output) header counters) := by
  change some (TM2.stepAux (Fuel.increment (coreTape 1) Label.oldGuard)
    (readyState H) (frame (oldData t index output) header counters)) = _
  simp only [Fuel.increment, TM2.stepAux, frame_core]
  change some (⟨some Label.oldGuard, readyState H,
    Function.update (frame (oldData t index output) header counters) (coreTape 1)
      (true :: encodeWord index)⟩ : TM2.Cfg (fun _ : Tape => Bool) Label State) = _
  rw [update_frame_global]
  simp only [cfg, oldData, encodeWord, List.replicate_succ, List.cons_append]

def oldPrefix (H : BaseTable) (t : GraphTables.Table) (k : Nat) : List Bool :=
  PreprocessingRegularLoopWords.blocksPrefix (MachineRegularOriginalBody.emittedBits H t) k

noncomputable def oldElapsed (H : BaseTable) (t : GraphTables.Table) (output : List Bool) : Nat → Nat
  | 0 => 0
  | k + 1 => oldElapsed H t output k +
      if h : k < t.darts then
        1 + MachineRegularOriginalBody.totalSteps H t ⟨k,h⟩ (output ++ oldPrefix H t k) + 1
      else 0

/-- Each actual fuel/body/increment segment appends exactly the next original
vertex block. This induction is over a specification index, not a register. -/
theorem oldPrefixTrace (H : BaseTable) (t : GraphTables.Table) (output : List Bool)
    (header : Header.Tape → List Bool) (k : Nat) : k ≤ t.darts →
    (advance (TM2.step (program H)))^[oldElapsed H t output k]
      (some (cfg H (some .oldGuard) (oldData t 0 output) header
        (counterStacks (encodeWord t.darts) [] [] []))) =
      some (cfg H (some .oldGuard) (oldData t k (output ++ oldPrefix H t k)) header
        (counterStacks (encodeWord (t.darts-k)) [] [] [])) := by
  induction k with
  | zero =>
    intro _
    simp [oldElapsed, oldPrefix]
  | succ k ih =>
    intro hk
    have hlt : k < t.darts := by omega
    have hremaining : t.darts-k = (t.darts-(k+1))+1 := by omega
    have previous := ih (by omega)
    have guard := oldGuardStep H (oldData t k (output ++ oldPrefix H t k)) header
      (t.darts-(k+1))
    rw [← hremaining] at guard
    have body := oldBodyTrace H t ⟨k,hlt⟩ (output ++ oldPrefix H t k) header
      (counterStacks (encodeWord (t.darts-(k+1))) [] [] [])
    have increment := oldIncrementStep H t k
      ((output ++ oldPrefix H t k) ++ MachineRegularOriginalBody.emittedBits H t ⟨k,hlt⟩)
      header (counterStacks (encodeWord (t.darts-(k+1))) [] [] [])
    have combined := joinTrace_p0 (joinTrace_p0 (joinTrace_p0 previous guard) body) increment
    have bits := PreprocessingRegularLoopWords.blocksPrefix_succ
      (MachineRegularOriginalBody.emittedBits H t) k hlt
    change oldPrefix H t (k+1) = oldPrefix H t k ++
      MachineRegularOriginalBody.emittedBits H t ⟨k,hlt⟩ at bits
    simpa only [oldElapsed, dite_eq_left hlt, bits, List.append_assoc, Nat.add_assoc] using combined

theorem oldLoopTrace (H : BaseTable) (t : GraphTables.Table) (output : List Bool)
    (header : Header.Tape → List Bool) :
    (advance (TM2.step (program H)))^[oldElapsed H t output t.darts + 1]
      (some (cfg H (some .oldGuard) (oldData t 0 output) header
        (counterStacks (encodeWord t.darts) [] [] []))) =
      some (cfg H (some Label.ownerSeed)
        (oldData t t.darts (output ++ oldPrefix H t t.darts)) header
        (counterStacks [] [] [] [])) := by
  have prefixRun := oldPrefixTrace H t output header t.darts (Nat.le_refl _)
  simp only [Nat.sub_self] at prefixRun
  exact joinTrace_p0 prefixRun (oldGuardExit H _ header)

@[simp] theorem frame_scratch (data : Data) (header : Header.Tape → List Bool)
    (old owners dummy work : List Bool) :
    frame data header (counterStacks old owners dummy work) scratch = work := rfl

@[simp] theorem frame_darts (data : Data) (header : Header.Tape → List Bool)
    (counters : Fin 4 → List Bool) : frame data header counters (coreTape 6) = data.darts := rfl

@[simp] theorem frame_header_n (data : Data) (n N R : List Bool)
    (counters : Fin 4 → List Bool) :
    frame data (headerAux n N R) counters (headerTape Header.nTape) = n := rfl

theorem oldSeedStep (H : BaseTable) (t : GraphTables.Table) (output : List Bool)
    (header : Header.Tape → List Bool) (counters : Fin 4 → List Bool) :
    (advance (TM2.step (program H)))^[1]
      (some (cfg H (some .oldSeed) (headerData t output) header counters)) =
      some (cfg H (some (.copyFirst .old)) (oldData t 0 output) header counters) := by
  change some (TM2.stepAux (.push (coreTape 1) (fun _ => false)
    (.goto fun _ => Label.copyFirst CopyPhase.old)) (readyState H) (frame (headerData t output) header counters)) = _
  change some (⟨some (Label.copyFirst CopyPhase.old), readyState H,
    Function.update (frame (headerData t output) header counters) (coreTape 1) [false]⟩ :
      TM2.Cfg (fun _ : Tape => Bool) Label State) = _
  rw [update_frame_global]
  rfl

theorem copyOldTrace (H : BaseTable) (t : GraphTables.Table) (output : List Bool)
    (header : Header.Tape → List Bool) :
    (advance (TM2.step (program H)))^[2*(t.darts+2)]
      (some (cfg H (some (.copyFirst .old)) (oldData t 0 output) header
        (counterStacks [] [] [] []))) =
      some (cfg H (some .oldGuard) (oldData t 0 output) header
        (counterStacks (encodeWord t.darts) [] [] [])) := by
  have h := MachineCopy.copyTrace (coreTape 6) oldFuel scratch
    (by decide) (by decide) (by decide) false (.copyFirst .old) (.copySecond .old)
    (some .oldGuard) (program H) rfl rfl
    (frame (oldData t 0 output) header (counterStacks [] [] [] [])) rfl
    (MachineRegularOriginalBody.readyState H) none
  simpa only [frame_darts, oldData, headerData, inputData, encodeWord_length,
    frame_oldFuel, List.append_nil, update_frame_oldFuel, cfg, readyState, Nat.add_assoc] using h

theorem oldStageTrace (H : BaseTable) (t : GraphTables.Table) (output : List Bool)
    (header : Header.Tape → List Bool) :
    (advance (TM2.step (program H)))^[1+2*(t.darts+2)+(oldElapsed H t output t.darts+1)]
      (some (cfg H (some .oldSeed) (headerData t output) header (counterStacks [] [] [] []))) =
      some (cfg H (some Label.ownerSeed)
        (oldData t t.darts (output ++ oldPrefix H t t.darts)) header
        (counterStacks [] [] [] [])) :=
  joinTrace_p0 (joinTrace_p0 (oldSeedStep H t output header _) (copyOldTrace H t output header))
    (oldLoopTrace H t output header)

@[simp] theorem update_frame_offset (data : Data) (header : Header.Tape → List Bool)
    (counters : Fin 4 → List Bool) (replacement : List Bool) :
    Function.update (frame data header counters) (coreTape 5) replacement =
      frame { data with offset := replacement } header counters := by
  funext j
  cases j with
  | inl j => cases j with
    | inl i => fin_cases i <;> rfl
    | inr e => cases e with
      | inl e => cases e <;> rfl
      | inr e => rfl
  | inr j => cases j <;> rfl

def ownerData (t : GraphTables.Table) (index : Nat) (output : List Bool) : Data :=
  { headerData t output with
    globalIndex := encodeWord (t.darts + PreprocessingPaddingOffsets.offset
      (PreprocessingRegularTables.padding t) index)
    owner := encodeWord index
    offset := encodeWord (PreprocessingPaddingOffsets.offset
      (PreprocessingRegularTables.padding t) index) }

theorem ownerSeedStep (H : BaseTable) (t : GraphTables.Table) (output : List Bool)
    (header : Header.Tape → List Bool) (counters : Fin 4 → List Bool) :
    (advance (TM2.step (program H)))^[1]
      (some (cfg H (some Label.ownerSeed) (oldData t t.darts output) header counters)) =
      some (cfg H (some (.copyFirst .owner)) (ownerData t 0 output) header counters) := by
  change some (TM2.stepAux
    (.push (coreTape 2) (fun _ => false) (.push (coreTape 5) (fun _ => false)
      (.goto fun _ => Label.copyFirst CopyPhase.owner))) (readyState H)
      (frame (oldData t t.darts output) header counters)) = _
  simp only [TM2.stepAux, frame_core]
  change some (⟨some (Label.copyFirst CopyPhase.owner), readyState H,
    Function.update (Function.update (frame (oldData t t.darts output) header counters)
      (coreTape 2) [false]) (coreTape 5) [false]⟩ :
      TM2.Cfg (fun _ : Tape => Bool) Label State) = _
  rw [update_frame_owner, update_frame_offset]
  simp only [cfg, ownerData, oldData, PreprocessingPaddingOffsets.offset_zero, Nat.add_zero,
    encodeWord, List.replicate_zero, List.nil_append]

theorem copyOwnerTrace (H : BaseTable) (t : GraphTables.Table) (output : List Bool) :
    (advance (TM2.step (program H)))^[2*(t.vertices+2)]
      (some (cfg H (some (.copyFirst .owner)) (ownerData t 0 output) (headerStacks t)
        (counterStacks [] [] [] []))) =
      some (cfg H (some .ownerGuard) (ownerData t 0 output) (headerStacks t)
        (counterStacks [] (encodeWord t.vertices) [] [])) := by
  have h := MachineCopy.copyTrace (headerTape Header.nTape) ownerFuel scratch
    (by decide) (by decide) (by decide) false (.copyFirst .owner) (.copySecond .owner)
    (some .ownerGuard) (program H) rfl rfl
    (frame (ownerData t 0 output) (headerStacks t) (counterStacks [] [] [] [])) rfl
    (MachineRegularOriginalBody.readyState H) none
  simpa only [headerStacks, frame_header_n, encodeWord_length, frame_ownerFuel,
    List.append_nil, update_frame_ownerFuel, cfg, readyState, Nat.add_assoc] using h

theorem ownerPlacement (data extra : Data) (header : Header.Tape → List Bool)
    (old owners : List Bool) :
    MachineCloudPadding.Placement.tapes ownerView (MachineRegularOwnerBody.frame data)
      (frame extra header (counterStacks old owners [] [])) =
      frame data header (counterStacks old owners [] []) := by
  funext j
  cases j with
  | inl j => rfl
  | inr j => cases j with
    | inl j => rfl
    | inr i => fin_cases i <;> rfl

theorem ownerInitialData_eq (t : GraphTables.Table) (v : Fin t.vertices) (output : List Bool) :
    MachineRegularOwnerBody.initialData t v output = ownerData t v.val output := rfl

theorem ownerBodyTrace (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) (header : Header.Tape → List Bool) (owners : List Bool) :
    (advance (TM2.step (program H)))^[MachineRegularOwnerBody.totalSteps H t v output]
      (some (cfg H (some (.ownerBody MachineRegularOwnerBody.entry))
        (ownerData t v.val output) header (counterStacks [] owners [] []))) =
      some (cfg H (some .ownerIncrement) (MachineRegularOwnerBody.finalData H t v output)
        header (counterStacks [] owners [] [])) := by
  have raw := MachineRegularOwnerBody.ownerTrace H t v output
  have placed := MachineCloudPadding.Placement.trace ownerTape ownerView ownerView_left ownerView_right
    Label.ownerBody (some .ownerIncrement)
    (frame (ownerData t v.val output) header (counterStacks [] owners [] []))
    (MachineRegularOwnerBody.program H) (program H) (fun _ => rfl) _ _ _ raw
  simpa only [MachineCloudPadding.Placement.configuration, MachineCloudPadding.Placement.label,
    ownerPlacement, MachineRegularOwnerBody.cfg, MachineRegularOwnerBody.readyState,
    ownerInitialData_eq, cfg, readyState] using placed

theorem ownerGuardStep (H : BaseTable) (data : Data) (header : Header.Tape → List Bool)
    (remaining : Nat) :
    (advance (TM2.step (program H)))^[1]
      (some (cfg H (some .ownerGuard) data header
        (counterStacks [] (encodeWord (remaining+1)) [] []))) =
      some (cfg H (some (.ownerBody MachineRegularOwnerBody.entry)) data header
        (counterStacks [] (encodeWord remaining) [] [])) := by
  change some (TM2.stepAux (Fuel.guard ownerFuel (.ownerBody MachineRegularOwnerBody.entry)
    (clearEntry 0)) (readyState H) _) = _
  simp only [Fuel.guard, TM2.stepAux, frame_ownerFuel, encodeWord, List.replicate_succ,
    List.cons_append, List.head?_cons, List.tail_cons, Option.getD_some,
    Bool.cond_true, update_frame_ownerFuel]
  rfl

theorem ownerGuardExit (H : BaseTable) (data : Data) (header : Header.Tape → List Bool) :
    (advance (TM2.step (program H)))^[1]
      (some (cfg H (some .ownerGuard) data header (counterStacks [] (encodeWord 0) [] []))) =
      some (cfg H (clearEntry 0) data header (counterStacks [] [] [] [])) := by
  change some (TM2.stepAux (Fuel.guard ownerFuel (.ownerBody MachineRegularOwnerBody.entry)
    (clearEntry 0)) (readyState H) _) = _
  simp only [Fuel.guard, TM2.stepAux, frame_ownerFuel, encodeWord, List.replicate_zero,
    List.nil_append, List.head?_cons, List.tail_cons, Option.getD_some,
    Bool.cond_false, update_frame_ownerFuel]
  rfl

theorem ownerIncrementStep (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) (header : Header.Tape → List Bool) (counters : Fin 4 → List Bool) :
    (advance (TM2.step (program H)))^[1]
      (some (cfg H (some .ownerIncrement) (MachineRegularOwnerBody.finalData H t v output)
        header counters)) =
      some (cfg H (some .ownerGuard)
        (ownerData t (v.val+1) (output ++ MachineRegularOwnerBody.ownerBits H t v)) header counters) := by
  change some (TM2.stepAux (Fuel.increment (coreTape 2) Label.ownerGuard) (readyState H)
    (frame (MachineRegularOwnerBody.finalData H t v output) header counters)) = _
  simp only [Fuel.increment, TM2.stepAux, frame_core]
  change some (⟨some Label.ownerGuard, readyState H,
    Function.update (frame (MachineRegularOwnerBody.finalData H t v output) header counters)
      (coreTape 2) (true :: encodeWord v.val)⟩ :
      TM2.Cfg (fun _ : Tape => Bool) Label State) = _
  rw [update_frame_owner]
  have offset := PreprocessingRegularBounds.offset_succ (PreprocessingRegularTables.padding t) v.val v.isLt
  simp only [cfg, ownerData, headerData, inputData, MachineRegularOwnerBody.finalData,
    MachineRegularOwnerBody.initialData, offset, encodeWord, List.replicate_succ,
    List.cons_append, Nat.add_assoc]

def ownerPrefix (H : BaseTable) (t : GraphTables.Table) (k : Nat) : List Bool :=
  PreprocessingRegularLoopWords.blocksPrefix (MachineRegularOwnerBody.ownerBits H t) k

noncomputable def ownerElapsed (H : BaseTable) (t : GraphTables.Table) (output : List Bool) : Nat → Nat
  | 0 => 0
  | k+1 => ownerElapsed H t output k +
      if h : k < t.vertices then
        1 + MachineRegularOwnerBody.totalSteps H t ⟨k,h⟩ (output ++ ownerPrefix H t k) + 1
      else 0

theorem ownerPrefixTrace (H : BaseTable) (t : GraphTables.Table) (output : List Bool)
    (header : Header.Tape → List Bool) (k : Nat) : k ≤ t.vertices →
    (advance (TM2.step (program H)))^[ownerElapsed H t output k]
      (some (cfg H (some .ownerGuard) (ownerData t 0 output) header
        (counterStacks [] (encodeWord t.vertices) [] []))) =
      some (cfg H (some .ownerGuard) (ownerData t k (output ++ ownerPrefix H t k)) header
        (counterStacks [] (encodeWord (t.vertices-k)) [] [])) := by
  induction k with
  | zero =>
    intro _
    simp [ownerElapsed, ownerPrefix]
  | succ k ih =>
    intro hk
    have hlt : k < t.vertices := by omega
    have hremaining : t.vertices-k = (t.vertices-(k+1))+1 := by omega
    have previous := ih (by omega)
    have guard := ownerGuardStep H (ownerData t k (output ++ ownerPrefix H t k)) header
      (t.vertices-(k+1))
    rw [← hremaining] at guard
    have body := ownerBodyTrace H t ⟨k,hlt⟩ (output ++ ownerPrefix H t k) header
      (encodeWord (t.vertices-(k+1)))
    have increment := ownerIncrementStep H t ⟨k,hlt⟩ (output ++ ownerPrefix H t k) header
      (counterStacks [] (encodeWord (t.vertices-(k+1))) [] [])
    have combined := joinTrace_p0 (joinTrace_p0 (joinTrace_p0 previous guard) body) increment
    have bits := PreprocessingRegularLoopWords.blocksPrefix_succ
      (MachineRegularOwnerBody.ownerBits H t) k hlt
    change ownerPrefix H t (k+1) = ownerPrefix H t k ++
      MachineRegularOwnerBody.ownerBits H t ⟨k,hlt⟩ at bits
    simpa only [ownerElapsed, dite_eq_left hlt, bits, List.append_assoc, Nat.add_assoc] using combined

theorem ownerLoopTrace (H : BaseTable) (t : GraphTables.Table) (output : List Bool)
    (header : Header.Tape → List Bool) :
    (advance (TM2.step (program H)))^[ownerElapsed H t output t.vertices+1]
      (some (cfg H (some .ownerGuard) (ownerData t 0 output) header
        (counterStacks [] (encodeWord t.vertices) [] []))) =
      some (cfg H (clearEntry 0)
        (ownerData t t.vertices (output ++ ownerPrefix H t t.vertices)) header
        (counterStacks [] [] [] [])) := by
  have prefixRun := ownerPrefixTrace H t output header t.vertices (Nat.le_refl _)
  simp only [Nat.sub_self] at prefixRun
  exact joinTrace_p0 prefixRun (ownerGuardExit H _ header)

theorem ownerStageTrace (H : BaseTable) (t : GraphTables.Table) (output : List Bool) :
    (advance (TM2.step (program H)))^[1+2*(t.vertices+2)+(ownerElapsed H t output t.vertices+1)]
      (some (cfg H (some Label.ownerSeed) (oldData t t.darts output) (headerStacks t)
        (counterStacks [] [] [] []))) =
      some (cfg H (clearEntry 0)
        (ownerData t t.vertices (output ++ ownerPrefix H t t.vertices)) (headerStacks t)
        (counterStacks [] [] [] [])) :=
  joinTrace_p0 (joinTrace_p0 (ownerSeedStep H t output (headerStacks t) _) (copyOwnerTrace H t output))
    (ownerLoopTrace H t output (headerStacks t))

theorem owner_output_eq_ownerPrefix (H : BaseTable) (t : GraphTables.Table) (k : Nat) :
    (Header.headerBits PreprocessingRegularTables.internalDegree t ++ oldPrefix H t t.darts) ++
        ownerPrefix H t k =
      PreprocessingRegularBounds.ownerPrefix t (PreprocessingRegularTables.padding t)
        (PreprocessingRegularTables.familyCloudTable H t) k := by
  have oldBits : MachineRegularOriginalBody.emittedBits H t =
      PreprocessingRegularWords.originalVertexBits t (PreprocessingRegularTables.padding t)
        (PreprocessingRegularTables.familyCloudTable H t) := rfl
  have ownerBits : MachineRegularOwnerBody.ownerBits H t =
      PreprocessingRegularBounds.ownerBits t (PreprocessingRegularTables.padding t)
        (PreprocessingRegularTables.familyCloudTable H t) := rfl
  simp only [Header.headerBits, Header.vertexTotal, Header.dartTotal, oldPrefix,
    ownerPrefix, PreprocessingRegularLoopWords.blocksPrefix_all,
    PreprocessingRegularBounds.ownerPrefix, PreprocessingRegularBounds.header]
  rw [oldBits, ownerBits]

def cleaned (base : Tape → List Bool) : Nat → Tape → List Bool
  | 0 => base
  | k+1 => if h : k < 7 then Function.update (cleaned base k) (clearTape ⟨k,h⟩) []
      else cleaned base k

def cleanupTime (base : Tape → List Bool) : Nat → Nat
  | 0 => 0
  | k+1 => cleanupTime base k + if h : k < 7 then
      ((cleaned base k) (clearTape ⟨k,h⟩)).length+1 else 0

theorem drainTrace (H : BaseTable) (i : Fin 7) (base : Tape → List Bool) :
    (advance (TM2.step (program H)))^[(base (clearTape i)).length+1]
      (some ⟨some (.clear i), readyState H, base⟩) =
      some ⟨clearEntry (i.val+1), readyState H, Function.update base (clearTape i) []⟩ := by
  have h := MachineDrain.drainTrace (clearTape i) (.clear i) (clearEntry (i.val+1))
    (program H) rfl base (base (clearTape i)) (MachineRegularOriginalBody.readyState H) none
  simpa only [Function.update_eq_self, readyState] using h

theorem cleanupPrefixTrace (H : BaseTable) (base : Tape → List Bool) (k : Nat) (hk : k ≤ 7) :
    (advance (TM2.step (program H)))^[cleanupTime base k]
      (some ⟨clearEntry 0, readyState H, base⟩) =
      some ⟨clearEntry k, readyState H, cleaned base k⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h : k < 7 := by omega
    have first := ih (by omega)
    have second := drainTrace H ⟨k,h⟩ (cleaned base k)
    have atEntry : clearEntry k = some (.clear ⟨k,h⟩) := by simp only [clearEntry, dite_eq_left h]
    rw [atEntry] at first
    simpa only [cleanupTime, cleaned, dite_eq_left h] using joinTrace_p0 first second

theorem cleanupTrace (H : BaseTable) (base : Tape → List Bool) :
    (advance (TM2.step (program H)))^[cleanupTime base 7]
      (some ⟨clearEntry 0, readyState H, base⟩) =
      some ⟨none, readyState H, cleaned base 7⟩ := by
  simpa only [clearEntry, lt_self_iff_false, dite_false] using cleanupPrefixTrace H base 7 le_rfl

def finalStacks (t : GraphTables.Table) (output : List Bool) : Tape → List Bool :=
  frame (ownerData t t.vertices output) (headerStacks t) (counterStacks [] [] [] [])

theorem cleaned_finalStacks (t : GraphTables.Table) (output : List Bool) :
    cleaned (finalStacks t output) 7 =
      frame (inputData t output) (fun _ => []) (counterStacks [] [] [] []) := by
  funext j
  cases j with
  | inl j => cases j with
    | inl i => fin_cases i <;> rfl
    | inr e => cases e with
      | inl e => cases e <;> rfl
      | inr e => rfl
  | inr j => cases j with
    | inl k => cases k with
      | inl k => cases k with
        | inner k => cases k <;> rfl
        | bound => rfl
        | remaining => rfl
        | total => rfl
      | inr k => cases k <;> rfl
    | inr i => fin_cases i <;> rfl

theorem cleaned_length_le (base : Tape → List Bool) (k : Nat) :
    ∀ j, (cleaned base k j).length ≤ (base j).length := by
  induction k with
  | zero => intro j; exact Nat.le_refl _
  | succ k ih =>
    intro j
    simp only [cleaned]
    split
    · rename_i hk
      by_cases hj : j = clearTape ⟨k,hk⟩
      · simp [hj]
      · simpa only [Function.update_of_ne hj] using ih j
    · exact ih j

theorem cleanupTime_le (base : Tape → List Bool) (cap : Nat)
    (bounded : ∀ i : Fin 7, (base (clearTape i)).length ≤ cap) (k : Nat) :
    cleanupTime base k ≤ k*(cap+1) := by
  induction k with
  | zero => simp [cleanupTime]
  | succ k ih =>
    simp only [cleanupTime]
    split
    · rename_i hk
      have hword := (cleaned_length_le base k (clearTape ⟨k,hk⟩)).trans (bounded ⟨k,hk⟩)
      calc
        cleanupTime base k + ((cleaned base k (clearTape ⟨k,hk⟩)).length+1) ≤
            k*(cap+1)+(cap+1) := by omega
        _ = (k+1)*(cap+1) := by simp only [Nat.add_mul, one_mul]
    · exact ih.trans (Nat.mul_le_mul_right _ (by omega))

theorem cleanupTime_final_le (t : GraphTables.Table) (output : List Bool) :
    cleanupTime (finalStacks t output) 7 ≤
      (7*(ExpanderFamily.growth*(PreprocessingRegularTables.internalDegree+4)+4)) *
        (PreprocessingMachineBounds.inputLength t+1) := by
  let L := PreprocessingMachineBounds.inputLength t
  let g := ExpanderFamily.growth
  let q := PreprocessingRegularTables.internalDegree
  let C := g*(q+4)+4
  have hm : t.darts ≤ L := GraphTables.darts_le_tableBits_length t
  have hn : t.vertices ≤ L := GraphTables.vertices_le_tableBits_length t
  have hs : PreprocessingPaddingOffsets.offset (PreprocessingRegularTables.padding t) t.vertices ≤ g*L :=
    PreprocessingMachineBounds.prefix_le_input t t.vertices
  have hN : Header.vertexTotal t ≤ g*L := PreprocessingMachineBounds.regularVertices_le_input t
  have hone : 1 ≤ C := by dsimp [C]; omega
  have hg : g ≤ C := by
    have h := Nat.mul_le_mul_left g (show 1 ≤ q+4 by omega)
    dsimp [C]
    omega
  have hgp : g+1 ≤ C := by
    have h := Nat.mul_le_mul_left g (show 1 ≤ q+4 by omega)
    dsimp [C]
    omega
  have hgq : g*(q+1) ≤ C := by
    have h := Nat.mul_le_mul_left g (show q+1 ≤ q+4 by omega)
    dsimp [C]
    omega
  have hmC : t.darts ≤ C*L := hm.trans (by simpa using Nat.mul_le_mul_right L hone)
  have hnC : t.vertices ≤ C*L := hn.trans (by simpa using Nat.mul_le_mul_right L hone)
  have hsC : PreprocessingPaddingOffsets.offset (PreprocessingRegularTables.padding t) t.vertices ≤ C*L :=
    hs.trans (Nat.mul_le_mul_right L hg)
  have hNC : Header.vertexTotal t ≤ C*L := hN.trans (Nat.mul_le_mul_right L hg)
  have hxC : t.darts +
      PreprocessingPaddingOffsets.offset (PreprocessingRegularTables.padding t) t.vertices ≤ C*L := by
    calc
      _ ≤ L+g*L := Nat.add_le_add hm hs
      _ = (g+1)*L := by simp only [Nat.add_mul, one_mul, Nat.add_comm]
      _ ≤ C*L := Nat.mul_le_mul_right L hgp
  have hRC : Header.dartTotal q t ≤ C*L := by
    calc
      _ ≤ (g*L)*(q+1) := Nat.mul_le_mul_right _ hN
      _ = (g*(q+1))*L := by ac_rfl
      _ ≤ C*L := Nat.mul_le_mul_right L hgq
  have bounds : ∀ i : Fin 7, (finalStacks t output (clearTape i)).length ≤ C*L+1 := by
    intro i
    fin_cases i
    · change (encodeWord _).length ≤ _
      simpa only [encodeWord_length] using Nat.add_le_add_right hxC 1
    · change (encodeWord _).length ≤ _
      simpa only [encodeWord_length] using Nat.add_le_add_right hnC 1
    · change (encodeWord _).length ≤ _
      simpa only [encodeWord_length] using Nat.add_le_add_right hsC 1
    · change (encodeWord _).length ≤ _
      simpa only [encodeWord_length] using Nat.add_le_add_right hmC 1
    · change (encodeWord _).length ≤ _
      simpa only [encodeWord_length] using Nat.add_le_add_right hnC 1
    · change (encodeWord _).length ≤ _
      simpa only [encodeWord_length] using Nat.add_le_add_right hNC 1
    · change (encodeWord _).length ≤ _
      simpa only [encodeWord_length] using Nat.add_le_add_right hRC 1
  have actual := cleanupTime_le (finalStacks t output) (C*L+1) bounds 7
  have hC : 2 ≤ C := by dsimp [C]; omega
  change cleanupTime (finalStacks t output) 7 ≤ (7*C)*(L+1)
  nlinarith

def headerOutput (t : GraphTables.Table) : List Bool :=
  Header.headerBits PreprocessingRegularTables.internalDegree t

def oldOutput (H : BaseTable) (t : GraphTables.Table) : List Bool :=
  headerOutput t ++ oldPrefix H t t.darts

def finalOutput (H : BaseTable) (t : GraphTables.Table) : List Bool :=
  oldOutput H t ++ ownerPrefix H t t.vertices

noncomputable def totalTime (H : BaseTable) (t : GraphTables.Table) : Nat :=
  Header.totalTime PreprocessingRegularTables.internalDegree t [] +
    (1+2*(t.darts+2)+(oldElapsed H t (headerOutput t) t.darts+1)) +
    (1+2*(t.vertices+2)+(ownerElapsed H t (oldOutput H t) t.vertices+1)) +
    cleanupTime (finalStacks t (finalOutput H t)) 7

theorem finalOutput_eq (H : BaseTable) (t : GraphTables.Table) :
    finalOutput H t = PortTables.tableBits (PreprocessingRegularTables.regularize H t) := by
  change finalOutput H t = PortTables.tableBits (PreprocessingRegularTables.ofCloudTables t
    (PreprocessingRegularTables.padding t) (PreprocessingRegularTables.familyCloudTable H t))
  rw [PreprocessingRegularWords.tableBits_ofCloudTables]
  have oldBits : MachineRegularOriginalBody.emittedBits H t =
      PreprocessingRegularWords.originalVertexBits t (PreprocessingRegularTables.padding t)
        (PreprocessingRegularTables.familyCloudTable H t) := rfl
  have ownerBits : MachineRegularOwnerBody.ownerBits H t =
      (fun v => (List.ofFn (PreprocessingRegularWords.dummyVertexBits t
        (PreprocessingRegularTables.padding t) (PreprocessingRegularTables.familyCloudTable H t) v)).flatten) := rfl
  simp only [finalOutput, oldOutput, headerOutput, Header.headerBits, Header.vertexTotal,
    Header.dartTotal, oldPrefix, ownerPrefix, PreprocessingRegularLoopWords.blocksPrefix_all,
    List.append_assoc]
  rw [oldBits, ownerBits]

end Top

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineRegularTableTrace
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top

open Turing MachineComposition
open UniqueGamesTheorem.Foundations.PCP

theorem headerStartTrace (H : BaseTable) (t : GraphTables.Table) :
    (advance (TM2.step (program H)))^[Header.totalTime PreprocessingRegularTables.internalDegree t []]
      (some (cfg H (some (.header .init)) (inputData t []) (fun _ => [])
        (counterStacks [] [] [] []))) =
      some (cfg H (some .oldSeed) (headerData t (headerOutput t)) (headerStacks t)
        (counterStacks [] [] [] [])) := by
  have run := headerTrace H t [] (counterStacks [] [] [] [])
  exact run.trans (normalizeEmptyAppend
    (fun output : List Bool => some (cfg H (some Label.oldSeed)
      (headerData t output) (headerStacks t) (counterStacks [] [] [] [])))
    (Header.headerBits PreprocessingRegularTables.internalDegree t))

theorem headerOldTrace (H : BaseTable) (t : GraphTables.Table) :
    (advance (TM2.step (program H)))^[
      Header.totalTime PreprocessingRegularTables.internalDegree t [] +
        (1+2*(t.darts+2)+(oldElapsed H t (headerOutput t) t.darts+1))]
      (some (cfg H (some (.header .init)) (inputData t []) (fun _ => [])
        (counterStacks [] [] [] []))) =
      some (cfg H (some .ownerSeed) (oldData t t.darts (oldOutput H t)) (headerStacks t)
        (counterStacks [] [] [] [])) := by
  have first := headerStartTrace H t
  have second := oldStageTrace H t (headerOutput t) (headerStacks t)
  have joined := joinTrace_p1 (f := advance (TM2.step (program H))) first second
  have output_eq : headerOutput t ++ oldPrefix H t t.darts = oldOutput H t := rfl
  exact joined.trans (congrArg
    (fun output : List Bool => some (cfg H (some Label.ownerSeed)
      (oldData t t.darts output) (headerStacks t) (counterStacks [] [] [] []))) output_eq)

theorem beforeCleanupTrace (H : BaseTable) (t : GraphTables.Table) :
    (advance (TM2.step (program H)))^[
      Header.totalTime PreprocessingRegularTables.internalDegree t [] +
        (1+2*(t.darts+2)+(oldElapsed H t (headerOutput t) t.darts+1)) +
        (1+2*(t.vertices+2)+(ownerElapsed H t (oldOutput H t) t.vertices+1))]
      (some (cfg H (some (.header .init)) (inputData t []) (fun _ => [])
        (counterStacks [] [] [] []))) =
      some ⟨clearEntry 0, readyState H, finalStacks t (finalOutput H t)⟩ := by
  have first := headerOldTrace H t
  have second := ownerStageTrace H t (oldOutput H t)
  have joined := joinTrace_p1 (f := advance (TM2.step (program H))) first second
  have output_eq : oldOutput H t ++ ownerPrefix H t t.vertices = finalOutput H t := rfl
  exact joined.trans (congrArg
    (fun output : List Bool => some (cfg H (clearEntry 0)
      (ownerData t t.vertices output) (headerStacks t) (counterStacks [] [] [] []))) output_eq)

theorem cleanupFinalTrace (H : BaseTable) (t : GraphTables.Table) (output : List Bool) :
    (advance (TM2.step (program H)))^[cleanupTime (finalStacks t output) 7]
      (some ⟨clearEntry 0, readyState H, finalStacks t output⟩) =
      some (cfg H none (inputData t output) (fun _ => []) (counterStacks [] [] [] [])) :=
  (cleanupTrace H (finalStacks t output)).trans
    (congrArg (fun terminalStacks => some (⟨none, readyState H, terminalStacks⟩ : TM2.Cfg Alphabet Label State))
      (cleaned_finalStacks t output))

theorem fullTrace (H : BaseTable) (t : GraphTables.Table) :
    (advance (TM2.step (program H)))^[totalTime H t]
      (some (cfg H (some (.header .init)) (inputData t []) (fun _ => [])
        (counterStacks [] [] [] []))) =
      some (cfg H none (inputData t (finalOutput H t)) (fun _ => [])
        (counterStacks [] [] [] [])) :=
  joinTrace_p1 (f := advance (TM2.step (program H))) (beforeCleanupTrace H t) (cleanupFinalTrace H t (finalOutput H t))

@[simp] theorem update_frame_output (data : Data) (header : Header.Tape → List Bool)
    (counters : Fin 4 → List Bool) (replacement : List Bool) :
    Function.update (frame data header counters) (coreTape 8) replacement =
      frame { data with output := replacement } header counters := by
  funext j
  cases j with
  | inl j => cases j with
    | inl i => fin_cases i <;> rfl
    | inr e => cases e with
      | inl e => cases e <;> rfl
      | inr e => rfl
  | inr j => cases j <;> rfl

theorem input_stacks_eq (H : BaseTable) (t : GraphTables.Table) :
    frame (inputData t []) (fun _ => []) (counterStacks [] [] [] []) =
      (Turing.initList (machine H) (GraphTables.tableBits t)).stk := by
  funext j
  cases j with
  | inl j => cases j with
    | inl i => (fin_cases i <;>
        simp [Turing.initList, machine, coreTape, frame, inputData,
          MachineRegularOriginalBody.frame, MachineRegularMetadata.frame]); rfl
    | inr e => cases e with
      | inl e => cases e <;>
          simp [Turing.initList, machine, coreTape, frame, inputData,
            MachineRegularOriginalBody.frame, MachineRegularMetadata.frame]
      | inr e =>
          simp [Turing.initList, machine, coreTape, frame,
            MachineRegularOriginalBody.frame]
  | inr j => cases j with
    | inl j => simp [Turing.initList, machine, coreTape, frame]
    | inr j => fin_cases j <;> simp [Turing.initList, machine, coreTape, frame, counterStacks]

theorem initial_cfg_eq (H : BaseTable) (t : GraphTables.Table) :
    cfg H (some (.header .init)) (inputData t []) (fun _ => []) (counterStacks [] [] [] []) =
      Turing.initList (machine H) (GraphTables.tableBits t) := by
  change (⟨some (.header .init), readyState H,
    frame (inputData t []) (fun _ => []) (counterStacks [] [] [] [])⟩ : TM2.Cfg Alphabet Label State) =
    ⟨some (.header .init), readyState H, (Turing.initList (machine H) (GraphTables.tableBits t)).stk⟩
  rw [input_stacks_eq]

/-- Complete execution from the actual serialized input. All header reads,
metadata, geometric rotors, rows, counters and cleanup are run by this one
finite machine. No body trace or target-table computation is supplied as a premise. -/
theorem trace (H : BaseTable) (t : GraphTables.Table) :
    (advance (TM2.step (program H)))^[totalTime H t]
      (some (Turing.initList (machine H) (GraphTables.tableBits t))) =
      some ⟨none, readyState H,
        Function.update (Turing.initList (machine H) (GraphTables.tableBits t)).stk
          (coreTape 8) (PortTables.tableBits (PreprocessingRegularTables.regularize H t))⟩ := by
  have full := fullTrace H t
  rw [initial_cfg_eq, finalOutput_eq] at full
  have final_stacks :
      frame (inputData t (PortTables.tableBits (PreprocessingRegularTables.regularize H t)))
          (fun _ => []) (counterStacks [] [] [] []) =
        Function.update (Turing.initList (machine H) (GraphTables.tableBits t)).stk (coreTape 8)
          (PortTables.tableBits (PreprocessingRegularTables.regularize H t)) := by
    rw [← input_stacks_eq]
    erw [update_frame_output]
    rfl
  change (advance (TM2.step (program H)))^[totalTime H t]
    (some (Turing.initList (machine H) (GraphTables.tableBits t))) =
    some ⟨none, readyState H,
      frame (inputData t (PortTables.tableBits (PreprocessingRegularTables.regularize H t)))
        (fun _ => []) (counterStacks [] [] [] [])⟩ at full
  rw [final_stacks] at full
  exact full

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineRegularTableBoundsLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-! A polynomial cap for the actual two regularization loops, their header,
and all seven final drain loops. Per-call sizes include the complete stored
output prefix. -/
namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top

open Turing MachineComposition PCP PreprocessingRegularTables
open PreprocessingRegularBounds PreprocessingMachineBounds


noncomputable def oldLoopPolynomial : Polynomial Nat :=
  Polynomial.X *
    (MachineRegularOriginalBodyBounds.timePolynomial.comp
      (Polynomial.X + regularPolynomial) + 2)

noncomputable def ownerLoopPolynomial : Polynomial Nat :=
  Polynomial.X *
    (MachineRegularOwnerBodyBounds.timePolynomial.comp
      (Polynomial.X + regularPolynomial) + 2)

noncomputable def timePolynomial : Polynomial Nat :=
  Header.timePolynomial internalDegree + oldLoopPolynomial + ownerLoopPolynomial +
    4 * Polynomial.X + 12 +
    Polynomial.C (7 * (ExpanderFamily.growth * (internalDegree + 4) + 4)) *
      (Polynomial.X + 1)

theorem oldElapsed_prefix_le (H : BaseTable) (t : GraphTables.Table) (k : Nat) :
    oldElapsed H t (Header.headerBits internalDegree t) k ≤
      k * (MachineRegularOriginalBodyBounds.timePolynomial.eval
        (inputLength t + regularPolynomial.eval (inputLength t)) + 2) := by
  induction k with
  | zero => simp [oldElapsed]
  | succ k ih =>
    simp only [oldElapsed]
    split_ifs with hk
    · have raw := MachineRegularOriginalBodyBounds.totalSteps_le H t ⟨k, hk⟩
        (Header.headerBits internalDegree t ++ oldPrefix H t k)
      have hprefix :
          (Header.headerBits internalDegree t ++ oldPrefix H t k).length ≤
            regularPolynomial.eval (inputLength t) := by
        exact regular_originalPrefix_le t H k
      have hcall := raw.trans (natPolynomial_eval_mono
        MachineRegularOriginalBodyBounds.timePolynomial (Nat.add_le_add_left hprefix _))
      rw [Nat.succ_mul]
      omega
    · rw [Nat.succ_mul]
      omega

theorem oldElapsed_le (H : BaseTable) (t : GraphTables.Table) :
    oldElapsed H t (Header.headerBits internalDegree t) t.darts ≤
      oldLoopPolynomial.eval (inputLength t) := by
  have bound := (oldElapsed_prefix_le H t t.darts).trans
    (Nat.mul_le_mul_right _ (GraphTables.darts_le_tableBits_length t))
  simpa only [oldLoopPolynomial, inputLength, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_add, Polynomial.eval_comp, Polynomial.eval_ofNat] using bound

theorem ownerElapsed_prefix_le (H : BaseTable) (t : GraphTables.Table) (k : Nat) :
    ownerElapsed H t
      (Header.headerBits internalDegree t ++ oldPrefix H t t.darts) k ≤
      k * (MachineRegularOwnerBodyBounds.timePolynomial.eval
        (inputLength t + regularPolynomial.eval (inputLength t)) + 2) := by
  induction k with
  | zero => simp [ownerElapsed]
  | succ k ih =>
    simp only [ownerElapsed]
    split_ifs with hk
    · have raw := MachineRegularOwnerBodyBounds.totalSteps_le H t ⟨k, hk⟩
        ((Header.headerBits internalDegree t ++ oldPrefix H t t.darts) ++ ownerPrefix H t k)
      have hprefix :
          ((Header.headerBits internalDegree t ++ oldPrefix H t t.darts) ++
            ownerPrefix H t k).length ≤ regularPolynomial.eval (inputLength t) := by
        rw [owner_output_eq_ownerPrefix]
        exact regular_ownerPrefix_le t H k
      have hcall := raw.trans (natPolynomial_eval_mono
        MachineRegularOwnerBodyBounds.timePolynomial (Nat.add_le_add_left hprefix _))
      rw [Nat.succ_mul]
      omega
    · rw [Nat.succ_mul]
      omega

theorem ownerElapsed_le (H : BaseTable) (t : GraphTables.Table) :
    ownerElapsed H t
      (Header.headerBits internalDegree t ++ oldPrefix H t t.darts) t.vertices ≤
      ownerLoopPolynomial.eval (inputLength t) := by
  have bound := (ownerElapsed_prefix_le H t t.vertices).trans
    (Nat.mul_le_mul_right _ (GraphTables.vertices_le_tableBits_length t))
  simpa only [ownerLoopPolynomial, inputLength, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_add, Polynomial.eval_comp, Polynomial.eval_ofNat] using bound

theorem totalTime_le (H : BaseTable) (t : GraphTables.Table) :
    totalTime H t ≤ timePolynomial.eval (inputLength t) := by
  have header := Header.totalTime_le internalDegree t []
  simp only [List.length_nil, Nat.add_zero] at header
  change Header.totalTime internalDegree t [] ≤
    (Header.timePolynomial internalDegree).eval (inputLength t) at header
  have old := oldElapsed_le H t
  have owners := ownerElapsed_le H t
  have cleanup := cleanupTime_final_le t (finalOutput H t)
  have hm : t.darts ≤ inputLength t := GraphTables.darts_le_tableBits_length t
  have hn : t.vertices ≤ inputLength t := GraphTables.vertices_le_tableBits_length t
  simp only [totalTime, headerOutput, oldOutput, timePolynomial,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_ofNat, Polynomial.eval_one]
  omega

noncomputable def machineInTime (H : BaseTable) (t : GraphTables.Table) :
    StateTransition.EvalsToInTime (TM2.step (program H))
      (initList (machine H) (GraphTables.tableBits t))
      (some ⟨none, readyState H,
        Function.update (initList (machine H) (GraphTables.tableBits t)).stk
          (coreTape 8) (PortTables.tableBits (regularize H t))⟩)
      (timePolynomial.eval (inputLength t)) where
  steps := totalTime H t
  evals_in_steps := trace H t
  steps_le_m := totalTime_le H t

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top



namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularTableRuntime

open Turing
open PCP
open MachineRegularTable.Top (Tape Label State coreTape readyState)


def rawProgram (H : PreprocessingRegularTables.BaseTable) :
    MachineCanonicalOutput.Program Tape Label State where
  input := coreTape 0
  output := coreTape 8
  main := .header .init
  initial := readyState H
  code := MachineRegularTable.Top.program H

theorem sourceMachine_eq (H : PreprocessingRegularTables.BaseTable) :
    MachineCanonicalOutput.sourceMachine (rawProgram H) =
      MachineRegularTable.Top.machine H := rfl

noncomputable def cleanupTapes : List Tape :=
  (Finset.univ : Finset Tape).toList.filter (fun k => decide (k ≠ coreTape 8))

theorem cleanup_complete (H : PreprocessingRegularTables.BaseTable) (k : Tape) :
    k ∈ cleanupTapes ↔ k ≠ (rawProgram H).output := by
  simp [cleanupTapes, rawProgram]

noncomputable def terminalRun (H : PreprocessingRegularTables.BaseTable)
    (t : GraphTables.Table) :
    MachineCanonicalOutput.TerminalRun (rawProgram H) (GraphTables.tableBits t)
      (PortTables.inputBits (PreprocessingStageMaps.regular H t))
      (MachineRegularTable.Top.timePolynomial.eval (GraphTables.tableBits t).length) where
  state := readyState H
  tapes := Function.update
    (initList (MachineRegularTable.Top.machine H) (GraphTables.tableBits t)).stk
    (coreTape 8) (PortTables.inputBits (PreprocessingStageMaps.regular H t))
  execution := by
    simpa only [sourceMachine_eq, FinTM2.Cfg, FinTM2.step, MachineRegularTable.Top.machine,
      PreprocessingMachineBounds.inputLength, PreprocessingStageMaps.regular,
      PortTables.inputBits] using!
      MachineRegularTable.Top.machineInTime H t
  output_eq := by
    dsimp only [rawProgram]
    erw [Function.update_self]

/-- The literal canonical output configuration computes the shared regular
preprocessing map, with the actual complete raw execution as its witness. -/
noncomputable def computableInPolyTime (H : PreprocessingRegularTables.BaseTable) :
    TM2ComputableInPolyTime GraphTables.tableBits
      (PortTables.inputBits (ports := PreprocessingRegularTables.internalDegree + 1))
      (PreprocessingStageMaps.regular H) :=
  MachineCanonicalOutput.computableInPolyTime (rawProgram H) cleanupTapes
    (cleanup_complete H) GraphTables.tableBits PortTables.inputBits
    (PreprocessingStageMaps.regular H) MachineRegularTable.Top.timePolynomial (terminalRun H)

/-- Finiteness refers to the exact machine in the preceding certificate. -/
theorem finite_alphabet (H : PreprocessingRegularTables.BaseTable) :
    ∀ k, Finite ((computableInPolyTime H).tm.Γ k) :=
  MachineCanonicalOutput.computableInPolyTime_finite_alphabet (rawProgram H) cleanupTapes
    (cleanup_complete H) GraphTables.tableBits PortTables.inputBits
    (PreprocessingStageMaps.regular H) MachineRegularTable.Top.timePolynomial (terminalRun H)

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularTableRuntime

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_PoweringMachineRelationLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringMachineRelation

open Turing
open MachineComposition
open PCP

variable {K Λ σ : Type} [DecidableEq K]
variable {n d : Nat}

theorem steps_le (table : PortTables.Table n d) (vertex : Fin n) (port : Fin d)
    (position : Fin 4096) :
    MachineAffineLookup.steps (PortTables.tableWords table) vertex.val
      (4098 * d) (4098 * port.val + 4 + position.val) ≤
      7 * (PortTables.tableBits table).length + 6 :=
  MachineAffineLookup.steps_le_table (PortTables.tableWords table) vertex.val
    (4098 * d) (4098 * port.val + 4 + position.val) (value table vertex port position)
    (selected table vertex port position)
    (Nat.le_trans (Nat.le_of_lt vertex.isLt) (PortTables.vertices_le_tableBits_length table))

end UniqueGamesTheorem.Foundations.Complexity.PoweringMachineRelation

/-! A rotor step on the live unary port-table encoding. First read the reverse
dart identifier; then read that dart's tail vertex. This uses no division or
runtime graph data in finite control. Both positional selections are proved
from the actual serialization. -/

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringMachineRotor

open Turing
open MachineComposition
open PCP

variable {K Λ σ : Type} [DecidableEq K]
variable {n d : Nat}

theorem steps_le (table : PortTables.Table n d) (vertex : Fin n) (port : Fin d) :
    steps table vertex port ≤ 14 * (PortTables.tableBits table).length + 12 := by
  have hvertex : vertex.val ≤ (encodeWords (PortTables.tableWords table)).length :=
    Nat.le_trans (Nat.le_of_lt vertex.isLt) (PortTables.vertices_le_tableBits_length table)
  have hreverse := MachineLookupSpec.output_length_le (PortTables.tableWords table)
    (reverseAddress vertex port) (reverseId table vertex port) (reverse_selected table vertex port)
  rw [encodeWord_length] at hreverse
  have hr := MachineAffineLookup.steps_le_table (PortTables.tableWords table)
    vertex.val (4098 * d) (4098 * port.val + 3) (reverseId table vertex port)
    (reverse_selected table vertex port) hvertex
  have he := MachineAffineLookup.steps_le_table (PortTables.tableWords table)
    (reverseId table vertex port) 4098 2 ((PortTables.rotation table (vertex, port)).1.val)
    (endpoint_selected table vertex port) (by omega)
  change _ ≤ 14 * (encodeWords (PortTables.tableWords table)).length + 12
  unfold steps
  omega

end UniqueGamesTheorem.Foundations.Complexity.PoweringMachineRotor

/-! Fixed port words are executed by a finite chain of actual rotor programs.
The six shared tapes hold table, query, scan, reverse identifier, scratch and
output. Each walk position has a separate physical vertex tape. The final
unary copy also handles the empty word and preserves the starting vertex. -/

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringMachineWord

open Turing
open MachineComposition
open PCP

variable {K Λ σ : Type} [DecidableEq K]
variable {n d : Nat}

theorem steps_le (table : PortTables.Table n d) (t : Nat)
    (vertex : Fin n) (ports : Fin t → Fin d) :
    steps table t vertex ports ≤ (14 * t + 2) * (PortTables.tableBits table).length + 12 * t + 3 := by
  induction t generalizing vertex with
  | zero =>
      have h := Nat.le_trans (Nat.le_of_lt vertex.isLt) (PortTables.vertices_le_tableBits_length table)
      simp only [steps, Nat.mul_zero, Nat.zero_add]
      omega
  | succ t ih =>
      have hr := PoweringMachineRotor.steps_le table vertex (ports 0)
      have ht := ih (PortTables.rotation table (vertex, ports 0)).1 (fun j => ports j.succ)
      simp only [steps, Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.mul_assoc] at ht ⊢
      omega

end UniqueGamesTheorem.Foundations.Complexity.PoweringMachineWord

/-! A fixed shared tape layout for the actual powering field subroutines.
The vertex identifiers live on physical tapes. The trajectory capacity is
fixed by `max`; each bounded word uses its first `t` trajectory tapes. -/

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_PoweringMachineEqualityField
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Actual producer for equality of two bounded walk endpoints

The two port words are fixed finite control. Each executes against the live
rotor table from the same preserved starting vertex. Their endpoint fields
are compared by the physical unary equality primitive. The emitted field is
the Boolean equality of the two actual walk endpoints.

Work tapes may retain arbitrary histories. The table, start, scratch and two
comparison copies satisfy exact frame theorems. There is no execution or
running-time premise in the composite trace theorem.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringMachineEqualityField

open Turing
open MachineComposition
open PCP

variable {K Λ A : Type} [DecidableEq K]
variable {max l r n d : Nat}

theorem steps_le (graph : PortTables.Table n d) (vertex : Fin n)
    (left : Fin l → Fin d) (right : Fin r → Fin d) :
    steps graph vertex left right ≤
      (14 * (l + r) + 10) * (PortTables.tableBits graph).length + 12 * (l + r) + 15 := by
  have hl := PoweringMachineWord.steps_le graph l vertex left
  have hr := PoweringMachineWord.steps_le graph r vertex right
  have he := MachineUnaryEqualityBit.steps_le
    (endpoint graph vertex left).val (endpoint graph vertex right).val
  have hleft := Nat.le_trans (Nat.le_of_lt (endpoint graph vertex left).isLt)
    (PortTables.vertices_le_tableBits_length graph)
  have hright := Nat.le_trans (Nat.le_of_lt (endpoint graph vertex right).isLt)
    (PortTables.vertices_le_tableBits_length graph)
  unfold steps
  simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc] at hl hr ⊢
  omega

end UniqueGamesTheorem.Foundations.Complexity.PoweringMachineEqualityField

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_PoweringGlobalEnumerationLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Explicit executable enumeration of the global powering tapes

The four header tapes come first, followed by the eleven shared roles, the
bounded trajectory tapes, and the final output tape. Both directions use
constructor cases and arithmetic sum encodings. No enumeration is selected
from a cardinality theorem.
-/

/-! A concrete relation-field producer: execute a fixed word from the live
start vertex, then read the predicate at the reached vertex and fixed port.
All instructions use the shared tape layout and preserve the finite row
buffer. No execution premise is supplied by the caller. -/

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringMachineRelationField

open Turing
open MachineComposition
open PCP

variable {K Λ A : Type} [DecidableEq K]
variable {n d max : Nat}

theorem steps_le (path : List (Fin d)) (port : Fin d) (left right : PortTables.Label)
    (table : PortTables.Table n d) (vertex : Fin n) :
    steps path port left right table vertex ≤
      (14 * path.length + 9) * (PortTables.tableBits table).length + 12 * path.length + 9 := by
  have hw := PoweringMachineWord.steps_le table path.length vertex path.get
  have hr := PoweringMachineRelation.steps_le table (endpoint table vertex path) port
    (GraphTables.relationIndex (left, right))
  simp only [steps, Nat.add_mul, Nat.mul_assoc] at hw ⊢
  omega

end UniqueGamesTheorem.Foundations.Complexity.PoweringMachineRelationField

/-! The concrete finite program that produces an entire powered-row input
block. Its static control executes the field plan backwards, so prepending each
computed unary Boolean field leaves the canonical serialized block in order. -/

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringMachineRowHeaders

open Turing MachineComposition
open PCP PoweringRowHeaderSemantics
open PoweringMachineTapes

variable {K Λ σ : Type} [DecidableEq K]
variable {vertices d max : Nat}

/-- Linear in the serialized input length for the fixed word length. -/
theorem steps_le (input : PortTables.Table vertices d) (n : Nat) (vertex : Fin vertices)
    (ports : Fin (n + 1) → Fin d) (direction : Bool) :
    steps input n vertex ports direction ≤
      (14 * (n + 1) + 4) * (PortTables.tableBits input).length + 12 * (n + 1) + 6 := by
  have hv : vertex.val ≤ (PortTables.tableBits input).length :=
    Nat.le_trans (Nat.le_of_lt vertex.isLt) (PortTables.vertices_le_tableBits_length input)
  have hw := PoweringMachineWord.steps_le input (n + 1) vertex ports
  cases direction <;> simp only [steps, Bool.false_eq_true, ite_false, ite_true, if_true]
  · simp only [Nat.add_mul]
    omega
  · calc
      _ ≤ (2 * (PortTables.tableBits input).length + 3) +
          ((14 * (n + 1) + 2) * (PortTables.tableBits input).length + 12 * (n + 1) + 3) :=
        Nat.add_le_add (by omega) hw
      _ = _ := by simp only [Nat.add_mul]; omega

end UniqueGamesTheorem.Foundations.Complexity.PoweringMachineRowHeaders

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_PoweringMachineFinish
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Physical output headers followed by complete work-tape cleanup

The finite program first copies the dart-count word onto the existing row
output, then copies the vertex-count word, and finally drains every tape except
the output. Both unary header values are read from physical tapes; they do not
parameterize the program. Header sources and their unread suffixes are restored
by the two copies before cleanup. The final configuration contains the full
encoded header and rows on the output tape and empty words on every other tape.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringMachineFinish

open Turing MachineComposition

variable {K Λ σ : Type} [DecidableEq K] {N : Nat}

/-- Exact execution inside any ambient program containing these instructions.
The only data premises describe physical header words and an empty scratch tape. -/
theorem traceAt (enumeration : Fin N ≃ K) (headerV headerD output scratch : K)
    (hvs : headerV ≠ scratch) (hvo : headerV ≠ output)
    (hds : headerD ≠ scratch) (hdo : headerD ≠ output) (hso : scratch ≠ output)
    (labels : Label enumeration output → Λ)
    (target : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLabels : ∀ l, target (labels l) =
      instruction enumeration headerV headerD output scratch labels l)
    (base : K → List Bool) (n m : Nat) (suffixV suffixD : List Bool)
    (wordV : base headerV = encodeWord n ++ suffixV)
    (wordD : base headerD = encodeWord m ++ suffixD)
    (scratchEmpty : base scratch = []) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step target))^[steps enumeration output base n m]
      (some ⟨some (labels (.inl .seed)), (ambient, register), base⟩) =
      some ⟨none, (ambient, none),
        MachineDrainMany.haltTapes output (encodeWords [n, m] ++ base output)⟩ := by
  have hd := MachineUnaryAffineAt.seededAffineTrace headerD scratch output hds hdo hso 1 0
    (labels (.inl .seed)) (labels (.inl .scan)) (labels (.inl .restore))
    (some (labels (.inr (.inl .seed)))) target
    (atLabels (.inl .seed)) (atLabels (.inl .scan)) (atLabels (.inl .restore))
    base m suffixD wordD scratchEmpty ambient register
  simp only [Nat.one_mul, Nat.add_zero] at hd
  change (advance (TM2.step target))^[2 * (m + 1) + 1]
    (some ⟨some (labels (.inl .seed)), (ambient, register), base⟩) =
    some ⟨some (labels (.inr (.inl .seed))), (ambient, none), afterD output base m⟩ at hd
  have wordV' : afterD output base m headerV = encodeWord n ++ suffixV := by
    simpa only [afterD, Function.update_of_ne hvo] using wordV
  have scratchEmpty' : afterD output base m scratch = [] := by
    simpa only [afterD, Function.update_of_ne hso] using scratchEmpty
  have hv := MachineUnaryAffineAt.seededAffineTrace headerV scratch output hvs hvo hso 1 0
    (labels (.inr (.inl .seed))) (labels (.inr (.inl .scan)))
    (labels (.inr (.inl .restore)))
    (MachineDrainMany.entry (MachineDrainMany.workTapes enumeration output)
      (fun q => labels (.inr (.inr q))) none)
    target (atLabels (.inr (.inl .seed))) (atLabels (.inr (.inl .scan)))
    (atLabels (.inr (.inl .restore))) (afterD output base m) n suffixV
    wordV' scratchEmpty' ambient none
  simp only [Nat.one_mul, Nat.add_zero] at hv
  have copied : Function.update (afterD output base m) output
      (encodeWord n ++ afterD output base m output) = afterHeaders output base n m := by
    simp only [afterD, afterHeaders, Function.update_self, Function.update_idem,
      encodeWords, List.append_nil, List.append_assoc]
  rw [copied] at hv
  have cleaned := MachineDrainMany.cleanupTrace enumeration output
    (fun q => labels (.inr (.inr q))) target (fun l => atLabels (.inr (.inr l)))
    (afterHeaders output base n m) ambient
  rw [afterHeaders_output] at cleaned
  have total := trace_trans _ (trace_trans _ hd hv) cleaned
  simpa only [steps, copySteps] using total

end UniqueGamesTheorem.Foundations.Complexity.PoweringMachineFinish

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_PoweringPlanBudget
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Execution budget of the concrete powered-row field plan

The cost is the sum of the actual relation and endpoint-comparison transition
counts. Each fixed command scans only the serialized input graph. The execution
certificates below instantiate the concrete plan trace; no execution witness or
running-time bound is assumed.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringPlanBudget

open Turing MachineComposition PCP PoweringFieldPlan

variable {K Λ A : Type} [DecidableEq K] {vertices d max : Nat}

theorem field_steps_le (graph : PortTables.Table vertices d) (vertex : Fin vertices)
    (op : Instruction d) (bounded : op.radius ≤ max) :
    PoweringMachineField.steps graph vertex op ≤
      fieldBudget max (PortTables.tableBits graph).length := by
  cases op with
  | relation path port left right =>
      change path.length ≤ max at bounded
      have h := PoweringMachineRelationField.steps_le path port left right graph vertex
      have coefficient : 14 * path.length + 9 ≤ 28 * max + 10 := by omega
      have product := Nat.mul_le_mul_right (PortTables.tableBits graph).length coefficient
      change PoweringMachineRelationField.steps path port left right graph vertex ≤ _
      unfold fieldBudget
      omega
  | equal left right =>
      change Nat.max left.length right.length ≤ max at bounded
      have hl : left.length ≤ max := (le_max_left _ _).trans bounded
      have hr : right.length ≤ max := (le_max_right _ _).trans bounded
      have h := PoweringMachineEqualityField.steps_le graph vertex left.get right.get
      have coefficient : 14 * (left.length + right.length) + 10 ≤ 28 * max + 10 := by
        omega
      have product := Nat.mul_le_mul_right (PortTables.tableBits graph).length coefficient
      change PoweringMachineEqualityField.steps graph vertex left.get right.get ≤ _
      unfold fieldBudget
      omega

/-- Sum the actual recursive cost, including its changing intermediate tapes. -/
theorem plan_steps_le (graph : PortTables.Table vertices d)
    (placement : PoweringMachineTapes.Tape max → K) (vertex : Fin vertices)
    (commands : List (PoweringMachinePlan.Command d max)) (base : K → List Bool) :
    PoweringMachinePlan.steps graph placement vertex commands base ≤
      commands.length * fieldBudget max (PortTables.tableBits graph).length := by
  induction commands generalizing base with
  | nil => simp only [PoweringMachinePlan.steps, MachineFiniteSequence.steps,
      List.length_nil, Nat.zero_mul, Nat.le_refl]
  | cons op commands ih =>
      have first := field_steps_le graph vertex op.val op.property
      have rest := ih (PoweringMachinePlan.result graph placement vertex op base)
      change PoweringMachineField.steps graph vertex op.val +
        PoweringMachinePlan.steps graph placement vertex commands
          (PoweringMachinePlan.result graph placement vertex op base) ≤ _
      simpa only [List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_comm] using
        Nat.add_le_add first rest

/-- The backwards plan that produces the actual row-data tape obeys this bound. -/
theorem rowPlan_steps_le (graph : PortTables.Table vertices d) (n : Nat)
    (ports : Fin (n + 1) → Fin d) (direction : Bool)
    (placement : PoweringMachineTapes.Tape (2 * (n + 1)) → K)
    (vertex : Fin vertices) (base : K → List Bool) :
    PoweringMachinePlan.steps graph placement vertex
        (PoweringMachinePlan.boundedRowPlan n ports direction).reverse base ≤
      PoweringMachineRow.inputSize (n + 1) (PoweringRowData.slotCount d n) *
        ((28 * (2 * (n + 1)) + 10) * (PortTables.tableBits graph).length +
          24 * (2 * (n + 1)) + 15) := by
  have h := plan_steps_le graph placement vertex
    (PoweringMachinePlan.boundedRowPlan n ports direction).reverse base
  simpa only [List.length_reverse, boundedRowPlan_length, fieldBudget] using h

end UniqueGamesTheorem.Foundations.Complexity.PoweringPlanBudget

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_PoweringMachineRowBody
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringMachineRowBody

open Turing MachineComposition PCP
open MachineFixedBlockMap

variable {K Λ : Type} [DecidableEq K] {vertices d : Nat}

theorem steps_le (graph : PortTables.Table vertices d) (vertex : Fin vertices)
    (n : Nat) (ports : Fin (n + 1) → Fin d) (direction : Bool) :
    steps graph vertex n ports direction ≤ budget d n (PortTables.tableBits graph).length := by
  have hp := PoweringPlanBudget.rowPlan_steps_le graph n ports direction id vertex (fun _ => [])
  rw [planSteps_eq] at hp
  have hh := PoweringMachineRowHeaders.steps_le graph n vertex ports direction
  change planSteps graph vertex (commands n ports direction) ≤
    PoweringPlanBudget.rowBudget d n (PortTables.tableBits graph).length at hp
  unfold steps budget
  omega

end UniqueGamesTheorem.Foundations.Complexity.PoweringMachineRowBody

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_PoweringMachineVertex
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringMachineVertex

open Turing MachineComposition PCP

variable {K Λ : Type} [DecidableEq K] {vertices d n : Nat}

theorem costSum_le (graph : PortTables.Table vertices d) (vertex : Fin vertices)
    (n : Nat) (ops : List (Command d n)) :
    costSum graph vertex n ops ≤
      ops.length * PoweringMachineRowBody.budget d n (PortTables.tableBits graph).length := by
  induction ops with
  | nil => simp only [costSum, List.length_nil, Nat.zero_mul, Nat.le_refl]
  | cons j ops ih =>
      have hfirst := PoweringMachineRowBody.steps_le graph vertex n (ports j) (direction j)
      change PoweringMachineRowBody.steps graph vertex n (ports j) (direction j) +
        costSum graph vertex n ops ≤ _
      simpa only [List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_comm] using
        Nat.add_le_add hfirst ih

theorem steps_le (graph : PortTables.Table vertices d) (vertex : Fin vertices) (n : Nat) :
    steps graph vertex n ≤ budget d n (PortTables.tableBits graph).length := by
  simpa only [steps, budget, commands_length] using costSum_le graph vertex n (commands d n)

end UniqueGamesTheorem.Foundations.Complexity.PoweringMachineVertex

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_PoweringMachineOuterLoopLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual variable-size vertex enumeration. The finite guard decrements the
live unary counter, a one-step bridge enters the fixed vertex producer, and the
producer returns to the guard. Work tapes may change after every vertex. -/

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringMachineOuterLoop

open Turing MachineComposition PCP

variable {K Λ : Type} [DecidableEq K] {vertices d n : Nat}

theorem steps_le (graph : PortTables.Table vertices d) (n remaining : Nat)
    (bounded : remaining ≤ vertices) :
    steps graph n remaining bounded ≤
      remaining * (PoweringMachineVertex.budget d n (PortTables.tableBits graph).length + 2) + 1 := by
  induction remaining with
  | zero => simp [steps]
  | succ r ih =>
      have hv := PoweringMachineVertex.steps_le graph (⟨r, by omega⟩ : Fin vertices) n
      have hi := ih (by omega)
      simp only [steps, Nat.add_mul, Nat.one_mul]
      omega

def loopInTime (graph : PortTables.Table vertices d) (n : Nat)
    (placement : Placement K n) (distinct : Function.Injective placement)
    (output : K) (outside : ∀ i, output ≠ placement i)
    (guardLabel bridgeLabel exitLabel : Λ) (labels : PoweringMachineVertex.Label d n → Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State d n))
    (atGuard : program guardLabel =
      MachineUnaryCounter.guard (placement (.inl 1)) bridgeLabel exitLabel)
    (atBridge : program bridgeLabel = bridge d n labels guardLabel)
    (atVertex : ∀ l, program (labels l) =
      PoweringMachineVertex.instruction n placement output labels (some guardLabel) l)
    (remaining : Nat) (bounded : remaining ≤ vertices) (base : K → List Bool)
    (ready : Ready graph n placement base) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some guardLabel, PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n),
        counter placement base remaining⟩
      (some ⟨some exitLabel, PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n),
        finalTapes graph n placement output remaining bounded base⟩)
      (remaining * (PoweringMachineVertex.budget d n (PortTables.tableBits graph).length + 2) + 1) where
  steps := steps graph n remaining bounded
  evals_in_steps := loopTrace graph n placement distinct output outside guardLabel bridgeLabel
    exitLabel labels program atGuard atBridge atVertex remaining bounded base ready
  steps_le_m := steps_le graph n remaining bounded

end UniqueGamesTheorem.Foundations.Complexity.PoweringMachineOuterLoop

/-!
# The fixed global powering machine

For fixed degree `d` and radius parameter `n`, this is one concrete finite
machine: initialization, unary vertex guard, the fixed vertex-row producer,
and output-header/cleanup instructions are connected by explicit labels.
Its definition takes no input graph, vertex count, or program callback.

The code equations below expose each actual branch for the separate runtime
proof. The variable-size input graph and counters reside on physical tapes.
-/

/-!
# Concrete global configurations and tape separation

These lemmas specialize the checked initializer placement to the fixed global
machine. The final configuration is the actual `Turing.haltList`, with the
machine's clean initial register and only the output tape populated.
-/

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_PoweringPolynomialBudgetLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finishing cost from the actual preceding machine execution

Every stack can grow by at most the fixed program's push bound in one
transition. Consequently an actual bounded execution from the standard input
configuration supplies the uniform stack bound needed by the finishing phase.
The bound below uses the same global machine for that preceding execution; no
separate tape-size hypothesis or numerical simulation is substituted for it.
-/

/-! Complete execution of the one fixed powering machine on the actual
port-table input and generic graph-table output encodings. The varying vertex
count remains on unary tapes throughout. -/

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringMachineRuntime

open Turing MachineComposition PCP PoweringMachineGlobal

variable {vertices d : Nat}

/-- Actual execution from the literal single-input configuration through every
vertex. No graph-dependent instruction or supplied body-execution premise. -/
def beforeFinishExecution (graph : PortTables.Table vertices d) (n : Nat) :
    StateTransition.EvalsToInTime (machine d n).step
      (initList (machine d n) (PortTables.tableBits graph))
      (some (finishConfiguration graph n)) (beforeFinishBudget graph n) := by
  have initialRun := PoweringInitializeFrame.initializeInTime graph n
  have loop := PoweringMachineOuterLoop.loopInTime graph n (placement n)
    (PoweringMachineInitialize.commonPlacement_injective _) (outputTape n)
    (fun i => Ne.symm (PoweringMachineInitialize.commonPlacement_ne_finalOutput _ i))
    (guardLabel d n) (bridgeLabel d n) (finishEntry d n) (vertexLabels d n)
    (program d n) (atGuard d n) (atBridge d n) (atVertex d n)
    vertices (Nat.le_refl _) (PoweringInitializeFrame.preparedTapes graph n)
    (PoweringInitializeFrame.prepared_ready graph n)
  rw [PoweringInitializeFrame.prepared_counter] at loop
  simpa only [beforeFinishBudget, Nat.add_comm] using
    (StateTransition.EvalsToInTime.trans (machine d n).step
    (3 * vertices + 5)
    (vertices * (PoweringMachineVertex.budget d n (PortTables.tableBits graph).length + 2) + 1)
    (initList (machine d n) (PortTables.tableBits graph))
    (PoweringInitializeFrame.preparedCfg graph n) (some (finishConfiguration graph n))
    initialRun loop)

/-- The terminal configuration has precisely the actual output stream and no
remaining work tapes. -/
def finishExecution (graph : PortTables.Table vertices d) (n : Nat) :
    StateTransition.EvalsToInTime (machine d n).step (finishConfiguration graph n)
      (some (haltList (machine d n) (PoweringTables.outputBits graph n)))
      (finishSteps graph n) := by
  have run := PoweringMachineFinish.traceAt (enumeration n)
    (headerVertices n) (headerDarts n) (outputTape n)
    (placement n (PoweringMachineTapes.scratch (PoweringMachineRowBody.capacity n)))
    (PoweringGlobalConfiguration.headerVertices_ne_scratch n)
    (PoweringGlobalConfiguration.headerVertices_ne_output n)
    (PoweringGlobalConfiguration.headerDarts_ne_scratch n)
    (PoweringGlobalConfiguration.headerDarts_ne_output n)
    (PoweringMachineInitialize.commonPlacement_ne_finalOutput _ _)
    (finishLabels d n) (program d n) (atFinish d n)
    (beforeFinish graph n) vertices (PoweringTableLayout.blockSize d n * vertices) [] []
    (by simpa only [List.append_nil] using beforeFinish_vertices graph n)
    (by simpa only [List.append_nil] using beforeFinish_darts graph n)
    (beforeFinish_ready graph n).scratch
    (PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n)).1 none
  rw [serialized_eq] at run
  refine { steps := finishSteps graph n, evals_in_steps := ?_, steps_le_m := Nat.le_refl _ }
  change (advance (TM2.step (program d n)))^[finishSteps graph n]
    (some (finishConfiguration graph n)) = _
  rw [PoweringGlobalConfiguration.haltList_eq]
  simpa only [finishConfiguration, finishEntry, finishSteps, PoweringMasterState.clean,
    PoweringMasterState.withBuffer] using! run

/-- Whole-machine execution on the concrete input and output encodings. -/
def execution (graph : PortTables.Table vertices d) (n : Nat) :
    TM2OutputsInTime (machine d n) (PortTables.tableBits graph)
      (some (PoweringTables.outputBits graph n))
      (beforeFinishBudget graph n + finishSteps graph n) := by
  simpa only [TM2OutputsInTime, Option.map_some, Nat.add_comm] using!
    (StateTransition.EvalsToInTime.trans (machine d n).step
    (beforeFinishBudget graph n) (finishSteps graph n)
    (initList (machine d n) (PortTables.tableBits graph))
    (finishConfiguration graph n)
    (some (haltList (machine d n) (PoweringTables.outputBits graph n)))
    (beforeFinishExecution graph n) (finishExecution graph n))

theorem finishSteps_le (graph : PortTables.Table vertices d) (n : Nat) :
    finishSteps graph n ≤
      2 * (vertices + PoweringTableLayout.blockSize d n * vertices) + 6 +
      PoweringRuntimeBudget.tapeCount n *
        ((PortTables.tableBits graph).length + beforeFinishBudget graph n *
          Runtime.programPushBound (machine d n) + vertices +
          PoweringTableLayout.blockSize d n * vertices + 3) :=
  PoweringRuntimeBudget.finish_steps_le_of_execution d n (PortTables.tableBits graph)
    (finishConfiguration graph n) (beforeFinishBudget graph n) vertices
    (PoweringTableLayout.blockSize d n * vertices) (beforeFinishExecution graph n)

theorem execution_budget_le (graph : PortTables.Table vertices d) (n : Nat) :
    beforeFinishBudget graph n + finishSteps graph n ≤
      (PoweringPolynomialBudget.time d n (Runtime.programPushBound (machine d n))
        (PoweringRuntimeBudget.tapeCount n)).eval (PortTables.tableBits graph).length := by
  exact PoweringPolynomialBudget.execution_budget_le_time d n
    (Runtime.programPushBound (machine d n)) (PoweringRuntimeBudget.tapeCount n)
    vertices (PortTables.tableBits graph).length (PortTables.vertices_le_tableBits_length graph)
    (Nat.le_refl _) (finishSteps_le graph n)

/-- A genuine polynomial-time certificate for the actual finite powering
constructor, with the existing concrete codecs on both sides. -/
noncomputable def computableInPolyTime (d n : Nat) :
    TM2ComputableInPolyTime (@PortTables.inputBits d) GenericGraphTables.tableBits
      (PoweringTables.transform d n) where
  tm := machine d n
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := PoweringPolynomialBudget.time d n (Runtime.programPushBound (machine d n))
    (PoweringRuntimeBudget.tapeCount n)
  outputsFun input := by
    rcases input with ⟨vertices, graph⟩
    have run := execution graph n
    let bounded : TM2OutputsInTime (machine d n) (PortTables.tableBits graph)
        (some (PoweringTables.outputBits graph n))
        ((PoweringPolynomialBudget.time d n (Runtime.programPushBound (machine d n))
          (PoweringRuntimeBudget.tapeCount n)).eval (PortTables.tableBits graph).length) :=
      ⟨run.toEvalsTo, run.steps_le_m.trans (execution_budget_le graph n)⟩
    change TM2OutputsInTime (machine d n) ((PortTables.tableBits graph).map id)
      (some ((PoweringTables.outputBits graph n).map id)) _
    have input_eq :
        @List.map ((machine d n).Γ (machine d n).k₀)
          ((machine d n).Γ (machine d n).k₀) id (PortTables.tableBits graph) =
          PortTables.tableBits graph := List.map_id _
    have output_eq :
        @List.map ((machine d n).Γ (machine d n).k₁)
          ((machine d n).Γ (machine d n).k₁) id (PoweringTables.outputBits graph n) =
          PoweringTables.outputBits graph n := List.map_id _
    simpa only [input_eq, output_eq, PortTables.inputBits] using bounded

/-- Every work tape, as well as the input/output tapes, has a finite alphabet. -/
theorem computableInPolyTime_finite_alphabet (d n : Nat) :
    ∀ k, Finite ((computableInPolyTime d n).tm.Γ k) := by
  intro k
  change Finite Bool
  infer_instance

end UniqueGamesTheorem.Foundations.Complexity.PoweringMachineRuntime

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Reduction_FinishReduction
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-!
The concrete final composition, once the matrix reduction has been proved.
This constructor copies the actual occurrence list, subdivides every occurrence
into four edges, and runs the full tuple-product machine. Its hypotheses are
the matrix reduction's actual value bounds and finite-machine computation.
It is an intermediate composition theorem, not the unconditional endpoint.
-/

namespace UniqueGamesTheorem.FinishReduction


open UniqueGamesTheorem.Foundations Target
open UniqueGamesTheorem.Foundations.Complexity
open UniqueGamesTheorem.Integration
open Explicit

noncomputable section

/-- Compose the proved matrix reduction with the explicit three-stage finish.
All parameters, machines, alphabets, and time polynomials precede the input.
The original raw binary input codec is retained by sequential composition. -/
def of_matrix_reduction {ε δ : ℝ} (P : ParameterSelection.OuterParameters ε δ)
    {q s : ℕ} (hq : 2 ≤ q) (hs : 1 ≤ s)
    (coordinates : Fin q ≃ BinaryLinear.Vector s)
    (matrix : List Bool → Instance q)
    (translations : ∀ input, TranslationTarget.IsTranslationInstance coordinates (matrix input))
    (computation : Turing.TM2ComputableInPolyTime (id : List Bool → List Bool)
      gameBits matrix)
    (finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet computation.tm)
    (d : ℚ) (hd : d ≤ P.epsilon0 / P.repetitions)
    (complete : ∀ input, BinaryLanguage.language input →
      1 - (d : ℝ) ≤ InstanceValue.value (matrix input))
    (sound : ∀ input, ¬BinaryLanguage.language input →
      InstanceValue.value (matrix input) ≤ 99 / 100) :
    MachineOutputContract.BinaryGapReduction ε δ := by
  classical
  have hqpos : 0 < q := by omega
  have hC : 0 < P.copies := by have h := P.copies_large; omega
  letI : Nonempty (Fin q) := ⟨⟨0, hqpos⟩⟩
  let rounded := fun input => UniformTarget.construct P.copies hC (matrix input)
  have roundedTranslations : ∀ input,
      TranslationTarget.IsTranslationInstance coordinates (rounded input) := fun input =>
    UniformTarget.translations P.copies hC (matrix input) coordinates (translations input)
  let roundedMachine := MachineSequential.composeBits
    (f := matrix) (g := UniformTarget.construct P.copies hC) computation
    (MachineUniformRun.computation (q := q) P.copies hC)
  have roundedFinite : MachineFiniteAlphabet.FiniteAlphabet roundedMachine.tm :=
    MachineFiniteAlphabet.composeBits
      (f := matrix) (g := UniformTarget.construct P.copies hC) computation
      (MachineUniformRun.computation (q := q) P.copies hC) finiteAlphabet
      (MachineUniformRun.finiteAlphabet (q := q) P.copies hC)
  let base := fun input => SubdivisionTarget.subdivide (rounded input)
  let basePresentation := fun input => SubdivisionTarget.simpleBipartite (rounded input)
  let baseMachine := MachineSubdivisionCompose.translationComputableInPolyTime
    coordinates roundedMachine roundedTranslations
  have baseFinite : MachineFiniteAlphabet.FiniteAlphabet baseMachine.tm :=
    MachineSubdivisionCompose.finiteAlphabet roundedMachine
      (fun input => MachineSubdivisionCorrespondence.translations_involutive
        coordinates (rounded input) (roundedTranslations input)) roundedFinite
  let output := fun input => ProductPaddedOutput.output (base input)
    (basePresentation input) P.repetitions P.repetitions_pos
  let outputMachine := MachineProductRuntime.compose baseMachine basePresentation
    P.repetitions P.repetitions_pos
  have hqout : 2 ≤ q ^ P.repetitions :=
    hq.trans (Nat.le_self_pow P.repetitions_pos.ne' q)
  have hqoutpos : 0 < q ^ P.repetitions := by omega
  have baseValue (input : List Bool) :
      InstanceValue.value (base input) =
        1 - (1 - InstanceValue.value (matrix input)) / 4 := by
    dsimp [base, rounded]
    rw [SubdivisionTarget.value_eq _ hqpos,
      UniformTarget.value P.copies hC (matrix input) hqpos]
  have hτ : (0 : ℝ) < (P.pStar : ℝ) := by exact_mod_cast P.pStar_pos
  have hτsmall : (P.pStar : ℝ) ≤ 1 / 200 := by
    simpa only [ParameterSelection.OuterParameters.pStar, Rat.cast_div, Rat.cast_ofNat,
      Rat.cast_one]
      using ((Rat.cast_le (K := ℝ)).mpr P.reciprocal_small)
  have hτbudget : (P.pStar : ℝ) ≤ (P.epsilon0 : ℝ) / P.repetitions := by
    exact_mod_cast P.reciprocal_budget
  have hdbudget : (d : ℝ) ≤ (P.epsilon0 : ℝ) / P.repetitions := by
    exact_mod_cast hd
  have hε0 : (0 : ℝ) ≤ (P.epsilon0 : ℝ) := by
    exact_mod_cast P.epsilon0_pos.le
  have roundingError (input : List Bool) :
      |InstanceValue.value (base input) -
        (1 - (1 - InstanceValue.value (matrix input)) / 4)| ≤ (P.pStar : ℝ) / 4 := by
    rw [baseValue input, sub_self, abs_zero]
    positivity
  refine {
    alphabet := q ^ P.repetitions
    alphabetAtLeastTwo := hqout
    dimension := s * P.repetitions
    dimensionPositive := by
      have hpos := Nat.mul_pos (show 0 < s by omega) P.repetitions_pos
      omega
    coordinates := ProductPaddedOutput.finalCoordinates coordinates P.repetitions
    construct := output
    simpleBipartite := fun input => ProductPaddedOutput.simpleBipartite
      (base input) (basePresentation input) P.repetitions P.repetitions_pos
    translations := fun input => ProductPaddedOutput.output_translations
      (base input) (basePresentation input) coordinates
      (SubdivisionTarget.subdivide_translation coordinates (rounded input)
        (roundedTranslations input)) P.repetitions P.repetitions_pos
    computation := outputMachine
    finiteAlphabet := MachineProductRuntime.compose_finiteAlphabet
      baseMachine basePresentation P.repetitions P.repetitions_pos baseFinite
    completeness := ?_
    soundness := ?_
  }
  · intro input yes
    apply (InstanceValue.exists_rate_ge_iff (output input) hqoutpos (1 - ε)).mpr
    have hbase := FinishBounds.subdivision_completeness _ _ (d : ℝ) (P.pStar : ℝ)
      (complete input yes) (roundingError input)
    have hproduct := ProductPaddedOutput.output_completeness (base input)
      (basePresentation input) P.repetitions P.repetitions_pos
      (error := 1 - InstanceValue.value (base input)) (by linarith)
    exact FinishBounds.final_completeness _ _ (d : ℝ) (P.pStar : ℝ)
      (P.epsilon0 : ℝ) ε P.repetitions P.repetitions_pos hbase hproduct
      hdbudget hτbudget hε0 P.epsilon0_le
  · intro input no
    apply (InstanceValue.forall_rate_le_iff (output input) hqoutpos δ).mpr
    have hbase := FinishBounds.subdivision_soundness _ _ (P.pStar : ℝ)
      (sound input no) hτsmall (roundingError input)
    exact (ProductPaddedOutput.output_soundness (base input) (basePresentation input)
      P.repetitions P.repetitions_pos P.soundness_rate hbase).trans P.delta0_le

end
end UniqueGamesTheorem.FinishReduction

end OAI
end


