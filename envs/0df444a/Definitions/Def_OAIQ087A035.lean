-- Prove2me | Definitions.Def_OAIQ087A035
-- name    : OAIQ087A035
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T18:11:09.923971+00:00
-- url     : https://prove2.me/theorems/7f6f633e-0d10-4a0a-b436-e535ac92b9b3
-- title:
--   Definitions bundle OAIQ087A035 of the split of OpenAI, A Direct Proof of Optimal Max-Cut Hardness (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.OptimalMaxCut.main`, carved from OpenAI's openai/math development (OpenAI, *A Direct Proof of Optimal Max-Cut Hardness (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 48 declarations of OpenAI's Lean: 15 definitions and 33 theorems. The definitions and types are `OAI.MaxCutGames.Foundations.Complexity.PoweringMachineRuntime.beforeFinishExecution`, `OAI.MaxCutGames.Foundations.Complexity.PoweringMachineRuntime.computableInPolyTime`, `OAI.MaxCutGames.Foundations.Complexity.PoweringMachineRuntime.execution`, `OAI.MaxCutGames.Foundations.Complexity.PoweringMachineRuntime.finishExecution`, `OAI.MaxCutGames.Foundations.Complexity.PoweringPolynomialBudget.preTime`, `OAI.MaxCutGames.Foundations.Complexity.PoweringPolynomialBudget.time`, `OAI.MaxCutGames.Foundations.PCP.PreprocessingFinishRuntime.computableInPolyTime`, `OAI.MaxCutGames.Foundations.PCP.PreprocessingRuntime.tablePolynomialTime`, `OAI.MaxCutGames.Foundations.PCP.RoundComputation.tablePolynomialTime`, `OAI.MaxCutGames.FromMatrixGap.reduction`, `OAI.MaxCutGames.Outer.BinaryParityReduction.computation`, `OAI.MaxCutGames.Outer.BinaryParityReduction.formulaMachine`, `OAI.MaxCutGames.Outer.HastadSource.computation`, `OAI.MaxCutGames.Outer.HastadSource.gapMachine`, `OAI.MaxCutGames.Outer.HastadSource.roundMachine`.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: [`MaxCut_Encoding_BinaryParityReduction`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/MaxCut/Encoding/BinaryParityReduction.lean), [`MaxCut_Games_MatrixGap`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/MaxCut/Games/MatrixGap.lean), [`MaxCut_Games_PoweringPolynomialBudget`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/MaxCut/Games/PoweringPolynomialBudget.lean), [`MaxCut_Machines_MachineLazyTableRuntime`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/MaxCut/Machines/MachineLazyTableRuntime.lean), [`MaxCut_Machines_MachineTableIteration`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/MaxCut/Machines/MachineTableIteration.lean), [`MaxCut_Machines_PoweringMachineRuntime`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/MaxCut/Machines/PoweringMachineRuntime.lean), [`MaxCut_PCP_Hastad`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/MaxCut/PCP/Hastad.lean), [`MaxCut_PCP_RawInitialTables`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/MaxCut/PCP/RawInitialTables.lean), [`MaxCut_PCP_RoundComputation`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/MaxCut/PCP/RoundComputation.lean), [`MaxCut_PCP_TableIteration`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/MaxCut/PCP/TableIteration.lean).
--
--   **Imports.** It imports the bundles `OAIQ087A033` and `OAIQ087A034` of this split.
--
--   **Imported by** (directly, in this split): the proof of `OAI.MaxCutGames.theorem11`.
-- source:
--   OpenAI, A Direct Proof of Optimal Max-Cut Hardness (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-Direct-Proof-of-Optimal-Max-Cut-Hardness-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ087A033
import Definitions.Def_OAIQ087A034

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineLazyTableRuntime
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.PCP.RoundTables.instNonemptyFinDartsValTableLtNatOfNat _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Canonical polynomial-time computation of the executable lazy preprocessing map.
The raw machine's retained original input is physically drained by the checked
canonical-output wrapper before it reaches the standard `haltList` endpoint.
-/

/-! The actual padding, expander overlay, and lazy-loop stages composed into
one polynomial-time finite machine. The initial degree-replacement stage is
assembled separately. -/
namespace MaxCutGames.Foundations.PCP.PreprocessingFinishRuntime

open Turing MaxCutGames.Foundations.Complexity
open PreprocessingRegularTables

/-- Both stages supply complete executions, cleanup, and polynomial bounds;
the sequential composition includes the physical interstage bit transfer. -/
noncomputable def computableInPolyTime (H : PreprocessingTables.BaseTable)
    (d : Nat) (hd : 0 < d) :
    TM2ComputableInPolyTime (PortTables.inputBits (ports := d))
      (PortTables.inputBits (ports := 2 * (d + internalDegree))) (finish H d) := by
  change TM2ComputableInPolyTime _ _
    (fun input => PreprocessingStageMaps.lazy (d + internalDegree)
      (PreprocessingStageMaps.paddedOverlay H d input))
  exact MachineSequential.composeBits (MachinePaddedOverlayRuntime.computableInPolyTime H d hd)
    (MachineLazyTableRuntime.computableInPolyTime (d + internalDegree)
      (finish_degree_positive d hd))

theorem finite_alphabet (H : PreprocessingTables.BaseTable) (d : Nat) (hd : 0 < d) :
    MachineFiniteAlphabet.FiniteAlphabet (computableInPolyTime H d hd).tm :=
  MachineFiniteAlphabet.composeBits
    (MachinePaddedOverlayRuntime.computableInPolyTime H d hd)
    (MachineLazyTableRuntime.computableInPolyTime (d + internalDegree)
      (finish_degree_positive d hd))
    (MachinePaddedOverlayRuntime.finite_alphabet H d hd)
    (MachineLazyTableRuntime.finite_alphabet (d + internalDegree)
      (finish_degree_positive d hd))

end MaxCutGames.Foundations.PCP.PreprocessingFinishRuntime

/-! The complete actual preprocessing machine, including degree replacement,
vertex padding, explicit expander construction, overlay, and lazy edges. -/
namespace MaxCutGames.Foundations.PCP.PreprocessingRuntime
open Turing MaxCutGames.Foundations.Complexity
open PreprocessingRegularTables

noncomputable def tablePolynomialTime (H : PreprocessingTables.BaseTable) :
    TM2ComputableInPolyTime GraphTables.tableBits
      (PortTables.inputBits (ports := PreprocessingTables.degree))
      (PreprocessingTables.output H) := by
  change TM2ComputableInPolyTime GraphTables.tableBits
    (PortTables.inputBits (ports := 2 * ((internalDegree + 1) + internalDegree)))
    (fun t => PreprocessingFinishRuntime.finish H (internalDegree + 1)
      (PreprocessingStageMaps.regular H t))
  exact MachineSequential.composeBits
    (MachineRegularTableRuntime.computableInPolyTime H)
    (PreprocessingFinishRuntime.computableInPolyTime H (internalDegree + 1)
      (Nat.succ_pos internalDegree))

theorem finiteAlphabet (H : PreprocessingTables.BaseTable) :
    MachineFiniteAlphabet.FiniteAlphabet (tablePolynomialTime H).tm :=
  MachineFiniteAlphabet.composeBits
    (MachineRegularTableRuntime.computableInPolyTime H)
    (PreprocessingFinishRuntime.computableInPolyTime H (internalDegree + 1)
      (Nat.succ_pos internalDegree))
    (MachineRegularTableRuntime.finite_alphabet H)
    (PreprocessingFinishRuntime.finite_alphabet H (internalDegree + 1)
      (Nat.succ_pos internalDegree))

end MaxCutGames.Foundations.PCP.PreprocessingRuntime

/-!
An actual logarithmic-round counter. Unary input is stripped to a raw tally;
each positive round emits one tally and halves the remaining input by pairing
symbols. The zero input emits one round explicitly. All tapes except the
canonical output are empty at termination.
-/

/-! A fixed Boolean-stack program prepending the logarithmic round count to
a graph table. It copies the original word, adds its two unary header values,
runs the actual logarithm machine, then emits the counter and original word. -/

/-! Actual archive-copy and unary-header addition before the embedded logarithm
machine. The two header values stay on tapes; they never enter finite control. -/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_RawInitialTables
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.MaxCutGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.ActualSource.sourceIndexNonempty _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit structural numberings of the raw 3SAT incidence graph. Unused
declared variable names are retained; their unary input header pays for them.
The graph has one dummy vertex and one tautological loop, even for an empty
formula. No input-dependent choice of a finite enumeration is made. -/

/-!
A stable type of finite graphs over one fixed alphabet. Vertex and dart types,
their finite enumeration and equality data, and the actual constraint graph
are stored together. The gap is computed from that graph's actual finite
labeling minimum. This mathematical bundle is not a serialized machine input;
no finite numbering is chosen here.
-/

/-! The concrete numbered amplification round, with one fixed base expander.
Every intermediate is an actual stored table, with explicit finite coordinates.
The running-time certificate is a separate theorem about these same functions. -/

namespace MaxCutGames.Foundations.PCP.RoundTables

theorem one_le_size_mul_gap (input : Input) (unsat : ¬ Satisfiable input) :
    1 ≤ (size input : ℝ) * gap input := by
  have h := (GraphTables.semantics input.val).inverse_card_le_gap_of_unsatisfiable unsat
  have hp : (0 : ℝ) < input.val.darts := Nat.cast_pos.mpr input.property
  simp only [Fintype.card_fin] at h
  have hd := (div_le_iff₀ hp).mp h
  have hsize : (input.val.darts : ℝ) ≤ (size input : ℝ) := by
    exact_mod_cast (Nat.le_add_left input.val.darts input.val.vertices)
  exact (show 1 ≤ (input.val.darts : ℝ) * gap input by
    simpa only [gap, mul_comm] using hd).trans
    (mul_le_mul_of_nonneg_right hsize (gap_nonnegative input))

end MaxCutGames.Foundations.PCP.RoundTables

/-!
The finite iteration and size arithmetic for an amplification transformation.
The transformation itself must be supplied by the actual graph construction;
these theorems do not assert that such a transformation exists.  In particular,
the polynomial size estimate below is not a machine runtime certificate.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_TableIteration
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.MaxCutGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.ActualSource.sourceIndexNonempty _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Iteration of the concrete stored-table round, with the original formula's
actual initial graph size controlling the number of rounds. -/

namespace MaxCutGames.Foundations.PCP.TableIteration

open RoundTables
open Target Complexity

theorem output_completeness (H : BaseTable) (F : Formula) (sat : F.Satisfiable) :
    Satisfiable (output H F) :=
  run_completeness H _ _ ((initial_satisfiable_iff F).mpr sat)

theorem gapMap_completeness (H : BaseTable) (F : Formula) (sat : F.Satisfiable) :
    (gapMap H F).Satisfiable := by
  apply (FinalTableFormula.satisfiable_iff (outputTable H F)).mpr
  rw [← output_val]
  exact output_completeness H F sat

end MaxCutGames.Foundations.PCP.TableIteration

/-! Exact transport of powering through a change of ports. The target's actual
address selector is pulled back, so no compatibility of enumeration orders or
consistency restriction on raw padded labels is needed. -/

/-! Gap amplification for the actual numbered table round. The fixed base
expander is the only supplied construction datum with a spectral certificate. -/

namespace MaxCutGames.Foundations.PCP.RoundTableGap

open RoundTables
open PoweringWalks SpectralReturn

variable (H : BaseTable)
  (certificate : SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))

include certificate

theorem powered_count_gap (input : Input)
    (labeling : Fin (powered H input.val).vertices → Fin alphabet) :
    RoundGap.poweredLower (gap input) * ((powered H input.val).darts : ℝ) ≤
      ((GenericGraphTables.semantics (powered H input.val)).rejectionCount labeling : ℝ) := by
  let old := PreprocessingOverlayTables.overlay
    (PreprocessingTables.padded H input.val) (PreprocessingTables.overlayFamily H input.val)
  have hd : 0 < (PreprocessingRegularTables.internalDegree + 1) +
      PreprocessingRegularTables.internalDegree := by omega
  let : Nonempty (Fin ((PreprocessingRegularTables.internalDegree + 1) +
      PreprocessingRegularTables.internalDegree)) := ⟨⟨0, hd⟩⟩
  have spectral : SpectralCertificate (lazyGraph (PortTables.portGraph old)) (31 / 32 : ℝ) :=
    LazySpectral.lazy_certificate_31_32 (PortTables.portGraph old)
      (PreprocessingGuarantees.overlay_certificate H certificate input.val)
  have lower := PreprocessingGuarantees.gap_transfer_real H certificate input.val input.property
    (gap input) (gap_nonnegative input)
    (by simpa only [Fintype.card_fin] using
      ((GraphTables.semantics input.val).le_gap_iff (gap input)).mp le_rfl)
  have hs : (0 : ℝ) < Preprocessing.sizeFactor := Nat.cast_pos.mpr Preprocessing.sizeFactor_positive
  have hn : walkParameter = 2 * PoweringSoundness.center 64 FinalConstants.windowHalf :=
    walkParameter_eq
  have bound := PoweringPortReindex.lazy_table_uniform_count_gap_at old
    (PreprocessingTables.vertices_positive input.val) hd (31 / 32) spectral
    FinalConstants.windowHalf FinalConstants.windowHalf_positive walkParameter hn
    (gap input / Preprocessing.sizeFactor) (div_nonneg (gap_nonnegative input) hs.le)
    lower labeling
  have hw : walkParameter + 1 = FinalConstants.walkLength := by
    rw [walkParameter_eq]
    rfl
  simpa only [RoundGap.poweredLower, PoweringFinalConstants.card_alphabet,
    hw, FinalConstants.cap, powered, PreprocessingTables.preprocess, old] using! bound

theorem build_count_gap (input : Input)
    (labeling : Fin (build H input.val).vertices → GraphTables.Label) :
    min (2 * gap input) FinalConstants.cap * ((build H input.val).darts : ℝ) ≤
      ((GraphTables.semantics (build H input.val)).rejectionCount labeling : ℝ) := by
  have h := AlphabetTableBounds.gap_transfer_real alphabet_positive (powered H input.val)
    (RoundGap.poweredLower (gap input))
    (RoundGap.poweredLower_nonnegative (gap input) (gap_nonnegative input))
    (powered_count_gap H certificate input) labeling
  have scalar : min (2 * gap input) FinalConstants.cap ≤
      RoundGap.poweredLower (gap input) / 12288 := by
    simpa only [RoundGap.poweredLower, FinalConstants.cap, FinalConstants.walkLength,
      PoweringFinalConstants.center_eq] using
      PoweringFinalConstants.composed_scaled_gap (gap input) (gap_nonnegative input)
  exact (mul_le_mul_of_nonneg_right scalar (Nat.cast_nonneg _)).trans h

theorem step_gap (input : Input) :
    min (2 * gap input) FinalConstants.cap ≤ gap (step H input) := by
  apply ((GraphTables.semantics (step H input).val).le_gap_iff _).mpr
  change ∀ labeling : Fin (build H input.val).vertices → GraphTables.Label,
    min (2 * gap input) FinalConstants.cap *
        (Fintype.card (Fin (build H input.val).darts) : ℝ) ≤
      ((GraphTables.semantics (build H input.val)).rejectionCount labeling : ℝ)
  simpa only [Fintype.card_fin, step] using build_count_gap H certificate input

end MaxCutGames.Foundations.PCP.RoundTableGap

/-! Both semantic implications for the actual stored-table 3SAT gap map.
The positive clause gap follows from the full actual repeated transformation.
The full map's polynomial-time machine is certified separately. -/

namespace MaxCutGames.Foundations.PCP.TableGapReduction

open RoundTables TableIteration SpectralReturn Target

variable (H : BaseTable)
  (certificate : SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))

include certificate

theorem output_gap (F : Formula) (unsat : ¬ F.Satisfiable) :
    FinalConstants.cap ≤ gap (TableIteration.output H F) := by
  have hu : ¬ Satisfiable (initial F) := fun sat => unsat ((initial_satisfiable_iff F).mp sat)
  exact AmplificationIteration.run_reaches_cap (step H) gap FinalConstants.cap
    FinalConstants.cap_positive.le FinalConstants.cap_le_one (RoundTableGap.step_gap H certificate)
    (size (initial F)) (initial F) (gap_nonnegative (initial F))
    (one_le_size_mul_gap (initial F) hu)

theorem output_count_gap (F : Formula) (unsat : ¬ F.Satisfiable)
    (labeling : Fin (outputTable H F).vertices → GraphTables.Label) :
    (outputTable H F).darts ≤ FinalConstants.walkLength *
      (GraphTables.semantics (outputTable H F)).rejectionCount labeling := by
  have hp := output_darts_positive H F
  let : Nonempty (Fin (outputTable H F).darts) := ⟨⟨0, hp⟩⟩
  have bound := output_gap H certificate F unsat
  change FinalConstants.cap ≤ (GraphTables.semantics (TableIteration.output H F).val).gap at bound
  rw [output_val] at bound
  have count := ((GraphTables.semantics (outputTable H F)).le_gap_iff FinalConstants.cap).mp bound labeling
  simp only [Fintype.card_fin] at count
  have ht : (0 : ℝ) < FinalConstants.walkLength := Nat.cast_pos.mpr FinalConstants.walkLength_positive
  have divided : ((outputTable H F).darts : ℝ) / FinalConstants.walkLength ≤
      ((GraphTables.semantics (outputTable H F)).rejectionCount labeling : ℝ) := by
    simpa only [FinalConstants.cap, one_div_mul_eq_div] using count
  have multiplied := (div_le_iff₀ ht).mp divided
  exact_mod_cast (show ((outputTable H F).darts : ℝ) ≤ (FinalConstants.walkLength : ℝ) *
      ((GraphTables.semantics (outputTable H F)).rejectionCount labeling : ℝ) by
    simpa only [mul_comm] using multiplied)

theorem gapMap_clauseGap (F : Formula) (unsat : ¬ F.Satisfiable) :
    Hastad.SourceGap.ClauseGap (gapMap H F) PCPIteration.finalClauseGap :=
  FinalTableFormula.clauseGap (outputTable H F) (output_darts_positive H F)
    (output_count_gap H certificate F unsat)

end MaxCutGames.Foundations.PCP.TableGapReduction

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineTableIteration
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual polynomial-time iteration of the concrete graph-table round. A
certificate for that one body is the only supplied machine input. Counter
preparation, repeated calls, tape handoffs, and final cleanup are all proved. -/

namespace MaxCutGames.Foundations.Complexity.TableIterationFiniteAlphabet

open PCP MachineFiniteAlphabet

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

end MaxCutGames.Foundations.Complexity.TableIterationFiniteAlphabet

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_PoweringPolynomialBudget
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Complexity.PoweringPolynomialBudget

open PCP

/-- Replace the vertex count by the input length in the actual setup/loop bound. -/
noncomputable def preTime (d n : Nat) : Polynomial Nat :=
  (Polynomial.C 3 * Polynomial.X + Polynomial.C 5) +
    (Polynomial.X * (vertexTime d n + Polynomial.C 2) + Polynomial.C 1)

@[simp] theorem preTime_eval (d n inputLength : Nat) :
    (preTime d n).eval inputLength = preBudget d n inputLength inputLength := by
  simp only [preTime, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, vertexTime_eval, preBudget]

/-- The explicit final polynomial. All coefficients depend only on the fixed
degree/radius and the chosen finite machine's push bound and tape count. -/
noncomputable def time (d n pushBound tapeCount : Nat) : Polynomial Nat :=
  preTime d n +
    (Polynomial.C 2 *
        (Polynomial.X + Polynomial.C (PoweringTableLayout.blockSize d n) * Polynomial.X) +
      Polynomial.C 6 + Polynomial.C tapeCount *
        (Polynomial.X + preTime d n * Polynomial.C pushBound + Polynomial.X +
          Polynomial.C (PoweringTableLayout.blockSize d n) * Polynomial.X + Polynomial.C 3))

@[simp] theorem time_eval (d n pushBound tapeCount inputLength : Nat) :
    (time d n pushBound tapeCount).eval inputLength =
      totalBudget d n pushBound tapeCount inputLength inputLength := by
  simp only [time, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, preTime_eval, totalBudget, finishBudget]

/-- The actual vertex count may be strictly smaller than the input length. -/
theorem totalBudget_le_time (d n pushBound tapeCount vertices inputLength : Nat)
    (hvertices : vertices ≤ inputLength) :
    totalBudget d n pushBound tapeCount vertices inputLength ≤
      (time d n pushBound tapeCount).eval inputLength := by
  rw [time_eval]
  exact totalBudget_mono_vertices d n pushBound tapeCount inputLength hvertices

/-- Numerical bounds on two actual phases can use the same fixed polynomial. -/
theorem execution_budget_le_time (d n pushBound tapeCount vertices inputLength : Nat)
    (hvertices : vertices ≤ inputLength) {preSteps finishSteps : Nat}
    (hpre : preSteps ≤ preBudget d n vertices inputLength)
    (hfinish : finishSteps ≤ finishBudget d n pushBound tapeCount vertices inputLength
      (preBudget d n vertices inputLength)) :
    preSteps + finishSteps ≤ (time d n pushBound tapeCount).eval inputLength := by
  calc
    preSteps + finishSteps ≤ totalBudget d n pushBound tapeCount vertices inputLength := by
      unfold totalBudget
      exact Nat.add_le_add hpre hfinish
    _ ≤ (time d n pushBound tapeCount).eval inputLength :=
      totalBudget_le_time d n pushBound tapeCount vertices inputLength hvertices

end MaxCutGames.Foundations.Complexity.PoweringPolynomialBudget

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_PoweringMachineRuntime
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Complete execution of the one fixed powering machine on the actual
port-table input and generic graph-table output encodings. The varying vertex
count remains on unary tapes throughout. -/

namespace MaxCutGames.Foundations.Complexity.PoweringMachineRuntime

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
    have hi := @List.map_id ((machine d n).Γ (machine d n).k₀)
      (PortTables.tableBits graph)
    have ho := @List.map_id ((machine d n).Γ (machine d n).k₁)
      (PoweringTables.outputBits graph n)
    simpa only [hi, ho, PortTables.inputBits] using bounded

/-- Every work tape, as well as the input/output tapes, has a finite alphabet. -/
theorem computableInPolyTime_finite_alphabet (d n : Nat) :
    ∀ k, Finite ((computableInPolyTime d n).tm.Γ k) := by
  intro k
  change Finite Bool
  infer_instance

end MaxCutGames.Foundations.Complexity.PoweringMachineRuntime

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_RoundComputation
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Actual sequential finite-machine composition for the concrete numbered round.
The initial composition lemma isolates the preprocessing and powering execution
certificates with their shared bit codecs. The final endpoint supplies the
checked powering and alphabet machines, leaving only preprocessing explicit.
-/

namespace MaxCutGames.Foundations.PCP.RoundComputation

open Turing
open MaxCutGames.Foundations.Complexity

/-- Powering and alphabet reduction now use their constructed finite machines.
The only remaining input is an execution certificate for preprocessing. -/
noncomputable def tablePolynomialTime (H : RoundTables.BaseTable)
    (preprocessing : PreprocessingCertificate H) :
    TM2ComputableInPolyTime GraphTables.tableBits GraphTables.tableBits
      (RoundTables.build H) :=
  tablePolynomialTimeOfCertificates H preprocessing
    (PoweringMachineRuntime.computableInPolyTime PreprocessingTables.degree
      RoundTables.walkParameter)

/-- The same certificate has finite work-tape alphabets whenever the supplied
preprocessing machine does; both later stages supply their own proof. -/
theorem tablePolynomialTime_finite_alphabet (H : RoundTables.BaseTable)
    (preprocessing : PreprocessingCertificate H)
    (hpreprocessing : MachineFiniteAlphabet.FiniteAlphabet preprocessing.tm) :
    MachineFiniteAlphabet.FiniteAlphabet
      (tablePolynomialTime H preprocessing).tm :=
  finiteAlphabet H preprocessing
    (PoweringMachineRuntime.computableInPolyTime PreprocessingTables.degree
      RoundTables.walkParameter) hpreprocessing
    (PoweringMachineRuntime.computableInPolyTime_finite_alphabet
      PreprocessingTables.degree RoundTables.walkParameter)

end MaxCutGames.Foundations.PCP.RoundComputation

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_Hastad
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Outer.HastadSource

open MaxCutGames.Foundations Target Complexity PCP
open MaxCutGames.Reduction ActualSource
open MachineFiniteAlphabet

theorem complete (H : RoundTables.BaseTable) (ξ : ℚ) (hξ : 0 < ξ)
    (F : Formula) (hF : F.Satisfiable) :
    ∃ bits, 1 - ξ ≤ success (output H ξ hξ F) bits := by
  exact Hastad.SourceGap.forError_complete PCPIteration.finalClauseGap ξ
    PCPIteration.finalClauseGap_positive TableGapReduction.finalClauseGap_le_one hξ
    (TableIteration.gapMap H F) (TableIteration.gapMap_completeness H F hF)

theorem sound (H : RoundTables.BaseTable)
    (certificate : SpectralReturn.SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))
    (ξ : ℚ) (hξ : 0 < ξ) (F : Formula) (hF : ¬ F.Satisfiable)
    (bits : Fin (output H ξ hξ F).«variables» → Bool) :
    success (output H ξ hξ F) bits ≤ (1 + ξ) / 2 := by
  exact Hastad.SourceGap.forError_sound PCPIteration.finalClauseGap ξ
    PCPIteration.finalClauseGap_positive TableGapReduction.finalClauseGap_le_one hξ
    (TableIteration.gapMap H F) (TableGapReduction.gapMap_clauseGap H certificate F hF) bits

noncomputable def roundMachine (H : RoundTables.BaseTable) :=
  RoundComputation.tablePolynomialTime H (PreprocessingRuntime.tablePolynomialTime H)

theorem roundMachine_finite (H : RoundTables.BaseTable) :
    FiniteAlphabet (roundMachine H).tm :=
  RoundComputation.tablePolynomialTime_finite_alphabet H
    (PreprocessingRuntime.tablePolynomialTime H) (PreprocessingRuntime.finiteAlphabet H)

noncomputable def gapMachine (H : RoundTables.BaseTable) :
    Turing.TM2ComputableInPolyTime formulaBits Hastad.SourceGeneratorContract.inputEncoding
      (gapInput H) where
  toTM2ComputableAux :=
    (MachineTableIteration.gapMapCertificate H (roundMachine H)).toTM2ComputableAux
  time := (MachineTableIteration.gapMapCertificate H (roundMachine H)).time
  outputsFun F := (MachineTableIteration.gapMapCertificate H (roundMachine H)).outputsFun F

noncomputable def computation (H : RoundTables.BaseTable) (ξ : ℚ) (hξ : 0 < ξ) :
    Turing.TM2ComputableInPolyTime formulaBits SourceEncoding.inputBits (output H ξ hξ) :=
  MachineSequential.composeBits (f := gapInput H) (g := sourceMap ξ hξ)
    (gapMachine H) (sourceMachine ξ hξ)

theorem finiteAlphabet (H : RoundTables.BaseTable) (ξ : ℚ) (hξ : 0 < ξ) :
    FiniteAlphabet (computation H ξ hξ).tm :=
  MachineFiniteAlphabet.composeBits (gapMachine H) (sourceMachine ξ hξ)
    (TableIterationFiniteAlphabet.gapMap H (roundMachine H) (roundMachine_finite H))
    (Hastad.SourceGenerator.forError_finite_work_alphabets PCPIteration.finalClauseGap ξ
      PCPIteration.finalClauseGap_positive TableGapReduction.finalClauseGap_le_one hξ)

end MaxCutGames.Outer.HastadSource

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_BinaryParityReduction
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Outer.BinaryParityReduction

open MaxCutGames.Foundations Target Complexity PCP
open MaxCutGames.Reduction ActualSource
open MachineFiniteAlphabet

noncomputable section

def formulaMachine (H : RoundTables.BaseTable) (ξ : ℚ) (hξ : 0 < ξ) :
    Turing.TM2ComputableInPolyTime formulaBits SourceEncoding.inputBits
      (SourceIncidence.input H ξ hξ) :=
  MachineSequential.composeBits
    (f := HastadSource.output H ξ hξ) (g := Clone100.clonedInput)
    (HastadSource.computation H ξ hξ)
    Explicit.MachineClone100.computation

theorem formulaMachine_finite (H : RoundTables.BaseTable) (ξ : ℚ) (hξ : 0 < ξ) :
    FiniteAlphabet (formulaMachine H ξ hξ).tm :=
  MachineFiniteAlphabet.composeBits
    (f := HastadSource.output H ξ hξ) (g := Clone100.clonedInput)
    (HastadSource.computation H ξ hξ)
    Explicit.MachineClone100.computation
    (HastadSource.finiteAlphabet H ξ hξ) Explicit.MachineClone100.finiteAlphabet

def computation (H : RoundTables.BaseTable) (ξ : ℚ) (hξ : 0 < ξ) :
    Turing.TM2ComputableInPolyTime (id : List Bool → List Bool) SourceEncoding.inputBits
      (output H ξ hξ) :=
  MachineSequential.composeBits
    (f := BinaryLanguage.totalRename) (g := SourceIncidence.input H ξ hξ)
    BinaryInputReduction.computation (formulaMachine H ξ hξ)

theorem computation_finite (H : RoundTables.BaseTable) (ξ : ℚ) (hξ : 0 < ξ) :
    FiniteAlphabet (computation H ξ hξ).tm :=
  MachineFiniteAlphabet.composeBits
    (f := BinaryLanguage.totalRename) (g := SourceIncidence.input H ξ hξ)
    BinaryInputReduction.computation (formulaMachine H ξ hξ)
    BinaryInputReduction.computation_finiteAlphabet (formulaMachine_finite H ξ hξ)

theorem complete (H : RoundTables.BaseTable) (ξ : ℚ) (hξ : 0 < ξ)
    (word : List Bool) (yes : BinaryLanguage.language word) :
    ∃ a, 1 - ξ ≤ Clone100.success (output H ξ hξ word).equations a := by
  obtain ⟨a, ha⟩ := HastadSource.complete H ξ hξ (BinaryLanguage.totalRename word)
    ((BinaryLanguage.totalRename_satisfiable_iff word).mpr yes)
  refine ⟨Clone100.lift a, ?_⟩
  change 1 - ξ ≤ Clone100.success
    (Clone100.clonedInput (HastadSource.output H ξ hξ (BinaryLanguage.totalRename word))).equations
      (Clone100.lift a)
  rw [Clone100.completeness]
  exact ha

theorem sound (H : RoundTables.BaseTable)
    (certificate : SpectralReturn.SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))
    (ξ : ℚ) (hξ : 0 < ξ) (small : ξ < 1 / 100)
    (word : List Bool) (no : ¬ BinaryLanguage.language word)
    (a : Fin (output H ξ hξ word).«variables» → Bool) :
    Clone100.success (output H ξ hξ word).equations a ≤ 4 / 5 := by
  have hno : ¬ (BinaryLanguage.totalRename word).Satisfiable :=
    fun h => no ((BinaryLanguage.totalRename_satisfiable_iff word).mp h)
  exact Clone100.soundness_four_fifths
    (HastadSource.output H ξ hξ (BinaryLanguage.totalRename word)) ξ small
    (HastadSource.sound H certificate ξ hξ (BinaryLanguage.totalRename word) hno) a

theorem exists_reduction (ξ : ℚ) (positive : 0 < ξ) (small : ξ < 1 / 100) :
    Nonempty (Reduction ξ) := by
  obtain ⟨H, certificate⟩ := ExpanderTables.exists_base_table
  exact ⟨⟨output H ξ positive,
    (fun word => SourceIncidence.source_distinct H ξ positive (BinaryLanguage.totalRename word)),
    complete H ξ positive, sound H certificate ξ positive small,
    computation H ξ positive, computation_finite H ξ positive⟩⟩

end
end MaxCutGames.Outer.BinaryParityReduction

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_MatrixGap
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.FromMatrixGap

open MaxCutGames.Foundations Target
open MaxCutGames.Foundations.Complexity
open MaxCutGames.Integration
open MaxCutGames.Reduction
open Explicit

noncomputable section

/-- Choose the parity error only after the matrix tuple length is fixed, then
compose the actual raw-input, matrix-test, and final graph machines. -/
def reduction {ε δ : ℝ} (P : ParameterSelection.OuterParameters ε δ)
    (M : Decoder.MatrixGap.Parameters P.pStar) :
    MachineOutputContract.BinaryGapReduction ε δ := by
  classical
  have hk : 0 < M.k := M.k_pos
  let ξ := Classical.choose (P.exists_parity_error M.k hk)
  have hξspec := Classical.choose_spec (P.exists_parity_error M.k hk)
  have hξ : 0 < ξ := hξspec.1
  have hξsmall : ξ < 1 / 100 := hξspec.2.1
  have hξbudget : ξ < P.epsilon0 / (2 * M.k * P.repetitions) := hξspec.2.2
  let R := Classical.choice (Outer.BinaryParityReduction.exists_reduction ξ hξ hξsmall)
  let matrix := fun input => MachineSingleOrbitBridge.output M.k M.T (R.reduce input)
  let matrixMachine := MachineSequential.composeBits
    (f := R.reduce) (g := MachineSingleOrbitBridge.output M.k M.T)
    R.computation (MachineSingleOrbitBridge.computableInPolyTime M.k M.T)
  have matrixFinite : MachineFiniteAlphabet.FiniteAlphabet matrixMachine.tm :=
    MachineFiniteAlphabet.composeBits
      (f := R.reduce) (g := MachineSingleOrbitBridge.output M.k M.T)
      R.computation (MachineSingleOrbitBridge.computableInPolyTime M.k M.T)
      R.finiteAlphabet (MachineSingleOrbitBridge.workAlphabetFinite M.k M.T)
  have hq : 2 ≤ 2 ^ M.s := Nat.le_self_pow (by have h := M.s_pos; omega) 2
  refine FinishReduction.of_matrix_reduction P hq M.s_pos
    (Encoding.alphabetEquiv M.s).symm matrix ?_ matrixMachine matrixFinite
    ((M.k : ℚ) * ξ + P.pStar / 2)
    (P.matrix_error_budget M.k hk ξ hξbudget.le) ?_ ?_
  · intro input
    exact M.output_translations (Outer.HastadSource.asSource (R.reduce input))
  · intro input yes
    obtain ⟨assignment, hfailure⟩ :=
      Outer.BinaryParityReduction.failure_completeness R input yes
    have h := M.completeness (Outer.HastadSource.asSource (R.reduce input))
      assignment ξ hfailure
    simpa only [matrix, MachineSingleOrbitBridge.output,
      MachineSingleOrbitBridge.SingleAddress.tableOutput, Outer.HastadSource.asSource,
      Rat.cast_add, Rat.cast_mul, Rat.cast_natCast,
      Rat.cast_div, Rat.cast_ofNat] using h
  · intro input no
    exact M.sound (Outer.HastadSource.asSource (R.reduce input))
      (R.distinct input) (Outer.BinaryParityReduction.parity_soundness R input no)

end
end MaxCutGames.FromMatrixGap

/-!
# Size of a binary row kernel

An `r`-row linear constraint on `ℓ` binary coordinates leaves a kernel with at
least `2^(ℓ-r)` elements.  This does not require independent constraint rows.
The exponent uses natural subtraction, so the assertion also covers `r > ℓ`.
The argument is rank--nullity followed by the exact finite-field cardinality
formula; it does not use any inverse theorem or rank-level inequality.
-/

end OAI
end


