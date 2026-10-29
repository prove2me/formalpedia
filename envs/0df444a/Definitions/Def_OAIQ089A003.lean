-- Prove2me | Definitions.Def_OAIQ089A003
-- name    : OAIQ089A003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T02:54:54.889988+00:00
-- url     : https://prove2.me/theorems/53e36dd7-39af-455b-b68b-b084cb6893e6
-- title:
--   Definitions bundle OAIQ089A003 of the split of OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ContingencyTables.boundedSampling`, `OAI.ContingencyTables.counting` and `OAI.ContingencyTables.exactSampling`, carved from OpenAI's openai/math development (OpenAI, *Sampling and counting contingency tables with arbitrary margins (result family 115)*, OpenAI Math Release, September 24, 2026, result family 115, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1002 declarations of OpenAI's Lean: 907 definitions, 2 instances and 93 theorems. The definitions and types are `OAI.ContingencyTables.BinIntervalProgram.drawRealizer`, `OAI.ContingencyTables.BinIntervalProgram.endpointRealizer`, `OAI.ContingencyTables.BinIntervalProgram.intervalSizeRealizer`, `OAI.ContingencyTables.BinIntervalProgram.nextRealizer`, `OAI.ContingencyTables.BinPopulationProgram.data`, `OAI.ContingencyTables.BinPopulationProgram.denominator`, `OAI.ContingencyTables.BinPopulationProgram.denominatorRealizer`, `OAI.ContingencyTables.BinPopulationProgram.factorNumerator`, `OAI.ContingencyTables.BinPopulationProgram.factorNumeratorRealizer`, `OAI.ContingencyTables.BinPopulationProgram.numerator`, `OAI.ContingencyTables.BinPopulationProgram.numeratorRealizer`, `OAI.ContingencyTables.BinPopulationProgram.output`, `OAI.ContingencyTables.BinPopulationProgram.outputRealizer`, `OAI.ContingencyTables.BinVectorProgram.Frame`, `OAI.ContingencyTables.BinVectorProgram.Input`, `OAI.ContingencyTables.BinVectorProgram.activeWidth`, `OAI.ContingencyTables.BinVectorProgram.activeWidthRealizer`, `OAI.ContingencyTables.BinVectorProgram.coordinate`, `OAI.ContingencyTables.BinVectorProgram.coordinateRealizer`, `OAI.ContingencyTables.BinVectorProgram.indices`, `OAI.ContingencyTables.BinVectorProgram.indicesRealizer`, `OAI.ContingencyTables.BinVectorProgram.item`, `OAI.ContingencyTables.BinVectorProgram.itemRealizer`, `OAI.ContingencyTables.BinVectorProgram.output`, `OAI.ContingencyTables.BinVectorProgram.outputRealizer`, `OAI.ContingencyTables.BinVectorProgram.reservedWidth`, `OAI.ContingencyTables.BinVectorProgram.reservedWidthRealizer`, `OAI.ContingencyTables.BinVectorProgram.widths`, `OAI.ContingencyTables.BinVectorProgram.widthsRealizer`, `OAI.ContingencyTables.BinaryContraction.AdditionProperty`, `OAI.ContingencyTables.BinaryContraction.OmissionProperty`, `OAI.ContingencyTables.BinaryPowerPrograms.powerRealizer`, `OAI.ContingencyTables.BinaryPowerPrograms.setupRealizer`, `OAI.ContingencyTables.BinaryPowerPrograms.singleton`, `OAI.ContingencyTables.BinarySearchProgram.State`, `OAI.ContingencyTables.BinarySearchProgram.advance`, `OAI.ContingencyTables.BinarySearchProgram.advanceRealizer`, `OAI.ContingencyTables.BinarySearchProgram.execute`, `OAI.ContingencyTables.BinarySearchProgram.executeRealizer`, `OAI.ContingencyTables.BinarySearchProgram.midpointRealizer` and 867 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `ContingencyTables_Counting_CompanionAnnealing`, `ContingencyTables_Counting_CompanionArithmeticProposal`, `ContingencyTables_Counting_CompanionArithmeticStep`, `ContingencyTables_Counting_CompanionBooleanPhase`, `ContingencyTables_Counting_CompanionBoundedWalkProgram`, `ContingencyTables_Counting_CompanionCellCatalogProgram`, `ContingencyTables_Counting_CompanionChainValidator`, `ContingencyTables_Counting_CompanionComputedProposal`, `ContingencyTables_Counting_CompanionEstimatorAmplification`, `ContingencyTables_Counting_CompanionEvaluatedWeightProgram`, `ContingencyTables_Counting_CompanionFactorialApplication`, `ContingencyTables_Counting_CompanionMetropolisProgram`, `ContingencyTables_Counting_CompanionMetropolisWordProgram`, `ContingencyTables_Counting_CompanionMultiplierMatrixProgram`, `ContingencyTables_Counting_CompanionNeighborProgram`, `ContingencyTables_Counting_CompanionPhaseCounts`, `ContingencyTables_Counting_CompanionStateMultiplierProgram`, `ContingencyTables_Counting_CompanionWeightOracle`, `ContingencyTables_Dense_CheegerCoarea`, `ContingencyTables_Dense_DenseAxisProgram`, `ContingencyTables_Dense_DenseAxisWordProgram`, `ContingencyTables_Dense_DenseBooleanWalkProgram`, `ContingencyTables_Dense_DenseCanonicalProgram`, `ContingencyTables_Dense_DenseCompletionProgram`, `ContingencyTables_Dense_DenseDrawProgram`, `ContingencyTables_Dense_DenseExponentListProgram`, `ContingencyTables_Dense_DenseExponentProgram`, `ContingencyTables_Dense_DenseFlatExponentProgram`, `ContingencyTables_Dense_DenseIntegerProgram`, `ContingencyTables_Dense_DenseMatrixLayoutProgram`, `ContingencyTables_Dense_DenseNormalizeProgram`, `ContingencyTables_Dense_DenseOffsetWidths`, `ContingencyTables_Dense_DenseReservedWord`, `ContingencyTables_Dense_DenseScaleCellProgram`, `ContingencyTables_Dense_DenseSwapProgram`, `ContingencyTables_Dense_DenseTrialProgram`, `ContingencyTables_Dense_DenseWordProgram`, `ContingencyTables_Machines_BinIntervalProgram`, `ContingencyTables_Machines_BinPopulationProgram`, `ContingencyTables_Machines_BinVectorProgram`, `ContingencyTables_Machines_BinaryContraction`, `ContingencyTables_Machines_BinaryPowerProgram`, `ContingencyTables_Machines_BinarySearchProgram`, `ContingencyTables_Machines_BooleanChunkProgram`, `ContingencyTables_Machines_BoundedComplementProgram`, `ContingencyTables_Machines_BoundedPowerProgram`, `ContingencyTables_Machines_CanonicalInitialEncoding`, `ContingencyTables_Machines_CellLowerTestProgram`, `ContingencyTables_Machines_CellMaximumProgram`, `ContingencyTables_Machines_CellMinimumProgram`, `ContingencyTables_Machines_CorrectionValueProgram`, `ContingencyTables_Machines_DependentWordProgram`, `ContingencyTables_Machines_DirectedBFSProgram`, `ContingencyTables_Machines_DirectedBFSRuntime`, `ContingencyTables_Machines_DyadicRootProgram`, `ContingencyTables_Machines_DyadicWordProgram`, `ContingencyTables_Machines_FiniteGraphCutProgram`, `ContingencyTables_Machines_FiniteGraphRootProgram`, `ContingencyTables_Machines_FixedCardinalityFlat`, `ContingencyTables_Machines_FixedCardinalityFold`, `ContingencyTables_Machines_FixedCardinalityProgram`, `ContingencyTables_Machines_FlowEntryProgram`, `ContingencyTables_Machines_FlowLoopProgram`, `ContingencyTables_Machines_FlowMatrixProgram`, `ContingencyTables_Machines_FlowPathProgram`, `ContingencyTables_Machines_FractionAcceptanceProgram`, `ContingencyTables_Machines_FractionAggregateProgram`, `ContingencyTables_Machines_FractionMetropolisProgram`, `ContingencyTables_Machines_InitialChoiceProgram`, `ContingencyTables_Machines_IntegerMatrixProgram`, `ContingencyTables_Machines_ListSubtractProgram`, `ContingencyTables_Machines_ListWordProgram`, `ContingencyTables_Machines_LowerCapacityProgram`, `ContingencyTables_Machines_MaximalListProgram`, `ContingencyTables_Machines_MedianFractionProgram`, `ContingencyTables_Machines_NaturalBlockProgram`, `ContingencyTables_Machines_NetworkCapacityProgram`, `ContingencyTables_Machines_NetworkFeasibilityProgram`, `ContingencyTables_Machines_PairedCatalogProgram`, `ContingencyTables_Machines_PairedDemandProgram`, `ContingencyTables_Machines_PairedFactorialProgram`, `ContingencyTables_Machines_PairedProfileProgram`, `ContingencyTables_Machines_PowerApproximationProgram`, `ContingencyTables_Machines_RationalIntervalProgram`, `ContingencyTables_Machines_ResidualDenseProgram`, `ContingencyTables_Machines_ResidualGraphProgram`, `ContingencyTables_Machines_RoundedPowerProgram`, `ContingencyTables_Machines_ScaledWordProgram`, `ContingencyTables_Machines_SignedFloorProgram`, `ContingencyTables_Machines_SignedPairProgram`, `ContingencyTables_Rooted_ForestAffineProgram`, `ContingencyTables_Rooted_ForestCountIdentification`, `ContingencyTables_Rooted_ForestPenaltyProgram`, `ContingencyTables_Rooted_LargeMarginProgram`, `ContingencyTables_Rooted_RootedBinFramesProgram`, `ContingencyTables_Rooted_RootedCellDataProgram`, `ContingencyTables_Rooted_RootedCoefficientProgram`, `ContingencyTables_Rooted_RootedComponentCode`, `ContingencyTables_Rooted_RootedComponentProgram`, `ContingencyTables_Rooted_RootedCorrectionProgram`, `ContingencyTables_Rooted_RootedCorrectionSampleProgram`, `ContingencyTables_Rooted_RootedDemandProgram`, `ContingencyTables_Rooted_RootedEstimatorBlockProgram`, `ContingencyTables_Rooted_RootedEstimatorLayoutProgram`, `ContingencyTables_Rooted_RootedEstimatorMedianLaw`, `ContingencyTables_Rooted_RootedEstimatorMedianProgram`, `ContingencyTables_Rooted_RootedEstimatorWordLaw`, `ContingencyTables_Rooted_RootedEstimatorWordProgram`, `ContingencyTables_Rooted_RootedForestCatalog`, `ContingencyTables_Rooted_RootedForestDataProgram`, `ContingencyTables_Rooted_RootedForestPrepareProgram`, `ContingencyTables_Rooted_RootedLabelWeightProgram`, `ContingencyTables_Rooted_RootedOffsetProgram`, `ContingencyTables_Rooted_RootedOracleFlatProgram`, `ContingencyTables_Rooted_RootedOracleStepProgram`, `ContingencyTables_Rooted_RootedOracleWalkProgram`, `ContingencyTables_Rooted_RootedOracleWordProgram`, `ContingencyTables_Rooted_RootedPenaltyEvaluateProgram`, `ContingencyTables_Rooted_RootedPointPenaltyProgram`, `ContingencyTables_Rooted_RootedRatioSampleProgram`, `ContingencyTables_Rooted_RootedTreeInputProgram`, `ContingencyTables_Sampling_FirstPaperCodeProposal`, `ContingencyTables_Sampling_FirstPaperPhysicalMarginal`, `ContingencyTables_Sampling_FirstPaperPhysicalVariance`, `ContingencyTables_Sampling_FirstPaperPreparedProposal`, `ContingencyTables_Sampling_FirstPaperProfiles`, `ContingencyTables_Sampling_FirstPaperSmallChain`, `ContingencyTables_Sampling_GreedyRowMachine`, `ContingencyTables_Sampling_GreedyTableMachine`, `ContingencyTables_Sampling_PaddedCompletions`, `ContingencyTables_Sampling_PaddedResidualProgram`, `ContingencyTables_Sampling_PhysicalCompletionFibres`, `ContingencyTables_Sampling_PhysicalLargeProfiles`, `ContingencyTables_Sampling_PhysicalOriginalResiduals`, `ContingencyTables_Sampling_PhysicalResidualMargins`, `ContingencyTables_Sampling_ProfileExchangeProgram`, `ContingencyTables_Sampling_ProfileRepairProgram`, `ContingencyTables_Sampling_SmallCellCatalogProgram`, `ContingencyTables_Sampling_SmallCellIndexProgram`, `ContingencyTables_Sampling_SmallComplementProgram`, `ContingencyTables_Sampling_SmallContextFibres`, `ContingencyTables_Sampling_SmallGraphProfiles`, `ContingencyTables_Sampling_SmallLineSumProgram`, `ContingencyTables_Sampling_SmallMarginTestProgram`, `ContingencyTables_Sampling_SmallPatternProgram`, `ContingencyTables_Sampling_SmallProfileCode`, `ContingencyTables_Sampling_SmallProfileValidator`, `ContingencyTables_Sampling_SmallViewLookupProgram`, `ContingencyTables_Transport_BoundedTableFeasibility`, `ContingencyTables_Transport_BoxCompletion`, `ContingencyTables_Transport_CompletionCounts`, `ContingencyTables_Transport_CompletionFibreEquiv`, `ContingencyTables_Transport_EdmondsKarpAlgorithm`, `ContingencyTables_Transport_FiniteGraphRootSemantics`, `ContingencyTables_Transport_FlowClamp`, `ContingencyTables_Transport_PairedLabels`, `ContingencyTables_Transport_PathAugmentation`, `ContingencyTables_Transport_RectangleCompletions`, `ContingencyTables_Transport_ReferenceCompletionBlock`, `ContingencyTables_Transport_ResidualAugmentation`, `ContingencyTables_Transport_RowColumnPenalties`, `MatchingCount_Arithmetic_BinarySubtract`, `MatchingCount_Arithmetic_TreeFraction`, `MatchingCount_Arithmetic_TreeGCD`, `MatchingCount_Arithmetic_TreeNatDivision`, `MatchingCount_Arithmetic_TreeSubtract`, `MatchingCount_Complexity_TreeChoiceCosts`, `MatchingCount_Complexity_TreePolynomial`, `MatchingCount_Machines_TreeColex`, `MatchingCount_Machines_TreeFastLookup`, `MatchingCount_Machines_TreeFinite`, `MatchingCount_Machines_TreeFiniteCollections`, `MatchingCount_Machines_TreeFiniteOps`, `MatchingCount_Machines_TreeIndex`, `MatchingCount_Machines_TreeListMore`, `MatchingCount_Machines_TreeListOps`, `MatchingCount_Machines_TreeNaturalComb`, `MatchingCount_Machines_TreePartialChoice`, `MatchingCount_Machines_TreePredicate`, `MatchingCount_Machines_TreeRepeat`, `MatchingCount_Machines_TreeSum`, `MatchingCount_Sampling_TreeCategorical`, `MatchingCount_Sampling_TreeDPCounts`, `MatchingCount_Sampling_TreeDPEntry`.
--
--   **Imports.** It imports the published bundle `Def_ContingencyTables`; the bundles `OAIQ089A000` and `OAIQ089A001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ089A006`, `OAIQ089A007` and `OAIQ089A008`; the statement `OAI.ContingencyTables.ObservableTrajectory.omission_chain_dual`; the proof of `OAI.ContingencyTables.ObservableTrajectory.omission_chain_dual`.
-- source:
--   OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 115; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Exact-Uniform-Sampling-of-Contingency-Tables-with-Arbitrary-Margins-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_ContingencyTables
import Definitions.Def_OAIQ089A000
import Definitions.Def_OAIQ089A001

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_BinaryContraction
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Fixed-degree binary cubic contraction

The full-matrix cubic contraction in paper 200-02,
Lemma `lem:binary-contraction`, follows from the generic spectral theorem
`CommonBasesFPRAS.cubic_signature` and its closed-limit lemma. A symmetric
cubic tensor is positive on distinct triples and zero on repetitions;
its coordinate slices have the quadratic signature; contraction by an
arbitrary nonnegative vector, in particular a pair indicator, preserves
that signature on the full remaining index set.

There is no assumption of positivity on unrelated subset cardinalities.
-/

namespace ContingencyTables.BinaryContraction

open scoped BigOperators Topology Classical
open LinearMap (BilinForm)
open CommonBasesFPRAS

variable {I : Type*} [Fintype I] [DecidableEq I]

omit [Fintype I] [DecidableEq I] in
/-- Our signature convention and the existing library convention agree
for symmetric forms; only the orthogonality argument order differs. -/
lemma signature_iff (B : BilinForm ℝ (I → ℝ)) (hsymm : B.IsSymm) :
    OnePositiveDirection B ↔ CommonBasesFPRAS.OnePositive B := by
  constructor
  · intro h e he v hv
    exact h e he v (by rw [hsymm.eq e v]; exact hv)
  · intro h e he v hv
    exact h e he v (by rw [hsymm.eq v e]; exact hv)

/-- The paper's addition property: fix precisely `k-2` elements and test
only the remaining quadratic matrix. -/
def AdditionProperty (f : Set I → ℝ) (k : ℕ) : Prop :=
  ∀ A, A.ncard + 2 = k → CommonBasesFPRAS.OnePositive (faceHessian f A).toBilin'

def OmissionProperty (f : Set I → ℝ) (k : ℕ) : Prop :=
  AdditionProperty (complementWeight f) (Fintype.card I - k)

end ContingencyTables.BinaryContraction

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_RowColumnPenalties
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Literal doubled row and column penalties

The false coordinate of a cell is its row value x. Its true coordinate
is y, with physical column value q=B-y. Thus row and column factor groups
are disjoint, while their small-cell subsets are nested inside them.
Offsets below are the actual full margins and capacity sums of the paper.
-/

namespace ContingencyTables.RowColumnPenalties

open scoped BigOperators Classical Matrix
open CommonBasesFPRAS ProductIntegerSignature NestedProductSignature
open NestedPenaltyApplication BalancedBox

variable {I J : Type*} [Fintype I] [Fintype J]

omit [Fintype J] in
lemma columnViews_add (B : I → J → ℕ) (z : ((I × J) × Bool) → ℕ)
    (hz : InBox (fun u => B u.1.1 u.1.2) z) (j : J) :
    (∑ i, columnView B z i j)+(∑ i, z ((i,j),true))=columnCapacity B j := by
  unfold columnView columnCapacity
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact Nat.sub_add_cancel (hz ((i,j),true))

omit [Fintype J] in
lemma smallColumnViews_add (small : I → J → Bool) (B : I → J → ℕ)
    (z : ((I × J) × Bool) → ℕ) (hz : InBox (fun u => B u.1.1 u.1.2) z) (j : J) :
    (∑ i, if small i j then columnView B z i j else 0)+
      (∑ i, if small i j then z ((i,j),true) else 0)=smallColumnCapacity small B j := by
  unfold columnView smallColumnCapacity
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases hs : small i j
  · simp
  · simp only [ite_true, if_true]
    exact Nat.sub_add_cancel (hz ((i,j),true))

lemma full_affine_column (B : I → J → ℕ) (rbar : I → ℕ) (cbar : J → ℕ)
    (z : ((I × J) × Bool) → ℕ) (hz : InBox (fun u => B u.1.1 u.1.2) z) (j : J) :
    fullOffset B rbar cbar (.inr j)+(lineTotal cellLine z (.inr j):ℝ)*viewSlope (I := I) (J := J) (.inr j) =
      ((∑ i, columnView B z i j):ℝ)-cbar j := by
  have h : ((∑ i, columnView B z i j):ℝ)+((∑ i, z ((i,j),true)):ℝ)=columnCapacity B j := by
    exact_mod_cast columnViews_add B z hz j
  rw [lineTotal_column]
  simp only [fullOffset,viewSlope,Sum.elim_inr,mul_neg_one]
  push_cast
  linarith

lemma small_affine_column (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (z : ((I × J) × Bool) → ℕ)
    (hz : InBox (fun u => B u.1.1 u.1.2) z) (j : J) :
    smallOffset small B r c (.inr j)+
      (smallTotal cellLine (smallCoordinate small) z (.inr j):ℝ)*viewSlope (I := I) (J := J) (.inr j) =
      ((∑ i, if small i j then columnView B z i j else 0):ℝ)-c j := by
  have h : ((∑ i, if small i j then columnView B z i j else 0):ℝ)+
      ((∑ i, if small i j then z ((i,j),true) else 0):ℝ)=smallColumnCapacity small B j := by
    exact_mod_cast smallColumnViews_add small B z hz j
  rw [smallTotal_column]
  simp only [smallOffset,viewSlope,Sum.elim_inr,mul_neg_one]
  push_cast
  linarith

/-- This is exactly the manuscript's full row/column deviation plus its
small residual violation penalty, on the actual doubled physical box. -/
theorem penalty_eq (small : I → J → Bool) (B : I → J → ℕ)
    (r cR : I → ℕ) (c cC : J → ℕ) (z : ((I × J) × Bool) → ℕ)
    (hz : InBox (fun u => B u.1.1 u.1.2) z) :
    penalty cellLine (smallCoordinate small) (fullOffset B cR cC) viewSlope
      (smallOffset small B r c) viewSlope z =
      (∑ i, |((∑ j, rowView z i j):ℝ)-cR i|)+
      (∑ j, |((∑ i, columnView B z i j):ℝ)-cC j|)+
      (∑ i, max (((∑ j, if small i j then rowView z i j else 0):ℝ)-r i) 0)+
      (∑ j, max (((∑ i, if small i j then columnView B z i j else 0):ℝ)-c j) 0) := by
  unfold penalty
  rw [Fintype.sum_sum_type,Fintype.sum_sum_type]
  simp_rw [full_affine_row,full_affine_column B cR cC z hz,
    small_affine_row,small_affine_column small B r c z hz]
  ring

/-- Zero penalty means precisely the enlarged full margins and
nonnegative original residuals, even for unbalanced defect profiles. -/
theorem penalty_zero_iff (small : I → J → Bool) (B : I → J → ℕ)
    (r rbar : I → ℕ) (c cbar : J → ℕ) (z : ((I × J) × Bool) → ℕ)
    (hz : InBox (fun u => B u.1.1 u.1.2) z) :
    penalty cellLine (smallCoordinate small) (fullOffset B rbar cbar) viewSlope
      (smallOffset small B r c) viewSlope z=0 ↔ FullConditions small B r rbar c cbar z := by
  rw [penalty_eq small B r rbar c cbar z hz]
  let a : I → ℝ := fun i => |((∑ j, rowView z i j):ℝ)-rbar i|
  let b : J → ℝ := fun j => |((∑ i, columnView B z i j):ℝ)-cbar j|
  let e : I → ℝ := fun i => max (((∑ j, if small i j then rowView z i j else 0):ℝ)-r i) 0
  let f : J → ℝ := fun j => max (((∑ i, if small i j then columnView B z i j else 0):ℝ)-c j) 0
  have ha : ∀ i, 0 ≤ a i := fun _ => abs_nonneg _
  have hb : ∀ j, 0 ≤ b j := fun _ => abs_nonneg _
  have he : ∀ i, 0 ≤ e i := fun _ => le_max_right _ _
  have hf : ∀ j, 0 ≤ f j := fun _ => le_max_right _ _
  change (∑ i, a i)+(∑ j, b j)+(∑ i, e i)+(∑ j, f j)=0 ↔ _
  constructor
  · intro hzero
    have hsa : 0 ≤ ∑ i, a i := Finset.sum_nonneg (fun i _ => ha i)
    have hsb : 0 ≤ ∑ j, b j := Finset.sum_nonneg (fun j _ => hb j)
    have hse : 0 ≤ ∑ i, e i := Finset.sum_nonneg (fun i _ => he i)
    have hsf : 0 ≤ ∑ j, f j := Finset.sum_nonneg (fun j _ => hf j)
    refine ⟨?_,?_,?_,?_⟩
    · intro i
      have hi := Finset.single_le_sum (fun k _ => ha k) (Finset.mem_univ i)
      have hzabs : a i=0 := by linarith [ha i]
      have hiReal := sub_eq_zero.mp (abs_eq_zero.mp hzabs)
      exact_mod_cast hiReal
    · intro j
      have hj := Finset.single_le_sum (fun k _ => hb k) (Finset.mem_univ j)
      have hzabs : b j=0 := by linarith [hb j]
      have hjReal := sub_eq_zero.mp (abs_eq_zero.mp hzabs)
      exact_mod_cast hjReal
    · intro i
      have hi := Finset.single_le_sum (fun k _ => he k) (Finset.mem_univ i)
      have ht : (((∑ j, if small i j then rowView z i j else 0):ℝ)-r i) ≤ 0 := by
        have hm := le_max_left (((∑ j, if small i j then rowView z i j else 0):ℝ)-r i) 0
        change _ ≤ e i at hm
        linarith
      exact_mod_cast (sub_nonpos.mp ht)
    · intro j
      have hj := Finset.single_le_sum (fun k _ => hf k) (Finset.mem_univ j)
      have ht : (((∑ i, if small i j then columnView B z i j else 0):ℝ)-c j) ≤ 0 := by
        have hm := le_max_left (((∑ i, if small i j then columnView B z i j else 0):ℝ)-c j) 0
        change _ ≤ f j at hm
        linarith
      exact_mod_cast (sub_nonpos.mp ht)
  · rintro ⟨hr,hc,hsr,hsc⟩
    have haz : ∀ i, a i=0 := by
      intro i
      have hh : ((∑ j, rowView z i j):ℝ)=rbar i := by exact_mod_cast hr i
      exact abs_eq_zero.mpr (sub_eq_zero.mpr hh)
    have hbz : ∀ j, b j=0 := by
      intro j
      have hh : ((∑ i, columnView B z i j):ℝ)=cbar j := by exact_mod_cast hc j
      exact abs_eq_zero.mpr (sub_eq_zero.mpr hh)
    have hez : ∀ i, e i=0 := by
      intro i
      apply max_eq_right
      exact sub_nonpos.mpr (by exact_mod_cast hsr i)
    have hfz : ∀ j, f j=0 := by
      intro j
      apply max_eq_right
      exact sub_nonpos.mpr (by exact_mod_cast hsc j)
    simp only [haz,hbz,hez,hfz,Finset.sum_const_zero,add_zero]

end ContingencyTables.RowColumnPenalties

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_PhysicalLargeProfiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing the arbitrary enumeration from the physical large-cell sum -/

namespace ContingencyTables.PhysicalLargeProfiles

open scoped BigOperators Classical
open LargePairEnumeration

variable {C : Type*}

noncomputable def physicalProfile (small : C → Bool) (M : C → ℕ)
    (z : SmallView small → ℕ) (a : PhysicalAssignments small M) (u : C×Bool) : ℕ :=
  if hs : small u.1=true then z (⟨u.1,hs⟩,u.2)
  else if u.2 then M u.1-(a ⟨u.1,Bool.eq_false_iff.mpr hs⟩).val
    else (a ⟨u.1,Bool.eq_false_iff.mpr hs⟩).val

end ContingencyTables.PhysicalLargeProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ForestCountIdentification
attribute [-instance] _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The companion signature marginal is the literal weighted completion count

The physical all-large product is split bijectively into tree and free
assignments. Exact nonroot equations then retain one tree completion per
free assignment, with exactly its root/tree exponential penalty.
-/

namespace ContingencyTables.ForestCountIdentification

open scoped BigOperators Classical
open SimpleGraph LargePairEnumeration PhysicalLargeProfiles
open ForestCapacity GraphCompletionCounts ForestAssignmentSplit ForestLiteralCount

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def smallX (small : I → J → Bool)
    (z : SmallView (fun a : I×J => small a.1 a.2) → ℕ) (i : I) (j : J) : ℕ :=
  if hs : small i j=true then z (⟨(i,j),hs⟩,false) else 0

noncomputable def smallY (small : I → J → Bool)
    (z : SmallView (fun a : I×J => small a.1 a.2) → ℕ) (i : I) (j : J) : ℕ :=
  if hs : small i j=true then z (⟨(i,j),hs⟩,true) else 0

noncomputable def sourceMarginal (small : I → J → Bool) (T : SimpleGraph (I⊕J))
    (_d : ℕ) (b : I → J → ℕ) (r : I → ℤ) (c : J → ℤ) (alpha : ℝ)
    (z : SmallView (fun a : I×J => small a.1 a.2) → ℕ) : ℝ :=
  ∑ f : FreeIndex small T b, (2:ℝ)^(-alpha*actualPenalty small T b
    (smallX small z) (smallY small z) (freeTable small T b f) r c
    (ForestPhysicalCompletion.solved small T r c
      (fun i j => (smallX small z i j:ℤ))
      (fun i j => ((b i j-smallY small z i j:ℕ):ℤ))
      (fun i j => (freeTable small T b f i j:ℤ))))

end ContingencyTables.ForestCountIdentification

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionFactorialApplication
attribute [-instance] _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The companion's literal completion count gives both labelled factorial signatures

The labels below are actual copies of the retained small cells. Their
fiber cardinalities are the capacities, so the original first and dual
factorial displays and the W² chain-state comparison have no abstract
signature or completion hypothesis.
-/

namespace ContingencyTables.CompanionFactorialApplication

open scoped BigOperators Classical Matrix
open SimpleGraph CommonBasesFPRAS
open ForestCapacity GraphIntegralCompletion ForestCountIdentification
open LargePairEnumeration BalancedBox LabelledFactorial

variable (I J : Type*) [Fintype I] [Fintype J]

variable {I J}

noncomputable def h (A : Instance I J) (alpha : ℝ) (z : View A → ℕ) : ℝ :=
  sourceMarginal A.small A.T A.d A.b A.r A.c alpha z

noncomputable def f (A : Instance I J) (alpha : ℝ) : Set (Labels A×Bool) → ℝ :=
  firstLift (TwoLiftStates.group (labelCell A)) (h A alpha) (denominator A)

end ContingencyTables.CompanionFactorialApplication

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_PairedLabels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual doubled labels form disjoint covering slots -/

namespace ContingencyTables.PairedLabels

open scoped BigOperators Classical
open CommonBasesFPRAS TwoLiftStates

variable {P : Type*}

lemma mapped_fresh (l : List P) (hl : l.Nodup) (B : Set (P×Bool))
    (hB : ∀ p ∈ l, ∀ b, (p,b)∉B) : SlotsFresh (l.map pair) B := by
  induction l generalizing B with
  | nil => trivial
  | cons p l ih =>
    have hd := List.nodup_cons.mp hl
    refine ⟨?_,hB p (by simp) false,hB p (by simp) true,?_⟩
    · intro he
      exact Bool.false_ne_true (congrArg Prod.snd he)
    · apply ih hd.2
      intro q hq b hm
      rcases hm with he|he|hm
      · have hqp : q=p := congrArg Prod.fst he
        exact hd.1 (hqp ▸ hq)
      · have hqp : q=p := congrArg Prod.fst he
        exact hd.1 (hqp ▸ hq)
      · exact hB q (by simp [hq]) b hm

variable [Fintype P]

theorem fresh : SlotsFresh (pairs : List ((P×Bool)×(P×Bool))) ∅ :=
  mapped_fresh Finset.univ.toList (Finset.nodup_toList _) _ (by intro p hp b; exact Set.notMem_empty _)

theorem cover : pairSupport (pairs : List ((P×Bool)×(P×Bool)))=Set.univ := by
  apply Set.eq_univ_of_forall
  rintro ⟨p,b⟩
  refine ⟨pair p,pair_mem p,?_⟩
  cases b
  · exact Or.inl rfl
  · exact Or.inr rfl

end ContingencyTables.PairedLabels

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionAnnealing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Adjacent actual companion weights and ideal multipliers

The parameter step is 1/(H/A). Its factor-two bounds are proved from
the literal forest penalty bound, then passed to the actual labelled
weights and their exact transversal/defect totals.
-/

namespace ContingencyTables.CompanionAnnealing

open scoped BigOperators Classical
open CommonBasesFPRAS CompanionFactorialApplication LabelledFactorial
open TwoLiftStates BalancedBox

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def weight (A : Instance I J) (j : ℕ) : Set (Labels A×Bool) → ℝ :=
  f A ((j:ℝ)/scale A)

end ContingencyTables.CompanionAnnealing

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionEstimatorAmplification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Logarithmic confidence amplification of the actual weight estimator -/

namespace ContingencyTables.CompanionOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary ResidualMixture FirstSuccess
open CommonBasesFPRAS
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

/-- Each complete estimator uses constant confidence; the requested
failure probability changes only the number of independent medians. -/
def medianEstimatorBits (A : Instance I J) (C K j : ℕ) (epsilon delta : ℚ) : ℕ :=
  repetitionCount delta * estimatorWordBits A C K j (innerTolerance (epsilon/2) j) 1

end

end ContingencyTables.CompanionOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionWeightOracle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual labelled-weight oracle used by the outer chain -/

namespace ContingencyTables.CompanionWeightOracle

open CompanionFactorialApplication CompanionOracleDensity GridBoundary LabelledFactorial TwoLiftStates
open CommonBasesFPRAS
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

abbrev WeightWord (A : Instance I J) (C K j : ℕ) (xi : ℚ) :=
  Fin (medianEstimatorBits A C K j xi xi) → Bool

end

end ContingencyTables.CompanionWeightOracle

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionBooleanPhase
attribute [-instance] _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The companion phase walk driven by disjoint bounded Boolean words -/

namespace ContingencyTables.CompanionBooleanPhase

open CompanionFactorialApplication CompanionOracleDensity CompanionWeightOracle CompanionRationalUpdates
open CommonBasesFPRAS FirstSuccess FairBits TwoLiftStates GridBoundary ResidualMixture
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

abbrev State (A : Instance I J) := ChainIndex (pairs : List ((Labels A×Bool)×(Labels A×Bool)))

lemma proposal_codes (A : Instance I J) (S : State A) :
    Fintype.card {T : State A // ExchangeAdjacent S.val T.val} ≤ 2^proposalBits A := by
  rw [Fintype.card_subtype]
  have hh := chain_neighbors_card pairs PairedLabels.fresh PairedLabels.cover S
  simp only [PairedLabels.length] at hh
  exact hh.trans (Nat.le_pow_clog (by decide) _)

/-- Each valid exchange neighbor has one code. Every unused code holds
the current state; the full transition has another independent lazy bit. -/
def proposal (A : Instance I J) (S : State A) (bits : Fin (proposalBits A) → Bool) : Option (State A) :=
  subsetBitDraw (fun T : State A => ExchangeAdjacent S.val T.val)
    (proposalBits A) (proposal_codes A S) bits

def stepBits (A : Instance I J) (C K j k : ℕ) (xi : ℚ) : ℕ :=
  1+(proposalBits A+((medianEstimatorBits A C K j xi xi+
    medianEstimatorBits A C K j xi xi)+k))

def stepWordEquiv (A : Instance I J) (C K j k : ℕ) (xi : ℚ) :
    (Fin (stepBits A C K j k xi) → Bool) ≃
      ((Fin 1 → Bool)×((Fin (proposalBits A) → Bool)×
        ((WeightWord A C K j xi×WeightWord A C K j xi)×(Fin k → Bool)))) :=
  (splitWordEquiv _ _).trans (Equiv.prodCongr (Equiv.refl _)
    ((splitWordEquiv _ _).trans (Equiv.prodCongr (Equiv.refl _)
      ((splitWordEquiv _ _).trans (Equiv.prodCongr (splitWordEquiv _ _) (Equiv.refl _))))))

end

end ContingencyTables.CompanionBooleanPhase

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Arithmetic_BinarySubtract
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.StackSubtract
open Turing MachineCost StackAddition

lemma subDigits_balance (A B : List Bool) (c : Bool) :
    value A+2^(max A.length B.length)*(subDigits c A B).1.toNat=
      value (subDigits c A B).2+value B+c.toNat := by
  induction A generalizing B c with
  | nil =>
    induction B generalizing c with
    | nil => simp [subDigits,value]
    | cons b B ih =>
      have hh:=ih (borrow c false b)
      have hd:=digit_balance c false b
      simp only [List.length_nil,Nat.zero_max,value] at hh
      simp only [subDigits,List.length_nil,List.length_cons,Nat.zero_max,value,pow_succ,
        Bool.toNat_false] at hd ⊢
      nlinarith
  | cons a A ih =>
    cases B with
    | nil =>
      have hh:=ih [] (borrow c a false)
      have hd:=digit_balance c a false
      simp only [List.length_nil,Nat.max_zero,value] at hh
      simp only [subDigits,List.length_nil,List.length_cons,Nat.max_zero,value,pow_succ,
        Bool.toNat_false] at hd ⊢
      nlinarith
    | cons b B =>
      have hh:=ih B (borrow c a b)
      have hd:=digit_balance c a b
      simp only [subDigits,List.length_cons,max_add_add_right,value,pow_succ]
      nlinarith

lemma subDigits_correct (A B : List Bool) (c : Bool) (h : value B+c.toNat≤value A) :
    (subDigits c A B).1=false ∧ value (subDigits c A B).2=value A-value B-c.toNat := by
  have hh:=subDigits_balance A B c
  have hl:=value_lt (subDigits c A B).2
  rw [subDigits_length] at hl
  cases hc : (subDigits c A B).1 with
  | false => simp only [hc,Bool.toNat_false,Nat.mul_zero,Nat.add_zero] at hh; exact ⟨rfl,by omega⟩
  | true => simp only [hc,Bool.toNat_true,Nat.mul_one] at hh; omega

end MatchingFPRAS.StackSubtract

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Arithmetic_TreeSubtract
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.MatchingFPRAS.TreeTyped.instCodecData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeArithmetic
open RegisterProc TreeData TreeMachine Turing

variable {R : Type} [DecidableEq R]

theorem sub_bits_exec (E : Env R) (i j : R) (hij : i≠j) (A B : List Bool)
    (hm : E i=bits A) (hn : E j=bits B) (hle : StackAddition.value B≤StackAddition.value A) :
    Exec (sub i j hij) (encodeEnv E) (encodeEnv (putPair E i j (nat (StackAddition.value A-StackAddition.value B)) .nil))
      (9*(A.length+B.length)+20) := by
  let S:=(StackSubtract.subDigits false A B).2
  have h₁:=on_left TreeBits.decodeForward E i j hij (TreeData.encode (bits A)) (TreeData.encode (bits B)) A _
    (TreeBits.decodeForward_exec A [])
  have h₂:=on_right TreeBits.decodeForward E i j hij A (TreeData.encode (bits B)) B _
    (TreeBits.decodeForward_exec B [])
  have h₃:=on_pair BinaryArithmeticProc.sub E i j hij A B S [] _ (BinaryArithmeticProc.sub_exec A B)
  have h₄:=on_left BinaryNormalize.program E i j hij S [] (BinaryNormalize.normalize S) _
    (BinaryNormalize.exec S [])
  have h₅:=on_left TreeBits.encodeForward E i j hij (BinaryNormalize.normalize S) []
    (TreeData.encode (bits (BinaryNormalize.normalize S))) _ (TreeBits.encodeForward_exec _ [])
  have h₆ : Exec (atom (.push (.inl j) (fun _=>false) .halt))
      (rawPair E i j (TreeData.encode (bits (BinaryNormalize.normalize S))) [])
      (rawPair E i j (TreeData.encode (bits (BinaryNormalize.normalize S))) [false]) 1 := by
    apply exec_atom
    simp only [TM2.stepAux,rawPair_right]
    congr 1
    simp [rawPair]
  have hh:=h₁.seq (h₂.seq (h₃.seq (h₄.seq (h₅.seq h₆))))
  have hS : BinaryNormalize.normalize S=(StackAddition.value A-StackAddition.value B).bits := by
    rw [BinaryNormalize.normalize_bits]
    congr 1
    simpa only [Bool.toNat_false,Nat.add_zero,Nat.sub_zero] using
      (StackSubtract.subDigits_correct A B false (by simpa using hle)).2
  rw [hS] at hh
  have hstart : rawPair E i j (TreeData.encode (bits A)) (TreeData.encode (bits B))=encodeEnv E := by
    rw [←hm,←hn]
    exact rawPair_same E i j
  have hend : rawPair E i j (TreeData.encode (bits (StackAddition.value A-StackAddition.value B).bits)) [false]=
      encodeEnv (putPair E i j (nat (StackAddition.value A-StackAddition.value B)) .nil) := rawPair_encode E i j (nat (StackAddition.value A-StackAddition.value B)) .nil
  rw [hstart,hend] at hh
  apply hh.mono
  have hl:=StackSubtract.subDigits_length A B false
  have hl' := BinaryNormalize.normalize_length S
  rw [hS] at hl'
  dsimp only [S] at hl hl' ⊢
  omega

lemma sub_exec (E : Env R) (i j : R) (hij : i≠j) (m n : ℕ)
    (hi : E i=nat m) (hj : E j=nat n) (hle : n ≤ m) :
    Exec (sub i j hij) (encodeEnv E) (encodeEnv (putPair E i j (nat (m-n)) .nil))
      (9*(m.bits.length+n.bits.length)+20) := by
  simpa only [StackAddition.value_bits] using sub_bits_exec E i j hij m.bits n.bits hi hj
    (by simpa only [StackAddition.value_bits] using hle)
end MatchingFPRAS.TreeArithmetic

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_TreePartialChoice
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open TreeData TreeMachine RegisterProc TreeFunction

variable {A B : Type} [Codec A] [Codec B]

lemma subProgram_exec (a b : ℕ) (s : Data) (hab : b ≤ a) :
    Exec subProgram (encodeEnv (env (encode (a,b)) .nil s))
      (encodeEnv (env (nat (a-b)) .nil s)) (subCost (a,b)) := by
  have h1:=split10 (nat a) (nat b) .nil s
  have h2:=TreeArithmetic.sub_exec (env (nat b) (nat a) s) 1 0 (by decide) a b rfl rfl hab
  simp only [putPair,env_update0,env_update1] at h2
  have h3:=copy10 .nil (nat (a-b)) s
  have h4:=clear1 (nat (a-b)) (nat (a-b)) s
  apply (h1.seq (h2.seq (h3.seq h4))).mono
  simp only [size_nil,subCost]; omega

def subtract : Realizer (fun ab : ℕ×ℕ=>ab.1-ab.2) := by
  let Z : Realizer (fun _ : ℕ×ℕ=>0) := constant 0
  let P:=choosePartial (fun ab : ℕ×ℕ=>decide (ab.1<ab.2)) (fun _=>0) (fun ab=>ab.1-ab.2)
    less Z.program subProgram Z.cost subCost (fun a s _=>Z.correct a s)
    (fun a s h=>subProgram_exec a.1 a.2 s (by simpa only [decide_eq_false_iff_not,not_lt] using h))
  refine ⟨P.program,P.cost,?_⟩
  intro ab stack
  by_cases hlt : ab.1<ab.2
  · simpa [hlt,Nat.sub_eq_zero_of_le (Nat.le_of_lt hlt)] using P.correct ab stack
  · simpa [hlt] using P.correct ab stack
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Arithmetic_TreeNatDivision
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open TreeData TreeMachine RegisterProc TreeFunction

def divStepRealizer : Realizer divStep := by
  let nP : Realizer (fun x : Bool×(ℕ×(ℕ×ℕ))=>x.2.1) := composition second first
  let qP : Realizer (fun x : Bool×(ℕ×(ℕ×ℕ))=>2*x.2.2.1) :=
    composition (composition (composition second second) first) double
  let rP : Realizer (fun x : Bool×(ℕ×(ℕ×ℕ))=>2*x.2.2.2+x.1.toNat) :=
    composition (pair (composition (composition (composition second second) second) double)
      (composition first digitValue)) add
  let lP := composition (pair rP nP) less
  let q1P := composition (pair qP (constant 1)) add
  let r1P := composition (pair rP nP) subtract
  exact (pair nP (choose lP (pair qP rP) (pair q1P r1P))).congr (by
    intro x; simp only [Function.comp_apply,divStep,decide_eq_true_eq])

lemma divFold_correct (m n : ℕ) (hn : 0<n) :
    (m.bits.reverse.foldl (fun z b=>divStep (b,z)) (n,0,0)).2=(m/n,m%n) := by
  have hm:=divFold_mass m.bits n 0 0
  have hr:=divFold_lt m.bits.reverse n 0 0 hn hn
  simp only [Nat.mul_zero,Nat.zero_add,Nat.zero_mul,StackAddition.value_bits] at hm
  have hu : m/n=(m.bits.reverse.foldl (fun z b=>divStep (b,z)) (n,0,0)).2.1 ∧
      m%n=(m.bits.reverse.foldl (fun z b=>divStep (b,z)) (n,0,0)).2.2 :=
    (Nat.div_mod_unique hn).2 ⟨by omega,hr⟩
  exact Prod.ext hu.1.symm hu.2.symm

def divCore : Realizer (fun ab : ℕ×ℕ=>
    (ab.1.bits.reverse.foldl (fun z b=>divStep (b,z)) (ab.2,0,0)).2) :=
  composition (composition (pair (composition (composition first toBits) reverse)
    (pair second (pair (constant 0) (constant 0)))) (fold divStepRealizer)) second

def division : Realizer (fun ab : ℕ×ℕ=>(ab.1/ab.2,ab.1%ab.2)) := by
  let posP : Realizer (fun ab : ℕ×ℕ=>decide (0<ab.2)) := composition (pair (constant 0) second) less
  let zeroP : Realizer (fun ab : ℕ×ℕ=>(0,ab.1)) := pair (constant 0) first
  exact (choose posP divCore zeroP).congr (by
    intro ab
    by_cases h : 0<ab.2
    · simp only [h,decide_true,↓reduceIte]
      exact divFold_correct ab.1 ab.2 h
    · have hn : ab.2=0 := by omega
      simp [hn])
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_TreeRepeat
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open TreeData TreeMachine RegisterProc TreeFunction

variable {B : Type} [Codec B]

def predecessor : Realizer (fun n : ℕ=>n-1) := composition (pair identity (constant 1)) subtract

namespace Repeat
open RegisterControl (Instr Runs Effect)

def nextRealizer {f : ℕ×B → B} (F : Realizer f) : Realizer (next f) :=
  pair (composition first predecessor) F

def code (P : Proc (K Reg)) : Point → RegisterControl.Instr Reg Point
  | .loop => .call (TreeFunction.split 1 0 (by decide)) .check
  | .check => .branch 1 .halt .rebuild
  | .rebuild => .call (TreeFunction.cons 1 0 (by decide)) .body
  | .body => .call P .loop
  | .halt => .halt

def cost (f : ℕ×B → B) (t : ℕ×B → ℕ) : ℕ → B → ℕ
  | 0,_ => 10
  | n+1,b => t (n+1,b)+4*TreeFunction.size (nat (n+1))+12+cost f t n (f (n+1,b))

lemma runs {f : ℕ×B → B} (F : Realizer f) (n : ℕ) (b : B) (s : Data) :
    Runs (code (nextRealizer F).program) (some Point.loop) (env (encode (n,b)) .nil s)
      (env (encode (countDown f n b)) .nil s) (cost f (nextRealizer F).cost n b) := by
  induction n generalizing b with
  | zero =>
    have hh : Runs (code (nextRealizer F).program) (some Point.halt) (env (encode b) .nil s)
        (env (encode b) .nil s) 1 := Runs.step _ _ _ _ _ 0 1 (Effect.halt _) (Runs.done _)
    have hc : Runs (code (nextRealizer F).program) (some Point.check) (env (encode b) .nil s)
        (env (encode b) .nil s) 2 := Runs.step _ _ _ _ _ 1 1 (Effect.nilBranch _ 1 _ _ rfl) hh
    have hs := split10 (nat 0) (encode b) .nil s
    change Exec _ _ _ 7 at hs
    exact Runs.step _ _ _ _ _ 2 8 (Effect.call _ _ _ _ 7 hs) hc
  | succ n ih =>
    have hr:=ih (f (n+1,b))
    have hb:=(nextRealizer F).correct (n+1,b) s
    have he : next f (n+1,b)=(n,f (n+1,b)) := by simp [next]
    change Exec _ _ (encodeEnv (env (encode (next f (n+1,b))) .nil s)) _ at hb
    rw [he] at hb
    let c := cost f (nextRealizer F).cost n (f (n+1,b))
    let t := (nextRealizer F).cost (n+1,b)
    let d := TreeFunction.size (nat (n+1))
    have hbody : Runs (code (nextRealizer F).program) (some Point.body) (env (encode (n+1,b)) .nil s)
        (env (encode (countDown f n (f (n+1,b)))) .nil s) ((t+1)+c) :=
      Runs.step _ _ _ _ _ c (t+1) (Effect.call _ _ _ _ t hb) hr
    have hcons:=cons10 (encode b) (nat (n+1)) s
    have hreb : Runs (code (nextRealizer F).program) (some Point.rebuild) (env (encode b) (nat (n+1)) s)
        (env (encode (countDown f n (f (n+1,b)))) .nil s) ((2*d+4)+((t+1)+c)) :=
      Runs.step _ _ _ _ _ _ (2*d+4) (Effect.call _ _ _ _ (2*d+3) hcons) hbody
    have hn : ∃ a z,nat (n+1)=.cons a z := by
      cases he : (n+1).bits with
      | nil =>
        have hv:=StackAddition.value_bits (n+1)
        rw [he] at hv
        simp [StackAddition.value] at hv
      | cons a z => exact ⟨bit a,bits z,by change bits (n+1).bits=Data.cons (bit a) (bits z); rw [he]; rfl⟩
    obtain ⟨a,z,ha⟩:=hn
    have hc : Runs (code (nextRealizer F).program) (some Point.check) (env (encode b) (nat (n+1)) s)
        (env (encode (countDown f n (f (n+1,b)))) .nil s) (1+((2*d+4)+((t+1)+c))) :=
      Runs.step _ _ _ _ _ _ 1 (Effect.consBranch _ 1 _ _ a z ha) hreb
    have hs:=split10 (nat (n+1)) (encode b) .nil s
    have hs' := hs.mono (show TreeFunction.size Data.nil+2*d+4 ≤ 2*d+5 by simp only [size_nil]; omega)
    have hh : Runs (code (nextRealizer F).program) (some Point.loop) (env (encode (n+1,b)) .nil s)
        (env (encode (countDown f n (f (n+1,b)))) .nil s) ((2*d+6)+(1+((2*d+4)+((t+1)+c)))) :=
      Runs.step _ _ _ _ _ _ (2*d+6) (Effect.call _ _ _ _ (2*d+5) hs') hc
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    all_goals try rfl
    simp only [cost,d,t,c]
    omega
end Repeat

def iterateDown {f : ℕ×B → B} (F : Realizer f) : Realizer (fun nb : ℕ×B=>countDown f nb.1 nb.2) :=
  ⟨RegisterControl.compile (Repeat.code (Repeat.nextRealizer F).program),
    fun nb=>Repeat.cost f (Repeat.nextRealizer F).cost nb.1 nb.2,
    fun nb s=>RegisterControl.compile_exec _ _ _ _ (Repeat.runs F nb.1 nb.2 s)⟩

def rangeStepRealizer : Realizer rangeStep := composition (pair (composition first predecessor) second) listCons
def range : Realizer List.range :=
  (composition (pair identity (constant ([] : List ℕ))) (iterateDown rangeStepRealizer)).congr (by
    intro n; simp [countDown_range])

end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_TreeNaturalComb
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open TreeData TreeMachine RegisterProc TreeFunction

def successor : Realizer Nat.succ :=
  (composition (pair identity (constant 1)) add).congr (fun _=>rfl)

def quotient : Realizer (fun x : ℕ×ℕ=>x.1/x.2) := composition division first
def remainder : Realizer (fun x : ℕ×ℕ=>x.1%x.2) := composition division second

def factorial : Realizer Nat.factorial :=
  (composition (pair identity (constant 1))
    (iterateDown multiply)).congr (by
      intro n
      change countDown factStep n 1=_
      rw [fact_countDown,Nat.mul_one])

end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_TreeListOps
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open TreeData TreeMachine RegisterProc TreeFunction

variable {A B X : Type} [Codec A] [Codec B] [Codec X]

def listCase (b : B) {g : A×List A → B} (G : Realizer g) :
    Realizer (fun as : List A=>match as with | []=>b | a::as=>g (a,as)) where
  program := RegisterStructured.select 0 (constant b (A:=List A)).program G.program
  cost := fun as=>3+match as with | []=>(constant b (A:=List A)).cost [] | a::as=>G.cost (a,as)
  correct := by
    intro as s
    cases as with
    | nil =>
      have hh:=RegisterStructured.select_nil 0 _ G.program (env (encode ([] : List A)) .nil s)
        (env (encode b) .nil s) _ rfl ((constant b (A:=List A)).correct [] s)
      exact hh.mono (by dsimp; omega)
    | cons a as =>
      have hh:=RegisterStructured.select_cons 0 (constant b (A:=List A)).program _
        (env (encode (a::as)) .nil s) (env (encode (g (a,as))) .nil s) _ (encode a) (encode as) rfl
        (G.correct (a,as) s)
      exact hh.mono (by dsimp; omega)

def head (d : A) : Realizer (fun as : List A=>as.headD d) :=
  (listCase d first).congr (by intro as; cases as <;> rfl)

def tail : Realizer (List.tail : List A → List A) := listCase [] second

def isEmpty : Realizer (List.isEmpty : List A → Bool) := listCase true (constant false)

omit [Codec A] [Codec B] [Codec X] in
lemma countDown_drop (n : ℕ) (as : List A) : countDown (dropStep (A:=A)) n as=as.drop n := by
  induction n generalizing as with
  | zero => rfl
  | succ n ih =>
    rw [countDown,ih]
    exact List.drop_tail

def mapStepRealizer {g : X×A → B} (G : Realizer g) : Realizer (mapStep g) :=
  pair (composition second first)
    (composition (pair (composition (pair (composition second first) first) G)
      (composition second second)) listCons)

omit [Codec A] [Codec B] [Codec X] in
lemma mapStep_fold (g : X×A → B) (as : List A) (x : X) (bs : List B) :
    as.foldl (fun z a=>mapStep g (a,z)) (x,bs)=(x,(as.map (fun a=>g (x,a))).reverse++bs) := by
  induction as generalizing bs with
  | nil => rfl
  | cons a as ih =>
    change as.foldl _ (x,g (x,a)::bs)=_
    rw [ih]
    simp only [List.map_cons,List.reverse_cons,List.append_assoc,List.singleton_append]

def mapWith {g : X×A → B} (G : Realizer g) : Realizer (fun xas : X×List A=>xas.2.map (fun a=>g (xas.1,a))) :=
  (composition (composition (pair second (pair first (constant ([] : List B)))) (fold (mapStepRealizer G)))
    (composition second reverse)).congr (by
      intro xas
      change ((xas.2.foldl _ (xas.1,[])).2).reverse=_
      rw [mapStep_fold]
      simp)

def map {g : A → B} (G : Realizer g) : Realizer (List.map g) := by
  let S : Realizer (fun x : A×List B=>g x.1::x.2) := composition (pair (composition first G) second) listCons
  exact (composition (composition (pair identity (constant ([] : List B))) (fold S)) reverse).congr (by
    intro as
    change (as.foldl (fun bs a=>g a::bs) []).reverse=as.map g
    simp)

def listLength : Realizer (List.length : List A → ℕ) :=
  (composition (pair identity (constant 0))
    (fold (composition (pair second (constant 1)) add))).congr (by
      intro as
      change as.foldl (fun n (_ : A)=>n+1) 0=as.length
      have h : ∀ n,as.foldl (fun n (_ : A)=>n+1) n=n+as.length := by
        induction as with
        | nil => intro n; simp
        | cons a as ih => intro n; simp only [List.foldl_cons,ih,List.length_cons]; omega
      simpa only [Nat.zero_add] using h 0)

def append : Realizer (fun x : List A×List A=>x.1++x.2) :=
  (composition (pair (composition first reverse) second) (fold listCons)).congr (by
    intro x
    change x.1.reverse.foldl (fun bs a=>a::bs) x.2=x.1++x.2
    rw [List.foldl_flip_cons_eq_append',List.reverse_reverse])

def filter {f : A → Bool} (F : Realizer f) : Realizer (List.filter f) := by
  let S : Realizer (fun x : A×List A=>if f x.1 then x.1::x.2 else x.2) :=
    choose (composition first F) listCons second
  exact (composition (composition (pair identity (constant ([] : List A))) (fold S)) reverse).congr (by
    intro as
    change (as.foldl (fun bs a=>if f a then a::bs else bs) []).reverse=as.filter f
    have h : ∀ bs,as.foldl (fun bs a=>if f a then a::bs else bs) bs=(as.filter f).reverse++bs := by
      induction as with
      | nil => intro bs; rfl
      | cons a as ih =>
        intro bs
        cases hf : f a <;> simp [List.foldl_cons,hf,ih,List.append_assoc]
    rw [h]
    simp)
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_TreePredicate
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open TreeData TreeMachine RegisterProc TreeFunction

variable {A B : Type} [Codec A] [Codec B]

def boolNot : Realizer Bool.not :=
  (choose identity (constant false) (constant true)).congr (by intro b; cases b <;> rfl)
def boolAnd : Realizer (fun x : Bool×Bool=>x.1 && x.2) :=
  (choose first second (constant false)).congr (by intro x; cases x.1 <;> rfl)
def natEqual : Realizer (fun x : ℕ×ℕ=>decide (x.1=x.2)) :=
  (choose less (constant false)
    (choose (composition (pair second first) less) (constant false) (constant true))).congr (by
    intro x
    change (if decide (x.1<x.2) then false else if decide (x.2<x.1) then false else true)=_
    by_cases h : x.1<x.2
    · simp [h,Nat.ne_of_lt h]
    · by_cases h' : x.2<x.1
      · simp [h,h',Ne.symm (Nat.ne_of_lt h')]
      · have e : x.1=x.2 := by omega
        simp [e])

def any : Realizer (fun bs : List Bool=>bs.any id) :=
  (composition (pair identity (constant false))
    (fold (choose first (constant true) second))).congr (by
      intro bs
      change bs.foldl (fun z b=>if b then true else z) false=bs.any id
      have h : ∀ z, bs.foldl (fun z b=>if b then true else z) z=(bs.any id || z) := by
        induction bs with
        | nil => intro z; rfl
        | cons b bs ih =>
          intro z
          simp only [List.foldl_cons,ih,List.any_cons]
          cases b <;> cases bs.any id <;> cases z <;> rfl
      rw [h]
      cases bs.any id <;> rfl)

def membership : Realizer (fun x : List ℕ×ℕ=>decide (x.2∈x.1)) :=
  (composition (composition (pair second first) (mapWith natEqual)) any).congr (by
    intro x
    simp only [Function.comp_apply,List.any_map]
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true,Function.comp_apply,decide_eq_true_eq,id_eq]
    constructor
    · rintro ⟨a,ha,e⟩; simpa [←e] using ha
    · intro h; exact ⟨x.2,h,rfl⟩)

def listSum : Realizer (List.sum : List ℕ → ℕ) :=
  (composition (pair identity (constant 0)) (fold add)).congr (by
    intro as
    change as.foldl (fun n a=>a+n) 0=as.sum
    have h : ∀ z,as.foldl (fun n a=>a+n) z=as.sum+z := by
      induction as with
      | nil => intro z; simp
      | cons a as ih => intro z; simp only [List.foldl_cons,ih,List.sum_cons]; omega
    simpa using h 0)

def listProd : Realizer (List.prod : List ℕ → ℕ) :=
  (composition (pair identity (constant 1)) (fold multiply)).congr (by
    intro as
    change as.foldl (fun n a=>a*n) 1=as.prod
    have h : ∀ z,as.foldl (fun n a=>a*n) z=as.prod*z := by
      induction as with
      | nil => intro z; simp
      | cons a as ih => intro z; simp only [List.foldl_cons,ih,List.prod_cons]; ring
    simpa using h 1)

end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Arithmetic_TreeGCD
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open TreeData TreeMachine RegisterProc TreeFunction

def digits : Realizer Nat.bits where
  program := identity.program (A:=ℕ)
  cost := fun _=>1
  correct := fun a s=>identity.correct a s

def bitSize : Realizer Nat.size :=
  (composition digits listLength).congr (fun a=>Nat.size_eq_bits_len a)

def sortedPairRealizer : Realizer sortedPair :=
  (choose less (pair second first) identity).congr (fun x=>by simp [sortedPair])

def gcdStepRealizer : Realizer gcdStep :=
  (choose (composition (pair second (constant 0)) natEqual) identity (pair second remainder)).congr
    (fun x=>by simp only [gcdStep,Function.comp_apply,decide_eq_true_eq,id_eq])

def gcd : Realizer (fun x : ℕ×ℕ=>x.1.gcd x.2) :=
  (composition (composition (pair (composition (pair (composition first bitSize)
    (composition second bitSize)) add) sortedPairRealizer)
    (iterateDown (composition second gcdStepRealizer))) first).congr (by
      intro x
      change (countDown gcdIterStep (x.1.size+x.2.size) (sortedPair x)).1=x.1.gcd x.2
      rw [gcdIter_result _ _ (sortedPair_order x) (by rw [sortedPair_size]),sortedPair_gcd])

end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Arithmetic_TreeFraction
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeFraction
open TreeTyped

def normalizeRealizer : Realizer normalize := by
  let G := gcd
  let Q := pair (composition (pair first G) quotient) (composition (pair second G) quotient)
  exact (choose (composition (pair second (constant 0)) natEqual) (constant (0,1)) Q).congr
    (fun x=>by simp only [normalize,Function.comp_apply,decide_eq_true_eq])

def mulRealizer : Realizer mul :=
  composition (pair (composition (pair (composition first first) (composition second first)) multiply)
    (composition (pair (composition first second) (composition second second)) multiply)) normalizeRealizer
def addRealizer : Realizer add :=
  composition (pair (composition (pair
    (composition (pair (composition first first) (composition second second)) multiply)
    (composition (pair (composition second first) (composition first second)) multiply)) TreeTyped.add)
    (composition (pair (composition first second) (composition second second)) multiply)) normalizeRealizer
def divRealizer : Realizer div :=
  composition (pair (composition (pair (composition first first) (composition second second)) multiply)
    (composition (pair (composition first second) (composition second first)) multiply)) normalizeRealizer
def lessRealizer : Realizer less :=
  composition (pair (composition (pair (composition first first) (composition second second)) multiply)
    (composition (pair (composition second first) (composition first second)) multiply)) TreeTyped.less

end MatchingFPRAS.TreeFraction

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Complexity_TreePolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open TreeData TreeFunction Polynomial

variable {A B C : Type} [Codec A] [Codec B] [Codec C]

@[simp] lemma weight_nil : weight ([] : List A)=1 := rfl
@[simp] lemma weight_cons (a : A) (as : List A) : weight (a::as)=1+weight a+weight as := by simp [weight]; omega
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Sampling_TreeDPEntry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
variable {A B C : Type} [Codec A] [Codec B] [Codec C]
def Realizer.fst {f : A → B×C} (F : Realizer f) : Realizer (fun a=>(f a).1) := composition F first
def Realizer.snd {f : A → B×C} (F : Realizer f) : Realizer (fun a=>(f a).2) := composition F second
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Sampling_TreeDPCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
variable {A B : Type} [Codec A] [Codec B]
def filterWith {f : A×B → Bool} (F : Realizer f) :
    Realizer (fun x : A×List B=>x.2.filter fun b=>f (x.1,b)) :=
  (composition (composition (mapWith (pair second F)) (filter second)) (map first)).congr (by
    intro x
    simp only [Function.comp_apply,List.filter_map,List.map_map]
    simp [Function.comp_def])
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_TreeFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

variable {A B C D : Type} [Codec A] [Codec B] [Codec C] [Codec D]

def Realizer.recode {f : C → D} (F : Realizer f) (i : A → C) (g : A → B)
    (hi : ∀ a,encode (i a)=encode a) (ho : ∀ a,encode (f (i a))=encode (g a)) : Realizer g where
  program := F.program
  cost := fun a=>F.cost (i a)
  correct := by
    intro a s
    have h:=F.correct (i a) s
    rw [hi,ho] at h
    exact h

instance finsetCodec [LinearOrder A] : Codec (Finset A) := ⟨fun s=>encode (s.sort (·≤·))⟩
@[simp] lemma encode_finset [LinearOrder A] (s : Finset A) : encode s=encode (s.sort (·≤·)) := rfl
@[simp] lemma weight_finset [LinearOrder A] (s : Finset A) : weight s=weight (s.sort (·≤·)) := rfl

end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_TreeFiniteOps
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

variable {A B C : Type} [Codec A] [Codec B] [Codec C]

def all : Realizer (fun bs : List Bool=>bs.all id) :=
  (composition (composition (map boolNot) any) boolNot).congr (by
    intro bs
    change (!((bs.map Bool.not).any id))=bs.all id
    induction bs with
    | nil => rfl
    | cons b bs ih => cases b <;> simp_all)

def pairEqual [DecidableEq A] [DecidableEq B]
    (E : Realizer (fun x : A×A=>decide (x.1=x.2)))
    (F : Realizer (fun x : B×B=>decide (x.1=x.2))) :
    Realizer (fun x : (A×B)×(A×B)=>decide (x.1=x.2)) :=
  (composition (pair (composition (pair first.fst second.fst) E)
    (composition (pair first.snd second.snd) F)) boolAnd).congr (by
      intro x
      apply Bool.eq_iff_iff.mpr
      simp only [Function.comp_apply,Bool.and_eq_true,decide_eq_true_eq,Prod.ext_iff])

def leNat : Realizer (fun x : ℕ×ℕ=>decide (x.1≤x.2)) :=
  (composition (composition (pair second first) less) boolNot).congr (by
    intro x
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply,Bool.not_eq_true',decide_eq_false_iff_not,decide_eq_true_eq,not_lt])
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_TreeFastLookup
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

variable {A : Type} [Codec A]

def minNat : Realizer (fun x : ℕ×ℕ=>min x.1 x.2) :=
  (choose leNat first second).congr (by intro x; simp only [decide_eq_true_eq]; exact (min_def x.1 x.2).symm)

def dropInit : Realizer (fun x : List A×ℕ=>(min x.2 x.1.length,x.1)) :=
  pair (composition (pair second (composition first listLength)) minNat) first

def dropFast : Realizer (fun x : List A×ℕ=>x.1.drop x.2) :=
  (composition dropInit (iterateDown (composition second tail))).congr (by
    intro x
    change countDown dropStep (min x.2 x.1.length) x.1=x.1.drop x.2
    rw [countDown_drop]
    by_cases h : x.2≤x.1.length
    · rw [min_eq_left h]
    · rw [min_eq_right (by omega),List.drop_length,List.drop_eq_nil_of_le (by omega)])

def getDFast (d : A) : Realizer (fun x : List A×ℕ=>x.1.getD x.2 d) :=
  (composition dropFast (head d)).congr (by
    intro x
    simp only [Function.comp_apply, List.headD_eq_head?_getD, List.head?_drop,
      List.getD_eq_getElem?_getD])

end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileExchangeProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A binary list program for a small-profile unit exchange -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped Polynomial

def exchangeEntryRealizer : Realizer exchangeEntry := by
  let V : Realizer (fun z : ExchangeInput×ℕ => z.1.1) := composition first first
  let A : Realizer (fun z : ExchangeInput×ℕ => z.2) := second
  let I : Realizer (fun z : ExchangeInput×ℕ => z.1.2.1) :=
    composition (composition first second) first
  let J : Realizer (fun z : ExchangeInput×ℕ => z.1.2.2) :=
    composition (composition first second) second
  let addOne := choose (composition (pair A I) natEqual) (constant 1) (constant 0)
  let subOne := choose (composition (pair A J) natEqual) (constant 1) (constant 0)
  exact (composition (pair (composition
    (pair (composition (pair V A) (getDFast 0)) addOne) add) subOne) subtract).congr
      (fun z => by simp only [Function.comp_apply,exchangeEntry,decide_eq_true_eq])

def listExchangeRealizer : Realizer listExchange :=
  composition (pair identity (composition (composition first listLength) range))
    (mapWith exchangeEntryRealizer)

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_TreeFiniteCollections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

variable {A B C : Type} [Codec A] [Codec B] [Codec C]
omit [Codec A] [Codec B] [Codec C] in
lemma fold_prepend (as : List (List A)) (bs : List A) :
    as.foldl (fun bs a=>a++bs) bs=as.reverse.flatten++bs := by
  induction as generalizing bs with
  | nil => rfl
  | cons a as ih => simp [List.foldl_cons,ih,List.flatten_append,List.append_assoc]

def flatten : Realizer (List.flatten (α:=A)) :=
  (composition (pair reverse (constant ([] : List A))) (fold append)).congr (by
    intro as
    change as.reverse.foldl (fun bs a=>a++bs) []=as.flatten
    rw [fold_prepend,List.reverse_reverse,List.append_nil])

def flatMapPoly {f : A → List B} (F : Realizer f) : Realizer (List.flatMap f) :=
  (composition (map F) flatten).congr (by intro as; rfl)
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_PaddedCompletions
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Zero penalties are exactly padded residual completions

Retain the small x,y views and fill every large cell with the balanced
pair (A,B-A). For an assignment supported on large cells, the full margin
equations are precisely the padded residual margin equations. The small
positive-part penalties enforce the original nonnegative residual tests.
-/

namespace ContingencyTables.PaddedCompletions

open scoped BigOperators Classical
open RowColumnPenalties NestedPenaltyApplication BalancedBox

variable {I J : Type*} [Fintype I] [Fintype J]

omit [Fintype I] [Fintype J] in
lemma profile_inBox (small : I → J → Bool) (B X Y A : I → J → ℕ)
    (hX : ∀ i j, small i j=true → X i j ≤ B i j)
    (hY : ∀ i j, small i j=true → Y i j ≤ B i j)
    (hA : ∀ i j, small i j=false → A i j ≤ B i j) :
    InBox (fun u => B u.1.1 u.1.2) (profile small B X Y A) := by
  rintro ⟨⟨i,j⟩,t⟩
  cases t <;> cases hs : small i j <;> simp only [profile,hs,ite_true, if_true]
  · exact hA i j hs
  · exact hX i j hs
  · exact Nat.sub_le _ _
  · exact hY i j hs

/-- No positivity or balance assumption is imposed on the retained
small profile. Thus this exact identity covers transversals and defects. -/
theorem zero_penalty_iff_padded_completion (small : I → J → Bool) (B X Y A : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (hA : Supported small A)
    (hX : ∀ i j, small i j=true → X i j ≤ B i j)
    (hY : ∀ i j, small i j=true → Y i j ≤ B i j)
    (hcap : ∀ i j, small i j=false → A i j ≤ B i j) :
    penalty RowColumnPenalties.cellLine (smallCoordinate small)
      (fullOffset B (fun i => r i+rowLargeCount small i*L) (fun j => c j+columnLargeCount small j*L))
      viewSlope (smallOffset small B r c) viewSlope (profile small B X Y A)=0 ↔
      OriginalResidualsNonnegative small B X Y r c ∧
        HasMargins A (fun i => r i-smallRow small X i+rowLargeCount small i*L)
          (fun j => c j-smallColumn small B Y j+columnLargeCount small j*L) := by
  rw [penalty_zero_iff small B r _ c _ _ (profile_inBox small B X Y A hX hY hcap)]
  simp only [FullConditions,profile_row small B X Y A hA,profile_column small B X Y A hA hcap,
    profile_small_row,profile_small_column,OriginalResidualsNonnegative,HasMargins]
  constructor
  · rintro ⟨hr,hc,hsr,hsc⟩
    refine ⟨⟨hsr,hsc⟩,?_,?_⟩
    · intro i; have h := hr i; have hs := hsr i; omega
    · intro j; have h := hc j; have hs := hsc j; omega
  · rintro ⟨⟨hsr,hsc⟩,hr,hc⟩
    refine ⟨?_,?_,hsr,hsc⟩
    · intro i; have h := hr i; have hs := hsr i; omega
    · intro j; have h := hc j; have hs := hsc j; omega

end ContingencyTables.PaddedCompletions

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_CompletionCounts
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The literal zero-penalty sum counts residual completions

Finite balanced large-cell assignments are represented by bounded natural
matrices supported on the large cells. The zero-penalty predicate is
equivalent to the actual padded residual table equations. An explicit
entry bound proves when the formal capacities exclude no completion.
-/

namespace ContingencyTables.CompletionCounts

open scoped BigOperators Classical
open RowColumnPenalties PaddedCompletions NestedPenaltyApplication

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def completionEquiv (small : I → J → Bool) (B X Y : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ)
    (hX : ∀ i j, small i j=true → X i j ≤ B i j)
    (hY : ∀ i j, small i j=true → Y i j ≤ B i j)
    (hres : OriginalResidualsNonnegative small B X Y r c)
    (hB : ∀ i j, small i j=false → (∑ k, (r k-smallRow small X k+rowLargeCount small k*L)) ≤ B i j) :
    ZeroAssignments small B X Y r c L ≃
      LargeCompletion small (fun i => r i-smallRow small X i+rowLargeCount small i*L)
        (fun j => c j-smallColumn small B Y j+columnLargeCount small j*L) where
  toFun a := ⟨⟨assignmentMatrix a.val,
    ((zero_penalty_iff_padded_completion small B X Y (assignmentMatrix a.val) r c L
      (assignment_supported a.val) hX hY (fun i j _ => assignment_bounded a.val i j)).mp a.property).2⟩,
    assignment_supported a.val⟩
  invFun A := by
    have hcap : ∀ i j, A.val.val i j ≤ B i j := by
      intro i j
      cases hs : small i j
      · exact (entry_le_total A.val.property i j).trans (hB i j hs)
      · rw [A.property i j hs]
        exact Nat.zero_le _
    let a : Assignment small B := ⟨fun i j => ⟨A.val.val i j,Nat.lt_succ_of_le (hcap i j)⟩,
      A.property⟩
    refine ⟨a,?_⟩
    exact (zero_penalty_iff_padded_completion small B X Y A.val.val r c L A.property hX hY
      (fun i j _ => hcap i j)).mpr ⟨hres,A.val.property⟩
  left_inv a := by
    apply Subtype.ext
    apply Subtype.ext
    funext i j
    apply Fin.ext
    rfl
  right_inv A := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- The finite hard marginal is exactly the padded completion count;
if an original residual is negative every zero-penalty term vanishes. -/
theorem hard_count_eq (small : I → J → Bool) (B X Y : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ)
    (hX : ∀ i j, small i j=true → X i j ≤ B i j)
    (hY : ∀ i j, small i j=true → Y i j ≤ B i j)
    (hB : ∀ i j, small i j=false → (∑ k, (r k-smallRow small X k+rowLargeCount small k*L)) ≤ B i j) :
    (∑ a : Assignment small B, if fullPenalty small B X Y (assignmentMatrix a) r c L=0 then (1:ℝ) else 0) =
      if OriginalResidualsNonnegative small B X Y r c then
        (Fintype.card (LargeCompletion small (fun i => r i-smallRow small X i+rowLargeCount small i*L)
          (fun j => c j-smallColumn small B Y j+columnLargeCount small j*L)):ℝ) else 0 := by
  by_cases hres : OriginalResidualsNonnegative small B X Y r c
  · rw [ite_eq_left hres]
    calc
      _ = (Fintype.card (ZeroAssignments small B X Y r c L):ℝ) := by
        rw [Finset.sum_boole,← Fintype.card_subtype]
        exact congrArg (fun n : ℕ => (n:ℝ)) (Fintype.card_congr
          (α := {a : Assignment small B // fullPenalty small B X Y (assignmentMatrix a) r c L=0})
          (β := ZeroAssignments small B X Y r c L) (Equiv.refl _))
      _ = _ := congrArg (fun n : ℕ => (n:ℝ))
        (Fintype.card_congr (completionEquiv small B X Y r c L hX hY hres hB))
  · rw [ite_eq_right hres]
    apply Finset.sum_eq_zero
    intro a _
    apply ite_eq_right
    intro hz
    exact hres ((zero_penalty_iff_padded_completion small B X Y (assignmentMatrix a) r c L
      (assignment_supported a) hX hY (fun i j _ => assignment_bounded a i j)).mp hz).1

end ContingencyTables.CompletionCounts

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperProfiles
attribute [-instance] _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The first paper's supported assignments are its physical large choices -/

namespace ContingencyTables.FirstPaperProfiles

open scoped BigOperators Classical
open LargePairEnumeration PhysicalLargeProfiles CompletionCounts

variable {I J : Type*}

noncomputable def smallView (small : I → J → Bool)
    (z : SmallView (fun a : I×J => small a.1 a.2) → ℕ)
    (v : Bool) (i : I) (j : J) : ℕ :=
  if hs : small i j=true then z (⟨(i,j),hs⟩,v) else 0

/-- A choice for each large cell extends uniquely by zero on small cells,
exactly as used by the manuscript's supported residual completion sum. -/
noncomputable def supportedAssignmentEquiv (small : I → J → Bool) (B : I → J → ℕ) :
    PhysicalAssignments (fun a : I×J => small a.1 a.2) (fun a => B a.1 a.2) ≃
      Assignment small B where
  toFun a := ⟨fun i j => if hs : small i j=true then 0
      else a ⟨(i,j),Bool.eq_false_iff.mpr hs⟩,
    by intro i j hs; simp only [hs,dite_eq_left,Fin.val_zero]⟩
  invFun a l := a.val l.val.1 l.val.2
  left_inv a := by
    funext l
    have hs : small l.val.1 l.val.2=false := l.property
    simp [hs]
  right_inv a := by
    apply Subtype.ext
    funext i j
    by_cases hs : small i j=true
    · apply Fin.ext
      simp [hs,a.property i j hs]
    · simp [hs]

lemma physicalProfile_supported (small : I → J → Bool) (B : I → J → ℕ)
    (z : SmallView (fun a : I×J => small a.1 a.2) → ℕ)
    (a : Assignment small B) :
    physicalProfile (fun a : I×J => small a.1 a.2) (fun a => B a.1 a.2) z
      ((supportedAssignmentEquiv small B).symm a)=
      PaddedCompletions.profile small B (smallView small z false) (smallView small z true)
        (assignmentMatrix a) := by
  funext u
  rcases u with ⟨⟨i,j⟩,v⟩
  by_cases hs : small i j=true
  · cases v <;> simp [physicalProfile,hs,PaddedCompletions.profile,smallView]
  · cases v <;> simp [physicalProfile,hs,PaddedCompletions.profile,
      supportedAssignmentEquiv,assignmentMatrix] <;> rfl

variable [Fintype I] [Fintype J]

/-- The finite product used in the signature proof counts exactly the
supported assignments used in the residual completion equivalence. -/
theorem physicalHardSum_eq_supported (small : I → J → Bool) (B : I → J → ℕ)
    (z : SmallView (fun a : I×J => small a.1 a.2) → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) :
    (∑ a : PhysicalAssignments (fun a : I×J => small a.1 a.2) (fun a => B a.1 a.2),
      NestedPenaltyApplication.hardWeight RowColumnPenalties.cellLine
        (RowColumnPenalties.smallCoordinate small)
        (RowColumnPenalties.fullOffset B
          (fun i => r i+PaddedCompletions.rowLargeCount small i*L)
          (fun j => c j+PaddedCompletions.columnLargeCount small j*L)) RowColumnPenalties.viewSlope
        (RowColumnPenalties.smallOffset small B r c) RowColumnPenalties.viewSlope
        (physicalProfile (fun a : I×J => small a.1 a.2) (fun a => B a.1 a.2) z a))=
      ∑ a : Assignment small B,
        if fullPenalty small B (smallView small z false) (smallView small z true)
          (assignmentMatrix a) r c L=0 then (1:ℝ) else 0 := by
  apply Fintype.sum_equiv (supportedAssignmentEquiv small B)
  intro a
  have he := physicalProfile_supported small B z ((supportedAssignmentEquiv small B) a)
  rw [Equiv.symm_apply_apply] at he
  rw [he]
  rfl

end ContingencyTables.FirstPaperProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperPhysicalMarginal
attribute [-instance] _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The first paper's physical hard marginal and its proved raw signature

This bridges the finite balanced-pair elimination theorem to the actual
supported padded-completion count, in the original row/column coordinates.
-/

namespace ContingencyTables.FirstPaperPhysicalMarginal

open scoped BigOperators Classical
open LargePairEnumeration PhysicalLargeProfiles FirstPaperProfiles CompletionCounts
open RowColumnPenalties PaddedCompletions NestedPenaltyApplication BalancedBox

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def hardMarginal (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ)
    (z : SmallView (fun a : I×J => small a.1 a.2) → ℕ) : ℝ :=
  ∑ a : PhysicalAssignments (fun a : I×J => small a.1 a.2) (fun a => B a.1 a.2),
    fullHardFamily small B r c L
      (physicalProfile (fun a : I×J => small a.1 a.2) (fun a => B a.1 a.2) z a)

/-- The exact finite marginal agrees with the original supported padded
completion count, on its actual capacity box. -/
theorem hardMarginal_eq_completionCount (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ)
    (z : SmallView (fun a : I×J => small a.1 a.2) → ℕ)
    (hz : ∀ u, z u≤B u.1.val.1 u.1.val.2)
    (hB : ∀ i j, small i j=false →
      (∑ k, (r k-smallRow small (smallView small z false) k+rowLargeCount small k*L))≤B i j) :
    hardMarginal small B r c L z=
      if OriginalResidualsNonnegative small B (smallView small z false) (smallView small z true) r c
      then (Fintype.card (LargeCompletion small
        (fun i => r i-smallRow small (smallView small z false) i+rowLargeCount small i*L)
        (fun j => c j-smallColumn small B (smallView small z true) j+columnLargeCount small j*L)):ℝ)
      else 0 := by
  unfold hardMarginal fullHardFamily
  rw [physicalHardSum_eq_supported]
  apply hard_count_eq
  · intro i j hs
    simpa only [smallView,hs,dite_eq_left] using hz (⟨(i,j),hs⟩,false)
  · intro i j hs
    simpa only [smallView,hs,dite_eq_left] using hz (⟨(i,j),hs⟩,true)
  · exact hB

end ContingencyTables.FirstPaperPhysicalMarginal

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_PhysicalCompletionFibres
attribute [-instance] _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Completion-retaining fibres of the literal hard marginal

Each physical large-cell assignment with zero penalty is exactly one pair
of full row and column views. The retained small profile is prescribed,
while large entries agree. No completion multiplicity is discarded.
-/

namespace ContingencyTables.PhysicalCompletionFibres

open scoped BigOperators Classical
open LargePairEnumeration PhysicalLargeProfiles RowColumnPenalties
open FirstPaperPhysicalMarginal PaddedCompletions NestedPenaltyApplication

variable {I J : Type*} [Fintype I] [Fintype J]

abbrev SmallProfile (small : I → J → Bool) :=
  SmallView (fun a : I×J => small a.1 a.2) → ℕ

/-- Full row/column views with one prescribed small profile. -/
def CompletionFibre (small : I → J → Bool) (B : I → J → ℕ)
    (r rbar : I → ℕ) (c cbar : J → ℕ) (z : SmallProfile small) :=
  {Z : RowColumnPair rbar cbar //
    (∀ i, smallRow small Z.val.1 i ≤ r i) ∧
    (∀ j, smallColumnView small Z.val.2 j ≤ c j) ∧
    (∀ i j (hs : small i j=true),
      Z.val.1 i j=z (⟨(i,j),hs⟩,false) ∧
      Z.val.2 i j=B i j-z (⟨(i,j),hs⟩,true)) ∧
    (∀ i j, small i j=false → Z.val.1 i j=Z.val.2 i j) ∧
    (∀ i j, small i j=false → Z.val.1 i j ≤ B i j)}

omit [Fintype I] [Fintype J] in
lemma physical_inBox (small : I → J → Bool) (B : I → J → ℕ)
    (z : SmallProfile small) (hz : ∀ u, z u ≤ B u.1.val.1 u.1.val.2)
    (a : PhysicalAssignments (fun a : I×J => small a.1 a.2) (fun a => B a.1 a.2)) :
    BalancedBox.InBox (fun u => B u.1.1 u.1.2)
      (physicalProfile (fun a : I×J => small a.1 a.2) (fun a => B a.1 a.2) z a) := by
  rintro ⟨⟨i,j⟩,b⟩
  by_cases hs : small i j=true
  · simpa only [physicalProfile,hs,dite_eq_left] using hz (⟨(i,j),hs⟩,b)
  · cases b
    · simpa only [physicalProfile,hs,dite_eq_right,Bool.false_eq_true,↓reduceIte,↓reduceDIte] using
        Nat.le_of_lt_succ (a ⟨(i,j),Bool.eq_false_iff.mpr hs⟩).isLt
    · simp only [physicalProfile,hs,↓reduceIte]
      exact Nat.sub_le _ _

noncomputable def fibreAssignment {small : I → J → Bool} {B : I → J → ℕ}
    {r rbar : I → ℕ} {c cbar : J → ℕ} {z : SmallProfile small}
    (Z : CompletionFibre small B r rbar c cbar z) :
    PhysicalAssignments (fun a : I×J => small a.1 a.2) (fun a => B a.1 a.2) :=
  fun a => ⟨Z.val.val.1 a.val.1 a.val.2,
    Nat.lt_succ_of_le (Z.property.2.2.2.2 _ _ a.property)⟩

lemma fibreAssignment_views {small : I → J → Bool} {B : I → J → ℕ}
    {r rbar : I → ℕ} {c cbar : J → ℕ} {z : SmallProfile small}
    (Z : CompletionFibre small B r rbar c cbar z) :
    let p := physicalProfile (fun a : I×J => small a.1 a.2)
      (fun a => B a.1 a.2) z (fibreAssignment Z)
    rowView p=Z.val.val.1 ∧ columnView B p=Z.val.val.2 := by
  dsimp only
  constructor
  · funext i j
    by_cases hs : small i j=true
    · simpa only [rowView,physicalProfile,hs,dite_eq_left] using
        (Z.property.2.2.1 i j hs).1.symm
    · simp only [rowView,physicalProfile,hs,Bool.false_eq_true,↓reduceIte,↓reduceDIte]
      rfl
  · funext i j
    by_cases hs : small i j=true
    · simpa only [columnView,physicalProfile,hs,dite_eq_left] using
        (Z.property.2.2.1 i j hs).2.symm
    · simp only [columnView,physicalProfile,hs,Bool.false_eq_true,↓reduceIte,↓reduceDIte,fibreAssignment]
      rw [Nat.sub_sub_self (Z.property.2.2.2.2 i j (Bool.eq_false_iff.mpr hs))]
      exact Z.property.2.2.2.1 i j (Bool.eq_false_iff.mpr hs)

noncomputable def zeroPhysicalEquiv (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (z : SmallProfile small)
    (hz : ∀ u, z u ≤ B u.1.val.1 u.1.val.2) :
    {a : PhysicalAssignments (fun a : I×J => small a.1 a.2) (fun a => B a.1 a.2) //
      penalty cellLine (smallCoordinate small)
        (fullOffset B (fun i => r i+rowLargeCount small i*L)
          (fun j => c j+columnLargeCount small j*L)) viewSlope
        (smallOffset small B r c) viewSlope
        (physicalProfile (fun a : I×J => small a.1 a.2) (fun a => B a.1 a.2) z a)=0} ≃
      CompletionFibre small B (r) (fun i => r i+rowLargeCount small i*L)
        c (fun j => c j+columnLargeCount small j*L) z where
  toFun a := by
    let p := physicalProfile (fun a : I×J => small a.1 a.2) (fun a => B a.1 a.2) z a.val
    have hp := (penalty_zero_iff small B r _ c _ p (physical_inBox small B z hz a.val)).mp a.property
    refine ⟨⟨(rowView p,columnView B p),hp.1,hp.2.1⟩,hp.2.2.1,hp.2.2.2,?_,?_,?_⟩
    · intro i j hs
      simp [p,rowView,columnView,physicalProfile,hs]
    · intro i j hs
      have hcap := Nat.le_of_lt_succ (a.val ⟨(i,j),hs⟩).isLt
      simpa only [p,rowView,columnView,physicalProfile,hs,Bool.false_eq_true,dite_eq_right,
        ↓reduceIte,↓reduceDIte,Prod.fst,Prod.snd] using (Nat.sub_sub_self hcap).symm
    · intro i j hs
      simpa only [p,rowView,physicalProfile,hs,Bool.false_eq_true,dite_eq_right,
        ↓reduceIte,↓reduceDIte,Prod.fst] using Nat.le_of_lt_succ (a.val ⟨(i,j),hs⟩).isLt
  invFun Z := by
    refine ⟨fibreAssignment Z,?_⟩
    have hp := fibreAssignment_views Z
    apply (penalty_zero_iff small B r _ c _ _ (physical_inBox small B z hz _)).mpr
    unfold FullConditions
    rw [hp.1,hp.2]
    exact ⟨Z.val.property.1,Z.val.property.2,Z.property.1,Z.property.2.1⟩
  left_inv a := by
    apply Subtype.ext
    funext l
    apply Fin.ext
    simp only [fibreAssignment,rowView,physicalProfile,l.property,Bool.false_eq_true,
      ↓reduceIte,↓reduceDIte]
  right_inv Z := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext (fibreAssignment_views Z).1 (fibreAssignment_views Z).2

end ContingencyTables.PhysicalCompletionFibres

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallContextFibres
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual small-prefix fibres and conditional repair

Only small cells in the row-major prefix are fixed. Large completions
remain free and retain their full counting multiplicity.
-/

namespace ContingencyTables.SmallContextFibres

open scoped BigOperators Classical
open PaddedCompletions CompletionCounts FirstPaperProfiles
open PhysicalCompletionFibres FirstPaperPhysicalMarginal LargePairEnumeration

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

abbrev BoundedProfile (small : I → J → Bool) (B : I → J → ℕ) :=
  (u : SmallView (fun a : I×J => small a.1 a.2)) → Fin (B u.1.val.1 u.1.val.2+1)

def naturalProfile {small : I → J → Bool} {B : I → J → ℕ}
    (z : BoundedProfile small B) : SmallProfile small := fun u => (z u).val

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
lemma naturalProfile_bounded {small : I → J → Bool} {B : I → J → ℕ}
    (z : BoundedProfile small B) (u) : naturalProfile z u ≤ B u.1.val.1 u.1.val.2 :=
  Nat.le_of_lt_succ (z u).isLt

noncomputable def smallQ (small : I → J → Bool) (B : I → J → ℕ)
    (z : SmallProfile small) (i : I) (j : J) : ℕ :=
  if hs : small i j=true then B i j-z (⟨(i,j),hs⟩,true) else 0

end ContingencyTables.SmallContextFibres

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallGraphProfiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The physical small graph and contextual unit exchanges -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextFibres
open PhysicalCompletionFibres LargePairEnumeration BalancedFamily BalancedBox
open FirstPaperProfiles FactorialSignatures

universe u

variable {I J : Type u} [LinearOrder I] [LinearOrder J]

def Balanced (small : I → J → Bool) (B : I → J → ℕ) (z : SmallProfile small) : Prop :=
  ∀ i j, smallView small z false i j=smallQ small B z i j

def SingleDefect (small : I → J → Bool) (B : I → J → ℕ) (z : SmallProfile small) : Prop :=
  ∃ s t : I×J, small s.1 s.2=true ∧ small t.1 t.2=true ∧
    IsDefect (smallView small z false) (smallQ small B z) s t

def Pattern (small : I → J → Bool) (B : I → J → ℕ) (z : SmallProfile small) : Prop :=
  Balanced small B z ∨ SingleDefect small B z

abbrev Profiles (small : I → J → Bool) (B : I → J → ℕ) :=
  {z : BoundedProfile small B // Pattern small B (naturalProfile z)}

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileRepairProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial binary program for the literal small-profile repair -/

namespace ContingencyTables.SmallGraphProfiles
open scoped Classical
open SmallContextCoordinates PhysicalCompletionFibres FirstPaperProfiles
open ProfilePrograms

noncomputable section
universe u
variable {I J : Type u} [LinearOrder I] [LinearOrder J]
variable (small : I → J → Bool) {n : ℕ} (e : Fin n ≃ Cells small)

def viewList (v : SmallProfile small) (b : Bool) : List ℕ :=
  List.ofFn (fun i => v (e i,b))

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_TreeColex
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
variable {A B : Type} [Codec A] [Codec B] [LinearOrder A] [LinearOrder B]

def boolOr : Realizer (fun x : Bool×Bool=>x.1 || x.2) :=
  (choose first (constant true) second).congr (by intro x; cases x.1 <;> rfl)
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_TreeSum
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
variable {A B C D : Type} [Codec A] [Codec B] [Codec C] [Codec D]

instance instCodecOptionOfInhabited [Inhabited A] : Codec (Option A) := ⟨fun x=>encode (optionRep x)⟩
def some [Inhabited A] : Realizer (Option.some : A→Option A) :=
  (pair (constant true) identity).recode id Option.some (fun _=>rfl) (fun _=>rfl)

def optionCases [Inhabited A] {f : C→D} {g : C×A→D} (F : Realizer f) (G : Realizer g) :
    Realizer (fun x : C×Option A=>x.2.elim (f x.1) (fun a=>g (x.1,a))) :=
  (choose second.fst (composition (pair first second.snd) G) (composition first F)).recode
    (fun x : C×Option A=>(x.1,optionRep x.2))
    (fun x=>x.2.elim (f x.1) (fun a=>g (x.1,a))) (fun _=>rfl) (by intro x; cases x.2 <;> rfl)
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_TreeIndex
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

variable {A : Type} [Codec A] [DecidableEq A] [BEq A] [LawfulBEq A]

def indexStepRealizer (E : Realizer (fun x : A×A=>decide (x.1=x.2))) : Realizer (indexStep (A:=A)) :=
  (pair second.fst (choose (composition (pair second.fst first) E) (constant 0)
    (composition second.snd successor))).congr (fun x=>by simp only [indexStep,Function.comp_apply,decide_eq_true_eq,Nat.succ_eq_add_one])

omit [Codec A] [DecidableEq A] [BEq A] [LawfulBEq A] in
lemma indexStep_fold_reverse [Codec A] [DecidableEq A] [BEq A] [LawfulBEq A]
    (xs : List A) (a : A) :
    (xs.reverse.foldl (fun z x=>indexStep (x,z)) (a,0)).2=xs.idxOf a := by
  rw [List.foldl_reverse]
  have h : xs.foldr (fun x z=>indexStep (x,z)) (a,0)=(a,xs.idxOf a) := by
    induction xs with
    | nil=>simp
    | cons x xs ih=>
      rw [List.foldr_cons,ih]
      simp only [indexStep,List.idxOf_cons]
      by_cases he : a=x
      · subst x; simp
      · simp [he,beq_eq_false_iff_ne.mpr (Ne.symm he)]
  rw [h]

def indexOf (E : Realizer (fun x : A×A=>decide (x.1=x.2))) :
    Realizer (fun x : A×List A=>x.2.idxOf x.1) :=
  (composition (composition (pair (composition second reverse) (pair first (constant 0)))
    (fold (indexStepRealizer E))) second).congr (fun x=>indexStep_fold_reverse x.2 x.1)
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallCellIndexProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executable indices for small cells and their crossing cells -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

def cellLookupRealizer : Realizer (fun z : (ℕ×ℕ)×List (ℕ×ℕ) => z.2.idxOf z.1) :=
  indexOf (pairEqual natEqual natEqual)

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallCellCatalogProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Enumerating the actual small cells from binary margins -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped Polynomial

def pairAtRealizer : Realizer pairAt :=
  composition (pair second first) (pair quotient remainder)

def cellPairCodes : Realizer (fun z : List ℕ×List ℕ =>
    List.range (z.1.length*z.2.length)) :=
  composition (composition (pair (composition first listLength)
    (composition second listLength)) multiply) range

def cellPairsRealizer : Realizer cellPairs :=
  composition (pair (composition second listLength) cellPairCodes) (mapWith pairAtRealizer)

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_TreeListMore
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
variable {A B X : Type} [Codec A] [Codec B] [Codec X]

def minimum : Realizer (fun x : ℕ×ℕ=>min x.1 x.2) :=
  (choose less first second).congr (by intro x; simp only [decide_eq_true_eq]; split_ifs with h <;> omega)
def maximum : Realizer (fun x : ℕ×ℕ=>max x.1 x.2) :=
  (choose less second first).congr (by intro x; simp only [decide_eq_true_eq]; split_ifs with h <;> omega)

end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Sampling_TreeCategorical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeFraction
open TreeTyped

def sumRealizer : Realizer sum :=
  (composition (pair (identity (A:=List Fraction)) (constant (0,1))) (fold addRealizer)).congr (fun _=>rfl)

end MatchingFPRAS.TreeFraction

namespace MatchingFPRAS.TreeTyped

def bitValue : Realizer StackAddition.value :=
  (composition (composition (pair (reverse (A:=Bool)) (constant (1,0)))
    (fold mulStepRealizer)) second).congr (by
      intro bs
      change (bs.reverse.foldl (fun z b=>mulStep (b,z)) (1,0)).2=_
      rw [mulStep_fold]
      simp)

def bitDenominatorRealizer : Realizer bitDenominator :=
  (composition (pair (identity (A:=List Bool)) (constant 1))
    (fold (composition second double))).congr (fun _=>rfl)
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Complexity_TreeChoiceCosts
attribute [-instance] _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

variable {A : Type} [Codec A]

def takeFast : Realizer (fun x : List A×ℕ=>x.1.take x.2) :=
  (composition (composition (pair (composition first reverse)
    (composition (pair (composition first listLength) second) subtract)) dropFast) reverse).congr (by
      intro x
      change (x.1.reverse.drop (x.1.length-x.2)).reverse=x.1.take x.2
      rw [←List.reverse_take,List.reverse_reverse])
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_ListWordProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary execution of the finite-list proposal

The list is scanned only up to its own length. A binary index beyond the
end produces `none`; its numerical magnitude never determines a loop bound.
-/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped
open scoped BigOperators

variable {A : Type} [Codec A] [Inhabited A]

def listWordChoice (x : List A×List Bool) : Option A :=
  x.1[StackAddition.value x.2]?

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionArithmeticProposal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An explicit coordinate-list proposal for the companion chain

Only ordered coordinates are enumerated. The arithmetic binary-profile
program generates the possible exchanges, after which the actual chain
state predicate removes disallowed states. A dyadic list index has exactly
the same proposal law as the abstract injection.
-/

namespace ContingencyTables.CompanionArithmeticProposal
open CommonBasesFPRAS ProfilePrograms FirstSuccess ResidualMixture FairBits
open CompanionFactorialApplication CompanionBooleanPhase TwoLiftStates
open scoped BigOperators Classical

noncomputable section

section Coordinates
variable {Γ : Type*} [Fintype Γ] {n : ℕ} (e : Γ ≃ Fin n)

/-- The state filter is applied after the quadratic coordinate scan. -/
def neighborStates (gs : List (Γ×Γ)) (S : ChainIndex gs) : List (ChainIndex gs) :=
  (neighborSets e S.val).filterMap (fun T => if h : ChainState gs T then some ⟨T,h⟩ else none)

end Coordinates

variable {I J : Type} [Fintype I] [Fintype J]

def neighbors (A : Instance I J) (S : State A) : List (State A) :=
  neighborStates (coordinateEquiv A) pairs S

/-- The selection stage is the actual binary list-index program. -/
def proposal (A : Instance I J) (S : State A) (bits : Fin (proposalBits A) → Bool) : Option (State A) :=
  listWordChoice (neighbors A S,List.ofFn bits)

end
end ContingencyTables.CompanionArithmeticProposal

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionArithmeticStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coordinate arithmetic for the companion proposal

The arithmetic and abstract proposals consume equal fixed word lengths.
Oracle and acceptance words are disjoint, and their full one-step laws
agree, giving the same trajectory error bound.
-/

namespace ContingencyTables.CompanionArithmeticStep
open CommonBasesFPRAS FirstSuccess ResidualMixture FairBits GridBoundary
open CompanionFactorialApplication CompanionOracleDensity CompanionWeightOracle
open CompanionBooleanPhase RealKernelApproximation
open scoped BigOperators Classical

noncomputable section

variable {I J : Type} [Fintype I] [Fintype J]

abbrev RestWord (A : Instance I J) (C K j k : ℕ) (xi : ℚ) :=
  (Fin 1 → Bool)×((WeightWord A C K j xi×WeightWord A C K j xi)×(Fin k → Bool))

end
end ContingencyTables.CompanionArithmeticStep

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallPatternProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial tests for the two allowed small-profile patterns -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped Polynomial

def pairSumRealizer : Realizer pairSum :=
  composition (pair
    (composition (pair (composition (composition first first) first) second) (getDFast 0))
    (composition (pair (composition (composition first first) second) second) (getDFast 0))) add

def indexIndicator : Realizer (fun z : ℕ×ℕ => if z.1=z.2 then (1:ℕ) else 0) :=
  (choose natEqual (constant 1) (constant 0)).congr (by
    intro z; simp only [decide_eq_true_eq])

def patternIndices : Realizer (fun z : PatternData => List.range z.1.1.length) :=
  composition (composition (composition first first) listLength) range

def defectAtRealizer : Realizer defectAt :=
  composition (pair
    (composition (pair
      (composition (pair (composition first first) second) pairSumRealizer)
      (composition (pair second (composition (composition first second) first)) indexIndicator)) add)
    (composition (pair (composition (composition first first) second)
      (composition (pair second (composition (composition first second) second)) indexIndicator)) add))
    natEqual

def defectTestRealizer : Realizer defectTest :=
  (composition (pair
    (composition (composition second natEqual) boolNot)
    (composition (composition (pair identity (composition first patternIndices))
      (mapWith defectAtRealizer)) all)) boolAnd).congr (by
        intro z
        apply Bool.eq_iff_iff.mpr
        simp only [Function.comp_apply,Bool.and_eq_true,Bool.not_eq_true',
          decide_eq_false_iff_not,defectTest,decide_eq_true_eq,List.all_map,Function.comp_def,id_eq])

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionChainValidator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial validation of paired binary states

The bounded-profile arithmetic test specializes to width one.
Thus the companion's state filter is a concrete list program on the two
coordinates of every labelled pair.
-/

namespace ContingencyTables.CompanionChainValidator
open CommonBasesFPRAS TwoLiftStates ProfilePrograms
open MatchingFPRAS.TreeTyped
open scoped BigOperators Classical

def pairFirstLookup : Realizer (fun z : List ℕ×(ℕ×ℕ) => z.1.getD z.2.1 0) :=
  composition (pair first (composition second first)) (getDFast 0)

def pairSecondLookup : Realizer (fun z : List ℕ×(ℕ×ℕ) => z.1.getD z.2.2 0) :=
  composition (pair first (composition second second)) (getDFast 0)

end ContingencyTables.CompanionChainValidator

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionNeighborProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executable valid-neighbor lists and their binary draw

This composes the actual integer-exchange program with the paired-state
validator and the bounded list-index program. The output code is exactly
the encoding of the semantic proposal, including its failure outcome.
-/

namespace ContingencyTables.CompanionNeighborProgram
open CompanionChainValidator CompanionArithmeticProposal CompanionFactorialApplication
open CompanionBooleanPhase ProfilePrograms MatchingFPRAS.TreeTyped
open CommonBasesFPRAS
open scoped BigOperators Classical

def codeProposal (z : ValidatorInput×List Bool) : Option (List ℕ) :=
  listWordChoice (validExchanges z.1,z.2)

end ContingencyTables.CompanionNeighborProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseAxisProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded binary coordinate moves in the dense grid -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms

def axisListStepRealizer : Realizer axisListStep := by
  let K : Realizer (fun z : AxisData => z.1.1.1) :=
    composition (composition first first) first
  let X : Realizer (fun z : AxisData => z.1.1.2) :=
    composition (composition first first) second
  let I : Realizer (fun z : AxisData => z.1.2) := composition first second
  let L := composition X listLength
  let V := composition (pair X I) (getDFast 0)
  let up := composition (composition (pair X (pair I L)) listExchangeRealizer) TreeTyped.some
  let down := composition (composition (pair X (pair L I)) listExchangeRealizer) TreeTyped.some
  exact (choose (composition (pair I L) less)
    (choose second (choose (composition (pair (composition V successor) K) less)
      up (constant none))
      (choose (composition (pair (constant 0) V) less) down (constant none)))
    (constant none)).congr (by
      intro z
      simp only [Function.comp_apply,decide_eq_true_eq,axisListStep])

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseAxisWordProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary-word decoding for a dense coordinate proposal -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms GridBoundary

def axisWordStep (z : AxisWordData) : Option (List ℕ) :=
  axisListStep ((z.1,StackAddition.value z.2/2),decide (StackAddition.value z.2%2=1))

def axisWordStepRealizer : Realizer axisWordStep := by
  let V : Realizer (fun z : AxisWordData => StackAddition.value z.2) := composition second bitValue
  let I := composition (pair V (constant 2)) quotient
  let S := composition (pair (composition (pair V (constant 2)) remainder) (constant 1)) natEqual
  exact composition (pair (pair first I) S) axisListStepRealizer

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseIntegerProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary list arithmetic for integral dense completion -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped
open scoped BigOperators

def columnReadRealizer : Realizer columnRead :=
  composition (pair second first) (getDFast 0)

def columnTotalRealizer : Realizer columnTotal :=
  composition (composition (pair second first) (mapWith columnReadRealizer)) listSum

def rowTotalRealizer : Realizer rowTotal := composition (getDFast []) listSum

def matrixTotalRealizer : Realizer matrixTotal := composition (map listSum) listSum

def matrixEntryRealizer : Realizer matrixEntry :=
  composition (pair (composition (pair first (composition second first)) (getDFast []))
    (composition second second)) (getDFast 0)

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseCompletionProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Signed dependent entries from binary margin and matrix lists -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped
open scoped BigOperators

def completionPartsRealizer : Realizer completionParts := by
  let R : Realizer (fun z : CompletionCell => z.1.1.1) :=
    composition (composition first first) first
  let C : Realizer (fun z : CompletionCell => z.1.1.2) :=
    composition (composition first first) second
  let Z : Realizer (fun z : CompletionCell => z.1.2) := composition first second
  let I : Realizer (fun z : CompletionCell => z.2.1) := composition second first
  let J : Realizer (fun z : CompletionCell => z.2.2) := composition second second
  let Im := composition (pair I (constant 1)) subtract
  let Jm := composition (pair J (constant 1)) subtract
  let Rval := composition (pair R I) (getDFast 0)
  let Cval := composition (pair C J) (getDFast 0)
  let Rsum := composition (pair Z Im) rowTotalRealizer
  let Csum := composition (pair Z Jm) columnTotalRealizer
  let total := pair
    (composition (pair (composition R (head 0)) (composition Z matrixTotalRealizer)) add)
    (composition (composition C tail) listSum)
  let entry := pair (composition (pair Z (pair Im Jm)) matrixEntryRealizer) (constant 0)
  exact (choose (composition (pair I (constant 0)) natEqual)
    (choose (composition (pair J (constant 0)) natEqual) total (pair Cval Csum))
    (choose (composition (pair J (constant 0)) natEqual) (pair Rval Rsum) entry)).congr
      (by intro z; simp only [Function.comp_apply,decide_eq_true_eq,completionParts])

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperPhysicalVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The Poincare inequality on the actual feasible small states -/

namespace ContingencyTables.SmallGraphProfiles

open scoped Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres FirstPaperProfiles
open FirstPaperPhysicalMarginal CompletionCounts

universe u

variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

abbrev PhysicalStates (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) :=
  {z : Profiles small B // 0 < hardMarginal small B r c L (naturalProfile z.val)}

noncomputable def physicalProfile (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (z : PhysicalStates small B r c L) : SmallProfile small :=
  naturalProfile z.val.val

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_RectangleCompletions
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Supported completions are tables on the actual large rectangle -/

namespace ContingencyTables.CompletionCounts

open scoped BigOperators Classical

variable {I J : Type*} [Fintype I] [Fintype J]

lemma sum_subtype_eq_of_zero {K : Type*} [Fintype K] (p : K → Prop)
    (f : K → ℕ) (hf : ∀ k,¬p k → f k=0) :
    (∑ k : {k // p k},f k.val)=∑ k,f k := by
  calc
    _ = ∑ k ∈ Finset.univ.filter p,f k := (Finset.sum_subtype _ (by simp) f).symm
    _ = ∑ k,f k := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : p k
      · rw [ite_eq_left hk]
      · rw [ite_eq_right hk,hf k hk]

noncomputable def rectangleRestrict (small : I → J → Bool)
    (p : I → Prop) (q : J → Prop)
    (hrect : ∀ i j,small i j=false ↔ p i ∧ q j)
    (R : I → ℕ) (C : J → ℕ) (A : LargeCompletion small R C) :
    Table (fun i : {i // p i} => R i.val) (fun j : {j // q j} => C j.val) := by
  refine ⟨fun i j => A.val.val i.val j.val,?_,?_⟩
  · intro i
    rw [sum_subtype_eq_of_zero q (A.val.val i.val)]
    · exact A.val.property.1 i.val
    · intro j hj
      apply A.property
      apply Bool.eq_true_of_not_eq_false
      intro hs
      exact hj ((hrect i.val j).mp hs).2
  · intro j
    rw [sum_subtype_eq_of_zero p (fun i => A.val.val i j.val)]
    · exact A.val.property.2 j.val
    · intro i hi
      apply A.property
      apply Bool.eq_true_of_not_eq_false
      intro hs
      exact hi ((hrect i j.val).mp hs).1

noncomputable def rectangleExtend (small : I → J → Bool)
    (p : I → Prop) (q : J → Prop)
    (hrect : ∀ i j,small i j=false ↔ p i ∧ q j)
    (R : I → ℕ) (C : J → ℕ)
    (hR : ∀ i,¬p i → R i=0) (hC : ∀ j,¬q j → C j=0)
    (A : Table (fun i : {i // p i} => R i.val) (fun j : {j // q j} => C j.val)) :
    LargeCompletion small R C := by
  let F : I → J → ℕ := fun i j => if hi : p i then if hj : q j then A.val ⟨i,hi⟩ ⟨j,hj⟩ else 0 else 0
  have hzero (i : I) (j : J) (hs : small i j=true) : F i j=0 := by
    dsimp only [F]
    split_ifs with hi hj
    · have hh := (hrect i j).mpr ⟨hi,hj⟩
      rw [hs] at hh
      contradiction
    · rfl
    · rfl
  refine ⟨⟨F,?_,?_⟩,hzero⟩
  · intro i
    by_cases hi : p i
    · rw [← sum_subtype_eq_of_zero q (F i) (by
        intro j hj; simp [F,hi,hj])]
      convert A.property.1 ⟨i,hi⟩ using 1
      all_goals try with_reducible_and_instances rfl
      apply Finset.sum_congr rfl
      intro j _
      simp only [F,dite_eq_left hi,dite_eq_left j.property]
    · simp [F,hi,hR i hi]
  · intro j
    by_cases hj : q j
    · rw [← sum_subtype_eq_of_zero p (fun i => F i j) (by
        intro i hi; simp [F,hi])]
      convert A.property.2 ⟨j,hj⟩ using 1
      all_goals try with_reducible_and_instances rfl
      apply Finset.sum_congr rfl
      intro i _
      simp only [F,dite_eq_left i.property,dite_eq_left hj]
    · have hz : ∀ i,F i j=0 := by intro i; dsimp only [F]; split_ifs <;> simp_all
      simp only [hz,Finset.sum_const_zero,hC j hj]

noncomputable def rectangleCompletionEquiv (small : I → J → Bool)
    (p : I → Prop) (q : J → Prop)
    (hrect : ∀ i j,small i j=false ↔ p i ∧ q j)
    (R : I → ℕ) (C : J → ℕ)
    (hR : ∀ i,¬p i → R i=0) (hC : ∀ j,¬q j → C j=0) :
    LargeCompletion small R C ≃
      Table (fun i : {i // p i} => R i.val) (fun j : {j // q j} => C j.val) where
  toFun := rectangleRestrict small p q hrect R C
  invFun := rectangleExtend small p q hrect R C hR hC
  left_inv A := by
    apply Subtype.ext
    apply Subtype.ext
    funext i j
    change (if hi : p i then if hj : q j then A.val.val i j else 0 else 0)=A.val.val i j
    split_ifs with hi hj
    · rfl
    · symm
      apply A.property
      apply Bool.eq_true_of_not_eq_false
      intro hs
      exact hj ((hrect i j).mp hs).2
    · symm
      apply A.property
      apply Bool.eq_true_of_not_eq_false
      intro hs
      exact hi ((hrect i j).mp hs).1
  right_inv A := by
    apply Subtype.ext
    funext i j
    change (if hi : p i.val then if hj : q j.val then A.val ⟨i.val,hi⟩ ⟨j.val,hj⟩ else 0 else 0)=A.val i j
    simp only [dite_eq_left i.property,dite_eq_left j.property]

end ContingencyTables.CompletionCounts

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_PhysicalResidualMargins
attribute [-instance] _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Literal padded residual completions of each positive physical state -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres FirstPaperProfiles
open FirstPaperPhysicalMarginal CompletionCounts PaddedCompletions

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

noncomputable def residualRows (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (z : PhysicalStates small B r c L) (i : I) : ℕ :=
  r i-smallRow small (smallView small (physicalProfile small B r c L z) false) i+rowLargeCount small i*L

noncomputable def residualColumns (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (z : PhysicalStates small B r c L) (j : J) : ℕ :=
  c j-smallColumn small B (smallView small (physicalProfile small B r c L z) true) j+columnLargeCount small j*L

lemma physical_weight_completions (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ)
    (z : PhysicalStates small B r c L)
    (hcap : ∀ i j,small i j=false → (∑ k,residualRows small B r c L z k) ≤ B i j) :
    hardMarginal small B r c L (physicalProfile small B r c L z)=
      (Fintype.card (LargeCompletion small (residualRows small B r c L z)
        (residualColumns small B r c L z)):ℝ) := by
  have h := hardMarginal_eq_completionCount small B r c L
    (physicalProfile small B r c L z) (naturalProfile_bounded z.val.val) hcap
  split_ifs at h with hres
  · exact h
  · have hp := z.property
    change 0 < hardMarginal small B r c L (physicalProfile small B r c L z) at hp
    rw [h] at hp
    exact False.elim (lt_irrefl _ hp)

lemma physical_completions_nonempty (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ)
    (z : PhysicalStates small B r c L)
    (hcap : ∀ i j,small i j=false → (∑ k,residualRows small B r c L z k) ≤ B i j) :
    Nonempty (LargeCompletion small (residualRows small B r c L z)
      (residualColumns small B r c L z)) := by
  apply Fintype.card_pos_iff.mp
  have hp := z.property
  change 0 < hardMarginal small B r c L (physicalProfile small B r c L z) at hp
  rw [physical_weight_completions small B r c L z hcap] at hp
  exact_mod_cast hp

/-- Rows outside the large-margin rectangle have zero residual, as
forced by the actual positive completion count. -/
lemma physical_residual_row_zero (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (z : PhysicalStates (firstPaperSmall r c U) B r c L)
    (hcap : ∀ i j,firstPaperSmall r c U i j=false →
      (∑ k,residualRows (firstPaperSmall r c U) B r c L z k) ≤ B i j)
    (i : I) (hi : ¬U ≤ r i) :
    residualRows (firstPaperSmall r c U) B r c L z i=0 := by
  obtain ⟨A⟩ := physical_completions_nonempty _ B r c L z hcap
  rw [← A.val.property.1 i]
  apply Finset.sum_eq_zero
  intro j _
  apply A.property
  apply Bool.eq_true_of_not_eq_false
  intro hs
  exact hi ((firstPaperSmall_false_iff r c U i j).mp hs).1

lemma physical_residual_column_zero (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (z : PhysicalStates (firstPaperSmall r c U) B r c L)
    (hcap : ∀ i j,firstPaperSmall r c U i j=false →
      (∑ k,residualRows (firstPaperSmall r c U) B r c L z k) ≤ B i j)
    (j : J) (hj : ¬U ≤ c j) :
    residualColumns (firstPaperSmall r c U) B r c L z j=0 := by
  obtain ⟨A⟩ := physical_completions_nonempty _ B r c L z hcap
  rw [← A.val.property.2 j]
  apply Finset.sum_eq_zero
  intro i _
  apply A.property
  apply Bool.eq_true_of_not_eq_false
  intro hs
  exact hj ((firstPaperSmall_false_iff r c U i j).mp hs).2

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_PhysicalOriginalResiduals
attribute [-instance] _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive completion weight enforces the original residual tests -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open PhysicalCompletionFibres FirstPaperProfiles FirstPaperPhysicalMarginal
open CompletionCounts PaddedCompletions SmallContextFibres

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

lemma physical_original_residuals (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ)
    (z : PhysicalStates small B r c L)
    (hcap : ∀ i j,small i j=false → (∑ k,residualRows small B r c L z k) ≤ B i j) :
    OriginalResidualsNonnegative small B
      (smallView small (physicalProfile small B r c L z) false)
      (smallView small (physicalProfile small B r c L z) true) r c := by
  have hh := hardMarginal_eq_completionCount small B r c L
    (physicalProfile small B r c L z) (naturalProfile_bounded z.val.val) hcap
  by_contra hn
  rw [ite_eq_right hn] at hh
  have hp := z.property
  change 0 < hardMarginal small B r c L (physicalProfile small B r c L z) at hp
  rw [hh] at hp
  exact lt_irrefl _ hp

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ReferenceCompletionBlock
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed reference row and column for the physical completion blocks -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open PhysicalCompletionFibres FirstPaperPhysicalMarginal CompletionCounts

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

noncomputable def referenceRows (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (i₀ : LargeRows r U) (z : PhysicalStates (firstPaperSmall r c U) B r c L)
    (i : Option {i : LargeRows r U // i ≠ i₀}) : ℕ :=
  residualRows (firstPaperSmall r c U) B r c L z ((Equiv.optionSubtypeNe i₀) i).val

noncomputable def referenceColumns (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (j₀ : LargeColumns c U) (z : PhysicalStates (firstPaperSmall r c U) B r c L)
    (j : Option {j : LargeColumns c U // j ≠ j₀}) : ℕ :=
  residualColumns (firstPaperSmall r c U) B r c L z ((Equiv.optionSubtypeNe j₀) j).val

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperSmallChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal first-paper completion chain has the stated Poincare bound -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open CommonBasesFPRAS PhysicalCompletionFibres FirstPaperPhysicalMarginal CompletionCounts
open CompletionTranslation

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

abbrev PaperStates (r : I → ℕ) (c : J → ℕ) :=
  PhysicalStates (paperSmall r c) (stateCapacity r c) r c
    ((dimensionAllowance (I := I) (J := J))^12)

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_CompletionFibreEquiv
attribute [-instance] _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Entry-preserving completion equivalences

The finite dense draw is transported to the retained completion fibre by
an equivalence preserving every table entry.
-/

namespace ContingencyTables.PhysicalCompletionFibres

open scoped BigOperators Classical
open LargePairEnumeration PhysicalLargeProfiles RowColumnPenalties
open FirstPaperPhysicalMarginal FirstPaperProfiles PaddedCompletions CompletionCounts

variable {I J : Type*} [Fintype I] [Fintype J]

abbrev ZeroPhysical (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (z : SmallProfile small) :=
  {a : PhysicalAssignments (fun a : I×J => small a.1 a.2) (fun a => B a.1 a.2) //
    NestedPenaltyApplication.penalty cellLine (smallCoordinate small)
      (fullOffset B (fun i => r i+rowLargeCount small i*L)
        (fun j => c j+columnLargeCount small j*L)) viewSlope
      (smallOffset small B r c) viewSlope
      (PhysicalLargeProfiles.physicalProfile (fun a : I×J => small a.1 a.2)
        (fun a => B a.1 a.2) z a)=0}

noncomputable def zeroSupportedEquiv (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (z : SmallProfile small) :
    ZeroPhysical small B r c L z ≃
      ZeroAssignments small B (smallView small z false) (smallView small z true) r c L :=
  (supportedAssignmentEquiv small B).subtypeEquiv (fun a => by
    have h := physicalProfile_supported small B z ((supportedAssignmentEquiv small B) a)
    rw [Equiv.symm_apply_apply] at h
    change _=0 ↔ fullPenalty small B _ _ _ r c L=0
    rw [h]
    rfl)

noncomputable def fibreLargeEquiv (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (z : SmallProfile small)
    (hz : ∀ u,z u ≤ B u.1.val.1 u.1.val.2)
    (hres : OriginalResidualsNonnegative small B (smallView small z false) (smallView small z true) r c)
    (hcap : ∀ i j,small i j=false →
      (∑ k,(r k-smallRow small (smallView small z false) k+rowLargeCount small k*L)) ≤ B i j) :
    CompletionFibre small B r (fun i => r i+rowLargeCount small i*L)
      c (fun j => c j+columnLargeCount small j*L) z ≃
    LargeCompletion small
      (fun i => r i-smallRow small (smallView small z false) i+rowLargeCount small i*L)
      (fun j => c j-smallColumn small B (smallView small z true) j+columnLargeCount small j*L) :=
  ((zeroPhysicalEquiv small B r c L z hz).symm.trans
    (zeroSupportedEquiv small B r c L z)).trans
    (completionEquiv small B (smallView small z false) (smallView small z true) r c L
      (fun i j hs => by simpa only [smallView,hs,dite_eq_left] using hz (⟨(i,j),hs⟩,false))
      (fun i j hs => by simpa only [smallView,hs,dite_eq_left] using hz (⟨(i,j),hs⟩,true)) hres hcap)

end ContingencyTables.PhysicalCompletionFibres

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open PhysicalCompletionFibres FirstPaperPhysicalMarginal CompletionCounts PaddedCompletions
open SmallContextFibres

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

/-- Actual retained completion fibre to the fixed-reference dense block. -/
noncomputable def referenceFibreEquiv (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U)
    (z : PhysicalStates (firstPaperSmall r c U) B r c L)
    (hcap : ∀ i j,firstPaperSmall r c U i j=false →
      (∑ k,residualRows (firstPaperSmall r c U) B r c L z k) ≤ B i j) :
    CompletionFibre (firstPaperSmall r c U) B r
      (fun i => r i+rowLargeCount (firstPaperSmall r c U) i*L) c
      (fun j => c j+columnLargeCount (firstPaperSmall r c U) j*L)
      (physicalProfile _ B r c L z) ≃
    Table (referenceRows r c U L B i₀ z) (referenceColumns r c U L B j₀ z) := by
  refine ((fibreLargeEquiv (firstPaperSmall r c U) B r c L
    (physicalProfile _ B r c L z) (naturalProfile_bounded z.val.val)
    (physical_original_residuals _ B r c L z hcap) hcap).trans ?_).trans
    (tableReindex (Equiv.optionSubtypeNe i₀) (Equiv.optionSubtypeNe j₀)
      (fun i : LargeRows r U => residualRows (firstPaperSmall r c U) B r c L z i.val)
      (fun j : LargeColumns c U => residualColumns (firstPaperSmall r c U) B r c L z j.val))
  let E := rectangleCompletionEquiv (firstPaperSmall r c U)
    (fun i => U ≤ r i) (fun j => U ≤ c j) (firstPaperSmall_false_iff r c U)
    (residualRows _ B r c L z) (residualColumns _ B r c L z)
    (physical_residual_row_zero r c U L B z hcap)
    (physical_residual_column_zero r c U L B z hcap)
  exact E.trans (tableFintypeTransport _ _ _ _ _ _)

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallViewLookupProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial lookup of the sparse small-cell view -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

def lookupViewRealizer : Realizer lookupView :=
  composition (pair (composition first second)
    (composition (pair second (composition first first)) cellLookupRealizer)) (getDFast 0)

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallLineSumProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary row and column sums of the sparse stored view -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped Polynomial
open scoped BigOperators

def lineEntryRealizer (row : Bool) : Realizer (lineEntry row) :=
  composition (pair (composition (composition first first) first)
    (choose (constant row) (pair (composition first second) second)
      (pair second (composition first second)))) lookupViewRealizer

def lineIndices : Realizer (fun z : LineData => List.range z.1.2.length) :=
  composition (composition (composition first second) listLength) range

def lineSumRealizer (row : Bool) : Realizer (lineSum row) :=
  composition (composition (pair identity lineIndices) (mapWith (lineEntryRealizer row))) listSum

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallComplementProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary execution of the complemented small column view -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

def complementValuesRealizer : Realizer complementValues := mapWith subtract

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallMarginTestProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial residual-margin inequality and equality tests -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped Polynomial

def marginListRealizer (row : Bool) : Realizer (marginList row) :=
  choose (constant row) (composition (composition first second) first)
    (composition (composition first second) second)

def lineArgumentRealizer (row : Bool) : Realizer (lineArgument row) :=
  pair (pair (composition (composition first first) first)
    (composition first (marginListRealizer (!row)))) second

def marginValueRealizer (row : Bool) : Realizer (fun z : MarginCheckData×ℕ =>
    (marginList row z.1).getD z.2 0) :=
  composition (pair (composition first (marginListRealizer row)) second) (getDFast 0)

def lineValueRealizer (row : Bool) : Realizer (fun z : MarginCheckData×ℕ =>
    lineSum row (lineArgument row z)) :=
  composition (f := lineArgument row) (g := lineSum row)
    (lineArgumentRealizer row) (lineSumRealizer row)

def marginIndices (row : Bool) : Realizer (fun z : MarginCheckData =>
    List.range (marginList row z).length) :=
  composition (composition (marginListRealizer row) listLength) range

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallProfileValidator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial binary validator for the positive profile space -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

def profileViews : Realizer (fun z : ProfileCheckData => z.1.1.2) :=
  composition (composition first first) second

def profileCatalog : Realizer (fun z : ProfileCheckData => z.1.1.1) :=
  composition (composition first first) first

def profileMargins : Realizer (fun z : ProfileCheckData => z.1.2) :=
  composition first second

def profileView (row : Bool) : Realizer (fun z : ProfileCheckData =>
    if row then z.1.1.2.1 else z.1.1.2.2) :=
  choose (constant row) (composition profileViews first) (composition profileViews second)

def profileColumnView : Realizer (fun z : ProfileCheckData =>
    complementValues (z.2,z.1.1.2.2)) :=
  composition (pair second (composition profileViews second)) complementValuesRealizer

def profileLineData (row : Bool) : Realizer (fun z : ProfileCheckData =>
    (((z.1.1.1,if row then z.1.1.2.1 else complementValues (z.2,z.1.1.2.2)),z.1.2),z.2)) :=
  pair (pair (pair profileCatalog
    (choose (constant row) (profileView true) profileColumnView)) profileMargins) second

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallProfileCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Literal lists encode exactly the positive physical states -/

namespace ContingencyTables.SmallGraphProfiles
open scoped BigOperators Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres FirstPaperProfiles
open ProfilePrograms FirstPaperPhysicalMarginal CompletionCounts

noncomputable section
variable {m n q : ℕ} (small : Fin m → Fin n → Bool) (e : Fin q ≃ Cells small)

def profileCode (z : SmallProfile small) : List ℕ×List ℕ :=
  (viewList small e z false,viewList small e z true)

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperCodeProposal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The compiled neighbor draw has the small-chain proposal law -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

def codeNeighborProposal (z : ProfileCheckData×List Bool) : Option (List ℕ×List ℕ) :=
  listWordChoice (codeNeighbors z.1,z.2)

end ContingencyTables.ProfilePrograms

namespace ContingencyTables.SmallGraphProfiles
open scoped BigOperators Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres FirstPaperProfiles
open ProfilePrograms FirstPaperPhysicalMarginal CompletionCounts FirstSuccess FairBits

noncomputable section
variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c))
local notation "small" => paperSmall r c
local notation "B" => stateCapacity r c
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "L" => d^12
local notation "U" => d^20

def stateCode (x : PaperStates r c) : List ℕ×List ℕ :=
  profileCode small e (physicalProfile small B r c L x)

def stateCodeData (x : PaperStates r c) : ProfileCheckData :=
  codeCheckData (cellCatalog small e) (List.ofFn r) (List.ofFn c) U (stateCode r c e x)

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperPreparedProposal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Preparing the complete proposal input from binary margin lists -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

def squareNat : Realizer (fun n : ℕ => n*n) :=
  composition (pair identity identity) multiply

def fourthPower : Realizer (fun n : ℕ => n^4) :=
  (composition squareNat squareNat).congr (by intro n; simp only [Function.comp_apply]; ring)

def fifthPower : Realizer (fun n : ℕ => n^5) :=
  (composition (pair fourthPower identity) multiply).congr
    (by intro n; simp only [Function.comp_apply,id_eq,pow_succ])

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseExponentProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary execution of one dense exponent component -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped ContingencyTables.ProfilePrograms

def eighthPower : Realizer (fun n : ℕ => n^8) :=
  (composition fourthPower squareNat).congr (by
    intro n
    simp only [Function.comp_apply]
    ring)

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseExponentListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing all dense exponent components and their maximum -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped ContingencyTables.ProfilePrograms Polynomial
open scoped BigOperators

def listMaximumRealizer : Realizer listMaximum := fold maximum

def exponentCellDataRealizer : Realizer exponentCellData := by
  let R : Realizer (fun z : ExponentData×(ℕ×ℕ) => z.1.1.1.1) :=
    composition (composition (composition first first) first) first
  let C : Realizer (fun z : ExponentData×(ℕ×ℕ) => z.1.1.1.2) :=
    composition (composition (composition first first) first) second
  let I : Realizer (fun z : ExponentData×(ℕ×ℕ) => z.2.1) := composition second first
  let J : Realizer (fun z : ExponentData×(ℕ×ℕ) => z.2.2) := composition second second
  exact pair (pair (composition first second)
    (composition (pair (composition (pair R I) (getDFast 0))
      (composition (pair C J) (getDFast 0))) minimum))
    (composition (pair (composition first first) second) completionPartsRealizer)

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseScaleCellProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary conversion from a grid coordinate to a free integer entry -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped
open GridBoundary

def shiftedCellRealizer : Realizer shiftedCell :=
  pair first (pair (composition (composition second first) successor)
    (composition (composition second second) successor))

def gridCellWidthRealizer : Realizer gridCellWidth :=
  composition (pair
    (composition (composition (composition shiftedCellRealizer exponentCellDataRealizer) first) second)
    (composition (composition first second) eighthPower)) quotient

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseMatrixLayoutProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial conversion between flat and rectangular grid encodings -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped Polynomial

def sliceRowRealizer : Realizer sliceRow :=
  composition (pair
    (composition (pair (composition first second)
      (composition (pair second (composition first first)) multiply)) dropFast)
    (composition first first)) takeFast

def layoutRowsRealizer : Realizer layoutRows :=
  composition (composition (composition (composition first first) tail) listLength) range

def layoutRowRealizer : Realizer layoutRow :=
  composition (pair (pair
    (composition (composition (composition (composition first first) second) tail) listLength)
    (composition first second)) second) sliceRowRealizer

def unflattenGridRealizer : Realizer unflattenGrid :=
  composition (pair identity layoutRowsRealizer) (mapWith layoutRowRealizer)

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseFlatExponentProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Evaluating the dense exponent on the flat coordinate encoding -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped GridBoundary

def flatToGridDataRealizer : Realizer flatToGridData :=
  pair (pair (composition first first) (composition first unflattenGridRealizer)) second

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_DyadicWordProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial binary evaluation of the finite Metropolis coin -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms

def dyadicWordAccept (z : List Bool×ℕ) : Bool :=
  decide (StackAddition.value z.1<2^(z.1.length-z.2))

/-- The power of two is built from a prefix of the supplied word. Thus
no binary integer supplied as a gap can cause an unbounded expansion. -/
def dyadicWordAcceptRealizer : Realizer dyadicWordAccept := by
  let N : Realizer (fun z : List Bool×ℕ => z.1.length-z.2) :=
    composition (pair (composition first listLength) second) subtract
  let B := composition (composition (pair first N) takeFast) bitDenominatorRealizer
  exact (composition (pair (composition first bitValue) B) less).congr (by
    intro z
    simp only [Function.comp_apply,bitDenominator_eq,List.length_take,dyadicWordAccept]
    rw [min_eq_left (Nat.sub_le _ _)])

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseWordProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Splitting the actual dense transition word in polynomial time -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped

def ceilLogTwoRealizer : Realizer (Nat.clog 2) :=
  (composition predecessor bitSize).congr (fun n => (clog_two_eq_size_pred n).symm)

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_BooleanChunkProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial partition of a supplied Boolean word into fixed-width rows -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped Polynomial

def wordChunkRealizer : Realizer wordChunk :=
  composition (pair
    (composition (pair (composition first second)
      (composition (pair second (composition first first)) multiply)) dropFast)
    (composition first first)) takeFast

def completeWordRowsRealizer : Realizer completeWordRows :=
  composition (composition (pair (composition second listLength) first) quotient) range

def wordChunksRealizer : Realizer wordChunks :=
  composition (pair identity completeWordRowsRealizer) (mapWith wordChunkRealizer)

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_DependentWordProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Splitting a binary word at input-dependent coordinate widths -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped Polynomial

def chunkStartRealizer : Realizer chunkStart :=
  composition (composition (pair (composition first first) second) takeFast) listSum

def dependentChunkRealizer : Realizer dependentChunk :=
  composition (pair
    (composition (pair (composition first second) chunkStartRealizer) dropFast)
    (composition (pair (composition first first) second) (getDFast 0))) takeFast

open scoped BigOperators

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_ScaledWordProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial binary execution of the bounded quotient draw -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped

def scaledWordRealizer : Realizer scaledWordValue :=
  (composition (pair
    (composition (pair first (composition second bitValue)) multiply)
    (composition second bitDenominatorRealizer)) quotient).congr (by
      intro x
      simp only [Function.comp_apply,bitDenominator_eq,scaledWordValue])

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FixedCardinalityProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial binary arithmetic for sequential subset inclusion

The rational inclusion threshold is computed by an integer product and
quotient. In particular the denominator is never expanded into a
unary loop; the only exponential integer has the supplied word length
as its binary length.
-/

namespace ContingencyTables.FixedCardinalityProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms

def includeCode (z : HeadInput) : Bool :=
  decide (StackAddition.value z.2<2^z.2.length*min z.1.2 z.1.1/z.1.1)

def includeRealizer : Realizer includeCode := by
  let N : Realizer (fun z : HeadInput => z.1.1) := composition first first
  let K : Realizer (fun z : HeadInput => z.1.2) := composition first second
  let M := composition (pair K N) minimum
  let D : Realizer (fun z : HeadInput => TreeTyped.bitDenominator z.2) :=
    composition second bitDenominatorRealizer
  let T := composition (pair (composition (pair D M) multiply) N) quotient
  exact (composition (pair (composition second bitValue) T) less).congr (by
    intro z
    simp only [Function.comp_apply,bitDenominator_eq,includeCode])

end ContingencyTables.FixedCardinalityProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FixedCardinalityFold
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial sequential list program for the subset draw

The accumulator retains the remaining population and requested size,
and records one inclusion bit per input word. Both counters decrease;
only the output list grows. The final program reverses that list once.
-/

namespace ContingencyTables.FixedCardinalityProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial

def advance (z : List Bool×DrawState) : DrawState :=
  let b := includeCode (z.2.1,z.1)
  ((z.2.1.1-1,if b then z.2.1.2-1 else min z.2.1.2 (z.2.1.1-1)),b::z.2.2)

def advanceRealizer : Realizer advance := by
  let N : Realizer (fun z : List Bool×DrawState => z.2.1.1) :=
    composition (composition second first) first
  let K : Realizer (fun z : List Bool×DrawState => z.2.1.2) :=
    composition (composition second first) second
  let B : Realizer (fun z : List Bool×DrawState => includeCode (z.2.1,z.1)) :=
    composition (pair (composition second first) first) includeRealizer
  let R := composition (pair N (constant 1)) subtract
  let T := choose B (composition (pair K (constant 1)) subtract)
    (composition (pair K R) minimum)
  exact pair (pair R T) (composition (pair B (composition second second)) listCons)

def drawWords (z : (ℕ×ℕ)×List (List Bool)) : List Bool :=
  (z.2.foldl (fun s word => advance (word,s)) (z.1,[])).2.reverse

def prepareWordsRealizer : Realizer prepareWords := pair second (pair first (constant []))

def runWords (z : (ℕ×ℕ)×List (List Bool)) : DrawState :=
  z.2.foldl (fun s word => advance (word,s)) (z.1,[])

def runWordsRealizer : Realizer runWords := composition prepareWordsRealizer (fold advanceRealizer)

def outputRealizer : Realizer (fun s : DrawState => s.2.reverse) := composition second reverse

def drawWordsRealizer : Realizer drawWords :=
  composition (f := runWords) (g := fun s : DrawState => s.2.reverse)
    runWordsRealizer outputRealizer

end ContingencyTables.FixedCardinalityProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FixedCardinalityFlat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A flat-word program for a local initial subset

The first B bits select the size. The remaining word is partitioned
into B-bit inclusion rows, so the input list bounds the number of loop
iterations even on malformed inputs.
-/

namespace ContingencyTables.FixedCardinalityProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms DensePrograms

def subsetCode (z : SubsetInput) : List Bool :=
  drawWords ((z.1.1,scaledWordValue (z.1.1+1,z.2.take z.1.2)),
    wordChunks (z.1.2,z.2.drop z.1.2))

def subsetCodeRealizer : Realizer subsetCode := by
  let N : Realizer (fun z : SubsetInput => z.1.1) := composition first first
  let B : Realizer (fun z : SubsetInput => z.1.2) := composition first second
  let head := composition (pair second B) takeFast
  let size := composition (pair (composition N successor) head) scaledWordRealizer
  let rest := composition (pair second B) dropFast
  let chunks := composition (pair B rest) wordChunksRealizer
  exact composition (pair (pair N size) chunks) drawWordsRealizer

end ContingencyTables.FixedCardinalityProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_InitialChoiceProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial independent-cell initialization program

The capacities are a supplied list. A polynomial index scan extracts
each disjoint variable-width word block and runs the local subset
program. The resulting rows are exactly the independent cell choices
in the initial finite-word law.
-/

namespace ContingencyTables.InitialChoiceProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial
open DensePrograms FixedCardinalityProgram

def cellWidthRealizer : Realizer cellWidth :=
  composition (pair first (composition (pair second first) multiply)) add

def widthsRealizer : Realizer widths :=
  composition (pair second first) (mapWith cellWidthRealizer)

def cellCode (z : Input×ℕ) : List Bool :=
  subsetCode ((z.1.1.1.getD z.2 0,z.1.1.2),
    dependentChunk ((widths z.1.1,z.1.2),z.2))

def cellCodeRealizer : Realizer cellCode := by
  let cap : Realizer (fun z : Input×ℕ => z.1.1.1.getD z.2 0) :=
    composition (pair (composition (composition first first) first) second) (getDFast 0)
  let B : Realizer (fun z : Input×ℕ => z.1.1.2) :=
    composition (composition first first) second
  let sizes : Realizer (fun z : Input×ℕ => widths z.1.1) :=
    composition (composition first first) widthsRealizer
  let bits : Realizer (fun z : Input×ℕ => z.1.2) := composition first second
  let block := composition (pair (pair sizes bits) second) dependentChunkRealizer
  exact composition (pair (pair cap B) block) subsetCodeRealizer

def indicesRealizer : Realizer indices :=
  composition (composition (composition first first) listLength) range

def choiceCode (z : Input) : List (List Bool) := (indices z).map (fun i => cellCode (z,i))

def choiceCodeRealizer : Realizer choiceCode :=
  composition (pair identity indicesRealizer) (mapWith cellCodeRealizer)

end ContingencyTables.InitialChoiceProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_CanonicalInitialEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Canonical paired-label order for the initial binary program

The order is the explicit list of cells, then their copies, then the
two sides of each pair. The code is obtained directly from the sampled
Boolean rows, so no enumeration of the set-valued state space occurs.
-/

namespace ContingencyTables.CanonicalInitialEncoding

open MatchingFPRAS MatchingFPRAS.TreeTyped
open CommonBasesFPRAS InitialTransversals FixedCardinalityMixture InitialFactorialBits
open scoped BigOperators Classical

def pairValueRealizer : Realizer pairValue :=
  composition (pair (choose identity (constant 1) (constant 0))
    (composition (pair (choose identity (constant 0) (constant 1)) (constant [])) listCons)) listCons

def pairedCodeRealizer : Realizer pairedCode := composition flatten (flatMapPoly pairValueRealizer)

def initialCode (z : InitialChoiceProgram.Input) : List ℕ := pairedCode (InitialChoiceProgram.choiceCode z)

def initialCodeRealizer : Realizer initialCode :=
  composition InitialChoiceProgram.choiceCodeRealizer pairedCodeRealizer

end ContingencyTables.CanonicalInitialEncoding

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionCellCatalogProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing the companion's retained small-cell capacities

The program scans the rectangular cell list determined by the two
margin-list lengths, then tests the binary cell bound against W. It
does not enumerate up to the numeric value of a capacity.
-/

namespace ContingencyTables.CompanionCellCatalog

open MatchingFPRAS.TreeTyped ProfilePrograms DensePrograms

def entryRealizer : Realizer entry :=
  composition (pair (composition (composition first first) second) second) matrixEntryRealizer

def retainedTestRealizer : Realizer retainedTest :=
  composition (pair entryRealizer (composition first second)) less

def catalogRealizer : Realizer catalog :=
  composition (pair identity
    (composition (composition first first) cellPairsRealizer)) (filterWith retainedTestRealizer)

def capacitiesRealizer : Realizer capacities :=
  composition (pair identity catalogRealizer) (mapWith entryRealizer)

end ContingencyTables.CompanionCellCatalog

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_PairedCatalogProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing paired-coordinate metadata from a binary profile

Consecutive coordinates are paired by the bounded list scan
(0,1),(2,3),.... This is the exact metadata of the canonical paired-label
order, rather than a catalog supplied as an external oracle.
-/

namespace ContingencyTables.PairedCatalogProgram

open MatchingFPRAS.TreeTyped ProfilePrograms

def twiceRealizer : Realizer (fun i : ℕ => 2*i) :=
  composition (f := fun i : ℕ => (2,i)) (g := fun z : ℕ×ℕ => z.1*z.2)
    (pair (constant 2) identity) multiply

def indexPairRealizer : Realizer indexPair :=
  pair twiceRealizer
    (composition (f := fun i : ℕ => (2*i,1)) (g := fun z : ℕ×ℕ => z.1+z.2)
      (pair twiceRealizer (constant 1)) add)

def indicesRealizer : Realizer (fun xs : List ℕ => List.range (xs.length/2)) :=
  composition (composition (pair listLength (constant 2)) quotient) range

def catalogRealizer : Realizer catalog := composition indicesRealizer (map indexPairRealizer)

end ContingencyTables.PairedCatalogProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionComputedProposal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The companion proposal with computed metadata

The executable proposal receives only a binary profile and fresh bits.
It computes the consecutive-pair catalog itself and scans coordinate
exchanges. Its semantic law is the same ordered proposal law.
-/

namespace ContingencyTables.CompanionComputedProposal

open MatchingFPRAS.TreeTyped CompanionFactorialApplication CompanionComputedInitial
open CompanionArithmeticProposal CompanionOrderedProposal CompanionNeighborProgram
open CompanionBooleanPhase
open scoped Classical

def proposalProgram (z : List ℕ×List Bool) : Option (List ℕ) :=
  codeProposal ((PairedCatalogProgram.catalog z.1,z.1),z.2)

end ContingencyTables.CompanionComputedProposal

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionPhaseCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executable counts in an outer counting phase

The stored trajectory is scanned directly. Both the transversal count
and each labelled defect count use the actual polynomial occupancy
tests. No set-state enumeration is performed.
-/

namespace ContingencyTables.CompanionPhaseCounts

open MatchingFPRAS.TreeTyped ProfilePrograms CompanionChainValidator
open CompanionTraceProgram CompanionOrderedProposal CompanionArithmeticProposal
open CompanionFactorialApplication CompanionBooleanPhase
open CommonBasesFPRAS TwoLiftStates
open scoped Classical

def pairedDefectTestRealizer : Realizer pairedDefectTest :=
  composition (pair (pair (pair
    (composition (pair (composition first second) (composition first first))
      (mapWith pairFirstLookup))
    (composition (pair (composition first second) (composition first first))
      (mapWith pairSecondLookup))) (constant 1)) second) defectTestRealizer

end ContingencyTables.CompanionPhaseCounts

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionMultiplierMatrixProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full multiplier update and abort test as list programs

Only the polynomial list of labelled pairs is traversed. Every matrix
entry is updated from the actual plain and defect counts of the stored
trajectory. The count check includes every off-diagonal labelled type.
-/

namespace ContingencyTables.CompanionMultiplierMatrixProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial
open CompanionPhaseCounts CompanionMultiplierProgram CompanionOrderedProposal CompanionTraceProgram
open CompanionFactorialApplication CompanionArithmeticProposal CompanionRationalUpdates
open CommonBasesFPRAS
open scoped Classical

def readEntryRealizer : Realizer readEntry :=
  composition (pair (composition (pair first (composition second first)) (getDFast []))
    (composition second second)) (getDFast (0,1))

end ContingencyTables.CompanionMultiplierMatrixProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionStateMultiplierProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reading the multiplier of an actual encoded chain state

The at most quadratic list of labelled defect types is searched using
the proved occupancy test. Uniqueness of defect labels identifies the
selected matrix entry with the mathematical chain multiplier.
-/

namespace ContingencyTables.CompanionStateMultiplierProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms
open CompanionChainValidator CompanionPhaseCounts CompanionMultiplierMatrixProgram

def coordinatesRealizer : Realizer coordinates := composition first (map first)
def candidatesRealizer : Realizer candidates :=
  composition (pair coordinatesRealizer coordinatesRealizer) cellPairsRealizer
def foundRealizer : Realizer found :=
  composition (pair identity candidatesRealizer) (filterWith pairedDefectTestRealizer)
def noDefectRealizer : Realizer noDefect := composition (composition second foundRealizer) isEmpty
def readDefectRealizer : Realizer readDefect :=
  composition (f := fun z : Input => (z.1,(found z.2).getD 0 (0,0))) (g := readEntry)
    (pair first (composition (pair (composition second foundRealizer) (constant 0))
      (getDFast (0,0)))) readEntryRealizer
def outputRealizer : Realizer output := choose noDefectRealizer (constant (1,1)) readDefectRealizer
end ContingencyTables.CompanionStateMultiplierProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FractionAcceptanceProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary execution of the rational acceptance coin

The integer quotient computes the exact floor threshold used by the
finite-word acceptance law. The word length controls all powering and
word traversal, even for malformed fraction inputs.
-/

namespace ContingencyTables.FractionAcceptanceProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms

def acceptCode (z : Input) : Bool := decide (StackAddition.value z.2<threshold z)

end ContingencyTables.FractionAcceptanceProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_RationalIntervalProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact binary arithmetic for a forest interval penalty

A signed affine numerator is stored as a difference of two naturals.
Its distance outside the interval [0,1] is a nonnegative fraction with
the same denominator; no signed rational comparison is required.
-/

namespace ContingencyTables.RationalIntervalProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped

def numeratorRealizer : Realizer numerator := by
  let P : Realizer (fun z : Input => z.1.1) := composition first first
  let N : Realizer (fun z : Input => z.1.2) := composition first second
  let D : Realizer (fun z : Input => z.2) := second
  exact composition (pair (composition (pair N P) subtract)
    (composition (pair P (composition (pair N D) add)) subtract)) add

def intervalCodeRealizer : Realizer intervalCode :=
  composition (f := fun z : Input => (numerator z,z.2)) (g := TreeFraction.normalize)
    (pair numeratorRealizer second) TreeFraction.normalizeRealizer

end ContingencyTables.RationalIntervalProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ForestAffineProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary list evaluation of the forest's signed affine numerators

Each coefficient is stored by its nonnegative and nonpositive parts.
The program performs two finite product sums and passes their difference
to the proved interval-cost routine. Large capacities are never iterated.
-/

namespace ContingencyTables.ForestAffineProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped
open scoped BigOperators Classical

def positiveTermRealizer : Realizer positiveTerm :=
  composition (f := fun z : Term => (z.1.1,z.2)) (g := fun z : ℕ×ℕ => z.1*z.2)
    (pair (composition first first) second) multiply

def negativeTermRealizer : Realizer negativeTerm :=
  composition (f := fun z : Term => (z.1.2,z.2)) (g := fun z : ℕ×ℕ => z.1*z.2)
    (pair (composition first second) second) multiply

def positiveSumRealizer : Realizer (fun xs : List Term => (xs.map positiveTerm).sum) :=
  composition (map positiveTermRealizer) listSum

def negativeSumRealizer : Realizer (fun xs : List Term => (xs.map negativeTerm).sum) :=
  composition (map negativeTermRealizer) listSum

def partsRealizer : Realizer parts :=
  pair
    (composition (pair (composition (composition first first) first)
      (composition (composition first second) positiveSumRealizer)) add)
    (composition (pair (composition (composition first first) second)
      (composition (composition first second) negativeSumRealizer)) add)

def evaluateRealizer : Realizer evaluate :=
  composition (f := fun z : Input => (parts z,z.2)) (g := RationalIntervalProgram.intervalCode)
    (pair partsRealizer second) RationalIntervalProgram.intervalCodeRealizer

end ContingencyTables.ForestAffineProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedComponentProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial signed component sums for the executed root labels -/

namespace ContingencyTables.RootedComponentProgram

open MatchingFPRAS.TreeTyped Polynomial
open scoped BigOperators Classical

def positiveTermRealizer : Realizer positiveTerm :=
  (choose (composition (pair first (composition second first)) natEqual)
    (composition (composition second second) first) (constant 0)).congr (by
      intro z
      simp only [Function.comp_apply,decide_eq_true_eq,positiveTerm])

def negativeTermRealizer : Realizer negativeTerm :=
  (choose (composition (pair first (composition second first)) natEqual)
    (composition (composition second second) second) (constant 0)).congr (by
      intro z
      simp only [Function.comp_apply,decide_eq_true_eq,negativeTerm])

def partsRealizer : Realizer parts :=
  pair (composition (mapWith positiveTermRealizer) listSum)
    (composition (mapWith negativeTermRealizer) listSum)

def absoluteDifferenceRealizer : Realizer absoluteDifference :=
  composition (pair subtract (composition (pair second first) subtract)) add

def componentRealizer : Realizer component := composition partsRealizer absoluteDifferenceRealizer

def totalRealizer : Realizer total :=
  composition (composition (pair identity (composition listLength range))
    (mapWith (composition (pair second first) componentRealizer))) listSum

end ContingencyTables.RootedComponentProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ForestPenaltyProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact rational assembly of the companion forest penalty

The natural root discrepancy and the finite list of tree affine forms
are combined by polynomial binary arithmetic to compute rationalD,
including the original maximum-forest cuts.
-/

namespace ContingencyTables.ForestPenaltyProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped
open CompanionFactorialApplication CompanionOracleDensity ForestAssignmentSplit GraphCompletionCounts
open ForestScaledPenalty
open scoped BigOperators Classical

def rootFractionRealizer : Realizer (fun z : Input => (z.1.2,(1:ℕ))) :=
  pair (composition first second) (constant 1)

def scaleFractionRealizer : Realizer (fun z : Input => (z.1.1,(1:ℕ))) :=
  pair (composition first first) (constant 1)

def treeSumRealizer : Realizer treeSum :=
  composition (f := fun z : Input => z.2.map ForestAffineProgram.evaluate)
    (g := TreeFraction.sum)
    (composition second (map ForestAffineProgram.evaluateRealizer)) TreeFraction.sumRealizer

def rootSumRealizer : Realizer (fun z : Input => TreeFraction.add ((z.1.2,1),treeSum z)) :=
  composition (f := fun z : Input => ((z.1.2,1),treeSum z)) (g := TreeFraction.add)
    (pair rootFractionRealizer treeSumRealizer) TreeFraction.addRealizer

def penaltyCodeRealizer : Realizer penaltyCode :=
  composition (f := fun z : Input => ((z.1.1,1),TreeFraction.add ((z.1.2,1),treeSum z)))
    (g := TreeFraction.mul)
    (pair scaleFractionRealizer rootSumRealizer)
    TreeFraction.mulRealizer

def weightedPenaltyRealizer : Realizer weightedPenalty :=
  composition (f := fun z : ExponentInput => (z.1,penaltyCode z.2)) (g := TreeFraction.mul)
    (pair first (composition (f := fun z : ExponentInput => z.2) (g := penaltyCode)
      second penaltyCodeRealizer)) TreeFraction.mulRealizer

def exponentCodeRealizer : Realizer exponentCode :=
  composition (f := weightedPenalty) (g := fun f : TreeFraction.Fraction => f.1/f.2)
    weightedPenaltyRealizer quotient

end ContingencyTables.ForestPenaltyProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FiniteGraphRootProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A binary list program computing a component root

The graph is supplied by adjacency lists. The program makes one growth
round per stored vertex, then minimizes the reached indices. No loop
depends on the numeric size of an index or of an edge capacity.
-/

namespace ContingencyTables.FiniteGraphRootProgram

open MatchingFPRAS.TreeTyped Polynomial

def indicesRealizer : Realizer indices := composition listLength range

def neighborHitRealizer : Realizer neighborHit :=
  (composition (mapWith membership) any).congr (by
    intro z
    simp only [Function.comp_apply,List.any_map,Function.comp_def,id_eq,neighborHit])

def growTestRealizer : Realizer growTest :=
  composition (f := fun z : SearchState×ℕ =>
      (decide (z.2∈z.1.2),neighborHit (z.1.2,z.1.1.getD z.2 [])))
    (g := fun z : Bool×Bool => z.1 || z.2)
    (pair (composition (pair (composition first second) second) membership)
      (composition (pair (composition first second)
        (composition (pair (composition first first) second) (getDFast [])))
        neighborHitRealizer)) boolOr

def growRealizer : Realizer grow :=
  composition (pair identity (composition first indicesRealizer))
    (filterWith growTestRealizer)

def advanceRealizer : Realizer advance :=
  pair (composition second first)
    (composition (f := fun z : List ℕ×SearchState => z.2) (g := grow) second growRealizer)

def prepareRealizer : Realizer prepare :=
  pair first (pair first (composition (pair second (constant [])) listCons))

def runRealizer : Realizer run := composition prepareRealizer (fold advanceRealizer)

def reachedRealizer : Realizer reached :=
  composition (f := run) (g := fun s : SearchState => s.2) runRealizer second

def rootCodeRealizer : Realizer rootCode :=
  composition (f := fun z : Input => (reached z,z.1.length))
    (g := fun z : List ℕ×ℕ => z.1.foldl (fun b a => min a b) z.2)
    (pair reachedRealizer (composition first listLength)) (fold minimum)

end ContingencyTables.FiniteGraphRootProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteGraphRootSemantics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact correctness of the finite component-root program

The stored adjacency list is identified with the given finite graph.
Each list growth round is the proved finite reachability growth, and
the final binary minimum is the least vertex of the actual component.
-/

namespace ContingencyTables.FiniteGraphRootProgram

open MatchingFPRAS.ComputableReach SimpleGraph

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

lemma graphCode_getD (b : Fin n) : (graphCode G).getD b.val []=adjacencyRow G b := by
  simp only [graphCode,List.getD_eq_getElem?_getD,List.getElem?_ofFn,b.isLt,dite_eq_left,
    Option.getD_some]

end ContingencyTables.FiniteGraphRootProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedComponentCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing every root label before summing its signed demand

The input contains an adjacency list and one positive/negative demand
pair per vertex. The polynomial program computes the root labels itself.
-/

namespace ContingencyTables.RootedComponentCode

open MatchingFPRAS.TreeTyped Polynomial
open RootedCompletion RootedComponentProgram FiniteGraphRootProgram
open scoped BigOperators Classical

def entryRealizer : Realizer entry :=
  pair (composition (pair (composition first first) second) rootCodeRealizer)
    (composition (pair (composition first second) second) (getDFast (0,0)))

def indicesRealizer : Realizer (fun z : Input => List.range z.2.length) :=
  composition (composition second listLength) range

def labelsRealizer : Realizer labels :=
  composition (pair identity indicesRealizer) (mapWith entryRealizer)

def countRealizer : Realizer count := composition labelsRealizer totalRealizer

open CompanionFactorialApplication

end ContingencyTables.RootedComponentCode

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseOffsetWidths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing the actual variable-width offset word layout -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped ProfilePrograms GridBoundary FairBits

def offsetLengthRealizer : Realizer offsetLength := by
  let cell : Realizer (fun z : OffsetWidthData×(ℕ×ℕ) => (z.1.1,z.2)) :=
    pair (composition first first) second
  let width := composition (composition (composition cell gridCellWidthRealizer) successor)
    ceilLogTwoRealizer
  let H : Realizer (fun z : OffsetWidthData×(ℕ×ℕ) => z.1.2) := composition first second
  let D : Realizer (fun z : OffsetWidthData×(ℕ×ℕ) => z.1.1.2) :=
    composition (composition first first) second
  let hd := composition (pair H D) add
  let accuracy := composition (pair (constant 4) hd) multiply
  exact composition (pair width accuracy) add

def freeCellsRealizer : Realizer freeCells :=
  composition (pair
    (composition (composition (composition (composition first first) first) first) tail)
    (composition (composition (composition (composition first first) first) second) tail)) cellPairsRealizer

def offsetLengthsRealizer : Realizer offsetLengths :=
  composition (pair identity freeCellsRealizer) (mapWith offsetLengthRealizer)

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_SignedPairProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary signed arithmetic used to prepare the forest evaluator

A pair stores a difference of naturals. Arithmetic never iterates through
the represented integer value, and normalization returns the exact
positive/negative parts expected by the affine penalty program.
-/

namespace ContingencyTables.SignedPairProgram

open MatchingFPRAS.TreeTyped
open scoped BigOperators

def plus (z : Signed×Signed) : Signed := (z.1.1+z.2.1,z.1.2+z.2.2)
def neg (a : Signed) : Signed := (a.2,a.1)
def minus (z : Signed×Signed) : Signed := plus (z.1,neg z.2)
def times (z : Signed×Signed) : Signed :=
  (z.1.1*z.2.1+z.1.2*z.2.2,z.1.1*z.2.2+z.1.2*z.2.1)

lemma normalize_eq (a : Signed) : normalize a=ForestAffineProgram.signedParts (value a) := by
  rcases a with ⟨p,q⟩
  apply Prod.ext <;> simp only [normalize,ForestAffineProgram.signedParts,value]
  · omega
  · omega

def plusRealizer : Realizer plus :=
  pair
    (composition (pair (composition first first) (composition second first)) add)
    (composition (pair (composition first second) (composition second second)) add)

def negRealizer : Realizer neg := pair second first

def minusRealizer : Realizer minus :=
  composition (pair first (composition second negRealizer)) plusRealizer

def timesRealizer : Realizer times :=
  pair
    (composition (pair
      (composition (pair (composition first first) (composition second first)) multiply)
      (composition (pair (composition first second) (composition second second)) multiply)) add)
    (composition (pair
      (composition (pair (composition first first) (composition second second)) multiply)
      (composition (pair (composition first second) (composition second first)) multiply)) add)

def normalizeRealizer : Realizer normalize :=
  pair subtract (composition (pair second first) subtract)

def sum (xs : List Signed) : Signed := ((xs.map Prod.fst).sum,(xs.map Prod.snd).sum)

def sumRealizer : Realizer sum :=
  pair (composition (map first) listSum) (composition (map second) listSum)

lemma value_sum (xs : List Signed) : value (sum xs)=(xs.map value).sum := by
  induction xs with
  | nil => simp [sum,value]
  | cons a xs ih =>
    simp only [sum,List.map_cons,List.sum_cons,value,Nat.cast_add] at *
    rw [←ih]
    ring

end ContingencyTables.SignedPairProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FiniteGraphCutProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executing the selected root-away cut

Deletion filters the stored adjacency rows. The endpoint and cut side
are then computed by the bounded reachability program.
-/

namespace ContingencyTables.FiniteGraphCutProgram

open MatchingFPRAS.TreeTyped Polynomial FiniteGraphRootProgram

def keepRealizer : Realizer keep := by
  let I : Realizer (fun z : KeepInput => z.1.2) := composition first second
  let U : Realizer (fun z : KeepInput => z.1.1.1) := composition (composition first first) first
  let V : Realizer (fun z : KeepInput => z.1.1.2) := composition (composition first first) second
  let neqU := composition (composition (pair second U) natEqual) boolNot
  let neqV := composition (composition (pair second V) natEqual) boolNot
  exact (choose (composition (pair I U) natEqual) neqV
    (choose (composition (pair I V) natEqual) neqU (constant true))).congr (by
      intro z
      simp [keep])

def deleteRowRealizer : Realizer deleteRow :=
  composition (f := fun z : EdgeInput×ℕ =>
      ((z.1.2,z.2),z.1.1.getD z.2 []))
    (g := fun z : ((ℕ×ℕ)×ℕ)×List ℕ => z.2.filter (fun a => keep (z.1,a)))
    (pair (pair (composition first second) second)
      (composition (pair (composition first first) second) (getDFast [])))
    (filterWith keepRealizer)

def deleteGraphRealizer : Realizer deleteGraph :=
  composition (pair identity (composition first indicesRealizer)) (mapWith deleteRowRealizer)

def reachableCodeRealizer : Realizer reachableCode :=
  composition (pair (composition first reachedRealizer) second) membership

def awayTestRealizer : Realizer (fun z : CutInput =>
    reachableCode ((deleteGraph z.1,z.1.2.1),z.2)) :=
  composition (pair (pair (composition first deleteGraphRealizer)
    (composition (composition first second) first)) second) reachableCodeRealizer

def awayCodeRealizer : Realizer awayCode :=
  choose awayTestRealizer (composition (composition first second) second)
    (composition (composition first second) first)

def cutCodeRealizer : Realizer cutCode :=
  composition (pair (pair
    (composition (composition first first) deleteGraphRealizer)
    (composition first awayCodeRealizer)) second) reachableCodeRealizer

def canonicalCutCodeRealizer : Realizer canonicalCutCode :=
  composition (pair (pair first
    (composition (pair (composition first first)
      (composition (composition first second) first)) rootCodeRealizer)) second)
    cutCodeRealizer

end ContingencyTables.FiniteGraphCutProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedCoefficientProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing signed affine coefficients from the actual forest graph

The tree and cell endpoints are ordinary vertex indices. The program
computes the canonical cut flags, tests the capacity threshold and tree
adjacency, and returns the normalized signed coefficient.
-/

namespace ContingencyTables.RootedCoefficientProgram

open MatchingFPRAS.TreeTyped
open SignedPairProgram FiniteGraphRootProgram FiniteGraphCutProgram
open scoped Classical

def bitRealizer : Realizer bit := choose identity (constant 1) (constant 0)

def signs (z : EdgeInput×(ℕ×ℕ)) : Signed :=
  (bit (canonicalCutCode (z.1,z.2.1)),bit (canonicalCutCode (z.1,z.2.2)))

def signsRealizer : Realizer signs :=
  pair
    (composition (composition (pair first (composition second first)) canonicalCutCodeRealizer)
      bitRealizer)
    (composition (composition (pair first (composition second second)) canonicalCutCodeRealizer)
      bitRealizer)

def treeSigns (z : EdgeInput) : Signed := signs (z,z.2)
def treeSignsRealizer : Realizer treeSigns := composition (pair identity second) signsRealizer
def adjacentRealizer : Realizer adjacent :=
  composition (pair (composition (pair first (composition second first)) (getDFast []))
    (composition second second)) membership

def freeTestRealizer : Realizer freeTest :=
  composition (pair (composition second leNat)
    (composition (composition (pair (composition (composition first first) first)
      (composition first second)) adjacentRealizer) boolNot)) boolAnd

def coefficient (z : Input) : Signed :=
  if freeTest z then SignedPairProgram.normalize (neg (times (signs z.1,treeSigns z.1.1))) else (0,0)

def coefficientRealizer : Realizer coefficient :=
  choose freeTestRealizer
    (composition (composition (composition (pair (composition first signsRealizer)
      (composition (composition first first) treeSignsRealizer)) timesRealizer) negRealizer)
      normalizeRealizer)
    (constant (0,0))

lemma adjacent_graph {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u v : Fin n) : adjacent (graphCode G,(u.val,v.val))=decide (G.Adj u v) := by
  apply Bool.eq_iff_iff.mpr
  simp only [adjacent,decide_eq_true_eq,graphCode_getD,adjacencyRow_mem]
  constructor
  · rintro ⟨w,hw,he⟩
    have hwu : w=v := Fin.ext hw
    subst w
    exact G.adj_symm he
  · intro h
    exact ⟨v,rfl,G.adj_symm h⟩

open CompanionFactorialApplication RootedCompletion RootedIntegerEvaluation

end ContingencyTables.RootedCoefficientProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedOffsetProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing the forest affine offset from the stored cell values

Every summand uses the executed cut flags and coefficient. The input
contains the baseline and the two stored views, rather than an affine
offset supplied by an oracle.
-/

namespace ContingencyTables.RootedOffsetProgram

open MatchingFPRAS.TreeTyped SignedPairProgram
open scoped BigOperators Classical

abbrev WeightedInput := (ℕ×ℕ)×(Signed×Signed)
abbrev Entry := (RootedCoefficientProgram.Input×(Signed×Signed))×Signed
abbrev Input := Signed×List Entry

def weightedDifference (z : WeightedInput) : Signed :=
  minus (times ((z.1.1,0),z.2.1),times ((z.1.2,0),z.2.2))

def weightedDifferenceRealizer : Realizer weightedDifference :=
  composition (pair
    (composition (pair (pair (composition first first) (constant 0))
      (composition second first)) timesRealizer)
    (composition (pair (pair (composition first second) (constant 0))
      (composition second second)) timesRealizer)) minusRealizer

def cellInput (z : Entry) : RootedCoefficientProgram.Input := z.1.1
def cellInputRealizer : Realizer cellInput := composition first first

def shifted (z : Entry) : Signed×Signed :=
  (minus (z.1.2.1,z.2),minus (z.1.2.2,z.2))
def shiftedRealizer : Realizer shifted :=
  pair
    (composition (f := fun z : Entry => (z.1.2.1,z.2)) (g := SignedPairProgram.minus)
      (pair (composition (composition first second) first) second) minusRealizer)
    (composition (f := fun z : Entry => (z.1.2.2,z.2)) (g := SignedPairProgram.minus)
      (pair (composition (composition first second) second) second) minusRealizer)

def cutTerm (z : Entry) : Signed :=
  weightedDifference (RootedCoefficientProgram.signs (cellInput z).1,shifted z)
def cutTermRealizer : Realizer cutTerm :=
  composition (pair (composition (composition cellInputRealizer first)
    RootedCoefficientProgram.signsRealizer) shiftedRealizer) weightedDifferenceRealizer

def smallTest (z : Entry) : Bool := !decide ((cellInput z).2.1 ≤ (cellInput z).2.2)
def smallTestRealizer : Realizer smallTest :=
  composition (composition (composition cellInputRealizer second) leNat) boolNot

def smallTerm (z : Entry) : Signed := if smallTest z then cutTerm z else (0,0)
def smallTermRealizer : Realizer smallTerm :=
  choose smallTestRealizer cutTermRealizer (constant (0,0))

def summand (z : Entry) : Signed :=
  plus (times (smallTerm z,RootedCoefficientProgram.treeSigns (cellInput z).1.1),
    times (RootedCoefficientProgram.coefficient (cellInput z),z.2))
def summandRealizer : Realizer summand :=
  composition (pair
    (composition (pair smallTermRealizer
      (composition (composition (composition cellInputRealizer first) first)
        RootedCoefficientProgram.treeSignsRealizer)) timesRealizer)
    (composition (pair (composition cellInputRealizer
      RootedCoefficientProgram.coefficientRealizer) second) timesRealizer)) plusRealizer

def offset (z : Input) : Signed :=
  SignedPairProgram.normalize (minus (z.1,sum (z.2.map summand)))
def offsetRealizer : Realizer offset :=
  composition (f := fun z : Input => minus (z.1,sum (z.2.map summand)))
    (g := SignedPairProgram.normalize)
    (composition (f := fun z : Input => (z.1,sum (z.2.map summand))) (g := SignedPairProgram.minus)
      (pair first (composition (composition second (map summandRealizer)) sumRealizer)) minusRealizer)
    normalizeRealizer

open CompanionFactorialApplication RootedCompletion RootedIntegerEvaluation

end ContingencyTables.RootedOffsetProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedForestDataProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Preparing a tree penalty from executed coefficients and offsets

All signed affine data are computed internally from the graph, capacities,
baseline and two stored views. Only ordinary cell indices and values occur
in the input; no affine coefficient or offset is supplied.
-/

namespace ContingencyTables.RootedForestDataProgram

open MatchingFPRAS.TreeTyped SignedPairProgram
open scoped Classical

abbrev Input := ((ℕ×ℕ)×RootedOffsetProgram.Input)×List TermInput

def scale (z : ℕ×Signed) : Signed :=
  SignedPairProgram.normalize (times ((z.1,0),z.2))

def scaleRealizer : Realizer scale :=
  composition (f := fun z : ℕ×Signed => times ((z.1,0),z.2))
    (g := SignedPairProgram.normalize)
    (composition (f := fun z : ℕ×Signed => ((z.1,0),z.2)) (g := times)
      (pair (pair first (constant 0)) second) timesRealizer) normalizeRealizer

def term (z : TermInput) : ForestAffineProgram.Term :=
  (scale (z.1.2.2+1,RootedCoefficientProgram.coefficient z.1),z.2)

def termRealizer : Realizer term :=
  pair
    (composition (f := fun z : TermInput =>
      (z.1.2.2+1,RootedCoefficientProgram.coefficient z.1)) (g := scale) (pair
      (composition (composition (composition first second) second) successor)
      (composition (f := fun z : TermInput => z.1) (g := RootedCoefficientProgram.coefficient)
        first RootedCoefficientProgram.coefficientRealizer)) scaleRealizer)
    second

def numeratorOffset (z : Input) : Signed :=
  scale (z.1.1.1,RootedOffsetProgram.offset z.1.2)

def numeratorOffsetRealizer : Realizer numeratorOffset :=
  composition (f := fun z : Input => (z.1.1.1,RootedOffsetProgram.offset z.1.2)) (g := scale)
    (pair (composition (composition first first) first)
      (composition (f := fun z : Input => z.1.2) (g := RootedOffsetProgram.offset)
        (composition first second) RootedOffsetProgram.offsetRealizer)) scaleRealizer

def prepare (z : Input) : ForestAffineProgram.Input :=
  ((numeratorOffset z,z.2.map term),z.1.1.1*z.1.1.2)

def prepareRealizer : Realizer prepare :=
  pair (pair numeratorOffsetRealizer (composition second (map termRealizer)))
    (composition (composition first first) multiply)

open CompanionFactorialApplication RootedCompletion RootedIntegerEvaluation ForestAssignmentSplit

end ContingencyTables.RootedForestDataProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedCellDataProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Assembling the affine input from ordinary rectangular cell arrays

The baseline and both stored views are binary natural matrices. The
program reads each cell once, computes its row/column vertex indices,
and constructs the offset evaluator input in row-major order.
-/

namespace ContingencyTables.RootedCellDataProgram

open MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms
open FiniteGraphRootProgram FiniteGraphCutProgram
open scoped Classical

def valuesRealizer : Realizer values :=
  pair
    (pair
      (composition (pair (composition (composition first first) first) second) matrixEntryRealizer)
      (composition (pair (composition (composition first first) second) second) matrixEntryRealizer))
    (pair
      (composition (pair (composition (composition first second) first) second) matrixEntryRealizer)
      (composition (pair (composition (composition first second) second) second) matrixEntryRealizer))

def endpointsRealizer : Realizer endpoints :=
  pair (composition second first)
    (composition (pair (composition (composition (composition first second) first) listLength)
      (composition second second)) add)
def cellValuesRealizer : Realizer cellValues :=
  composition (f := fun z : CellInput => (z.1.2,z.2)) (g := values)
    (pair (composition first second) second) valuesRealizer
def coefficientInputRealizer : Realizer coefficientInput :=
  pair
    (pair (composition (composition (composition first first) first) first)
      (composition (pair (composition first first) second) endpointsRealizer))
    (pair (composition (composition (composition first first) first) second)
      (composition (composition cellValuesRealizer first) first))

def entry (z : CellInput) : RootedOffsetProgram.Entry :=
  ((coefficientInput z,(((cellValues z).2.1,0),((cellValues z).2.2,0))),
    ((cellValues z).1.2,0))
def entryRealizer : Realizer entry :=
  pair (pair coefficientInputRealizer
    (pair (pair (composition (composition cellValuesRealizer second) first) (constant 0))
      (pair (composition (composition cellValuesRealizer second) second) (constant 0))))
    (pair (composition (composition cellValuesRealizer first) second) (constant 0))
def baselineCellRealizer : Realizer baselineCell :=
  pair (composition (composition (composition first first) second) first)
    (composition (pair (composition (composition (composition first first) second) second)
      (composition (composition second first) listLength)) subtract)

def offsetInput (z : Input) : RootedOffsetProgram.Input :=
  ((matrixEntry (z.2.1.2,baselineCell z.1),0),
    (cellPairs z.1.2).map (fun a => entry (z,a)))
def offsetInputRealizer : Realizer offsetInput :=
  pair (pair
    (composition (pair (composition (composition second first) second)
      (composition first baselineCellRealizer)) matrixEntryRealizer) (constant 0))
    (composition (pair identity (composition (composition first second) cellPairsRealizer))
      (mapWith entryRealizer))

open CompanionFactorialApplication RootedCompletion

end ContingencyTables.RootedCellDataProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedForestCatalog
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing the tree and free-cell catalogs

Both catalogs scan the rectangular cell array. A free cell is selected
by its binary capacity and absence from the supplied forest graph; a
tree cell is selected by graph adjacency. Empty forests need no chosen
edge and are handled by the same program.
-/

namespace ContingencyTables.RootedForestCatalog

open MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms
open RootedCoefficientProgram FiniteGraphRootProgram
open scoped Classical

def edgeRealizer : Realizer edge :=
  pair (composition (composition (composition first first) first) first)
    (pair (composition second first)
      (composition (pair (composition (composition (composition (composition first first) second) first)
        listLength) (composition second second)) add))
def treeTestRealizer : Realizer treeTest := composition edgeRealizer adjacentRealizer
def largeTestRealizer : Realizer largeTest :=
  composition (pair (composition (composition (composition first first) first) second)
    (composition (pair (composition first second) second) matrixEntryRealizer)) leNat
def freeTestRealizer : Realizer freeTest :=
  composition (pair largeTestRealizer (composition treeTestRealizer boolNot)) boolAnd
def selectedTestRealizer : Realizer selectedTest :=
  choose (composition first second)
    (composition (f := fun z : (Data×Bool)×(ℕ×ℕ) => (z.1.1,z.2)) (g := treeTest)
      (pair (composition first first) second) treeTestRealizer)
    (composition (f := fun z : (Data×Bool)×(ℕ×ℕ) => (z.1.1,z.2)) (g := freeTest)
      (pair (composition first first) second) freeTestRealizer)
def catalogRealizer : Realizer catalog :=
  composition (pair identity (composition (composition (composition first first) second)
    cellPairsRealizer)) (filterWith selectedTestRealizer)

open CompanionFactorialApplication ForestAssignmentSplit GraphCompletionCounts

lemma treeTest_data {m n : ℕ} (A : Instance (Fin m) (Fin n)) (i : Fin m) (j : Fin n) :
    treeTest (data A,(i.val,j.val))=decide (A.T.Adj (.inl i) (.inr j)) := by
  change adjacent (graphCode (A.T.comap finSumFinEquiv.symm),
    (i.val,(List.ofFn (fun k => (A.r k).toNat)).length+j.val))=_
  rw [List.length_ofFn]
  have he := adjacent_graph (A.T.comap finSumFinEquiv.symm)
    (finSumFinEquiv (m := m) (n := n) (.inl i))
    (finSumFinEquiv (m := m) (n := n) (.inr j))
  simpa only [SimpleGraph.comap_adj,Equiv.symm_apply_apply,finSumFinEquiv_apply_left,
    finSumFinEquiv_apply_right,Fin.val_castAdd,Fin.val_natAdd,
    finSumFinEquiv_symm_apply_castAdd,finSumFinEquiv_symm_apply_natAdd] using he

lemma freeTest_data {m n : ℕ} (A : Instance (Fin m) (Fin n)) (i : Fin m) (j : Fin n) :
    freeTest (data A,(i.val,j.val))=
      decide (A.small i j=false ∧ ¬A.T.Adj (.inl i) (.inr j)) := by
  have hlarge : A.W≤A.b i j ↔ A.small i j=false := by
    cases hs : A.small i j with
    | false => exact ⟨fun _ => rfl,fun _ => (A.hlarge _ _ hs).1⟩
    | true => simp only [Bool.true_eq_false,iff_false]; exact Nat.not_le.mpr (A.hsmall _ _ hs)
  unfold freeTest largeTest
  rw [treeTest_data]
  simp only [data,matrixEntry_code]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true,Bool.not_eq_true',decide_eq_true_eq,decide_eq_false_iff_not,hlarge]

lemma selectedTest_data {m n : ℕ} (A : Instance (Fin m) (Fin n)) (tree : Bool)
    (i : Fin m) (j : Fin n) :
    selectedTest ((data A,tree),(i.val,j.val))=decide (Selected A tree (i,j)) := by
  cases tree <;> simp only [selectedTest,Selected,Bool.false_eq_true,ite_false,ite_true, if_true,
    treeTest_data,freeTest_data]

lemma mem_catalog_data {m n : ℕ} (A : Instance (Fin m) (Fin n)) (tree : Bool)
    (ij : ℕ×ℕ) : ij∈catalog (data A,tree) ↔ ∃ a : Cell A tree,(a.val.1.val,a.val.2.val)=ij := by
  rw [catalog,List.mem_filter]
  change (ij∈cellPairs (List.ofFn (fun i => (A.r i).toNat),
    List.ofFn (fun j => (A.c j).toNat)) ∧ selectedTest ((data A,tree),ij)=true) ↔ _
  rw [mem_cellPairs]
  simp only [List.length_ofFn]
  constructor
  · rintro ⟨⟨hi,hj⟩,hs⟩
    let i : Fin m := ⟨ij.1,hi⟩
    let j : Fin n := ⟨ij.2,hj⟩
    have hp : Selected A tree (i,j) := by
      apply of_decide_eq_true
      rwa [←selectedTest_data]
    exact ⟨⟨(i,j),hp⟩,rfl⟩
  · rintro ⟨a,rfl⟩
    exact ⟨⟨a.val.1.isLt,a.val.2.isLt⟩,
      (selectedTest_data A tree a.val.1 a.val.2).trans (decide_eq_true a.property)⟩

noncomputable def catalogCell {m n : ℕ} (A : Instance (Fin m) (Fin n)) (tree : Bool)
    (i : Fin (catalog (data A,tree)).length) : Cell A tree :=
  Classical.choose ((mem_catalog_data A tree _).mp (List.getElem_mem i.isLt))

lemma catalogCell_coordinates {m n : ℕ} (A : Instance (Fin m) (Fin n)) (tree : Bool)
    (i : Fin (catalog (data A,tree)).length) :
    ((catalogCell A tree i).val.1.val,(catalogCell A tree i).val.2.val)=
      (catalog (data A,tree))[i.val] :=
  Classical.choose_spec ((mem_catalog_data A tree _).mp (List.getElem_mem i.isLt))

lemma catalogCell_bijective {m n : ℕ} (A : Instance (Fin m) (Fin n)) (tree : Bool) :
    Function.Bijective (catalogCell A tree) := by
  constructor
  · intro i j h
    have he := congrArg (fun a : Cell A tree => (a.val.1.val,a.val.2.val)) h
    rw [catalogCell_coordinates,catalogCell_coordinates] at he
    exact Fin.ext ((catalog_nodup (data A,tree)).getElem_inj_iff.mp he)
  · intro a
    have hm : (a.val.1.val,a.val.2.val)∈catalog (data A,tree) :=
      (mem_catalog_data A tree _).mpr ⟨a,rfl⟩
    obtain ⟨i,hi,hval⟩ := List.mem_iff_getElem.mp hm
    refine ⟨⟨i,hi⟩,?_⟩
    have he := (catalogCell_coordinates A tree ⟨i,hi⟩).trans hval
    apply Subtype.ext
    exact Prod.ext (Fin.ext (congrArg Prod.fst he)) (Fin.ext (congrArg Prod.snd he))

noncomputable def freeEquiv {m n : ℕ} (A : Instance (Fin m) (Fin n)) :
    Fin (catalog (data A,false)).length ≃ FreeCell A.small A.T :=
  Equiv.ofBijective (catalogCell A false) (catalogCell_bijective A false)

end ContingencyTables.RootedForestCatalog

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedDemandProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing the root-demand input from the actual cell arrays

The two natural entries at a vertex encode its signed small-cell
discrepancy. They are formed by rectangular scans and then passed to the
component/root program.
-/

namespace ContingencyTables.RootedDemandProgram

open MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms SignedPairProgram
open FiniteGraphRootProgram
open scoped BigOperators Classical

def valuesRealizer : Realizer values :=
  composition (f := fun z : TermInput =>
    (((z.1.1.1.2,z.1.1.2.1),z.1.1.2.2),z.2)) (g := RootedCellDataProgram.values) (pair
    (pair (pair (composition (composition (composition first first) first) second)
      (composition (composition (composition first first) second) first))
      (composition (composition (composition first first) second) second))
    second) RootedCellDataProgram.valuesRealizer
def retainedTestRealizer : Realizer retainedTest :=
  composition (composition (pair (composition (composition first first) first) second)
    RootedForestCatalog.largeTestRealizer) boolNot
def rowTestRealizer : Realizer rowTest :=
  composition (pair (composition first second) (composition second first)) natEqual
def columnTestRealizer : Realizer columnTest :=
  composition (pair (composition first second)
    (composition (pair
      (composition (composition (composition (composition (composition (composition first first)
        first) first) second) first) listLength) (composition second second)) add)) natEqual

def rowPair (z : TermInput) : Signed := ((values z).1.2,(values z).2.1)
def rowPairRealizer : Realizer rowPair :=
  pair
    (composition (f := values) (g := fun v : (ℕ×ℕ)×(ℕ×ℕ) => v.1.2)
      valuesRealizer (composition first second))
    (composition (f := values) (g := fun v : (ℕ×ℕ)×(ℕ×ℕ) => v.2.1)
      valuesRealizer (composition second first))

def columnPair (z : TermInput) : Signed := ((values z).2.2,(values z).1.2)
def columnPairRealizer : Realizer columnPair :=
  pair
    (composition (f := values) (g := fun v : (ℕ×ℕ)×(ℕ×ℕ) => v.2.2)
      valuesRealizer (composition second second))
    (composition (f := values) (g := fun v : (ℕ×ℕ)×(ℕ×ℕ) => v.1.2)
      valuesRealizer (composition first second))

def term (z : TermInput) : Signed :=
  if retainedTest z then
    plus ((if rowTest z then rowPair z else (0,0)),
      (if columnTest z then columnPair z else (0,0)))
  else (0,0)
def termRealizer : Realizer term :=
  choose retainedTestRealizer
    (composition (pair (choose rowTestRealizer rowPairRealizer (constant (0,0)))
      (choose columnTestRealizer columnPairRealizer (constant (0,0)))) plusRealizer)
    (constant (0,0))

def demand (z : Input×ℕ) : Signed :=
  sum ((cellPairs z.1.1.1.2).map (fun a => term (z,a)))
def demandRealizer : Realizer demand :=
  composition (composition (pair identity
    (composition (composition (composition (composition first first) first) second)
      cellPairsRealizer)) (mapWith termRealizer)) sumRealizer
def vertexCountRealizer : Realizer vertexCount :=
  composition (pair
    (composition (composition (composition (composition first first) second) first) listLength)
    (composition (composition (composition (composition first first) second) second) listLength)) add
def verticesRealizer : Realizer vertices := composition vertexCountRealizer range

def demandList (z : Input) : List Signed := (vertices z).map (fun v => demand (z,v))
def demandListRealizer : Realizer demandList :=
  composition (pair identity verticesRealizer) (mapWith demandRealizer)

def rootCount (z : Input) : ℕ := RootedComponentCode.count (z.1.1.1.1,demandList z)
def rootCountRealizer : Realizer rootCount :=
  composition (pair (composition (composition (composition first first) first) first)
    demandListRealizer) RootedComponentCode.countRealizer

open CompanionFactorialApplication RootedCompletion

end ContingencyTables.RootedDemandProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedTreeInputProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Building tree-local inputs from the common raw arrays

The graph, capacity array, baseline and stored views are shared across
all tree terms. A term uses only its pair of cell indices; the program
builds its offset frame and reads the free-grid coordinates in catalog
order.
-/

namespace ContingencyTables.RootedTreeInputProgram

open MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms
open scoped Classical

def metadataRealizer : Realizer metadata := composition first first
def edgeRealizer : Realizer edge :=
  composition (pair metadataRealizer second) RootedForestCatalog.edgeRealizer
def treeInputRealizer : Realizer treeInput :=
  pair
    (pair (pair edgeRealizer
      (composition (f := metadata) (g := fun d : RootedForestCatalog.Data => d.1.1.2)
        metadataRealizer (composition (composition first first) second)))
      (composition (f := metadata) (g := fun d : RootedForestCatalog.Data => d.1.2)
        metadataRealizer (composition first second)))
    (pair (pair (composition (f := metadata) (g := fun d : RootedForestCatalog.Data => d.2)
      metadataRealizer second)
      (composition (composition first second) first))
      (composition (composition first second) second))
def termAtRealizer : Realizer termAt :=
  pair
    (composition (f := fun z : TermBundle×ℕ => (z.1.1.1,z.1.1.2.getD z.2 (0,0)))
      (g := RootedCellDataProgram.coefficientInput)
      (pair (composition (composition first first) first)
        (composition (pair (composition (composition first first) second) second)
          (getDFast (0,0)))) RootedCellDataProgram.coefficientInputRealizer)
    (composition (pair (composition first second) second) (getDFast 0))
def indicesRealizer : Realizer indices := composition listLength range
def termsRealizer : Realizer terms :=
  composition (pair identity (composition (composition first second) indicesRealizer))
    (mapWith termAtRealizer)

open CompanionFactorialApplication RootedCompletion ForestAssignmentSplit

end ContingencyTables.RootedTreeInputProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedForestPrepareProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Preparing the whole selected-root forest penalty

The program takes the four cell arrays and the graph. It computes the
root discrepancy, both catalogs, every cut coefficient and every affine
offset before invoking the rational penalty evaluator.
-/

namespace ContingencyTables.RootedForestPrepareProgram

open MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms
open scoped Classical

def treeFrameRealizer : Realizer treeFrame :=
  composition (f := fun z : TreeInput => (z.1.1.1,z.2))
    (g := RootedTreeInputProgram.treeInput)
    (pair (composition (composition first first) first) second)
    RootedTreeInputProgram.treeInputRealizer
def freeCellsRealizer : Realizer freeCells :=
  composition (f := fun z : TreeInput => (z.1.1.1.1,false))
    (g := RootedForestCatalog.catalog)
    (pair (composition (composition (composition first first) first) first)
      (constant false)) RootedForestCatalog.catalogRealizer
def widthCapacityRealizer : Realizer widthCapacity :=
  pair (composition (composition first first) second)
    (composition (f := fun z : TreeInput => (z.1.1.1.1.2,z.2))
      (g := matrixEntry)
      (pair (composition (composition (composition (composition first first) first) first)
        second) second) matrixEntryRealizer)

def forestInput (z : TreeInput) : RootedForestDataProgram.Input :=
  ((widthCapacity z,RootedCellDataProgram.offsetInput (treeFrame z)),
    RootedTreeInputProgram.terms ((treeFrame z,freeCells z),z.1.2))
def forestInputRealizer : Realizer forestInput :=
  pair (pair widthCapacityRealizer
    (composition (f := treeFrame) (g := RootedCellDataProgram.offsetInput)
      treeFrameRealizer RootedCellDataProgram.offsetInputRealizer))
    (composition (f := fun z : TreeInput => ((treeFrame z,freeCells z),z.1.2))
      (g := RootedTreeInputProgram.terms)
      (pair (pair treeFrameRealizer freeCellsRealizer) (composition first second))
      RootedTreeInputProgram.termsRealizer)

def prepareTree (z : TreeInput) : ForestAffineProgram.Input :=
  RootedForestDataProgram.prepare (forestInput z)
def prepareTreeRealizer : Realizer prepareTree :=
  composition (f := forestInput) (g := RootedForestDataProgram.prepare)
    forestInputRealizer RootedForestDataProgram.prepareRealizer
def treeBundleRealizer : Realizer treeBundle :=
  pair (pair (composition first second) (composition (composition first first) second)) second
def treeCellsRealizer : Realizer treeCells :=
  composition (f := fun z : Input => (z.1.2.1,true)) (g := RootedForestCatalog.catalog)
    (pair (composition (composition first second) first) (constant true))
    RootedForestCatalog.catalogRealizer

def prepareTrees (z : Input) : List ForestAffineProgram.Input :=
  (treeCells z).map (fun a => prepareTree (treeBundle z,a))
def prepareTreesRealizer : Realizer prepareTrees :=
  composition (f := fun z : Input => (treeBundle z,treeCells z))
    (g := fun z => z.2.map (fun a => prepareTree (z.1,a)))
    (pair treeBundleRealizer treeCellsRealizer) (mapWith prepareTreeRealizer)

def prepare (z : Input) : ForestPenaltyProgram.Input :=
  ((z.1.1.1,RootedDemandProgram.rootCount z.1.2),prepareTrees z)
def prepareRealizer : Realizer prepare :=
  pair (pair (composition (composition first first) first)
    (composition (f := fun z : Input => z.1.2) (g := RootedDemandProgram.rootCount)
      (composition first second) RootedDemandProgram.rootCountRealizer)) prepareTreesRealizer

open CompanionFactorialApplication RootedCompletion ForestAssignmentSplit

end ContingencyTables.RootedForestPrepareProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedPenaltyEvaluateProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial binary program for the actual forest exponent

The bin width and height are computed from the dimension allowance,
capacity scale and phase coefficient. All forest metadata is generated
from the cell arrays by `RootedForestPrepareProgram`.
-/

namespace ContingencyTables.RootedPenaltyEvaluateProgram

open MatchingFPRAS.TreeTyped
open scoped Classical

def squareDimensionRealizer : Realizer squareDimension :=
  composition (pair (composition first first) (composition first first)) multiply
def scaledSquareRealizer : Realizer scaledSquare :=
  composition (f := fun z : Parameters => (z.2.1,squareDimension z)) (g := fun z => z.1*z.2)
    (pair (composition second first) squareDimensionRealizer) multiply
def widthRealizer : Realizer width :=
  composition (f := fun z : Parameters => (16,scaledSquare z)) (g := fun z => z.1*z.2)
    (pair (constant 16) scaledSquareRealizer) multiply
def baseHeightRealizer : Realizer baseHeight :=
  composition (f := fun z : Parameters => (10,scaledSquare z)) (g := fun z => z.1*z.2)
    (pair (constant 10) scaledSquareRealizer) multiply
def heightRealizer : Realizer height :=
  composition (f := fun z : Parameters => (baseHeight z,z.1.2+1)) (g := fun z => z.1*z.2)
    (pair baseHeightRealizer (composition (composition first second) successor)) multiply
def forestInputRealizer : Realizer forestInput :=
  pair (pair (pair (composition (composition first second) first)
    (composition (f := fun z : Input => z.1) (g := width) first widthRealizer))
    (composition second first)) (composition second second)

def exponentInput (z : Input) : ForestPenaltyProgram.ExponentInput :=
  ((z.1.2.2,height z.1),RootedForestPrepareProgram.prepare (forestInput z))
def exponentInputRealizer : Realizer exponentInput :=
  pair (pair (composition (composition first second) second)
    (composition (f := fun z : Input => z.1) (g := height) first heightRealizer))
    (composition (f := forestInput) (g := RootedForestPrepareProgram.prepare)
      forestInputRealizer RootedForestPrepareProgram.prepareRealizer)

def evaluate (z : Input) : ℕ := ForestPenaltyProgram.exponentCode (exponentInput z)
def evaluateRealizer : Realizer evaluate :=
  composition (f := exponentInput) (g := ForestPenaltyProgram.exponentCode)
    exponentInputRealizer ForestPenaltyProgram.exponentCodeRealizer

open CompanionFactorialApplication RootedCompletion ForestAssignmentSplit

end ContingencyTables.RootedPenaltyEvaluateProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedOracleStepProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial execution of the catalog-order oracle step

The program uses the computed forest exponent twice, one arithmetic
axis proposal and one independent bounded dyadic acceptance word.
-/

namespace ContingencyTables.RootedOracleStepProgram

open MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms
open scoped Classical

abbrev Data := ℕ×RootedPenaltyEvaluateProgram.Input
abbrev StepInput := Data×(List Bool×List Bool)

def replace (z : RootedPenaltyEvaluateProgram.Input×List ℕ) :
    RootedPenaltyEvaluateProgram.Input := (z.1.1,(z.1.2.1,z.2))
def replaceRealizer : Realizer replace :=
  pair (composition first first) (pair (composition (composition first second) first) second)

def candidate (z : StepInput) : Option (List ℕ) :=
  axisWordStep ((z.1.1,z.1.2.2.2),z.2.1)
def candidateRealizer : Realizer candidate :=
  composition (f := fun z : StepInput => ((z.1.1,z.1.2.2.2),z.2.1)) (g := axisWordStep)
    (pair (pair (composition first first)
      (composition (composition (composition first second) second) second))
      (composition second first)) axisWordStepRealizer

def currentData (z : StepInput×List ℕ) : RootedPenaltyEvaluateProgram.Input := z.1.1.2
def currentDataRealizer : Realizer currentData := composition (composition first first) second

def candidateData (z : StepInput×List ℕ) : RootedPenaltyEvaluateProgram.Input :=
  replace (currentData z,z.2)
def candidateDataRealizer : Realizer candidateData :=
  composition (f := fun z : StepInput×List ℕ => (currentData z,z.2)) (g := replace)
    (pair currentDataRealizer second) replaceRealizer

def gap (z : StepInput×List ℕ) : ℕ :=
  RootedPenaltyEvaluateProgram.evaluate (candidateData z)-
    RootedPenaltyEvaluateProgram.evaluate (currentData z)
def gapRealizer : Realizer gap :=
  composition (f := fun z : StepInput×List ℕ =>
    (RootedPenaltyEvaluateProgram.evaluate (candidateData z),
      RootedPenaltyEvaluateProgram.evaluate (currentData z))) (g := fun z => z.1-z.2)
    (pair
      (composition (f := candidateData) (g := RootedPenaltyEvaluateProgram.evaluate)
        candidateDataRealizer RootedPenaltyEvaluateProgram.evaluateRealizer)
      (composition (f := currentData) (g := RootedPenaltyEvaluateProgram.evaluate)
        currentDataRealizer RootedPenaltyEvaluateProgram.evaluateRealizer)) subtract

def acceptCandidate (z : StepInput×List ℕ) : List ℕ :=
  if dyadicWordAccept (z.1.2.2,gap z) then z.2 else z.1.1.2.2.2
def acceptCandidateRealizer : Realizer acceptCandidate :=
  choose
    (composition (f := fun z : StepInput×List ℕ => (z.1.2.2,gap z)) (g := dyadicWordAccept)
      (pair (composition (composition first second) second) gapRealizer) dyadicWordAcceptRealizer)
    second (composition (composition currentDataRealizer second) second)

def step (z : StepInput) : List ℕ :=
  (candidate z).elim z.1.2.2.2 (fun xs => acceptCandidate (z,xs))
def stepRealizer : Realizer step :=
  composition (f := fun z : StepInput => (z,candidate z))
    (g := fun z => z.2.elim z.1.1.2.2.2 (fun xs => acceptCandidate (z.1,xs)))
    (pair identity candidateRealizer)
    (optionCases (composition (composition (composition first second) second) second)
      acceptCandidateRealizer)

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary FairBits

end ContingencyTables.RootedOracleStepProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedOracleWordProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A single fixed word drives an executed oracle transition -/

namespace ContingencyTables.RootedOracleStepProgram

open MatchingFPRAS.TreeTyped DensePrograms
open scoped Classical

abbrev WordInput := Data×List Bool

def proposalWidth (z : WordInput) : ℕ := Nat.clog 2 (8*z.1.2.1.1.1)
def proposalWidthRealizer : Realizer proposalWidth := by
  let D : Realizer (fun z : WordInput => z.1.2.1.1.1) :=
    composition (composition (composition (composition first second) first) first) first
  let M : Realizer (fun z : WordInput => 8*z.1.2.1.1.1) :=
    composition (f := fun z : WordInput => (8,z.1.2.1.1.1))
      (g := fun x : ℕ×ℕ => x.1*x.2) (pair (constant 8) D) multiply
  exact composition (f := fun z : WordInput => 8*z.1.2.1.1.1)
    (g := Nat.clog 2) M ceilLogTwoRealizer

def wordStep (z : WordInput) : List ℕ :=
  step (z.1,(z.2.take (proposalWidth z),z.2.drop (proposalWidth z)))
def wordStepRealizer : Realizer wordStep :=
  composition (f := fun z : WordInput =>
    (z.1,(z.2.take (proposalWidth z),z.2.drop (proposalWidth z)))) (g := step)
    (pair first (pair
      (composition (pair second proposalWidthRealizer) takeFast)
      (composition (pair second proposalWidthRealizer) dropFast))) stepRealizer

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary FairBits

end ContingencyTables.RootedOracleStepProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedOracleWalkProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial execution of an oracle walk

The immutable graph and cell arrays are kept separately from the grid
coordinates. A coordinate changes by at most one per transition, which
bounds every accumulator reached by the binary list fold.
-/

namespace ContingencyTables.RootedOracleWalkProgram

open MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms Polynomial
open scoped Classical

def toData (z : State) : RootedOracleStepProgram.Data :=
  (z.1.1,(z.1.2.1,(z.1.2.2,z.2)))
def toDataRealizer : Realizer toData :=
  pair (composition first first)
    (pair (composition (composition first second) first)
      (pair (composition (composition first second) second) second))

def advance (z : List Bool×State) : State :=
  (z.2.1,RootedOracleStepProgram.wordStep (toData z.2,z.1))
def advanceRealizer : Realizer advance :=
  pair (composition second first)
    (composition (f := fun z : List Bool×State => (toData z.2,z.1))
      (g := RootedOracleStepProgram.wordStep)
      (pair (composition (f := fun z : List Bool×State => z.2) (g := toData)
        second toDataRealizer) first) RootedOracleStepProgram.wordStepRealizer)

def walkWords (z : State×List (List Bool)) : State :=
  z.2.foldl (fun state bits => advance (bits,state)) z.1
def walkWordsRealizer : Realizer walkWords :=
  composition (pair second first) (fold advanceRealizer)

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary FirstSuccess

noncomputable section
variable {m n : ℕ}

def data (A : Instance (Fin m) (Fin n)) (C a K : ℕ) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) : State :=
  ((K,(((A.d,A.W),(C,a)),
    RootedDemandProgram.data A (ForestCountIdentification.smallX A.small z)
      (fun i j => A.b i j-ForestCountIdentification.smallY A.small z i j))),gridNatCode v)

end
end ContingencyTables.RootedOracleWalkProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_NaturalBlockProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded scans of natural-number blocks

Numeric widths select bounded slices of the supplied list. They never
control an allocation, so malformed widths preserve polynomial cost.
-/

namespace ContingencyTables.NaturalBlockProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial

def startRealizer : Realizer start :=
  composition (composition (pair (composition first first) second) takeFast) listSum
def blockRealizer : Realizer block :=
  composition (pair
    (composition (pair (composition first second) startRealizer) dropFast)
    (composition (pair (composition first first) second) (getDFast 0))) takeFast
def indicesRealizer : Realizer indices := composition (composition first listLength) range
def blocksRealizer : Realizer blocks :=
  composition (pair identity indicesRealizer) (mapWith blockRealizer)

end ContingencyTables.NaturalBlockProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_PairedProfileProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reading the two cell counts from the actual paired code

The block widths come from the stored capacity list. Each count scans
only supplied code entries and clips them to one, including on malformed
input. No numeric capacity controls an unbounded allocation.
-/

namespace ContingencyTables.PairedProfileProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial

def sideValueRealizer : Realizer sideValue :=
  composition (f := fun z : ReadInput =>
      (z.1.1.getD (if z.1.2 then z.2.2 else z.2.1) 0,1))
    (g := fun p : ℕ × ℕ => min p.1 p.2)
    (pair (composition (pair (composition first first)
      (choose (composition first second) (composition second second)
        (composition second first))) (getDFast 0)) (constant 1)) minimum
def sideEntriesRealizer : Realizer sideEntries :=
  composition (pair identity (composition first PairedCatalogProgram.catalogRealizer))
    (mapWith sideValueRealizer)
def sideCountRealizer : Realizer sideCount := composition sideEntriesRealizer listSum
def widthRealizer : Realizer width :=
  composition (f := fun n : ℕ => (2,n)) (g := fun p : ℕ × ℕ => p.1*p.2)
    (pair (constant 2) identity) multiply
def rowsRealizer : Realizer rows :=
  composition (pair (composition first (map widthRealizer)) second)
    NaturalBlockProgram.blocksRealizer

end ContingencyTables.PairedProfileProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_PairedDemandProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Replacing the oracle demand by the current encoded paired state

Only the retained-cell catalog and the supplied state are scanned. The
large cells receive zero in each sparse view and hence retain their full
capacity in the complemented column demand.
-/

namespace ContingencyTables.PairedDemandProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms

def cellInputRealizer : Realizer cellInput :=
  pair (pair (composition first second) second) (composition (composition first first) second)
def cellsRealizer : Realizer cells :=
  composition (f := fun z : Input => z.1.1) (g := cellInput)
    (composition first first) cellInputRealizer
end ContingencyTables.PairedDemandProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FractionAggregateProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial exact fraction averages and products

These are the arithmetic folds used by the executed weight estimator.
Normalization makes the average valid on every input, including a raw
fraction with denominator zero.
-/

namespace ContingencyTables.FractionAggregateProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial
open scoped BigOperators

def averageRealizer : Realizer average :=
  composition (f := fun xs : List TreeFraction.Fraction =>
    (TreeFraction.sum (xs.map TreeFraction.normalize),(xs.length,1))) (g := TreeFraction.div)
    (pair (composition (map TreeFraction.normalizeRealizer) TreeFraction.sumRealizer)
      (pair listLength (constant 1))) TreeFraction.divRealizer
def productRealizer : Realizer product :=
  composition (f := fun xs : List TreeFraction.Fraction => (xs,(1,1)))
    (g := fun z : List TreeFraction.Fraction×TreeFraction.Fraction =>
      z.1.foldl (fun a b => TreeFraction.mul (b,a)) z.2)
    (pair identity (constant (1,1))) (fold TreeFraction.mulRealizer)

end ContingencyTables.FractionAggregateProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_PairedFactorialProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact factorial multiplier from the encoded paired state

Every factorial argument is bounded by the supplied code length. In a
valid code each cell block has length twice its capacity, so the computed
denominator is exactly the manuscript's capacity factorial.
-/

namespace ContingencyTables.PairedFactorialProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial PairedProfileProgram
open scoped BigOperators Classical

def sideFactorRealizer : Realizer sideFactor := composition sideCountRealizer factorial
def pairCountRealizer : Realizer pairCount :=
  composition (pair listLength (constant 2)) quotient
def denominatorRealizer : Realizer denominator := composition pairCountRealizer factorial
def numeratorRealizer : Realizer numerator :=
  composition (f := fun xs : List ℕ => (sideFactor (xs,false),sideFactor (xs,true)))
    (g := fun p : ℕ × ℕ => p.1*p.2)
    (pair
      (composition (f := fun xs : List ℕ => (xs,false)) (g := sideFactor)
        (pair identity (constant false)) sideFactorRealizer)
      (composition (f := fun xs : List ℕ => (xs,true)) (g := sideFactor)
        (pair identity (constant true)) sideFactorRealizer)) multiply
def rowRatioRealizer : Realizer rowRatio :=
  composition (pair numeratorRealizer denominatorRealizer) TreeFraction.normalizeRealizer
def outputRealizer : Realizer output :=
  composition (composition rowsRealizer (map rowRatioRealizer))
    FractionAggregateProgram.productRealizer
end ContingencyTables.PairedFactorialProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_MedianFractionProgram
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary fraction median with polynomial running time -/

namespace ContingencyTables.MedianFractionProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped MatchingFPRAS.TreeFraction Polynomial

def stepRealizer : Realizer step := by
  let q : Realizer (fun z : Fraction × State => z.2.1) := composition second first
  let xs : Realizer (fun z : Fraction × State => z.1::z.2.2.1) :=
    composition (pair first (composition (composition second second) first)) listCons
  let yes : Realizer (fun z : Fraction × State => z.1::z.2.2.2) :=
    composition (pair first (composition (composition second second) second)) listCons
  let no : Realizer (fun z : Fraction × State => z.2.1::z.1::z.2.2.1) :=
    composition (pair q xs) listCons
  exact pair q (pair xs (choose (composition (pair first q) TreeFraction.lessRealizer) yes no))

def insertRealizer : Realizer insert := by
  let prep : Realizer (fun z : Fraction × List Fraction => (z.2.reverse,(z.1,([],[z.1])))) :=
    pair (composition second reverse)
      (pair first (pair (constant ([] : List Fraction)) (composition (pair first (constant ([] : List Fraction))) listCons)))
  let tail : Realizer (fun z : List Fraction × State =>
      (z.1.foldl (fun s x => step (x,s)) z.2).2.2) :=
    composition (f := fun z : List Fraction × State =>
      (z.1.foldl (fun s x => step (x,s)) z.2).2) (g := fun z => z.2)
      (composition (fold stepRealizer) second) second
  exact composition
    (f := fun z : Fraction × List Fraction => (z.2.reverse,(z.1,([],[z.1]))))
    (g := fun z : List Fraction × State =>
      (z.1.foldl (fun s x => step (x,s)) z.2).2.2) prep tail

def sortRealizer : Realizer sort :=
  composition (f := fun xs : List Fraction => (xs.reverse,([] : List Fraction)))
    (g := fun z : List Fraction × List Fraction => z.1.foldl (fun s x => insert (x,s)) z.2)
    (pair reverse (constant [])) (fold insertRealizer)

def medianRealizer : Realizer median :=
  composition (f := fun xs : List Fraction => (sort (xs.map TreeFraction.normalize),xs.length/2))
    (g := fun z : List Fraction × ℕ => z.1.getD z.2 (0,1)) (pair (composition (f := fun xs : List Fraction => xs.map TreeFraction.normalize)
      (g := sort) (TreeTyped.map normalizeRealizer) sortRealizer)
    (composition (pair listLength (constant 2)) quotient)) (getDFast (0,1))

end ContingencyTables.MedianFractionProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_SignedFloorProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary floor of a signed rational

Two natural quotients and the comparison of their remainders compute
the exact floor. No loop depends on the numeric numerator or denominator.
-/

namespace ContingencyTables.SignedFloorProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped SignedPairProgram

def numeratorQuotientRealizer : Realizer numeratorQuotient :=
  composition (pair (composition first first) second) quotient
def negativeQuotientRealizer : Realizer negativeQuotient :=
  composition (pair (composition first second) second) quotient
def carryRealizer : Realizer carry :=
  composition (pair
    (composition (pair (composition first first) second) remainder)
    (composition (pair (composition first second) second) remainder)) less
def carryValueRealizer : Realizer carryValue :=
  choose carryRealizer (constant 1) (constant 0)
def rawRealizer : Realizer raw := pair numeratorQuotientRealizer
  (composition (pair negativeQuotientRealizer carryValueRealizer) add)
def floorCodeRealizer : Realizer floorCode :=
  (choose (composition (pair second (constant 0)) natEqual) (constant (0,0))
    rawRealizer).congr (fun z=>by simp only [floorCode,Function.comp_apply,decide_eq_true_eq])

lemma raw_value (p n d : ℕ) (hd : 0<d) :
    value (raw ((p,n),d))=⌊((p:ℚ)-n)/d⌋ := by
  have hdQ: (0:ℚ)<d:=by exact_mod_cast hd
  have hp: ((p%d:ℕ):ℚ)+(d:ℚ)*((p/d:ℕ):ℚ)=(p:ℚ):=by
    exact_mod_cast Nat.mod_add_div p d
  have hn: ((n%d:ℕ):ℚ)+(d:ℚ)*((n/d:ℕ):ℚ)=(n:ℚ):=by
    exact_mod_cast Nat.mod_add_div n d
  have hpr: ((p%d:ℕ):ℚ)<d:=by exact_mod_cast Nat.mod_lt p hd
  have hnr: ((n%d:ℕ):ℚ)<d:=by exact_mod_cast Nat.mod_lt n hd
  have hp0: (0:ℚ)≤((p%d:ℕ):ℚ):=Nat.cast_nonneg _
  have hn0: (0:ℚ)≤((n%d:ℕ):ℚ):=Nat.cast_nonneg _
  symm
  apply Int.floor_eq_iff.mpr
  by_cases h: p%d<n%d
  · have hr: ((p%d:ℕ):ℚ)<((n%d:ℕ):ℚ):=by exact_mod_cast h
    simp only [raw,numeratorQuotient,negativeQuotient,carryValue,carry,h,decide_true,
      ite_true, if_true,value,Nat.cast_add,Nat.cast_one,Int.cast_sub,
      Int.cast_add,Int.cast_one,Int.cast_natCast]
    constructor
    · rw [le_div_iff₀ hdQ]
      nlinarith
    · rw [div_lt_iff₀ hdQ]
      nlinarith
  · have hr: ((n%d:ℕ):ℚ)≤((p%d:ℕ):ℚ):=by exact_mod_cast (Nat.le_of_not_gt h)
    simp only [raw,numeratorQuotient,negativeQuotient,carryValue,carry,h,decide_false,
      Bool.false_eq_true,ite_false,Nat.add_zero,value,Int.cast_sub,Int.cast_natCast]
    constructor
    · rw [le_div_iff₀ hdQ]
      nlinarith
    · rw [div_lt_iff₀ hdQ]
      nlinarith

theorem floorCode_value (p n d : ℕ) :
    value (floorCode ((p,n),d))=⌊((p:ℚ)-n)/d⌋ := by
  by_cases hd: d=0
  · simp [floorCode,hd,value]
  · simp only [floorCode,hd,ite_false]
    exact raw_value p n d (Nat.pos_of_ne_zero hd)

abbrev ScaledInput := Input×List Bool

def scale (z : ScaledInput) : Input :=
  ((z.2.length*z.1.1.1,z.2.length*z.1.1.2),z.1.2)
def scaleRealizer : Realizer scale :=
  pair (pair
    (composition (pair (composition second listLength)
      (composition (composition first first) first)) multiply)
    (composition (pair (composition second listLength)
      (composition (composition first first) second)) multiply)) (composition first second)

def scaledFloor (z : ScaledInput) : Signed := floorCode (scale z)
def scaledFloorRealizer : Realizer scaledFloor := composition scaleRealizer floorCodeRealizer

end ContingencyTables.SignedFloorProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_BinIntervalProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary evaluation of a bin interval and its bounded quotient draw

The lower endpoint is computed as the negative floor of a negative
rational. Thus the executed arithmetic uses natural quotient/remainder,
without enumerating any of the integers in the interval.
-/

namespace ContingencyTables.BinIntervalProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped SignedPairProgram ProfilePrograms

def endpointRealizer : Realizer endpoint :=
  composition (f := fun z : Input => SignedPairProgram.normalize
      (SignedFloorProgram.floorCode (negativeInput z))) (g := Prod.snd)
    (composition (f := fun z : Input => SignedFloorProgram.floorCode (negativeInput z))
      (g := SignedPairProgram.normalize)
      (composition negativeInputRealizer SignedFloorProgram.floorCodeRealizer)
      SignedPairProgram.normalizeRealizer) second

theorem endpoint_eq (K N beta : ℕ) : endpoint ((K,N),beta)=FairBits.endpoint K N beta := by
  unfold endpoint negativeInput
  rw [SignedPairProgram.normalize_eq,SignedFloorProgram.floorCode_value]
  change (-⌊((0:ℚ)-((beta*N:ℕ):ℚ))/K⌋).toNat=FairBits.endpoint K N beta
  have he : ((0:ℚ)-((beta*N:ℕ):ℚ))/K= -((beta:ℚ)*N/K) := by
    push_cast
    ring
  rw [he,Int.floor_neg,neg_neg,Int.ceil_toNat]
  rfl

def nextRealizer : Realizer next := pair first (composition second successor)
def intervalSizeRealizer : Realizer intervalSize :=
  composition (f := fun z : Input => (endpoint (next z),endpoint z))
    (g := fun p : ℕ×ℕ => p.1-p.2)
    (pair (composition (f := next) (g := endpoint) nextRealizer endpointRealizer)
      endpointRealizer) subtract

theorem intervalSize_eq (K N beta : ℕ) :
    intervalSize ((K,N),beta)=CompanionOracleDensity.intervalSize K N beta := by
  unfold intervalSize next
  rw [endpoint_eq,endpoint_eq]
  rfl

def drawRealizer : Realizer draw :=
  composition (f := fun z : Input×List Bool =>
      (endpoint z.1,scaledWordValue (intervalSize z.1,z.2)))
    (g := fun p : ℕ×ℕ => p.1+p.2)
    (pair (composition (f := fun z : Input×List Bool => z.1) (g := endpoint)
        first endpointRealizer)
      (composition (f := fun z : Input×List Bool => (intervalSize z.1,z.2))
        (g := scaledWordValue)
        (pair (composition (f := fun z : Input×List Bool => z.1) (g := intervalSize)
          first intervalSizeRealizer) second) scaledWordRealizer)) add

end ContingencyTables.BinIntervalProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_BinVectorProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The executed independent bin-coordinate draws

Each coordinate reserves a width determined by its full range, and
uses only the prefix needed by the selected interval. The implementation
splits one Boolean list and performs binary arithmetic per coordinate.
-/

namespace ContingencyTables.BinVectorProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms
open scoped BigOperators

/-- The interval input together with accuracy and dimension allowances. -/
abbrev Frame := BinIntervalProgram.Input×(ℕ×ℕ)

def reservedWidth (z : Frame) : ℕ := Nat.clog 2 (z.1.1.2+1)+4*(z.2.1+z.2.2)
def reservedWidthRealizer : Realizer reservedWidth := by
  let rangeR : Realizer (fun z : Frame => z.1.1.2) :=
    composition (composition first first) second
  let binary := composition (composition rangeR successor) ceilLogTwoRealizer
  let accuracy := composition (f := fun z : Frame => (4,z.2.1+z.2.2))
    (g := fun p : ℕ×ℕ => p.1*p.2)
    (pair (constant 4) (composition second add)) multiply
  exact composition (f := fun z : Frame =>
    (Nat.clog 2 (z.1.1.2+1),4*(z.2.1+z.2.2)))
    (g := fun p : ℕ×ℕ => p.1+p.2) (pair binary accuracy) add

def activeWidth (z : Frame) : ℕ :=
  Nat.clog 2 (BinIntervalProgram.intervalSize z.1+1)+4*(z.2.1+z.2.2)
def activeWidthRealizer : Realizer activeWidth := by
  let sizeR : Realizer (fun z : Frame => BinIntervalProgram.intervalSize z.1) :=
    composition (f := fun z : Frame => z.1) (g := BinIntervalProgram.intervalSize)
      first BinIntervalProgram.intervalSizeRealizer
  let binary : Realizer (fun z : Frame => Nat.clog 2 (BinIntervalProgram.intervalSize z.1+1)) :=
    composition (composition sizeR successor) ceilLogTwoRealizer
  let accuracy := composition (f := fun z : Frame => (4,z.2.1+z.2.2))
    (g := fun p : ℕ×ℕ => p.1*p.2)
    (pair (constant 4) (composition second add)) multiply
  exact composition (f := fun z : Frame =>
    (Nat.clog 2 (BinIntervalProgram.intervalSize z.1+1),4*(z.2.1+z.2.2)))
    (g := fun p : ℕ×ℕ => p.1+p.2) (pair binary accuracy) add

def coordinate (z : Frame×List Bool) : ℕ :=
  BinIntervalProgram.draw (z.1.1,z.2.take (activeWidth z.1))
def coordinateRealizer : Realizer coordinate :=
  composition (f := fun z : Frame×List Bool => (z.1.1,z.2.take (activeWidth z.1)))
    (g := BinIntervalProgram.draw)
    (pair (composition first first)
      (composition (pair second (composition first activeWidthRealizer)) takeFast))
    BinIntervalProgram.drawRealizer

lemma active_le_reserved (K N beta h d : ℕ) (hK : 0<K) (hN : 0<N) (hb : beta<K) :
    activeWidth (((K,N),beta),(h,d)) ≤ reservedWidth (((K,N),beta),(h,d)) := by
  unfold activeWidth reservedWidth
  rw [BinIntervalProgram.intervalSize_eq]
  exact Nat.add_le_add_right (Nat.clog_mono_right 2
    (Nat.add_le_add_right (intervalSize_le K N beta hK hN hb) 1)) _

abbrev Input := List Frame×List Bool

def widths (z : Input) : List ℕ := z.1.map reservedWidth
def widthsRealizer : Realizer widths := composition first (map reservedWidthRealizer)

def item (z : Input×ℕ) : ℕ := coordinate
  (z.1.1.getD z.2 (((0,0),0),(0,0)),dependentChunk ((widths z.1,z.1.2),z.2))
def itemRealizer : Realizer item :=
  composition (f := fun z : Input×ℕ =>
    (z.1.1.getD z.2 (((0,0),0),(0,0)),dependentChunk ((widths z.1,z.1.2),z.2)))
    (g := coordinate)
    (pair (composition (pair (composition first first) second)
      (getDFast (((0,0),0),(0,0))))
      (composition (pair (pair (composition first widthsRealizer)
        (composition first second)) second) dependentChunkRealizer)) coordinateRealizer

def indices (z : Input) : List ℕ := List.range z.1.length
def indicesRealizer : Realizer indices := composition (composition first listLength) range

def output (z : Input) : List ℕ := (indices z).map (fun i => item (z,i))
def outputRealizer : Realizer output :=
  composition (pair identity indicesRealizer) (mapWith itemRealizer)

end ContingencyTables.BinVectorProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedBinFramesProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Preparing the actual bin draws from the computed free-cell catalog

Only the capacity matrix, catalog metadata, grid coordinate list and
numeric sampling parameters are supplied. The program computes each
full range and bin index before invoking the proved vector draw.
-/

namespace ContingencyTables.RootedBinFramesProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms
open scoped BigOperators Classical

def catalogRealizer : Realizer catalog :=
  composition (f := fun z : Input => (z.2.1,false)) (g := RootedForestCatalog.catalog)
    (pair (composition second first) (constant false)) RootedForestCatalog.catalogRealizer
def cellRealizer : Realizer cell :=
  composition (pair (composition first catalogRealizer) second) (getDFast (0,0))
def rangeSizeRealizer : Realizer rangeSize :=
  composition (composition (f := fun z : Input×ℕ => (z.1.2.1.2,cell z))
    (g := matrixEntry)
    (pair (composition (composition (composition first second) first) second) cellRealizer)
    matrixEntryRealizer) successor
def coordinateRealizer : Realizer coordinate :=
  composition (pair (composition (composition first second) second) second) (getDFast 0)

def item (z : Input×ℕ) : BinVectorProgram.Frame :=
  (((z.1.1.1,rangeSize z),coordinate z),z.1.1.2)
def itemRealizer : Realizer item :=
  pair (pair (pair (composition (composition first first) first) rangeSizeRealizer)
    coordinateRealizer) (composition (composition first first) second)
def indicesRealizer : Realizer indices :=
  composition (f := catalog) (g := RootedTreeInputProgram.indices)
    catalogRealizer RootedTreeInputProgram.indicesRealizer

def frames (z : Input) : List BinVectorProgram.Frame :=
  (indices z).map (fun i => item (z,i))
def framesRealizer : Realizer frames :=
  composition (pair identity indicesRealizer) (mapWith itemRealizer)

def draw (z : Input×List Bool) : List ℕ := BinVectorProgram.output (frames z.1,z.2)
def drawRealizer : Realizer draw :=
  composition (f := fun z : Input×List Bool => (frames z.1,z.2)) (g := BinVectorProgram.output)
    (pair (composition first framesRealizer) second) BinVectorProgram.outputRealizer

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary

end ContingencyTables.RootedBinFramesProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_BinPopulationProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing the exact population correction in binary

The program multiplies one interval size and one full-range denominator
per free coordinate. It never lists the integer assignments in a bin.
-/

namespace ContingencyTables.BinPopulationProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped
open scoped BigOperators Classical

def factorNumerator (z : BinIntervalProgram.Input) : ℕ :=
  z.1.1*BinIntervalProgram.intervalSize z
def factorNumeratorRealizer : Realizer factorNumerator :=
  composition (f := fun z : BinIntervalProgram.Input =>
    (z.1.1,BinIntervalProgram.intervalSize z)) (g := fun p : ℕ×ℕ => p.1*p.2)
    (pair (composition first first) BinIntervalProgram.intervalSizeRealizer) multiply

def numerator (zs : List BinIntervalProgram.Input) : ℕ := (zs.map factorNumerator).prod
def numeratorRealizer : Realizer numerator := composition (map factorNumeratorRealizer) listProd

def denominator (zs : List BinIntervalProgram.Input) : ℕ := (zs.map (fun z => z.1.2)).prod
def denominatorRealizer : Realizer denominator :=
  composition (map (composition first second)) listProd

def output (zs : List BinIntervalProgram.Input) : TreeFraction.Fraction :=
  TreeFraction.normalize (numerator zs,denominator zs)
def outputRealizer : Realizer output :=
  composition (pair numeratorRealizer denominatorRealizer) TreeFraction.normalizeRealizer

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary

noncomputable section
variable {m n : ℕ}

def data (A : Instance (Fin m) (Fin n)) (K : ℕ)
    (v : Grid (I := Fin (CompanionOracleDensity.dimension A)) K) : List BinIntervalProgram.Input :=
  List.ofFn (fun i : Fin (RootedCatalogGrid.freeCount A) =>
    ((K,CompanionOracleDensity.freeRange A (RootedForestCatalog.freeEquiv A i)),
      CompanionOracleDensity.naturalBin A v (RootedForestCatalog.freeEquiv A i)))

end
end ContingencyTables.BinPopulationProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_IntegerMatrixProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary integer matrix propagation for exact law tabulation -/

namespace ContingencyTables.IntegerMatrixPrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped
open scoped BigOperators

def entryRealizer : Realizer
    (fun z : (List ℕ×List ℕ)×ℕ => z.1.1.getD z.2 0*z.1.2.getD z.2 0) :=
  composition (pair
    (composition (pair (composition first first) second) (getDFast 0))
    (composition (pair (composition first second) second) (getDFast 0))) multiply

def dotRealizer : Realizer dot :=
  composition (f := fun z : List ℕ×List ℕ => (z,List.range z.1.length))
    (g := fun z : (List ℕ×List ℕ)×List ℕ =>
      (z.2.map (fun i => z.1.1.getD i 0*z.1.2.getD i 0)).sum)
    (pair identity (composition (composition first listLength) range))
    (composition (mapWith entryRealizer) listSum)

def propagateRealizer : Realizer propagate :=
  composition (pair second first) (mapWith dotRealizer)

def stepRealizer : Realizer step :=
  pair (composition second first) (composition second propagateRealizer)

def iterateRealizer : Realizer iterate :=
  composition (composition identity (iterateDown stepRealizer)) second

end ContingencyTables.IntegerMatrixPrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_BinaryPowerProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary powers with a polynomial bound in the exponent and input bits -/

namespace ContingencyTables.BinaryPowerPrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped
open scoped BigOperators

def singleton {A : Type} [Codec A] : Realizer (fun a : A => [a]) :=
  composition (pair identity (constant [])) listCons

def setupRealizer : Realizer setup :=
  pair second (pair (composition (composition first singleton) singleton) (constant [1]))

def powerRealizer : Realizer power :=
  composition (composition setupRealizer IntegerMatrixPrograms.iterateRealizer) (head 0)

end ContingencyTables.BinaryPowerPrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_DyadicRootProgram
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial binary execution of the rational correction bisection

The root degree is the length of a supplied allowance list. One fixed
depth list controls the outer loop. Thus both natural-power evaluation
and the bisection loop have polynomial cost in the supplied binary data
and the two explicit allowances.
-/

namespace ContingencyTables.DyadicRootProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial

def powerInputRealizer : Realizer powerInput := pair first (composition second listLength)
def markedPowerRealizer : Realizer markedPower :=
  composition powerInputRealizer BinaryPowerPrograms.powerRealizer

def lowRealizer : Realizer (fun z : State=>z.2.1.1) :=
  composition (composition second first) first
def highRealizer : Realizer (fun z : State=>z.2.1.2) :=
  composition (composition second first) second
def denominatorRealizer : Realizer (fun z : State=>z.2.2) := composition second second
def numeratorRealizer : Realizer (fun z : State=>z.1.1.1) :=
  composition (composition first first) first
def targetDenominatorRealizer : Realizer (fun z : State=>z.1.1.2) :=
  composition (composition first first) second
def allowanceRealizer : Realizer (fun z : State=>z.1.2) := composition first second

def midRealizer : Realizer mid := composition (pair lowRealizer highRealizer) add
def twiceDenominatorRealizer : Realizer twiceDenominator :=
  composition (f:=fun z : State=>(2,z.2.2)) (g:=fun p : ℕ×ℕ=>p.1*p.2)
    (pair (constant 2) denominatorRealizer) multiply
def leftProductRealizer : Realizer leftProduct :=
  composition (pair
    (composition (pair midRealizer allowanceRealizer) markedPowerRealizer)
    targetDenominatorRealizer) multiply
def rightProductRealizer : Realizer rightProduct :=
  composition (pair numeratorRealizer
    (composition (pair twiceDenominatorRealizer allowanceRealizer) markedPowerRealizer)) multiply
def testRealizer : Realizer test := composition (pair leftProductRealizer rightProductRealizer) leNat

def lowerBranchRealizer : Realizer (fun z : State=>
    ((mid z,2*z.2.1.2),twiceDenominator z)) :=
  pair (pair midRealizer (composition
    (f:=fun z : State=>(2,z.2.1.2)) (g:=fun p : ℕ×ℕ=>p.1*p.2)
    (pair (constant 2) highRealizer) multiply))
    twiceDenominatorRealizer
def upperBranchRealizer : Realizer (fun z : State=>
    ((2*z.2.1.1,mid z),twiceDenominator z)) :=
  pair (pair (composition
    (f:=fun z : State=>(2,z.2.1.1)) (g:=fun p : ℕ×ℕ=>p.1*p.2)
    (pair (constant 2) lowRealizer) multiply) midRealizer)
    twiceDenominatorRealizer

def nextRealizer : Realizer next :=
  pair first (choose testRealizer lowerBranchRealizer upperBranchRealizer)

def advanceRealizer : Realizer advance := composition second nextRealizer
def prepareRealizer : Realizer prepare := pair second (pair first (constant ((0,8),1)))
def executeRealizer : Realizer execute := composition prepareRealizer (fold advanceRealizer)
def finishRealizer : Realizer finish :=
  composition (pair midRealizer twiceDenominatorRealizer) TreeFraction.normalizeRealizer
def outputRealizer : Realizer output := composition executeRealizer finishRealizer

end ContingencyTables.DyadicRootProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_RoundedPowerProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executing the rounded power used by the correction oracle

The exponent lies in [-2,2]. Clipping the computed signed floor
at twice the supplied degree allowance plus one is therefore inactive
on valid inputs, and keeps every binary execution polynomial even on
arbitrary malformed numerator/denominator data.
-/

namespace ContingencyTables.RoundedPowerProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial SignedPairProgram

abbrev Input := SignedFloorProgram.ScaledInput

def normalized (z : Input) : Signed := SignedPairProgram.normalize (SignedFloorProgram.scaledFloor z)
def normalizedRealizer : Realizer normalized :=
  composition SignedFloorProgram.scaledFloorRealizer SignedPairProgram.normalizeRealizer

def cap (z : Input) : ℕ := 2*z.2.length+1
def capRealizer : Realizer cap := composition
  (f:=fun z : Input=>2*z.2.length) (g:=Nat.succ)
  (composition (f:=fun z : Input=>(2,z.2.length)) (g:=fun p : ℕ×ℕ=>p.1*p.2)
    (pair (constant 2) (composition second listLength)) multiply) successor

def clipped (z : Input) : Signed :=
  (min (normalized z).1 (cap z),min (normalized z).2 (cap z))
def clippedRealizer : Realizer clipped := pair
  (composition (pair (composition normalizedRealizer first) capRealizer) minimum)
  (composition (pair (composition normalizedRealizer second) capRealizer) minimum)

def positiveInput (z : Input) : ℕ×ℕ := (2,(clipped z).1)
def negativeInput (z : Input) : ℕ×ℕ := (2,(clipped z).2)
def positiveInputRealizer : Realizer positiveInput := pair (constant 2) (composition clippedRealizer first)
def negativeInputRealizer : Realizer negativeInput := pair (constant 2) (composition clippedRealizer second)

def positivePower (z : Input) : ℕ := BinaryPowerPrograms.power (positiveInput z)
def negativePower (z : Input) : ℕ := BinaryPowerPrograms.power (negativeInput z)
def positivePowerRealizer : Realizer positivePower :=
  composition positiveInputRealizer BinaryPowerPrograms.powerRealizer
def negativePowerRealizer : Realizer negativePower :=
  composition negativeInputRealizer BinaryPowerPrograms.powerRealizer

def output (z : Input) : TreeFraction.Fraction :=
  TreeFraction.normalize (positivePower z,negativePower z)
def outputRealizer : Realizer output :=
  composition (pair positivePowerRealizer negativePowerRealizer) TreeFraction.normalizeRealizer

end ContingencyTables.RoundedPowerProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_PowerApproximationProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The executed power-of-two approximation used by the weight oracle

Both stages are concrete binary programs: compute the rounded signed
power, then bisect using natural cross-products and shared denominators.
The two allowance lists determine the precision parameters.
-/

namespace ContingencyTables.PowerApproximationProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped

abbrev Input := SignedFloorProgram.Input×(List Bool×List Bool)

def prepare (z : Input) : DyadicRootProgram.Input :=
  ((RoundedPowerProgram.output (z.1,z.2.1),z.2.1),z.2.2)
def prepareRealizer : Realizer prepare :=
  pair (pair
    (composition (f := fun z : Input => (z.1,z.2.1)) (g := RoundedPowerProgram.output)
      (pair first (composition second first)) RoundedPowerProgram.outputRealizer)
    (composition second first)) (composition second second)

def output (z : Input) : TreeFraction.Fraction := DyadicRootProgram.output (prepare z)
def outputRealizer : Realizer output :=
  composition prepareRealizer DyadicRootProgram.outputRealizer

end ContingencyTables.PowerApproximationProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_CorrectionValueProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary composition of the correction value

The input contains the computed grid exponent, phase ratio, point
penalty, population factor and two precision marker lists. Normalized
fraction multiplication supplies a positive denominator for the signed
exponent passed to the executed power approximation.
-/

namespace ContingencyTables.CorrectionValueProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped

def weightedRealizer : Realizer weighted :=
  composition (f := fun z : Frame => (z.1.2,z.2)) (g := TreeFraction.mul)
    (pair (composition first second) second) TreeFraction.mulRealizer

def exponentInput (z : Frame) : SignedFloorProgram.Input :=
  ((z.1.1*(weighted z).2,(weighted z).1),(weighted z).2)
def exponentInputRealizer : Realizer exponentInput :=
  pair (pair
    (composition (f := fun z : Frame => (z.1.1,(weighted z).2))
      (g := fun p : ℕ×ℕ => p.1*p.2)
      (pair (composition first first) (composition weightedRealizer second)) multiply)
    (composition weightedRealizer first)) (composition weightedRealizer second)

def powerInput (z : Input) : PowerApproximationProgram.Input :=
  (exponentInput z.1.1,z.2)
def powerInputRealizer : Realizer powerInput :=
  pair (composition (composition first first) exponentInputRealizer) second

def power (z : Input) : TreeFraction.Fraction := PowerApproximationProgram.output (powerInput z)
def powerRealizer : Realizer power :=
  composition (f := powerInput) (g := PowerApproximationProgram.output)
    powerInputRealizer PowerApproximationProgram.outputRealizer

def output (z : Input) : TreeFraction.Fraction := TreeFraction.mul (z.1.2,power z)
def outputRealizer : Realizer output :=
  composition (f := fun z : Input => (z.1.2,power z)) (g := TreeFraction.mul)
    (pair (composition first second) powerRealizer) TreeFraction.mulRealizer

end ContingencyTables.CorrectionValueProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedPointPenaltyProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executed penalty evaluation at a sampled integer assignment

At an integer point, the coordinate scale in the affine coefficient
cancels its inverse in the coordinate. The program therefore forms the
unscaled signed affine numerator directly from the sampled integers.
-/

namespace ContingencyTables.RootedPointPenaltyProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped RootedForestPrepareProgram
open scoped BigOperators Classical

def term (z : RootedForestDataProgram.TermInput) : ForestAffineProgram.Term :=
  (RootedCoefficientProgram.coefficient z.1,z.2)
def termRealizer : Realizer term :=
  pair (composition (f := fun z : RootedForestDataProgram.TermInput => z.1)
    (g := RootedCoefficientProgram.coefficient) first RootedCoefficientProgram.coefficientRealizer) second

def tree (z : RootedForestDataProgram.Input) : ForestAffineProgram.Input :=
  ((RootedOffsetProgram.offset z.1.2,z.2.map term),z.1.1.2)
def treeRealizer : Realizer tree :=
  pair (pair (composition (f := fun z : RootedForestDataProgram.Input => z.1.2)
      (g := RootedOffsetProgram.offset) (composition first second) RootedOffsetProgram.offsetRealizer)
    (composition second (map termRealizer))) (composition (composition first first) second)

def prepareTree (z : TreeInput) : ForestAffineProgram.Input := tree (forestInput z)
def prepareTreeRealizer : Realizer prepareTree :=
  composition (f := forestInput) (g := tree) forestInputRealizer treeRealizer

def trees (z : Input) : List ForestAffineProgram.Input :=
  (treeCells z).map (fun a => prepareTree (treeBundle z,a))
def treesRealizer : Realizer trees :=
  composition (f := fun z : Input => (treeBundle z,treeCells z))
    (g := fun z => z.2.map (fun a => prepareTree (z.1,a)))
    (pair treeBundleRealizer treeCellsRealizer) (mapWith prepareTreeRealizer)

def prepare (z : Input) : ForestPenaltyProgram.Input :=
  ((z.1.1.1,RootedDemandProgram.rootCount z.1.2),trees z)
def prepareRealizer : Realizer prepare :=
  pair (pair (composition (composition first first) first)
    (composition (f := fun z : Input => z.1.2) (g := RootedDemandProgram.rootCount)
      (composition first second) RootedDemandProgram.rootCountRealizer)) treesRealizer

def output (z : Input) : TreeFraction.Fraction := ForestPenaltyProgram.penaltyCode (prepare z)
def outputRealizer : Realizer output := composition prepareRealizer ForestPenaltyProgram.penaltyCodeRealizer

open CompanionFactorialApplication RootedCompletion ForestAssignmentSplit GraphCompletionCounts

end ContingencyTables.RootedPointPenaltyProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedCorrectionProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The executed selected-root correction

The stored grid point and sampled integer point share their literal
capacity, forest, baseline and small-view arrays.  The program computes
the grid exponent, point penalty and population factor before the
bounded rational power approximation.
-/

namespace ContingencyTables.RootedCorrectionProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms
open scoped BigOperators Classical

def exponentInput (z : Input) : RootedPenaltyEvaluateProgram.Input :=
  (z.1.1.1.2.1,(z.1.1.1.2.2,z.1.1.2))
def exponentInputRealizer : Realizer exponentInput :=
  pair (composition (composition (composition (composition first first) first) second) first)
    (pair (composition (composition (composition (composition first first) first) second) second)
      (composition (composition first first) second))

def pointInput (z : Input) : RootedForestPrepareProgram.Input :=
  ((((exponentInput z).1.2.1,RootedPenaltyEvaluateProgram.width (exponentInput z).1),
    (exponentInput z).2.1),z.1.2)
def pointInputRealizer : Realizer pointInput := by
  let params : Realizer (fun z : Input => (exponentInput z).1) :=
    composition (f := exponentInput) (g := fun z => z.1) exponentInputRealizer first
  let c : Realizer (fun z : Input => (exponentInput z).1.2.1) :=
    composition (composition params second) first
  let width : Realizer (fun z : Input => RootedPenaltyEvaluateProgram.width (exponentInput z).1) :=
    composition (f := fun z : Input => (exponentInput z).1)
      (g := RootedPenaltyEvaluateProgram.width) params RootedPenaltyEvaluateProgram.widthRealizer
  exact pair (pair (pair c width)
    (composition (composition exponentInputRealizer second) first)) (composition first second)

def binInput (z : Input) : RootedBinFramesProgram.Input :=
  ((z.1.1.1.1,(0,z.1.1.1.2.1.1.1)),((exponentInput z).2.1.1,z.1.1.2))
def binInputRealizer : Realizer binInput :=
  pair (pair (composition (composition (composition first first) first) first)
    (pair (constant 0) (composition
      (composition (composition (composition (composition (composition first first) first)
        second) first) first) first)))
    (pair (composition (composition (composition exponentInputRealizer second) first) first)
      (composition (composition first first) second))

def populationInput (z : Input) : List BinIntervalProgram.Input :=
  (RootedBinFramesProgram.frames (binInput z)).map Prod.fst
def populationInputRealizer : Realizer populationInput :=
  composition (f := fun z : Input => RootedBinFramesProgram.frames (binInput z))
    (g := fun xs : List BinVectorProgram.Frame => xs.map Prod.fst)
    (composition binInputRealizer RootedBinFramesProgram.framesRealizer) (map first)

def phase (z : Input) : TreeFraction.Fraction :=
  ((exponentInput z).1.2.2,RootedPenaltyEvaluateProgram.height (exponentInput z).1)
def phaseRealizer : Realizer phase :=
  pair (composition (composition (composition exponentInputRealizer first) second) second)
    (composition (f := fun z : Input => (exponentInput z).1)
      (g := RootedPenaltyEvaluateProgram.height)
      (composition exponentInputRealizer first) RootedPenaltyEvaluateProgram.heightRealizer)

attribute [local irreducible] RootedPenaltyEvaluateProgram.evaluate
  RootedPointPenaltyProgram.output BinPopulationProgram.output

def exponentValue (z : Input) : ℕ :=
  RootedPenaltyEvaluateProgram.evaluate (exponentInput z)
def exponentValueRealizer : Realizer exponentValue :=
  composition (f := exponentInput) (g := RootedPenaltyEvaluateProgram.evaluate)
    exponentInputRealizer RootedPenaltyEvaluateProgram.evaluateRealizer

def pointValue (z : Input) : TreeFraction.Fraction :=
  RootedPointPenaltyProgram.output (pointInput z)
def pointValueRealizer : Realizer pointValue :=
  composition (f := pointInput) (g := RootedPointPenaltyProgram.output)
    pointInputRealizer RootedPointPenaltyProgram.outputRealizer

def populationValue (z : Input) : TreeFraction.Fraction :=
  BinPopulationProgram.output (populationInput z)
def populationValueRealizer : Realizer populationValue :=
  composition (f := populationInput) (g := BinPopulationProgram.output)
    populationInputRealizer BinPopulationProgram.outputRealizer

attribute [local irreducible] exponentValue pointValue populationValue

def frame (z : Input) : CorrectionValueProgram.Frame :=
  ((exponentValue z,phase z),pointValue z)
def frameRealizer : Realizer frame :=
  pair (pair exponentValueRealizer phaseRealizer) pointValueRealizer

attribute [local irreducible] frame

def prepare (z : Input) : CorrectionValueProgram.Input := ((frame z,populationValue z),z.2)
def prepareRealizer : Realizer prepare := pair (pair frameRealizer populationValueRealizer) second

def output (z : Input) : TreeFraction.Fraction := CorrectionValueProgram.output (prepare z)
def outputRealizer : Realizer output :=
  composition (f := prepare) (g := CorrectionValueProgram.output)
    prepareRealizer CorrectionValueProgram.outputRealizer

end ContingencyTables.RootedCorrectionProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedOracleFlatProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial flat-word program for the actual oracle walk -/

namespace ContingencyTables.RootedOracleWalkProgram

open MatchingFPRAS.TreeTyped DensePrograms
open scoped Classical

def proposalWidthRealizer : Realizer proposalWidth := by
  let D : Realizer (fun z : Frame => z.2.1.1.1) :=
    composition (composition (composition second first) first) first
  let M : Realizer (fun z : Frame => 8*z.2.1.1.1) :=
    composition (f := fun z : Frame => (8,z.2.1.1.1))
      (g := fun x : ℕ×ℕ => x.1*x.2) (pair (constant 8) D) multiply
  exact composition (f := fun z : Frame => 8*z.2.1.1.1)
    (g := Nat.clog 2) M ceilLogTwoRealizer
def stepWidthRealizer : Realizer stepWidth :=
  composition (f := fun z : Frame => (proposalWidth z,RootedPenaltyEvaluateProgram.height z.2.1))
    (g := fun x : ℕ×ℕ => x.1+x.2)
    (pair proposalWidthRealizer
      (composition (f := fun z : Frame => z.2.1) (g := RootedPenaltyEvaluateProgram.height)
        (composition second first) RootedPenaltyEvaluateProgram.heightRealizer)) add

def flatWalk (z : State×List Bool) : State :=
  walkWords (z.1,wordChunks (stepWidth z.1.1,z.2))
def flatWalkRealizer : Realizer flatWalk :=
  composition (f := fun z : State×List Bool => (z.1,wordChunks (stepWidth z.1.1,z.2)))
    (g := walkWords)
    (pair first (composition (f := fun z : State×List Bool => (stepWidth z.1.1,z.2))
      (g := wordChunks)
      (pair (composition (f := fun z : State×List Bool => z.1.1) (g := stepWidth)
        (composition first first) stepWidthRealizer) second) wordChunksRealizer)) walkWordsRealizer

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary FirstSuccess ResidualMixture

end ContingencyTables.RootedOracleWalkProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedCorrectionSampleProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executing one selected-root correction sample

Separate finite words drive the grid walk and the integer draw. The
computed final bin and sampled integer are then passed to the exact
population and rational-power correction program.
-/

namespace ContingencyTables.RootedCorrectionSampleProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms
open scoped Classical

def walked (z : Input) : State :=
  RootedOracleWalkProgram.flatWalk (z.1.1,z.2.2.1)
def walkedRealizer : Realizer walked :=
  composition (f := fun z : Input => (z.1.1,z.2.2.1))
    (g := RootedOracleWalkProgram.flatWalk)
    (pair (composition first first) (composition (composition second second) first))
    RootedOracleWalkProgram.flatWalkRealizer

attribute [local irreducible] walked

def binFrame (z : Input) : RootedBinFramesProgram.Input :=
  (((walked z).1.1,(z.1.2,(walked z).1.2.1.1.1)),
    ((walked z).1.2.2.1,(walked z).2))
def binFrameRealizer : Realizer binFrame := by
  let k : Realizer (fun z : Input => (walked z).1.1) :=
    composition (composition walkedRealizer first) first
  let d : Realizer (fun z : Input => (walked z).1.2.1.1.1) :=
    composition (composition (composition (composition (composition walkedRealizer first)
      second) first) first) first
  let catalog : Realizer (fun z : Input => (walked z).1.2.2.1) :=
    composition (composition (composition (composition walkedRealizer first) second) second) first
  exact pair (pair k (pair (composition first second) d))
    (pair catalog (composition walkedRealizer second))

attribute [local irreducible] binFrame

def sampled (z : Input) : List ℕ := RootedBinFramesProgram.draw (binFrame z,z.2.2.2)
def sampledRealizer : Realizer sampled :=
  composition (f := fun z : Input => (binFrame z,z.2.2.2))
    (g := RootedBinFramesProgram.draw)
    (pair binFrameRealizer (composition (composition second second) second))
    RootedBinFramesProgram.drawRealizer

attribute [local irreducible] sampled

def prepare (z : Input) : RootedCorrectionProgram.Input :=
  ((walked z,sampled z),z.2.1)
def prepareRealizer : Realizer prepare :=
  pair (pair walkedRealizer sampledRealizer) (composition second first)

attribute [local irreducible] prepare

def output (z : Input) : TreeFraction.Fraction := RootedCorrectionProgram.output (prepare z)
def outputRealizer : Realizer output :=
  composition (f := prepare) (g := RootedCorrectionProgram.output)
    prepareRealizer RootedCorrectionProgram.outputRealizer

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open CompanionOracleDensity FairBits
open scoped BigOperators

end ContingencyTables.RootedCorrectionSampleProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedRatioSampleProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial execution of an adjacent-parameter ratio sample

The exact ratio is either one or one half. The program compares the two
computed integer exponents and never materializes an exponential weight.
-/

namespace ContingencyTables.RootedRatioSampleProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms
open scoped Classical

abbrev Input := RootedPenaltyEvaluateProgram.Input

def bump (z : Input) : Input := ((z.1.1,(z.1.2.1,z.1.2.2+1)),z.2)
def bumpRealizer : Realizer bump :=
  pair (pair (composition first first)
    (pair (composition (composition first second) first)
      (composition (composition (composition first second) second) successor))) second

attribute [local irreducible] RootedPenaltyEvaluateProgram.evaluate

def equalExponents (z : Input) : Bool :=
  decide (RootedPenaltyEvaluateProgram.evaluate (bump z)=RootedPenaltyEvaluateProgram.evaluate z)
def equalExponentsRealizer : Realizer equalExponents :=
  composition (f := fun z : Input => (RootedPenaltyEvaluateProgram.evaluate (bump z),
    RootedPenaltyEvaluateProgram.evaluate z)) (g := fun x : ℕ×ℕ => decide (x.1=x.2))
    (pair (composition (f := bump) (g := RootedPenaltyEvaluateProgram.evaluate)
      bumpRealizer RootedPenaltyEvaluateProgram.evaluateRealizer)
      RootedPenaltyEvaluateProgram.evaluateRealizer) natEqual

def ratio (z : Input) : TreeFraction.Fraction := if equalExponents z then (1,1) else (1,2)
def ratioRealizer : Realizer ratio :=
  choose equalExponentsRealizer (constant (1,1)) (constant (1,2))

def currentInput (z : SampleInput) : Input :=
  (RootedOracleWalkProgram.toData (RootedOracleWalkProgram.flatWalk z)).2
def currentInputRealizer : Realizer currentInput :=
  composition (f := RootedOracleWalkProgram.flatWalk)
    (g := fun z : RootedOracleWalkProgram.State => (RootedOracleWalkProgram.toData z).2)
    RootedOracleWalkProgram.flatWalkRealizer
    (composition RootedOracleWalkProgram.toDataRealizer second)

def output (z : SampleInput) : TreeFraction.Fraction := ratio (currentInput z)
def outputRealizer : Realizer output :=
  composition (f := currentInput) (g := ratio) currentInputRealizer ratioRealizer

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open CompanionOracleDensity RootedCompletion
open scoped BigOperators

end ContingencyTables.RootedRatioSampleProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedEstimatorBlockProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executed sample blocks and the product weight estimator

The lists contain the actual sample inputs and their disjoint finite
words. Each sample is evaluated by the checked binary program before
its average or product is formed.
-/

namespace ContingencyTables.RootedEstimatorBlockProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped

abbrev CorrectionBlock := List RootedCorrectionSampleProgram.Input

def ratioAverage (xs : RatioBlock) : TreeFraction.Fraction :=
  FractionAggregateProgram.average (xs.map RootedRatioSampleProgram.output)
def ratioAverageRealizer : Realizer ratioAverage :=
  composition (f := fun xs : RatioBlock => xs.map RootedRatioSampleProgram.output)
    (g := FractionAggregateProgram.average) (map RootedRatioSampleProgram.outputRealizer)
    FractionAggregateProgram.averageRealizer

def correctionAverage (xs : CorrectionBlock) : TreeFraction.Fraction :=
  FractionAggregateProgram.average (xs.map RootedCorrectionSampleProgram.output)
def correctionAverageRealizer : Realizer correctionAverage :=
  composition (f := fun xs : CorrectionBlock => xs.map RootedCorrectionSampleProgram.output)
    (g := FractionAggregateProgram.average) (map RootedCorrectionSampleProgram.outputRealizer)
    FractionAggregateProgram.averageRealizer

abbrev Input := (ℕ × List RatioBlock) × CorrectionBlock

attribute [local irreducible] ratioAverage correctionAverage

def ratioProduct (z : Input) : TreeFraction.Fraction :=
  FractionAggregateProgram.product (z.1.2.map ratioAverage)
def ratioProductRealizer : Realizer ratioProduct :=
  composition (f := fun z : Input => z.1.2.map ratioAverage)
    (g := FractionAggregateProgram.product)
    (composition (f := fun z : Input => z.1.2) (g := fun xs : List RatioBlock => xs.map ratioAverage)
      (composition first second) (map ratioAverageRealizer)) FractionAggregateProgram.productRealizer

def factors (z : Input) : TreeFraction.Fraction :=
  TreeFraction.mul (ratioProduct z,correctionAverage z.2)
def factorsRealizer : Realizer factors :=
  composition (f := fun z : Input => (ratioProduct z,correctionAverage z.2)) (g := TreeFraction.mul)
    (pair ratioProductRealizer (composition (f := fun z : Input => z.2)
      (g := correctionAverage) second correctionAverageRealizer)) TreeFraction.mulRealizer

def output (z : Input) : TreeFraction.Fraction := TreeFraction.mul ((z.1.1,1),factors z)
def outputRealizer : Realizer output :=
  composition (f := fun z : Input => ((z.1.1,1),factors z)) (g := TreeFraction.mul)
    (pair (pair (composition first first) (constant 1)) factorsRealizer) TreeFraction.mulRealizer

end ContingencyTables.RootedEstimatorBlockProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedEstimatorLayoutProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computed sizes of the estimator's disjoint word banks

The schedule supplies the phase and sample counts and the two walk times.
The catalog itself supplies both the integer-draw widths and the initial
free-assignment count. No list is allocated from a binary count here.
-/

namespace ContingencyTables.RootedEstimatorLayoutProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms

def stepWidthRealizer : Realizer stepWidth :=
  composition (f := fun z : Context => z.1.1) (g := RootedOracleWalkProgram.stepWidth)
    (composition first first) RootedOracleWalkProgram.stepWidthRealizer
def ratioWidthRealizer : Realizer ratioWidth :=
  composition (f := fun z : Context => (z.2.2.1.1,stepWidth z))
    (g := fun p : ℕ×ℕ => p.1*p.2)
    (pair (composition (composition (composition second second) first) first) stepWidthRealizer)
    multiply
def ratioBlockWidthRealizer : Realizer ratioBlockWidth :=
  composition (f := fun z : Context => (z.2.1.2,ratioWidth z))
    (g := fun p : ℕ×ℕ => p.1*p.2)
    (pair (composition (composition second first) second) ratioWidthRealizer) multiply
def ratioBankWidthRealizer : Realizer ratioBankWidth :=
  composition (f := fun z : Context => (z.2.1.1,ratioBlockWidth z))
    (g := fun p : ℕ×ℕ => p.1*p.2)
    (pair (composition (composition second first) first) ratioBlockWidthRealizer) multiply

def binFrame (z : Context) : RootedBinFramesProgram.Input :=
  ((z.1.1.1,(z.2.2.2,z.1.1.2.1.1.1)),(z.1.1.2.2.1,z.1.2))
def binFrameRealizer : Realizer binFrame := by
  let k : Realizer (fun z : Context => z.1.1.1) := composition (composition first first) first
  let h : Realizer (fun z : Context => z.2.2.2) := composition (composition second second) second
  let d : Realizer (fun z : Context => z.1.1.2.1.1.1) :=
    composition (composition (composition (composition (composition first first) second) first) first) first
  let catalog : Realizer (fun z : Context => z.1.1.2.2.1) :=
    composition (composition (composition (composition first first) second) second) first
  exact pair (pair k (pair h d)) (pair catalog (composition first second))

def frames (z : Context) : List BinVectorProgram.Frame := RootedBinFramesProgram.frames (binFrame z)
def framesRealizer : Realizer frames :=
  composition (f := binFrame) (g := RootedBinFramesProgram.frames)
    binFrameRealizer RootedBinFramesProgram.framesRealizer

attribute [local irreducible] frames

def binWidth (z : Context) : ℕ := ((frames z).map BinVectorProgram.reservedWidth).sum
def binWidthRealizer : Realizer binWidth :=
  composition (f := frames) (g := fun xs : List BinVectorProgram.Frame =>
    (xs.map BinVectorProgram.reservedWidth).sum) framesRealizer
    (composition (map BinVectorProgram.reservedWidthRealizer) listSum)

def assignmentCount (z : Context) : ℕ := ((frames z).map (fun x => x.1.1.2)).prod
def rangeValue (x : BinVectorProgram.Frame) : ℕ := x.1.1.2
def rangeValueRealizer : Realizer rangeValue := composition (composition first first) second

def rangeValues (xs : List BinVectorProgram.Frame) : List ℕ := xs.map rangeValue
def rangeValuesRealizer : Realizer rangeValues := MatchingFPRAS.TreeTyped.map rangeValueRealizer

attribute [local irreducible] rangeValue rangeValues

def assignmentCountRealizer : Realizer assignmentCount := by
  let values : Realizer (fun z : Context => rangeValues (frames z)) :=
    composition (f := frames) (g := rangeValues) framesRealizer rangeValuesRealizer
  exact (composition (f := fun z : Context => rangeValues (frames z))
    (g := (List.prod : List ℕ → ℕ)) values listProd).congr (by
      intro z
      unfold assignmentCount rangeValues rangeValue
      rfl)

def correctionWalkWidth (z : Context) : ℕ := z.2.2.1.2*stepWidth z
def correctionWalkWidthRealizer : Realizer correctionWalkWidth :=
  composition (f := fun z : Context => (z.2.2.1.2,stepWidth z))
    (g := fun p : ℕ×ℕ => p.1*p.2)
    (pair (composition (composition (composition second second) first) second) stepWidthRealizer)
    multiply

def correctionWidth (z : Context) : ℕ := correctionWalkWidth z+binWidth z
def correctionWidthRealizer : Realizer correctionWidth :=
  composition (f := fun z : Context => (correctionWalkWidth z,binWidth z))
    (g := fun p : ℕ×ℕ => p.1+p.2) (pair correctionWalkWidthRealizer binWidthRealizer) add

def wordWidth (z : Context) : ℕ := ratioBankWidth z+z.2.1.2*correctionWidth z

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ}

def data (A : Instance (Fin m) (Fin n)) (C K j S Tr Tc h : ℕ) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) : Context :=
  (RootedOracleWalkProgram.data A C 0 K z v,((j,S),((Tr,Tc),h)))

end
end ContingencyTables.RootedEstimatorLayoutProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedEstimatorWordProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One flat word executes the complete weight estimator

The number of generated rows is bounded by the supplied word length.
The binary schedule therefore remains safe even on malformed inputs.
-/

namespace ContingencyTables.RootedEstimatorWordProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms
open RootedEstimatorLayoutProgram

abbrev Input := Context×((List Bool×List Bool)×List Bool)

def ratioPrefix (z : Input) : List Bool := z.2.2.take (ratioBankWidth z.1)

def ratioRows (z : Input) : List ℕ := completeWordRows (ratioBlockWidth z.1,ratioPrefix z)

def ratioChunk (z : Input×ℕ) : List Bool :=
  wordChunk ((ratioBlockWidth z.1.1,ratioPrefix z.1),z.2)

def ratioState (z : Input×ℕ) : State := phase (z.1.1.1,z.2)

def ratioWords (z : Input×ℕ) : List (List Bool) := wordChunks (ratioWidth z.1.1,ratioChunk z)

def ratioBlock (z : Input×ℕ) : RootedEstimatorBlockProgram.RatioBlock :=
  (ratioWords z).map (fun bits => (ratioState z,bits))

def ratioBlocks (z : Input) : List RootedEstimatorBlockProgram.RatioBlock :=
  (ratioRows z).map (fun i => ratioBlock (z,i))

def correctionTail (z : Input) : List Bool := z.2.2.drop (ratioBankWidth z.1)

def correctionWords (z : Input) : List (List Bool) :=
  (wordChunks (correctionWidth z.1,correctionTail z)).take z.1.2.1.2

def terminalState (z : Input) : State := phase (z.1.1,z.1.2.1.1)

def correctionSample (z : Input×List Bool) : RootedCorrectionSampleProgram.Input :=
  ((terminalState z.1,z.1.1.2.2.2),
    (z.1.2.1,(z.2.take (correctionWalkWidth z.1.1),z.2.drop (correctionWalkWidth z.1.1))))

def correctionBlock (z : Input) : RootedEstimatorBlockProgram.CorrectionBlock :=
  (correctionWords z).map (fun bits => correctionSample (z,bits))

def prepare (z : Input) : RootedEstimatorBlockProgram.Input :=
  ((assignmentCount z.1,ratioBlocks z),correctionBlock z)

attribute [local irreducible] prepare

def output (z : Input) : TreeFraction.Fraction := RootedEstimatorBlockProgram.output (prepare z)

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open scoped Classical
end ContingencyTables.RootedEstimatorWordProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedEstimatorWordLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact finite-word law of the executed selected-root weight oracle -/

namespace ContingencyTables.RootedEstimatorWordProgram

open MatchingFPRAS CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open CompanionOracleDensity RootedEstimatorLayoutProgram CommonBasesFPRAS
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ}

def scheduledContext (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (delta failure : ℚ)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) : Context :=
  RootedEstimatorLayoutProgram.data A C K j (sampleCount j delta failure)
    (oracleTime A C K 1 delta) (oracleTime A C K 1 (correctionTheta delta))
    (offsetAccuracy A delta) z v

end
end ContingencyTables.RootedEstimatorWordProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedEstimatorMedianProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executing independent complete estimators and their rational median -/

namespace ContingencyTables.RootedEstimatorMedianProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms
open RootedEstimatorLayoutProgram

abbrev Input := (Context×ℕ)×((List Bool×List Bool)×List Bool)

def words (z : Input) : List (List Bool) :=
  (wordChunks (wordWidth z.1.1,z.2.2)).take z.1.2

def sample (z : Input×List Bool) : TreeFraction.Fraction :=
  RootedEstimatorWordProgram.output (z.1.1.1,(z.1.2.1,z.2))

def samples (z : Input) : List TreeFraction.Fraction := (words z).map (fun bits => sample (z,bits))

attribute [local irreducible] samples

def output (z : Input) : TreeFraction.Fraction := MedianFractionProgram.median (samples z)

open GridBoundary CommonBasesFPRAS
open scoped Classical

end ContingencyTables.RootedEstimatorMedianProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedEstimatorMedianLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The executed inner median is the analysed amplified weight oracle -/

namespace ContingencyTables.RootedEstimatorMedianProgram

open MatchingFPRAS CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open CompanionOracleDensity RootedEstimatorLayoutProgram CommonBasesFPRAS
open scoped Classical

noncomputable section
variable {m n : ℕ}

def context (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (epsilon : ℚ)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) : Context :=
  RootedEstimatorWordProgram.scheduledContext A C K j (innerTolerance (epsilon/2) j) 1 z v

end
end ContingencyTables.RootedEstimatorMedianProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedLabelWeightProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The executed weight oracle at a current paired state

The immutable schedule and graph are shared. Each call reconstructs the
two small-cell views from its actual state, runs the independent median
estimator, and multiplies by the exact factorial ratio.
-/

namespace ContingencyTables.RootedLabelWeightProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped
open RootedEstimatorLayoutProgram

abbrev Config := (Context × ℕ) × (List Bool × List Bool)
abbrev Input := Config × (List ℕ × List Bool)

def stateInput (z : Input) : RootedOracleWalkProgram.State × List ℕ :=
  (z.1.1.1.1,z.2.1)
def stateInputRealizer : Realizer stateInput :=
  pair (composition (composition (composition first first) first) first)
    (composition second first)

def context (z : Input) : Context :=
  (replaceState (stateInput z),z.1.1.1.2)

def medianInput (z : Input) : RootedEstimatorMedianProgram.Input :=
  ((context z,z.1.1.2),(z.1.2,z.2.2))

def demandInput (z : Input) : PairedDemandProgram.Input :=
  ((stateInput z).1.1.2.2,z.2.1)
def demandInputRealizer : Realizer demandInput :=
  pair (composition (f := stateInput)
      (g := fun s : RootedOracleWalkProgram.State × List ℕ => s.1.1.2.2)
      stateInputRealizer (composition (composition (composition first first) second) second))
    (composition second first)

def factorialInput (z : Input) : PairedProfileProgram.Input :=
  (CompanionCellCatalog.capacities (PairedDemandProgram.cells (demandInput z)),z.2.1)
def factorialInputRealizer : Realizer factorialInput :=
  pair (composition (f := demandInput)
    (g := fun s : PairedDemandProgram.Input => CompanionCellCatalog.capacities (PairedDemandProgram.cells s))
    demandInputRealizer (composition (f := PairedDemandProgram.cells)
      (g := CompanionCellCatalog.capacities) PairedDemandProgram.cellsRealizer
        CompanionCellCatalog.capacitiesRealizer)) (composition second first)

attribute [local irreducible] medianInput factorialInput

def medianResult (z : Input) : TreeFraction.Fraction := RootedEstimatorMedianProgram.output (medianInput z)

def factorialResult (z : Input) : TreeFraction.Fraction := PairedFactorialProgram.output (factorialInput z)
def factorialResultRealizer : Realizer factorialResult :=
  composition (f := factorialInput) (g := PairedFactorialProgram.output)
    factorialInputRealizer PairedFactorialProgram.outputRealizer

attribute [local irreducible] medianResult factorialResult

def output (z : Input) : TreeFraction.Fraction := TreeFraction.mul (medianResult z,factorialResult z)

noncomputable section
open CompanionFactorialApplication CompanionArithmeticProposal GridBoundary
open CompanionOracleDensity CommonBasesFPRAS
open scoped Classical
variable {m n : ℕ}

def config (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (epsilon delta : ℚ)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (degree depth : List Bool) : Config :=
  ((RootedEstimatorMedianProgram.context A C K j epsilon z v,repetitionCount delta),(degree,depth))

end
end ContingencyTables.RootedLabelWeightProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionEvaluatedWeightProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The executed multiplier times labelled weight

Both factors are computed from the supplied current state. The matrix
lookup and the oracle consume no hidden finite-state enumeration.
-/

namespace ContingencyTables.CompanionEvaluatedWeightProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped
open CompanionMultiplierMatrixProgram

abbrev Frame := RootedLabelWeightProgram.Config × FractionMatrix
abbrev Input := (Frame × List ℕ) × List Bool

def multiplierInput (z : Input) : CompanionStateMultiplierProgram.Input :=
  (z.1.1.2,(PairedCatalogProgram.catalog z.1.2,z.1.2))
def multiplierInputRealizer : Realizer multiplierInput :=
  pair (composition (composition first first) second)
    (pair (composition (f := fun z : Input => z.1.2) (g := PairedCatalogProgram.catalog)
      (composition first second) PairedCatalogProgram.catalogRealizer) (composition first second))

def multiplier (z : Input) : TreeFraction.Fraction :=
  CompanionStateMultiplierProgram.output (multiplierInput z)
def multiplierRealizer : Realizer multiplier :=
  composition (f := multiplierInput) (g := CompanionStateMultiplierProgram.output)
    multiplierInputRealizer CompanionStateMultiplierProgram.outputRealizer

def weightInput (z : Input) : RootedLabelWeightProgram.Input := (z.1.1.1,(z.1.2,z.2))
def weightInputRealizer : Realizer weightInput :=
  pair (composition (composition first first) first) (pair (composition first second) second)

attribute [local irreducible] weightInput RootedLabelWeightProgram.output

def weight (z : Input) : TreeFraction.Fraction := RootedLabelWeightProgram.output (weightInput z)

attribute [local irreducible] multiplier weight

def output (z : Input) : TreeFraction.Fraction := TreeFraction.mul (multiplier z,weight z)

attribute [local irreducible] output

end ContingencyTables.CompanionEvaluatedWeightProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FractionMetropolisProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Clipped rational Metropolis acceptance as a binary program -/

namespace ContingencyTables.FractionMetropolisProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped

attribute [local irreducible] probability

def accept (z : Input) : Bool := FractionAcceptanceProgram.acceptCode (probability z,z.2)

end ContingencyTables.FractionMetropolisProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionMetropolisProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One physical companion-chain step with independent word fields

The proposed state is computed by the quadratic arithmetic candidate
list. Two disjoint words evaluate the current and candidate states, and
a third field supplies the rational acceptance coin.
-/

namespace ContingencyTables.CompanionMetropolisProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped

abbrev Frame := CompanionEvaluatedWeightProgram.Frame
abbrev Input := (Frame × List ℕ) × Words

def proposed (z : Input) : Option (List ℕ) :=
  CompanionComputedProposal.proposalProgram (z.1.2,z.2.2.1)

def candidate (z : Input) : List ℕ := (proposed z).getD z.1.2

attribute [local irreducible] candidate

def currentInput (z : Input) : CompanionEvaluatedWeightProgram.Input := (z.1,z.2.2.2.1.1)

def targetInput (z : Input) : CompanionEvaluatedWeightProgram.Input :=
  ((z.1.1,candidate z),z.2.2.2.1.2)

attribute [local irreducible] currentInput targetInput CompanionEvaluatedWeightProgram.output

def currentValue (z : Input) : TreeFraction.Fraction := CompanionEvaluatedWeightProgram.output (currentInput z)

def targetValue (z : Input) : TreeFraction.Fraction := CompanionEvaluatedWeightProgram.output (targetInput z)

attribute [local irreducible] currentValue targetValue

def acceptanceInput (z : Input) : FractionMetropolisProgram.Input :=
  ((currentValue z,targetValue z),z.2.2.2.2)

def accepted (z : Input) : Bool := FractionMetropolisProgram.accept (acceptanceInput z)

attribute [local irreducible] accepted

def output (z : Input) : List ℕ := if z.2.1 then z.1.2 else if accepted z then candidate z else z.1.2

end ContingencyTables.CompanionMetropolisProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionMetropolisWordProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded slicing of one flat companion transition word -/

namespace ContingencyTables.CompanionMetropolisWordProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms

/-- The fixed frame, the acceptance precision, current code, and fresh word. -/
abbrev Input := ((CompanionMetropolisProgram.Frame × ℕ) × List ℕ) × List Bool

def proposalWidth (z : Input) : ℕ := Nat.clog 2 ((z.1.2.length/2)^2)

def context (z : Input) : RootedEstimatorLayoutProgram.Context := z.1.1.1.1.1.1

def queryWidth (z : Input) : ℕ := z.1.1.1.1.1.2*RootedEstimatorLayoutProgram.wordWidth (context z)

attribute [local irreducible] context queryWidth proposalWidth

/-- Offsets are computed in binary; the physical `take`/`drop` calls remain
bounded by the supplied word on every malformed input. -/
def firstOffset (z : Input) : ℕ := 1+proposalWidth z

def secondOffset (z : Input) : ℕ := firstOffset z+queryWidth z
attribute [local irreducible] firstOffset

def coinOffset (z : Input) : ℕ := secondOffset z+queryWidth z
attribute [local irreducible] secondOffset

def slice (start count : Input → ℕ) (z : Input) : List Bool :=
  (z.2.drop (start z)).take (count z)

def fields (z : Input) : CompanionMetropolisProgram.Words :=
  (z.2.getD 0 false,
    (slice (fun _ => 1) proposalWidth z,
      ((slice firstOffset queryWidth z,slice secondOffset queryWidth z),
        slice coinOffset (fun z => z.1.1.2) z)))

def stepInput (z : Input) : CompanionMetropolisProgram.Input := ((z.1.1.1,z.1.2),fields z)

attribute [local irreducible] stepInput

def output (z : Input) : List ℕ := CompanionMetropolisProgram.output (stepInput z)

end ContingencyTables.CompanionMetropolisWordProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseBooleanWalkProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial program for the complete flat-word dense walk -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped GridBoundary ProfilePrograms

def denseWidthRealizer : Realizer denseStepBits := by
  let index := composition (composition (pair (constant 8) identity) multiply) ceilLogTwoRealizer
  let coins := composition (pair (constant 8) fifthPower) multiply
  exact composition (pair index coins) add

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseTrialProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The complete dense trial as a polynomial binary program -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped ProfilePrograms

def fiftiethPower : Realizer (fun n : ℕ => n^50) :=
  (composition (composition fifthPower squareNat) fifthPower).congr (by
    intro n
    simp only [Function.comp_apply]
    ring)

def trialWalkBitsRealizer : Realizer trialWalkBits := by
  let D : Realizer (fun z : DenseTrialData => z.1.1.2) :=
    composition (composition first first) second
  let H : Realizer (fun z : DenseTrialData => z.1.2) := composition first second
  let time := composition (pair (composition D fiftiethPower)
    (composition (composition H successor) squareNat)) multiply
  exact (composition (pair time (composition D denseWidthRealizer)) multiply).congr (by
    intro z
    simp only [Function.comp_apply,trialWalkBits,pow_two,Nat.succ_eq_add_one])

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseDrawProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The bounded dense draw as a single polynomial binary program -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped ProfilePrograms

def trialWidthRealizer : Realizer trialWidth := by
  let blank : Realizer (fun z : DenseDrawParameters => (z,([] : List Bool))) :=
    pair identity (constant [])
  let widths := composition (pair (composition first flatToGridDataRealizer) second)
    offsetLengthsRealizer
  exact composition (pair (composition blank trialWalkBitsRealizer)
    (composition widths listSum)) add

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_MaximalListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing a maximal margin in binary -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped

def maximumIndexRealizer : Realizer maximumIndex :=
  composition (pair (composition (pair identity (constant 0)) listMaximumRealizer) identity)
    (indexOf natEqual)

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseSwapProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary row and column permutations for dense input normalization -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped Polynomial

def swapZeroIndexRealizer : Realizer swapZeroIndex :=
  (choose (composition (pair second (constant 0)) natEqual) first
    (choose (composition (pair second first) natEqual) (constant 0) second)).congr
      (by intro z; simp only [swapZeroIndex,Function.comp_apply,decide_eq_true_eq])

variable {A : Type} [Codec A] [Inhabited A]

def swapZeroEntryRealizer : Realizer (swapZeroEntry (A := A)) :=
  composition (pair (composition first second)
    (composition (pair (composition first first) second) swapZeroIndexRealizer)) (getDFast default)

def swapZeroIndicesRealizer : Realizer (swapZeroIndices (A := A)) :=
  composition (composition second listLength) range

def swapZeroListRealizer : Realizer (swapZeroList (A := A)) :=
  composition (pair identity swapZeroIndicesRealizer) (mapWith swapZeroEntryRealizer)

def swapMatrixColumnsRealizer : Realizer swapMatrixColumns := mapWith swapZeroListRealizer

def swapMatrixRealizer : Realizer swapMatrix :=
  composition (pair (composition first second)
    (composition (pair (composition first first) second) swapZeroListRealizer)) swapMatrixColumnsRealizer

open scoped Classical

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseNormalizeProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Moving maximal margins into the distinguished positions -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped

def swapMarginsRealizer : Realizer swapMargins :=
  pair (composition (pair (composition first first) (composition second first)) swapZeroListRealizer)
    (composition (pair (composition first second) (composition second second)) swapZeroListRealizer)

def swapFlatDataRealizer : Realizer swapFlatData := by
  let data : Realizer (fun z : (ℕ×ℕ)×FlatExponentData => z.2) := second
  let margins := composition (pair first (composition (composition data first) first)) swapMarginsRealizer
  exact pair (pair margins (composition (composition data first) second)) (composition data second)

def permuteDrawDataRealizer : Realizer permuteDrawData := by
  let draw : Realizer (fun z : (ℕ×ℕ)×DenseDrawData => z.2) := second
  let params := composition (composition draw first) first
  let data := composition (pair first (composition params first)) swapFlatDataRealizer
  let fallback := composition (pair first (composition (composition draw first) second)) swapMatrixRealizer
  exact pair (pair (pair data (composition params second)) fallback) (composition draw second)

def marginIndicesRealizer : Realizer marginIndices :=
  pair (composition first maximumIndexRealizer) (composition second maximumIndexRealizer)

def drawIndicesRealizer : Realizer drawIndices := by
  let margins : Realizer (fun z : DenseDrawData => z.1.1.1.1.1) :=
    composition (composition (composition (composition first first) first) first) first
  exact composition margins marginIndicesRealizer

def preparedDrawRealizer : Realizer preparedDraw :=
  composition (pair drawIndicesRealizer identity) permuteDrawDataRealizer

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_GreedyRowMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A binary list program for one row of the greedy initializer -/

namespace ContingencyTables.GreedyFeasibleTable
open MatchingFPRAS.TreeTyped

def rowCellRealizer : Realizer rowCell := by
  let A : Realizer (fun z : ℕ × RowAccumulator => z.2.1) := composition second first
  let C : Realizer (fun z : ℕ × RowAccumulator => z.1) := first
  let Q := composition (pair A C) minimum
  let X : Realizer (fun z : ℕ × RowAccumulator => z.2.2.1) :=
    composition (composition second second) first
  let Y : Realizer (fun z : ℕ × RowAccumulator => z.2.2.2) :=
    composition (composition second second) second
  exact (pair (composition (pair A Q) subtract)
    (pair (composition (pair Q X) listCons)
      (composition (pair (composition (pair C Q) subtract) Y) listCons))).congr (fun _ => rfl)

def rowSplitRealizer : Realizer (fun z : ℕ × List ℕ => listSplitRow z.1 z.2) := by
  let start : Realizer (fun z : ℕ × List ℕ => (z.2,(z.1,(([] : List ℕ),([] : List ℕ))))) :=
    pair second (pair first (constant ([],[])))
  let finish : Realizer (fun z : RowAccumulator => (z.1,(z.2.1.reverse,z.2.2.reverse))) :=
    pair first (pair (composition (composition second first) reverse)
      (composition (composition second second) reverse))
  exact (composition (composition start (fold rowCellRealizer)) finish).congr (by
    intro z
    change (fun v : RowAccumulator => (v.1,(v.2.1.reverse,v.2.2.reverse)))
      (z.2.foldl (fun s c => rowCell (c,s)) (z.1,([],[])))=listSplitRow z.1 z.2
    rw [fold_rowCell]
    simp)

end ContingencyTables.GreedyFeasibleTable

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_GreedyTableMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed binary list program constructing the greedy table -/

namespace ContingencyTables.GreedyFeasibleTable
open MatchingFPRAS.TreeTyped

def tableRowRealizer : Realizer tableRow := by
  let row : Realizer (fun z : ℕ × TableAccumulator => listSplitRow z.1 z.2.1) :=
    composition (pair first (composition second first)) rowSplitRealizer
  exact (pair (composition (composition row second) second)
    (composition (pair (composition (composition row second) first)
      (composition second second)) listCons)).congr (fun _ => rfl)

/-- Every loop is over an input row or column; binary margins are never
counted down one unit at a time. -/
def tableRealizer : Realizer (fun z : List ℕ × List ℕ => listMatrix z.1 z.2) := by
  let start : Realizer (fun z : List ℕ × List ℕ => (z.1,(z.2,([] : List (List ℕ))))) :=
    pair first (pair second (constant []))
  exact (composition (composition (composition start (fold tableRowRealizer)) second) reverse).congr (by
    intro z
    change ((z.1.foldl (fun s a => tableRow (a,s)) (z.2,[])).2).reverse=_
    rw [fold_tableRow]
    simp)

end ContingencyTables.GreedyFeasibleTable

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseCanonicalProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Dense sampling from margins with a computed grid and fallback -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped ProfilePrograms

def zeroGridRealizer : Realizer zeroGrid :=
  composition (composition (pair (composition first tail) (composition second tail))
    cellPairsRealizer) (map (constant 0))

def canonicalInputRealizer : Realizer canonicalInput := by
  let margins : Realizer (fun z : CanonicalDrawData => z.1.1) := composition first first
  let parameters : Realizer (fun z : CanonicalDrawData => z.1.2) := composition first second
  let grid := composition margins zeroGridRealizer
  let fallback := composition margins GreedyFeasibleTable.tableRealizer
  exact pair (pair (pair (pair (pair margins grid) (composition parameters first))
    (composition parameters second)) fallback) second

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseReservedWord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing and consuming the exact dense-word prefix -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped ProfilePrograms FirstSuccess

def denseParameterBitsRealizer : Realizer denseParameterBits :=
  composition (pair (composition (pair (composition (composition first second) fourthPower)
    (composition second successor)) multiply) trialWidthRealizer) multiply

def preparedCanonicalParametersRealizer : Realizer preparedCanonicalParameters := by
  let blank : Realizer (fun z : CanonicalParameters => (z,([] : List Bool))) :=
    pair identity (constant [])
  let input : Realizer (fun z : CanonicalParameters => canonicalInput (z,[])) :=
    composition (f := fun z : CanonicalParameters => (z,([] : List Bool)))
      (g := canonicalInput) blank canonicalInputRealizer
  let prep : Realizer (fun z : CanonicalParameters => preparedDraw (canonicalInput (z,[]))) :=
    composition (f := fun z : CanonicalParameters => canonicalInput (z,[]))
      (g := preparedDraw) input preparedDrawRealizer
  exact composition (f := fun z : CanonicalParameters => preparedDraw (canonicalInput (z,[])))
    (g := fun z : DenseDrawData => z.1.1) prep (composition first first)

def canonicalBitCountRealizer : Realizer canonicalBitCount :=
  composition preparedCanonicalParametersRealizer denseParameterBitsRealizer

open GridBoundary
open scoped BigOperators Classical
end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_PaddedResidualProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing padded residual margins from the stored small profile -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

def largeFlagRealizer : Realizer largeFlag :=
  (choose leNat (constant 1) (constant 0)).congr
    (by intro z; simp only [largeFlag,decide_eq_true_eq])

def largeCountRealizer : Realizer largeCount := composition (mapWith largeFlagRealizer) listSum

def paddedMarginAtRealizer (row : Bool) : Realizer (paddedMarginAt row) := by
  let arg : Realizer (fun z : PaddingData×ℕ => (z.1.1,z.2)) :=
    pair (composition first first) second
  let value := composition arg (marginValueRealizer row)
  let used := composition arg (lineValueRealizer row)
  let threshold : Realizer (fun z : PaddingData×ℕ => z.1.1.2) :=
    composition (composition first first) second
  let pad : Realizer (fun z : PaddingData×ℕ => z.1.2) := composition first second
  let flag := composition (pair threshold value) largeFlagRealizer
  let count := composition (pair threshold
    (composition (composition first first) (marginListRealizer (!row)))) largeCountRealizer
  let amount := composition (pair (composition (pair flag count) multiply) pad) multiply
  let remain := composition (pair value used) subtract
  let result := composition (pair remain amount) add
  exact result

def paddedMarginsRealizer (row : Bool) : Realizer (paddedMargins row) :=
  composition (pair identity (composition first (marginIndices row))) (mapWith (paddedMarginAtRealizer row))

open scoped BigOperators

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_LargeMarginProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing the large rectangle and its padded margins -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

def largeIndexTestRealizer : Realizer largeIndexTest :=
  composition (pair (composition first first)
    (composition (pair (composition first second) second) (getDFast 0))) leNat

def largeIndicesRealizer : Realizer largeIndices :=
  composition (pair identity (composition (composition second listLength) range))
    (filterWith largeIndexTestRealizer)

def selectListRealizer {A : Type} [Codec A] (a : A) : Realizer (selectList a) :=
  composition (pair second first) (mapWith (getDFast a))

def largePaddedMarginsRealizer (row : Bool) : Realizer (largePaddedMargins row) :=
  composition (pair
    (composition (pair (composition first second)
      (composition first (marginListRealizer row))) largeIndicesRealizer)
    (paddedMarginsRealizer row)) (selectListRealizer 0)

def profilePaddedMargins (row : Bool) (z : ProfileCheckData×ℕ) : List ℕ :=
  largePaddedMargins row
    (((((z.1.1.1.1,if row then z.1.1.1.2.1 else complementValues (z.1.2,z.1.1.1.2.2)),
      z.1.1.2),z.1.2)),z.2)

def profilePaddedMarginsRealizer (row : Bool) : Realizer (profilePaddedMargins row) :=
  composition (pair (composition first (profileLineData row)) second)
    (largePaddedMarginsRealizer row)

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_ResidualDenseProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A computed dense completion call from a retained small profile -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

abbrev ResidualParameters := (ProfileCheckData×ℕ)×(ℕ×ℕ)

def residualParameters (z : ResidualParameters) : DensePrograms.CanonicalParameters :=
  ((profilePaddedMargins true z.1,profilePaddedMargins false z.1),z.2)

def residualParametersRealizer : Realizer residualParameters := by
  let rows : Realizer (fun z : ResidualParameters => profilePaddedMargins true z.1) :=
    composition (f := fun z : ResidualParameters => z.1) (g := profilePaddedMargins true)
      first (profilePaddedMarginsRealizer true)
  let columns : Realizer (fun z : ResidualParameters => profilePaddedMargins false z.1) :=
    composition (f := fun z : ResidualParameters => z.1) (g := profilePaddedMargins false)
      first (profilePaddedMarginsRealizer false)
  exact pair (pair rows columns) second

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionBoundedWalkProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial iteration of the physical companion transition

Clipping is redundant on the encoded binary chain states. It gives a
uniform bound on malformed inputs, so repeated calls remain polynomial.
-/

namespace ContingencyTables.CompanionBoundedWalkProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial

abbrev Fixed := (CompanionMetropolisProgram.Frame × ℕ) × List ℕ
abbrev State := Fixed × List ℕ

def transitionInput (z : List Bool × State) : CompanionMetropolisWordProgram.Input :=
  ((z.2.1.1,z.2.2),z.1)
def transitionInputRealizer : Realizer transitionInput :=
  pair (pair (composition (composition second first) first) (composition second second)) first

def candidate (z : List Bool × State) : List ℕ := CompanionMetropolisWordProgram.output (transitionInput z)

def bound (z : List Bool × State) : ℕ := z.2.1.2.length
def boundRealizer : Realizer bound :=
  composition (composition (composition second first) second) listLength

attribute [local irreducible] candidate

def next (z : List Bool × State) : List ℕ := ProfilePrograms.capView ((bound z,1),candidate z)

def advance (z : List Bool × State) : State := (z.2.1,next z)

abbrev RecordState := State × List (List ℕ)

end ContingencyTables.CompanionBoundedWalkProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_CheegerCoarea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Weighted finite coarea for the published Cheeger input -/
namespace ContingencyTables.CheegerProof
open MeasureTheory CommonBasesFPRAS
open scoped BigOperators Classical
noncomputable section

variable {X : Type*} [Fintype X] (C : FiniteChain X)

def mass (S : Finset X) : ℝ := ∑ x ∈ S, C.π x
def cut (S : Finset X) : ℝ := ∑ x ∈ S, ∑ y ∈ Sᶜ, C.π x*C.P x y

end
end ContingencyTables.CheegerProof

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_DirectedBFSProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial binary programs for one stored BFS round -/

namespace ContingencyTables.DirectedBFSProgram

open MatchingFPRAS.TreeTyped Polynomial DirectedBFSCode

def indicesRealizer : Realizer indices := composition listLength range

def pathSomeRealizer : Realizer (fun o : Option (List ℕ)=>o.isSome) :=
  (composition (pair (constant false) identity)
    (optionCases (constant false) (constant true))).congr (by
      intro o
      cases o <;> rfl)

def lookupRealizer : Realizer lookupPath := getDFast none
def readEdgeRealizer : Realizer readEdge :=
  composition (pair (composition first (getDFast [])) second) (getDFast false)

def candidateRealizer : Realizer candidate := by
  let G : Realizer (fun z : Candidate=>z.1.1.1) := composition (composition first first) first
  let P : Realizer (fun z : Candidate=>z.1.1.2) := composition (composition first first) second
  let V : Realizer (fun z : Candidate=>z.1.2) := composition first second
  let U : Realizer (fun z : Candidate=>z.2) := second
  let known : Realizer (fun z : Candidate=>(lookup z.1.1.2 z.2).isSome) :=
    composition (composition (pair P U) lookupRealizer) pathSomeRealizer
  let edge : Realizer (fun z : Candidate=>adjacent z.1.1.1 z.2 z.1.2) :=
    composition (pair (pair G U) V) readEdgeRealizer
  exact composition (pair known edge) boolAnd

def headOptionRealizer : Realizer (fun xs : List ℕ=>xs.head?) :=
  (listCase none (composition first some)).congr (by intro xs;cases xs <;> rfl)

def predecessorRealizer : Realizer predecessorInput :=
  (composition (composition (pair identity
      (composition (composition first first) indicesRealizer)) (filterWith candidateRealizer))
    headOptionRealizer).congr (by
      intro z
      simp only [Function.comp_apply,id_eq,predecessorInput,DirectedBFSCode.predecessor,indices,
        List.head?_filter,candidate])

def appendPathRealizer : Realizer appendPath :=
  composition (composition (pair second
      (composition (pair (composition first second) (constant [])) listCons)) append) some

def fromPredecessorRealizer : Realizer fromPredecessor :=
  (composition (pair first
      (composition (pair (composition (composition first first) second) second) lookupRealizer))
    (optionCases (constant none) appendPathRealizer)).congr (by
      intro z
      dsimp only [Function.comp_apply,lookupPath,fromPredecessor,appendPath]
      cases h : lookup z.1.1.2 z.2 <;> rfl)

def missingRealizer : Realizer missing :=
  (composition (pair identity predecessorRealizer)
    (optionCases (constant none) fromPredecessorRealizer)).congr (by
      intro z
      dsimp only [Function.comp_apply,id_eq,missing]
      cases h : predecessorInput z <;> rfl)

def rowRealizer : Realizer rowInput :=
  (composition (pair identity
      (composition (pair (composition first second) second) lookupRealizer))
    (optionCases missingRealizer (composition second some))).congr (by
      intro z
      dsimp only [Function.comp_apply,id_eq,lookupPath,rowInput,roundRow]
      cases h : lookup z.1.2 z.2 <;> rfl)

def roundRealizer : Realizer roundInput :=
  composition (pair identity (composition first indicesRealizer)) (mapWith rowRealizer)

end ContingencyTables.DirectedBFSProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_DirectedBFSRuntime
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial binary execution of the entire materialized BFS -/

namespace ContingencyTables.DirectedBFSRuntime

open MatchingFPRAS.TreeTyped Polynomial DirectedBFSCode DirectedBFSProgram

def advanceRealizer : Realizer advance :=
  pair (composition second first) (composition second roundRealizer)

def initialRowRealizer : Realizer initialRow :=
  (choose (composition (pair second first) natEqual)
    (composition (composition (pair first (constant [])) listCons) some)
    (constant none)).congr (by
      intro z
      simp only [Function.comp_apply,initialRow,decide_eq_true_eq])

def initialRealizer : Realizer initialInput :=
  composition (pair second (composition first indicesRealizer)) (mapWith initialRowRealizer)

def prepareRealizer : Realizer prepare :=
  pair (composition (f := fun z : Graph×ℕ=>z.1) (g := indices) first indicesRealizer)
    (pair first initialRealizer)

def runRealizer : Realizer runInput :=
  (composition (composition prepareRealizer (MatchingFPRAS.TreeTyped.fold advanceRealizer))
    second).congr (by
      intro z
      change ((indices z.1).foldl (fun s i=>advance (i,s)) (z.1,initial z.1 z.2)).2 = _
      rw [fold_eq]
      rfl)

def searchRealizer : Realizer searchInput :=
  composition (pair (composition first runRealizer) second) lookupRealizer

end ContingencyTables.DirectedBFSRuntime

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_ResidualGraphProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary construction and search of the actual residual graph -/

namespace ContingencyTables.ResidualGraphProgram

open MatchingFPRAS.TreeTyped DirectedBFSProgram SignedPairProgram

abbrev FlowMatrix := List (List Signed)
abbrev Data := NatMatrix×FlowMatrix
abbrev ArcInput := Data×(ℕ×ℕ)

def matrixIndicesRealizer : Realizer matrixIndices := composition listLength range

def capacityEntryRealizer : Realizer capacityEntry :=
  composition (pair (composition (pair first (composition second first)) (getDFast []))
    (composition second second)) (getDFast 0)

def flowEntry (z : FlowMatrix×(ℕ×ℕ)) : Signed :=
  (z.1.getD z.2.1 []).getD z.2.2 (0,0)

def flowEntryRealizer : Realizer flowEntry :=
  composition (pair (composition (pair first (composition second first)) (getDFast []))
    (composition second second)) (getDFast (0,0))

def arcData (z : ArcInput) : ℕ×Signed :=
  (capacityEntry (z.1.1,z.2),flowEntry (z.1.2,z.2))

def arcDataRealizer : Realizer arcData :=
  pair (composition (pair (composition first first) second) capacityEntryRealizer)
    (composition (pair (composition first second) second) flowEntryRealizer)

def residualValue (z : ℕ×Signed) : ℕ := (z.1+z.2.2)-z.2.1

def residualValueRealizer : Realizer residualValue :=
  composition (pair (composition (pair first (composition second second)) add)
    (composition second first)) subtract

def positive (z : ℕ×Signed) : Bool := decide (z.2.1< z.1+z.2.2)

def positiveRealizer : Realizer positive :=
  composition (pair (composition second first)
    (composition (pair first (composition second second)) add)) less

def arc (z : ArcInput) : Bool := positive (arcData z)
def arcRealizer : Realizer arc := composition arcDataRealizer positiveRealizer

def arcRow (z : Data×ℕ) : List Bool :=
  (List.range z.1.1.length).map (fun v=>arc (z.1,(z.2,v)))

def arcRowRealizer : Realizer arcRow :=
  composition
    (f := fun z : Data×ℕ=>(z,List.range z.1.1.length))
    (g := fun z : (Data×ℕ)×List ℕ=>z.2.map (fun v=>arc (z.1.1,(z.1.2,v))))
    (pair identity (composition
      (f := fun z : Data×ℕ=>z.1.1) (g := matrixIndices)
      (composition first first) matrixIndicesRealizer))
    (mapWith (composition
      (f := fun z : (Data×ℕ)×ℕ=>(z.1.1,(z.1.2,z.2))) (g := arc)
      (pair (composition first first) (pair (composition first second) second)) arcRealizer))

def graph (z : Data) : DirectedBFSCode.Graph :=
  (List.range z.1.length).map (fun u=>arcRow (z,u))

def graphRealizer : Realizer graph :=
  composition
    (f := fun z : Data=>(z,List.range z.1.length))
    (g := fun z : Data×List ℕ=>z.2.map (fun u=>arcRow (z.1,u)))
    (pair identity (composition (f := fun z : Data=>z.1) (g := matrixIndices)
      first matrixIndicesRealizer)) (mapWith arcRowRealizer)

def flowCode {m n : ℕ} (f : Fin m→Fin n→ℤ) : FlowMatrix :=
  List.ofFn (fun u=>List.ofFn (fun v=>ForestAffineProgram.signedParts (f u v)))

lemma flowEntry_code {m n : ℕ} (f : Fin m→Fin n→ℤ) (u : Fin m) (v : Fin n) :
    flowEntry (flowCode f,(u.val,v.val))=ForestAffineProgram.signedParts (f u v) := by
  simp only [flowEntry,flowCode,List.getD_eq_getElem?_getD,List.getElem?_ofFn,
    u.isLt,v.isLt,dite_true,Option.getD_some,Fin.eta]

lemma residualValue_correct (c : ℕ) (z : Signed) :
    residualValue (c,z)=((c:ℤ)-SignedPairProgram.value z).toNat := by
  unfold residualValue SignedPairProgram.value
  dsimp only
  omega

lemma positive_correct (c : ℕ) (z : Signed) :
    positive (c,z)=decide (0<(c:ℤ)-SignedPairProgram.value z) := by
  apply Bool.eq_iff_iff.mpr
  change (decide (z.1 < c+z.2)=true) ↔
    (decide (0<(c:ℤ)-SignedPairProgram.value z)=true)
  rw [decide_eq_true_eq,decide_eq_true_eq]
  change z.1 < c+z.2 ↔ 0<(c:ℤ)-((z.1:ℤ)-z.2)
  omega

lemma arc_code {n : ℕ} (c : PublishedEdmondsKarp.Capacity n)
    (f : PublishedEdmondsKarp.Flow n) (u v : Fin n) :
    arc ((natCode c,flowCode f),(u.val,v.val))=ResidualSearch.edge c f u v := by
  simp only [arc,arcData,capacityEntry_code,flowEntry_code,positive_correct,
    SignedPairProgram.value,ForestAffineProgram.signedParts_sub,ResidualSearch.edge]

lemma graph_code {n : ℕ} (c : PublishedEdmondsKarp.Capacity n)
    (f : PublishedEdmondsKarp.Flow n) :
    graph (natCode c,flowCode f)=DirectedBFSCode.graphCode (ResidualSearch.edge c f) := by
  simp only [graph,arcRow,natCode,List.length_ofFn,DirectedBFSCode.range_eq_map,
    ←List.ofFn_eq_map,List.map_ofFn,DirectedBFSCode.graphCode]
  apply congrArg List.ofFn
  funext u
  apply congrArg List.ofFn
  funext v
  exact arc_code c f u v

def search (z : Data×(ℕ×ℕ)) : Option (List ℕ) :=
  DirectedBFSCode.search (graph z.1) z.2.1 z.2.2

def searchRealizer : Realizer search :=
  composition (pair (pair (composition first graphRealizer) (composition second first))
    (composition second second)) DirectedBFSRuntime.searchRealizer

lemma search_code {n : ℕ} (c : PublishedEdmondsKarp.Capacity n)
    (f : PublishedEdmondsKarp.Flow n) (s t : Fin n) :
    search ((natCode c,flowCode f),(s.val,t.val))=
      (ResidualSearch.search c f s t).map (List.map Fin.val) := by
  rw [search,graph_code,DirectedBFSCode.search_code]
  rfl

end ContingencyTables.ResidualGraphProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FlowClamp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary flow magnitudes and a harmless total-domain clamp

Skew symmetry bounds a feasible entry between its two directed
capacities. The executed list program clamps normalized entries to this
interval. This is the identity on every valid flow and bounds every
stored value even on unrelated raw program inputs.
-/

namespace ContingencyTables.FlowClamp

open MatchingFPRAS.TreeTyped SignedPairProgram PublishedEdmondsKarp

def clamp (z : (ℕ×ℕ)×Signed) : Signed :=
  (min z.1.1 (z.2.1-z.2.2),min z.1.2 (z.2.2-z.2.1))

def clampRealizer : Realizer clamp := by
  let A : Realizer (fun z : (ℕ×ℕ)×Signed=>z.1.1) := composition first first
  let B : Realizer (fun z : (ℕ×ℕ)×Signed=>z.1.2) := composition first second
  let N : Realizer (fun z : (ℕ×ℕ)×Signed=>SignedPairProgram.normalize z.2) :=
    composition second normalizeRealizer
  exact pair (composition (pair A (composition N first)) minimum)
    (composition (pair B (composition N second)) minimum)

theorem clamp_eq_normalize (limits : ℕ×ℕ) (z : Signed)
    (hl : -(limits.2:ℤ)≤SignedPairProgram.value z) (hu : SignedPairProgram.value z≤limits.1) :
    clamp (limits,z)=SignedPairProgram.normalize z := by
  apply Prod.ext
  · change min limits.1 (z.1-z.2)=z.1-z.2
    apply min_eq_right
    unfold SignedPairProgram.value at hu
    omega
  · change min limits.2 (z.2-z.1)=z.2-z.1
    apply min_eq_right
    unfold SignedPairProgram.value at hl
    omega

theorem clamp_feasible {n : ℕ} (c : Capacity n) (s t : Fin n) (f : Flow n)
    (hf : Feasible c s t f) (u v : Fin n) (z : Signed) (hz : SignedPairProgram.value z=f u v) :
    clamp ((c u v,c v u),z)=ForestAffineProgram.signedParts (f u v) := by
  rw [clamp_eq_normalize _ z (by rw [hz];exact feasible_lower c s t f hf u v)
    (by rw [hz];exact hf.2.1 u v),SignedPairProgram.normalize_eq,hz]

end ContingencyTables.FlowClamp

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_PathAugmentation
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integral augmentation along a simple path

The identities here prove conservation and capacity preservation for the
literal forward-minus-reverse update in the published-input interface.
-/

namespace ContingencyTables.PathAugmentation

open PublishedEdmondsKarp
open scoped BigOperators

variable {n k : ℕ}

lemma arcCount_eq_zero (p : Fin (k+1) → Fin n) (u v : Fin n)
    (h : ¬∃ i : Fin k,p i.castSucc=u ∧ p i.succ=v) : arcCount p u v=0 := by
  apply Finset.sum_eq_zero
  intro i _
  exact ite_eq_right (fun hi=>h ⟨i,hi⟩)

lemma arcCount_eq_one (p : Fin (k+1) → Fin n) (hp : Function.Injective p)
    (i : Fin k) : arcCount p (p i.castSucc) (p i.succ)=1 := by
  unfold arcCount
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    apply ite_eq_right
    intro h
    exact hji (Fin.castSucc_inj.mp (hp h.1))
  · simp

lemma update_capacity (c : Capacity n) (f : Flow n)
    (hf : ∀ u v,f u v ≤ c u v) (p : Fin (k+1) → Fin n)
    (hp : Function.Injective p) (a : ℤ) (ha : 0≤a)
    (hres : ∀ i : Fin k,a≤(c (p i.castSucc) (p i.succ):ℤ)-f (p i.castSucc) (p i.succ)) :
    ∀ u v,update f p a u v ≤ c u v := by
  intro u v
  have hr := arcCount_nonneg p v u
  by_cases he : ∃ i : Fin k,p i.castSucc=u ∧ p i.succ=v
  · obtain ⟨i,rfl,rfl⟩ := he
    rw [update,arcCount_eq_one p hp i]
    have h := hres i
    have hn := mul_nonneg ha hr
    nlinarith
  · rw [update,arcCount_eq_zero p u v he]
    have h := hf u v
    have hn := mul_nonneg ha hr
    nlinarith

theorem update_feasible (c : Capacity n) (s t : Fin n) (f : Flow n)
    (hf : Feasible c s t f) (p : Fin (k+1) → Fin n)
    (hp : ResidualPath c f s t k p) (a : ℤ) (ha : 0≤a)
    (hres : ∀ i : Fin k,a≤(c (p i.castSucc) (p i.succ):ℤ)-f (p i.castSucc) (p i.succ)) :
    Feasible c s t (update f p a) := by
  refine ⟨update_skew f hf.1 p a,update_capacity c f hf.2.1 p hp.2.2.1 a ha hres,?_⟩
  intro u hus hut
  rw [update_sum,hp.1,hp.2.1,hf.2.2 u hus hut]
  simp [Ne.symm hus,Ne.symm hut]

end ContingencyTables.PathAugmentation

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ResidualAugmentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executed bottleneck and residual augmentation

The program takes the actual BFS path list, scans its residual capacities
for a minimum, and adds the resulting skew path flow. No path or amount
is chosen through a mathematical existence proof.
-/

namespace ContingencyTables.ResidualAugmentation

open PublishedEdmondsKarp
open scoped BigOperators

variable {n : ℕ}

theorem step_feasible (c : Capacity n) (s t : Fin n) (hst : s≠t)
    (f g : Flow n) (hf : Feasible c s t f) (h : step c s t f=some g) :
    Feasible c s t g := by
  obtain ⟨k,p,a,hp,_,ha,hr,_,hu⟩ := step_augmentation c s t hst f g h
  have he : g=PathAugmentation.update f p a := funext (fun u=>funext (hu u))
  rw [he]
  exact PathAugmentation.update_feasible c s t f hf p hp a ha.le hr

end ContingencyTables.ResidualAugmentation

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FlowPathProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary path bottlenecks and one integral flow-entry update -/

namespace ContingencyTables.FlowPathProgram

open MatchingFPRAS.TreeTyped DirectedBFSProgram ResidualGraphProgram SignedPairProgram

def pairAtRealizer : Realizer pairAt :=
  pair (getDFast 0) (composition
    (pair first (composition second successor)) (getDFast 0))

def arcIndicesRealizer : Realizer arcIndices :=
  composition (composition listLength predecessor) range

def arcPairsRealizer : Realizer arcPairs :=
  composition (pair identity arcIndicesRealizer) (mapWith pairAtRealizer)

def minimumScanRealizer : Realizer minimumScan :=
  (listCase 0 (composition (pair second first) (fold minimum))).congr (by
    intro xs
    cases xs <;> rfl)

def residuals (z : Data×List ℕ) : List ℕ :=
  (arcPairs z.2).map (fun uv=>residualValue (arcData (z.1,uv)))

def residualsRealizer : Realizer residuals :=
  composition (pair first (composition second arcPairsRealizer))
    (mapWith (composition arcDataRealizer residualValueRealizer))

def bottleneck (z : Data×List ℕ) : ℕ := minimumScan (residuals z)
def bottleneckRealizer : Realizer bottleneck := composition residualsRealizer minimumScanRealizer

lemma bottleneck_code {n : ℕ} (c : PublishedEdmondsKarp.Capacity n)
    (f : PublishedEdmondsKarp.Flow n) (xs : List (Fin n))
    (hres : ∀ uv∈ResidualAugmentation.arcs xs,0≤(c uv.1 uv.2:ℤ)-f uv.1 uv.2) :
    (bottleneck ((natCode c,flowCode f),xs.map Fin.val):ℤ)=
      ResidualAugmentation.bottleneck c f xs := by
  rw [bottleneck,minimumScan_cast]
  apply congrArg (fun zs : List ℤ=>zs.min?.getD 0)
  simp only [residuals,arcPairs_map,List.map_map]
  change (ResidualAugmentation.arcs xs).map (fun uv=>
      (residualValue (arcData ((natCode c,flowCode f),(uv.1.val,uv.2.val))):ℤ))=
    (ResidualAugmentation.arcs xs).map (fun uv=>(c uv.1 uv.2:ℤ)-f uv.1 uv.2)
  apply List.map_congr_left
  intro uv huv
  simp only [arcData,capacityEntry_code,flowEntry_code,
    residualValue_correct,SignedPairProgram.value,ForestAffineProgram.signedParts_sub]
  exact Int.toNat_of_nonneg (hres uv huv)

def pairEqualRealizer : Realizer pairEqual :=
  composition (pair
    (composition (pair (composition first first) (composition second first)) natEqual)
    (composition (pair (composition first second) (composition second second)) natEqual)) boolAnd

def arcCountRealizer : Realizer arcCount :=
  composition (filterWith pairEqualRealizer) listLength

end ContingencyTables.FlowPathProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FlowEntryProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary signed augmentation of one matrix entry -/

namespace ContingencyTables.FlowEntryProgram

open MatchingFPRAS.TreeTyped ResidualGraphProgram SignedPairProgram FlowPathProgram

abbrev UpdateData := Data×(List (ℕ×ℕ)×ℕ)
abbrev EntryInput := UpdateData×(ℕ×ℕ)
abbrev RawInput := Signed×(ℕ×(ℕ×ℕ))

def rawUpdate (z : RawInput) : Signed :=
  (z.1.1+z.2.1*z.2.2.1,z.1.2+z.2.1*z.2.2.2)

def rawUpdateRealizer : Realizer rawUpdate := by
  let old : Realizer (fun z : RawInput=>z.1) := first
  let a : Realizer (fun z : RawInput=>z.2.1) := composition second first
  let f : Realizer (fun z : RawInput=>z.2.2.1) := composition (composition second second) first
  let b : Realizer (fun z : RawInput=>z.2.2.2) := composition (composition second second) second
  exact composition (pair old (pair (composition (pair a f) multiply)
    (composition (pair a b) multiply))) plusRealizer

lemma rawUpdate_value (old : Signed) (a f b : ℕ) :
    SignedPairProgram.value (rawUpdate (old,(a,(f,b))))=
      SignedPairProgram.value old+(a:ℤ)*((f:ℤ)-b) := by
  simp only [rawUpdate,SignedPairProgram.value,Nat.cast_add,Nat.cast_mul]
  ring

def limits (z : EntryInput) : ℕ×ℕ :=
  (capacityEntry (z.1.1.1,z.2),capacityEntry (z.1.1.1,(z.2.2,z.2.1)))

def limitsRealizer : Realizer limits := by
  let C : Realizer (fun z : EntryInput=>z.1.1.1) := composition (composition first first) first
  let uv : Realizer (fun z : EntryInput=>z.2) := second
  let vu : Realizer (fun z : EntryInput=>(z.2.2,z.2.1)) :=
    pair (composition second second) (composition second first)
  exact pair (composition (pair C uv) capacityEntryRealizer)
    (composition (pair C vu) capacityEntryRealizer)

def rawInput (z : EntryInput) : RawInput :=
  (flowEntry (z.1.1.2,z.2),(z.1.2.2,
    (arcCount (z.2,z.1.2.1),arcCount ((z.2.2,z.2.1),z.1.2.1))))

def rawInputRealizer : Realizer rawInput := by
  let F : Realizer (fun z : EntryInput=>z.1.1.2) :=
    composition (composition first first) second
  let as : Realizer (fun z : EntryInput=>z.1.2.1) :=
    composition (composition first second) first
  let a : Realizer (fun z : EntryInput=>z.1.2.2) :=
    composition (composition first second) second
  let uv : Realizer (fun z : EntryInput=>z.2) := second
  let vu : Realizer (fun z : EntryInput=>(z.2.2,z.2.1)) :=
    pair (composition second second) (composition second first)
  let forward : Realizer (fun z : EntryInput => arcCount (z.2,z.1.2.1)) :=
    composition (f := fun z : EntryInput => (z.2,z.1.2.1))
      (g := FlowPathProgram.arcCount) (pair uv as) arcCountRealizer
  let backward : Realizer (fun z : EntryInput => arcCount ((z.2.2,z.2.1),z.1.2.1)) :=
    composition (f := fun z : EntryInput => ((z.2.2,z.2.1),z.1.2.1))
      (g := FlowPathProgram.arcCount) (pair vu as) arcCountRealizer
  exact pair (composition (pair F uv) flowEntryRealizer)
    (pair a (pair forward backward))

def updateCell (z : EntryInput) : Signed :=
  FlowClamp.clamp (limits z,rawUpdate (rawInput z))

def updateCellRealizer : Realizer updateCell :=
  composition (pair limitsRealizer (composition rawInputRealizer rawUpdateRealizer))
    FlowClamp.clampRealizer

lemma updateCell_code {n : ℕ} (c : PublishedEdmondsKarp.Capacity n)
    (s t : Fin n) (f : PublishedEdmondsKarp.Flow n) (xs : List (Fin n)) (a : ℕ)
    (hnew : PublishedEdmondsKarp.Feasible c s t
      (ResidualAugmentation.listUpdate f xs (a:ℤ))) (u v : Fin n) :
    updateCell (((natCode c,flowCode f),
      ((ResidualAugmentation.arcs xs).map (fun uv=>(uv.1.val,uv.2.val)),a)),(u.val,v.val))=
      ForestAffineProgram.signedParts (ResidualAugmentation.listUpdate f xs (a:ℤ) u v) := by
  unfold updateCell limits rawInput
  rw [capacityEntry_code,capacityEntry_code,flowEntry_code]
  apply FlowClamp.clamp_feasible c s t _ hnew u v
  rw [rawUpdate_value,arcCount_map,arcCount_map]
  simp only [SignedPairProgram.value,ForestAffineProgram.signedParts_sub,
    ResidualAugmentation.listUpdate]

end ContingencyTables.FlowEntryProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_EdmondsKarpAlgorithm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The bounded deterministic integral max-flow algorithm

Conditional on the augmentation-count bound, concrete residual searches,
bottlenecks and flow updates preserve feasibility and yield a stopping
certificate.
-/

namespace ContingencyTables.EdmondsKarpAlgorithm

open PublishedEdmondsKarp ResidualAugmentation

variable {n : ℕ}

lemma run_feasible (c : Capacity n) (s t : Fin n) (hst : s≠t) (k : ℕ) :
    Feasible c s t (run c s t k) := by
  induction k with
  | zero => exact zero_feasible c s t
  | succ k ih =>
    cases hs : step c s t (run c s t k) with
    | none => simpa only [run,advance,hs,Option.getD_none] using ih
    | some g =>
      simpa only [run,advance,hs,Option.getD_some] using
        step_feasible c s t hst (run c s t k) g ih hs

theorem termination (hEK : EdmondsKarp1972Theorem1)
    (c : Capacity n) (hc : ∀ u,c u u=0) (s t : Fin n) (hst : s≠t) :
    ∃ i≤n^3,step c s t (run c s t i)=none := by
  by_contra hn
  have hsome : ∀ i≤n^3,∃ g,step c s t (run c s t i)=some g := by
    intro i hi
    cases hs : step c s t (run c s t i) with
    | none => exact False.elim (hn ⟨i,hi,hs⟩)
    | some g => exact ⟨g,rfl⟩
  let F : Fin (n^3+2) → Flow n := fun i=>run c s t i.val
  have hF : AugmentationTrace c s t F := by
    refine ⟨rfl,?_,?_⟩
    · intro i
      exact run_feasible c s t hst i.val
    · intro i
      obtain ⟨g,hg⟩ := hsome i.val (by have hi:=i.isLt; omega)
      have he : F i.succ=g := run_step c s t i.val g hg
      rw [he]
      exact step_augmentation c s t hst (F i.castSucc) g hg
  exact no_long_trace hEK c hc s t hst F hF

theorem maxFlow_correct (hEK : EdmondsKarp1972Theorem1)
    (c : Capacity n) (hc : ∀ u,c u u=0) (s t : Fin n) (hst : s≠t) :
    IsMaximum c s t (maxFlow c s t) := by
  obtain ⟨i,hi,hs⟩ := termination hEK c hc s t hst
  have hstop := run_stops c s t i hs (n^3+1-i)
  have he : i+(n^3+1-i)=n^3+1 := by omega
  rw [he] at hstop
  unfold maxFlow
  rw [hstop]
  exact step_none_maximum c s t (run c s t i) (run_feasible c s t hst i) hs

end ContingencyTables.EdmondsKarpAlgorithm

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FlowMatrixProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Materialized binary residual augmentation

The path and bottleneck are computed once, then every matrix entry is
updated from the preceding matrix. Missing paths leave that matrix
unchanged.
-/

namespace ContingencyTables.FlowMatrixProgram

open MatchingFPRAS.TreeTyped DirectedBFSProgram ResidualGraphProgram FlowPathProgram
  FlowEntryProgram

def updateRow (z : UpdateData×ℕ) : List SignedPairProgram.Signed :=
  (List.range z.1.1.1.length).map (fun v=>updateCell (z.1,(z.2,v)))

def updateRowRealizer : Realizer updateRow :=
  composition
    (f := fun z : UpdateData×ℕ=>(z,List.range z.1.1.1.length))
    (g := fun z : (UpdateData×ℕ)×List ℕ=>
      z.2.map (fun v=>updateCell (z.1.1,(z.1.2,v))))
    (pair identity (composition (f := fun z : UpdateData×ℕ=>z.1.1.1)
      (g := matrixIndices) (composition (composition first first) first) matrixIndicesRealizer))
    (mapWith (composition
      (f := fun z : (UpdateData×ℕ)×ℕ=>(z.1.1,(z.1.2,z.2))) (g := updateCell)
      (pair (composition first first) (pair (composition first second) second)) updateCellRealizer))

def updateMatrix (z : UpdateData) : FlowMatrix :=
  (List.range z.1.1.length).map (fun u=>updateRow (z,u))

def updateMatrixRealizer : Realizer updateMatrix :=
  composition
    (f := fun z : UpdateData=>(z,List.range z.1.1.length))
    (g := fun z : UpdateData×List ℕ=>z.2.map (fun u=>updateRow (z.1,u)))
    (pair identity (composition (f := fun z : UpdateData=>z.1.1) (g := matrixIndices)
      (composition first first) matrixIndicesRealizer)) (mapWith updateRowRealizer)

lemma updateMatrix_code {n : ℕ} (c : PublishedEdmondsKarp.Capacity n)
    (s t : Fin n) (f : PublishedEdmondsKarp.Flow n) (xs : List (Fin n)) (a : ℕ)
    (hnew : PublishedEdmondsKarp.Feasible c s t
      (ResidualAugmentation.listUpdate f xs (a:ℤ))) :
    updateMatrix ((natCode c,flowCode f),
      ((ResidualAugmentation.arcs xs).map (fun uv=>(uv.1.val,uv.2.val)),a))=
      flowCode (ResidualAugmentation.listUpdate f xs (a:ℤ)) := by
  simp only [updateMatrix,updateRow,natCode,List.length_ofFn,DirectedBFSCode.range_eq_map,
    List.map_ofFn,←List.ofFn_eq_map,flowCode]
  apply congrArg List.ofFn
  funext u
  apply congrArg List.ofFn
  funext v
  exact updateCell_code c s t f xs a hnew u v

def prepareAugment (z : Data×List ℕ) : UpdateData :=
  (z.1,(arcPairs z.2,bottleneck z))

def prepareAugmentRealizer : Realizer prepareAugment :=
  pair first (pair (composition second arcPairsRealizer) bottleneckRealizer)

def augment (z : Data×List ℕ) : FlowMatrix := updateMatrix (prepareAugment z)

def augmentRealizer : Realizer augment :=
  composition prepareAugmentRealizer updateMatrixRealizer

def advance (z : Data×(ℕ×ℕ)) : FlowMatrix :=
  match ResidualGraphProgram.search z with
  | none => z.1.2
  | Option.some xs => augment (z.1,xs)

def advanceRealizer : Realizer advance :=
  (composition (pair identity ResidualGraphProgram.searchRealizer)
    (optionCases (composition first second)
      (composition (pair (composition first first) second) augmentRealizer))).congr (by
    intro z
    dsimp only [Function.comp_apply,id_eq,advance]
    cases h : ResidualGraphProgram.search z <;> rfl)

theorem advance_code {n : ℕ} (c : PublishedEdmondsKarp.Capacity n)
    (s t : Fin n) (hst : s≠t) (f : PublishedEdmondsKarp.Flow n)
    (hf : PublishedEdmondsKarp.Feasible c s t f) :
    advance ((natCode c,flowCode f),(s.val,t.val))=
      flowCode (EdmondsKarpAlgorithm.advance c s t f) := by
  cases hs : ResidualSearch.search c f s t with
  | none =>
    simp only [advance,ResidualGraphProgram.search_code,hs,Option.map_none,
      EdmondsKarpAlgorithm.advance,ResidualAugmentation.step,Option.getD_none]
  | some xs =>
    have hn := search_residual_nonnegative c f s t xs hs
    let a := bottleneck ((natCode c,flowCode f),xs.map Fin.val)
    have ha : (a:ℤ)=ResidualAugmentation.bottleneck c f xs := bottleneck_code c f xs hn
    have hstep : ResidualAugmentation.step c s t f=
        Option.some (ResidualAugmentation.listUpdate f xs (a:ℤ)) := by
      simp only [ResidualAugmentation.step,hs,Option.map_some,ha]
    have hnew := ResidualAugmentation.step_feasible c s t hst f _ hf hstep
    simp only [advance,ResidualGraphProgram.search_code,hs,Option.map_some]
    change updateMatrix ((natCode c,flowCode f),
      (arcPairs (xs.map Fin.val),a))=_
    rw [arcPairs_map,updateMatrix_code c s t f xs a hnew]
    simp only [EdmondsKarpAlgorithm.advance,hstep,Option.getD_some]

end ContingencyTables.FlowMatrixProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FlowLoopProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial binary execution of the bounded residual-flow loop -/

namespace ContingencyTables.FlowLoopProgram

open MatchingFPRAS.TreeTyped Polynomial ResidualGraphProgram

abbrev State := Context×FlowMatrix

def step (z : ℕ×State) : State :=
  (z.2.1,FlowMatrixProgram.advance ((z.2.1.1,z.2.2),z.2.1.2))

def stepRealizer : Realizer step :=
  pair (composition second first)
    (composition (pair (pair (composition (composition second first) first)
      (composition second second)) (composition (composition second first) second))
      FlowMatrixProgram.advanceRealizer)

def zeroMatrix (C : NatMatrix) : FlowMatrix :=
  C.map (fun row=>row.map (fun _=>(0,0)))

def zeroMatrixRealizer : Realizer zeroMatrix := map (map (constant (0,0)))

lemma zeroMatrix_code {n : ℕ} (c : PublishedEdmondsKarp.Capacity n) :
    zeroMatrix (natCode c)=flowCode (0 : PublishedEdmondsKarp.Flow n) := by
  simp only [zeroMatrix,natCode,flowCode,List.map_ofFn,Function.comp_def]
  rfl

def cubeRealizer : Realizer cube :=
  composition (pair (composition (pair identity identity) multiply) identity) multiply

def iterationCountRealizer : Realizer iterationCount :=
  composition (composition listLength cubeRealizer) successor

def stepsRealizer : Realizer steps := composition iterationCountRealizer range

def prepare (z : Context) : List ℕ×State := (steps z.1,(z,zeroMatrix z.1))

def prepareRealizer : Realizer prepare :=
  pair (composition (f := fun z : Context=>z.1) (g := steps) first stepsRealizer)
    (pair identity (composition (f := fun z : Context=>z.1)
      (g := zeroMatrix) first zeroMatrixRealizer))

def run (z : Context) : FlowMatrix :=
  ((steps z.1).foldl (fun s i=>step (i,s)) (z,zeroMatrix z.1)).2

def runRealizer : Realizer run :=
  composition (composition prepareRealizer (MatchingFPRAS.TreeTyped.fold stepRealizer)) second

lemma step_code {n : ℕ} (c : PublishedEdmondsKarp.Capacity n)
    (s t : Fin n) (hst : s≠t) (k i : ℕ) :
    step (i,((natCode c,(s.val,t.val)),flowCode (EdmondsKarpAlgorithm.run c s t k)))=
      ((natCode c,(s.val,t.val)),flowCode (EdmondsKarpAlgorithm.run c s t (k+1))) := by
  change ((natCode c,(s.val,t.val)),
    FlowMatrixProgram.advance ((natCode c,flowCode (EdmondsKarpAlgorithm.run c s t k)),
      (s.val,t.val)))=_
  apply congrArg (fun F : FlowMatrix=>((natCode c,(s.val,t.val)),F))
  exact FlowMatrixProgram.advance_code c s t hst _ (EdmondsKarpAlgorithm.run_feasible c s t hst k)

lemma fold_code {n : ℕ} (c : PublishedEdmondsKarp.Capacity n)
    (s t : Fin n) (hst : s≠t) (steps : List ℕ) (k : ℕ) :
    steps.foldl (fun s i=>step (i,s))
      ((natCode c,(s.val,t.val)),flowCode (EdmondsKarpAlgorithm.run c s t k))=
      ((natCode c,(s.val,t.val)),flowCode (EdmondsKarpAlgorithm.run c s t (k+steps.length))) := by
  induction steps generalizing k with
  | nil => simp only [List.foldl_nil,List.length_nil,Nat.add_zero]
  | cons i steps ih =>
    rw [List.foldl_cons,step_code c s t hst k i,ih]
    simp only [List.length_cons,Nat.add_comm,Nat.add_left_comm]

theorem run_code {n : ℕ} (c : PublishedEdmondsKarp.Capacity n)
    (s t : Fin n) (hst : s≠t) :
    run (natCode c,(s.val,t.val))=flowCode (EdmondsKarpAlgorithm.maxFlow c s t) := by
  unfold run
  rw [zeroMatrix_code]
  change (List.foldl _ ((natCode c,(s.val,t.val)),
    flowCode (EdmondsKarpAlgorithm.run c s t 0)) (steps (natCode c))).2=_
  rw [fold_code c s t hst]
  simp only [steps,List.length_range,iterationCount,cube,natCode,List.length_ofFn,
    Nat.zero_add,EdmondsKarpAlgorithm.maxFlow,pow_succ,pow_zero,one_mul]

end ContingencyTables.FlowLoopProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_BoundedTableFeasibility
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executed bounded-table feasibility from the cited flow bound

The test runs the concrete residual algorithm on the literal three-layer
network. It handles zero margins, empty row or column types, and structural
zeros. No bounded-table feasibility oracle is assumed.
-/

namespace ContingencyTables.BoundedTableFeasibility

open LayeredTableNetwork
open scoped BigOperators

variable {m n : ℕ}

theorem computedFlow_feasible (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m → ℕ) (c : Fin n → ℕ) (b : Fin m → Fin n → ℕ) :
    Feasible r c b (computedFlow r c b) :=
  pull_feasible r c b _ (EdmondsKarpAlgorithm.maxFlow_correct hEK
    (networkCapacity r c b) (capacity_loop r c b) _ _ source_ne_sink).1

theorem feasibleTest_correct (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m → ℕ) (c : Fin n → ℕ) (b : Fin m → Fin n → ℕ) :
    feasibleTest r c b=true ↔ ∃ X,HasMargins X r c ∧ ∀ i j,X i j≤b i j := by
  rw [feasibleTest,decide_eq_true_eq]
  constructor
  · rintro ⟨htotal,hvalue⟩
    exact ⟨decode (computedFlow r c b),decode_boundedTable r c b _
      (computedFlow_feasible hEK r c b) hvalue htotal⟩
  · rintro ⟨X,hm,hb⟩
    refine ⟨totals_equal hm,?_⟩
    have hmax := EdmondsKarpAlgorithm.maxFlow_correct hEK
      (networkCapacity r c b) (capacity_loop r c b)
      (vertices m n source) (vertices m n sink) source_ne_sink
    have hle := hmax.2 (push (tableFlow r c X))
      (push_feasible r c b _ (tableFlow_feasible r c b X hm hb))
    rw [push_value,tableFlow_value,←pull_value] at hle
    exact le_antisymm (value_le_total r c b _ (computedFlow_feasible hEK r c b)) hle

end ContingencyTables.BoundedTableFeasibility

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_NetworkCapacityProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructing the bounded-table capacity network in binary -/

namespace ContingencyTables.NetworkCapacityProgram

open MatchingFPRAS.TreeTyped Polynomial NetworkVertexCode ResidualGraphProgram

def kindRealizer : Realizer (fun z : ℕ×ℕ=>kind z.1 z.2) :=
  (choose (composition (pair second (constant 0)) natEqual) (constant 0)
    (choose (composition (pair second (constant 1)) natEqual) (constant 1)
      (choose (composition (pair second (composition (pair (constant 2) first) add)) less)
        (constant 2) (constant 3)))).congr (by
          intro z
          simp only [Function.comp_apply,kind,decide_eq_true_eq])

def rowCountRealizer : Realizer rowCount :=
  composition (composition (composition first first) first) listLength

def columnBaseRealizer : Realizer columnBase :=
  composition (f := fun z : EntryInput=>(2,rowCount z))
    (g := fun a : ℕ×ℕ=>a.1+a.2) (pair (constant 2) rowCountRealizer) add

def kindsRealizer : Realizer kinds :=
  pair (composition (pair rowCountRealizer (composition second first)) kindRealizer)
    (composition (pair rowCountRealizer (composition second second)) kindRealizer)

def patternRealizer (a b : ℕ) : Realizer (pattern a b) :=
  composition kindsRealizer (composition (pair
    (composition (pair first (constant a)) natEqual)
    (composition (pair second (constant b)) natEqual)) boolAnd)

def rowReadRealizer : Realizer rowRead :=
  composition (pair (composition (composition first first) first)
    (composition (pair (composition second second) (constant 2)) subtract)) (getDFast 0)

def columnReadRealizer : Realizer columnRead :=
  composition (pair (composition (composition first first) second)
    (composition (pair (composition second first) columnBaseRealizer) subtract)) (getDFast 0)

def boundReadRealizer : Realizer boundRead :=
  composition (pair (composition first second)
    (pair (composition (pair (composition second first) (constant 2)) subtract)
      (composition (pair (composition second second) columnBaseRealizer) subtract)))
    capacityEntryRealizer

def entryRealizer : Realizer entry :=
  (choose (patternRealizer 0 2) rowReadRealizer
    (choose (patternRealizer 2 3) boundReadRealizer
      (choose (patternRealizer 3 1) columnReadRealizer (constant 0)))).congr (by
        intro z
        have hp (a b : ℕ) : pattern a b z=true ↔
            kind z.1.1.1.length z.2.1=a ∧ kind z.1.1.1.length z.2.2=b := by
          change ((decide (kind z.1.1.1.length z.2.1=a)) &&
            (decide (kind z.1.1.1.length z.2.2=b)))=true ↔ _
          rw [Bool.and_eq_true]
          constructor
          · rintro ⟨ha,hb⟩
            exact ⟨_root_.of_decide_eq_true ha,_root_.of_decide_eq_true hb⟩
          · rintro ⟨ha,hb⟩
            exact ⟨_root_.decide_eq_true ha,_root_.decide_eq_true hb⟩
        simp only [hp,columnBase,rowRead,columnRead,boundRead,entry,rowCount])

def vertexCountRealizer : Realizer vertexCount :=
  composition (f := fun z : Input=>(2,z.1.1.length+z.1.2.length))
    (g := fun a : ℕ×ℕ=>a.1+a.2)
    (pair (constant 2) (composition
      (f := fun z : Input=>(z.1.1.length,z.1.2.length))
      (g := fun a : ℕ×ℕ=>a.1+a.2)
      (pair (composition (composition first first) listLength)
        (composition (composition first second) listLength)) add)) add

def verticesRealizer : Realizer vertices := composition vertexCountRealizer range

def rowRealizer : Realizer row :=
  composition (pair identity (composition first verticesRealizer))
    (mapWith (composition
      (pair (composition first first) (pair (composition first second) second)) entryRealizer))

def matrixRealizer : Realizer matrix :=
  composition (pair identity verticesRealizer) (mapWith rowRealizer)

def solve (z : Input) : FlowMatrix := FlowLoopProgram.run (matrix z,(0,1))

def solveRealizer : Realizer solve :=
  composition (pair matrixRealizer (constant (0,1))) FlowLoopProgram.runRealizer

theorem solve_code {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ) :
    solve (data r c b)=flowCode (EdmondsKarpAlgorithm.maxFlow
      (BoundedTableFeasibility.networkCapacity r c b)
      (BoundedTableFeasibility.vertices m n LayeredTableNetwork.source)
      (BoundedTableFeasibility.vertices m n LayeredTableNetwork.sink)) := by
  have hs : (BoundedTableFeasibility.vertices m n (LayeredTableNetwork.source :
      LayeredTableNetwork.Vertex m n)).val=0 := index_vertices _
  have ht : (BoundedTableFeasibility.vertices m n (LayeredTableNetwork.sink :
      LayeredTableNetwork.Vertex m n)).val=1 := index_vertices _
  unfold solve
  rw [matrix_code]
  simpa only [hs,ht] using FlowLoopProgram.run_code
    (BoundedTableFeasibility.networkCapacity r c b)
    (BoundedTableFeasibility.vertices m n LayeredTableNetwork.source)
    (BoundedTableFeasibility.vertices m n LayeredTableNetwork.sink)
    BoundedTableFeasibility.source_ne_sink

end ContingencyTables.NetworkCapacityProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_NetworkFeasibilityProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual polynomial binary bounded-table feasibility test -/

namespace ContingencyTables.NetworkFeasibilityProgram

open MatchingFPRAS.TreeTyped NetworkVertexCode NetworkCapacityProgram ResidualGraphProgram
open scoped BigOperators

def sourcePair (z : Input) : SignedPairProgram.Signed :=
  SignedPairProgram.sum ((solve z).getD 0 [])

def sourcePairRealizer : Realizer sourcePair :=
  composition (composition (pair solveRealizer (constant 0)) (getDFast []))
    SignedPairProgram.sumRealizer

def inputValues (z : Input) : (ℕ×ℕ)×SignedPairProgram.Signed :=
  ((z.1.1.sum,z.1.2.sum),sourcePair z)

def inputValuesRealizer : Realizer inputValues :=
  pair (pair (composition (composition first first) listSum)
    (composition (composition first second) listSum)) sourcePairRealizer

def testValues (z : (ℕ×ℕ)×SignedPairProgram.Signed) : Bool :=
  decide (z.1.1=z.1.2) && decide (z.2.1=z.1.1+z.2.2)

def testValuesRealizer : Realizer testValues :=
  composition (pair (composition first natEqual)
    (composition (pair (composition second first)
      (composition (pair (composition first first) (composition second second)) add))
      natEqual)) boolAnd

def test (z : Input) : Bool := testValues (inputValues z)
def testRealizer : Realizer test := composition inputValuesRealizer testValuesRealizer

lemma flowCode_row_value {n : ℕ} (f : PublishedEdmondsKarp.Flow n) (s : Fin n) :
    SignedPairProgram.value (SignedPairProgram.sum ((flowCode f).getD s.val []))=
      PublishedEdmondsKarp.value s f := by
  have hr : (flowCode f).getD s.val []=
      List.ofFn (fun v=>ForestAffineProgram.signedParts (f s v)) := by
    simp only [flowCode,List.getD_eq_getElem?_getD,List.getElem?_ofFn,s.isLt,
      dite_true,Option.getD_some,Fin.eta]
  rw [hr,SignedPairProgram.value_sum]
  simp only [List.map_ofFn,Function.comp_def,SignedPairProgram.value,
    ForestAffineProgram.signedParts_sub,List.sum_ofFn,PublishedEdmondsKarp.value]

lemma sourcePair_value {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ) :
    SignedPairProgram.value (sourcePair (data r c b))=
      LayeredTableNetwork.value (BoundedTableFeasibility.computedFlow r c b) := by
  unfold sourcePair
  rw [solve_code]
  have hs : (BoundedTableFeasibility.vertices m n (LayeredTableNetwork.source :
      LayeredTableNetwork.Vertex m n)).val=0 := index_vertices _
  rw [←hs,flowCode_row_value]
  exact (BoundedTableFeasibility.pull_value _).symm

lemma test_eq_feasible {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ) :
    test (data r c b)=BoundedTableFeasibility.feasibleTest r c b := by
  apply Bool.eq_iff_iff.mpr
  simp only [test,testValues,inputValues,Bool.and_eq_true,decide_eq_true_eq,
    BoundedTableFeasibility.feasibleTest,data,List.sum_ofFn]
  have hv := sourcePair_value r c b
  have he : (sourcePair (data r c b)).1=
      (∑ i,r i)+(sourcePair (data r c b)).2 ↔
      SignedPairProgram.value (sourcePair (data r c b))=∑ i,(r i:ℤ) := by
    unfold SignedPairProgram.value
    rw [←Nat.cast_sum]
    omega
  exact and_congr_right (fun _=>he.trans (by rw [hv]))

theorem test_correct {m n : ℕ} (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ) :
    test (data r c b)=true ↔ ∃ X,HasMargins X r c ∧ ∀ i j,X i j≤b i j := by
  rw [test_eq_feasible]
  exact BoundedTableFeasibility.feasibleTest_correct hEK r c b

end ContingencyTables.NetworkFeasibilityProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_BinarySearchProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial binary program for monotone endpoint search

The supplied test is a realized binary predicate. The loop
performs one midpoint test per bit of the upper bound and keeps the
unchanged test data throughout.
-/

namespace ContingencyTables.BinarySearchProgram

open MatchingFPRAS.TreeTyped Polynomial BoundedBinarySearch

def midpointRealizer : Realizer midpoint :=
  composition (pair first (composition (pair
    (composition (composition (pair second first) subtract) successor) (constant 2)) quotient)) add

variable {A : Type} [Codec A]
variable (test : A×ℕ→Bool) (T : Realizer test)

abbrev State (A : Type) := A×Window

def advance (z : ℕ×State A) : State A :=
  (z.2.1,step (fun t=>test (z.2.1,t)) z.2.2)

def advanceRealizer : Realizer (advance test) := by
  let M : Realizer (fun z : ℕ×State A=>midpoint z.2.2) :=
    composition (composition second second) midpointRealizer
  let P : Realizer (fun z : ℕ×State A=>test (z.2.1,midpoint z.2.2)) :=
    composition (f := fun z : ℕ×State A=>(z.2.1,midpoint z.2.2)) (g := test)
      (pair (composition second first) M) T
  let yes : Realizer (fun z : ℕ×State A=>(midpoint z.2.2,z.2.2.2)) :=
    pair M (composition (composition second second) second)
  let no : Realizer (fun z : ℕ×State A=>(z.2.2.1,midpoint z.2.2-1)) :=
    pair (composition (composition second second) first) (composition M predecessor)
  exact pair (composition second first) (choose P yes no)

def steps (z : A×ℕ) : List ℕ := List.range z.2.size

def stepsRealizer : Realizer (steps (A := A)) :=
  composition (composition second bitSize) range

def prepare (z : A×ℕ) : List ℕ×State A := (steps z,(z.1,(0,z.2)))

def prepareRealizer : Realizer (prepare (A := A)) :=
  pair stepsRealizer (pair first (pair (constant 0) second))

def execute (z : A×ℕ) : State A :=
  (steps z).foldl (fun s i=>advance test (i,s)) (z.1,(0,z.2))

def executeRealizer : Realizer (execute test) :=
  composition (f := prepare (A := A))
    (g := fun z : List ℕ×State A=>z.1.foldl (fun s i=>advance test (i,s)) z.2)
    prepareRealizer (fold (advanceRealizer test T))

def search (z : A×ℕ) : ℕ := (execute test z).2.1

def searchRealizer : Realizer (search test) :=
  composition (f := execute test) (g := fun s : State A=>s.2.1)
    (executeRealizer test T) (composition second first)

omit [Codec A] in
lemma fold_code (xs : List ℕ) (a : A) (p : Window) :
    xs.foldl (fun s i=>advance test (i,s)) (a,p)=
      (a,run (fun t=>test (a,t)) xs.length p) := by
  induction xs generalizing p with
  | nil => rfl
  | cons i xs ih =>
    change xs.foldl (fun s i=>advance test (i,s))
      (a,step (fun t=>test (a,t)) p)=(a,run (fun t=>test (a,t)) (xs.length+1) p)
    exact ih _

omit [Codec A] in
theorem search_eq (a : A) (K U : ℕ)
    (ht : ∀ t,test (a,t)=true ↔ t≤K) (hK : K≤U) : search test (a,U)=K := by
  unfold search execute
  rw [fold_code]
  simp only [steps,List.length_range]
  exact congrArg Prod.fst (run_eq_cutoff _ K U U.size ht hK (Nat.lt_size_self U))

end ContingencyTables.BinarySearchProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_BoundedComplementProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing complementary bounded-table margins in binary -/

namespace ContingencyTables.BoundedComplementProgram

open MatchingFPRAS.TreeTyped Polynomial NetworkVertexCode

def rowValueRealizer : Realizer rowValue :=
  composition (pair
    (composition (composition (pair (composition first second) second) (getDFast [])) listSum)
    (composition (pair (composition (composition first first) first) second) (getDFast 0))) subtract

def columnValuesRealizer : Realizer columnValues :=
  composition (pair second (composition first second))
    (mapWith (composition (pair second first) (getDFast 0)))

def columnValueRealizer : Realizer columnValue :=
  composition (pair (composition columnValuesRealizer listSum)
    (composition (pair (composition (composition first first) second) second) (getDFast 0))) subtract

def rowIndicesRealizer : Realizer rowIndices :=
  composition (composition (composition first first) listLength) range

def columnIndicesRealizer : Realizer columnIndices :=
  composition (composition (composition first second) listLength) range

def complementRealizer : Realizer complement :=
  pair (pair
    (composition (pair identity rowIndicesRealizer) (mapWith rowValueRealizer))
    (composition (pair identity columnIndicesRealizer) (mapWith columnValueRealizer))) second

end ContingencyTables.BoundedComplementProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_BoundedPowerProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reusing a unary allowance across a binary transition table -/

namespace ContingencyTables.BoundedPowerPrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped

def powerInputRealizer : Realizer powerInput :=
  pair (constant 2) (composition (pair (composition first listLength) second) subtract)

def powerRealizer : Realizer power :=
  composition powerInputRealizer BinaryPowerPrograms.powerRealizer

end ContingencyTables.BoundedPowerPrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_ListSubtractProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary subtraction at one list coordinate

The scan depends on the stored list length. The subtracted amount remains
binary throughout and never controls a loop.
-/

namespace ContingencyTables.ListSubtractProgram

open MatchingFPRAS.TreeTyped Polynomial

def entryRealizer : Realizer entry := by
  let read : Realizer (fun z : Cell=>z.1.1.1.getD z.2 0) :=
    composition (pair (composition (composition first first) first) second) (getDFast 0)
  let amount : Realizer (fun z : Cell=>if z.2=z.1.1.2 then z.1.2 else 0) :=
    (choose (composition (pair second (composition (composition first first) second)) natEqual)
      (composition first second) (constant 0)).congr (by
        intro z
        simp only [Function.comp_apply,decide_eq_true_eq])
  exact composition (pair read amount) subtract

def indicesRealizer : Realizer indices :=
  composition (composition (composition first first) listLength) range

def subtractAtRealizer : Realizer subtractAt :=
  composition (pair identity indicesRealizer) (mapWith entryRealizer)

end ContingencyTables.ListSubtractProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_LowerCapacityProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executable subtraction of a lower bound from a capacity matrix -/

namespace ContingencyTables.LowerCapacityProgram

open MatchingFPRAS.TreeTyped Polynomial ResidualGraphProgram

def readRowRealizer : Realizer readRow :=
  composition (pair (composition (composition first first) first) second) (getDFast [])

def selectedRealizer : Realizer selected :=
  composition (pair second (composition (composition (composition first first) second) first)) natEqual

def shiftedInputRealizer : Realizer shiftedInput :=
  pair (pair readRowRealizer
    (composition (composition (composition first first) second) second))
    (composition first second)

def rowRealizer : Realizer row :=
  (choose selectedRealizer
    (composition (f := shiftedInput) (g := ListSubtractProgram.subtractAt)
      shiftedInputRealizer ListSubtractProgram.subtractAtRealizer) readRowRealizer).congr (by
        intro z
        simp only [Function.comp_apply,row,selected,decide_eq_true_eq])

def indicesRealizer : Realizer indices :=
  composition (composition (composition first first) listLength) range

def matrixRealizer : Realizer matrix :=
  composition (pair identity indicesRealizer) (mapWith rowRealizer)

end ContingencyTables.LowerCapacityProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_CellLowerTestProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The executed feasibility test with one extra lower cell bound -/

namespace ContingencyTables.CellLowerTestProgram

open MatchingFPRAS.TreeTyped Polynomial

def rowInputRealizer : Realizer (fun z : Input=>((z.1.1.1.1,z.1.2.1),z.2)) :=
  pair (pair (composition (composition (composition first first) first) first)
    (composition (composition first second) first)) second

def columnInputRealizer : Realizer (fun z : Input=>((z.1.1.1.2,z.1.2.2),z.2)) :=
  pair (pair (composition (composition (composition first first) first) second)
    (composition (composition first second) second)) second

def capacityInputRealizer : Realizer (fun z : Input=>((z.1.1.2,z.1.2),z.2)) :=
  pair (pair (composition (composition first first) second) (composition first second)) second

def shiftedRealizer : Realizer shifted :=
  pair (pair
    (composition (f := fun z : Input=>((z.1.1.1.1,z.1.2.1),z.2))
      (g := ListSubtractProgram.subtractAt) rowInputRealizer ListSubtractProgram.subtractAtRealizer)
    (composition (f := fun z : Input=>((z.1.1.1.2,z.1.2.2),z.2))
      (g := ListSubtractProgram.subtractAt) columnInputRealizer ListSubtractProgram.subtractAtRealizer))
    (composition (f := fun z : Input=>((z.1.1.2,z.1.2),z.2))
      (g := LowerCapacityProgram.matrix) capacityInputRealizer LowerCapacityProgram.matrixRealizer)

def guardsRealizer : Realizer guards := by
  let rowBound : Realizer (fun z : Input=>z.1.1.1.1.getD z.1.2.1 0) :=
    composition (composition rowInputRealizer first) (getDFast 0)
  let columnBound : Realizer (fun z : Input=>z.1.1.1.2.getD z.1.2.2 0) :=
    composition (composition columnInputRealizer first) (getDFast 0)
  let capacityBound : Realizer (fun z : Input=>ResidualGraphProgram.capacityEntry (z.1.1.2,z.1.2)) :=
    composition (composition capacityInputRealizer first) ResidualGraphProgram.capacityEntryRealizer
  exact composition (pair (composition (pair second rowBound) leNat)
    (composition (pair (composition (pair second columnBound) leNat)
      (composition (pair second capacityBound) leNat)) boolAnd)) boolAnd

def test (z : Input) : Bool := guards z && NetworkFeasibilityProgram.test (shifted z)

def testRealizer : Realizer test :=
  composition (pair guardsRealizer
    (composition (f := shifted) (g := NetworkFeasibilityProgram.test)
      shiftedRealizer NetworkFeasibilityProgram.testRealizer)) boolAnd

theorem test_correct {m n : ℕ} (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (i : Fin m) (j : Fin n) (t : ℕ) :
    test ((NetworkVertexCode.data r c b,(i.val,j.val)),t)=true ↔
      ∃ X,HasMargins X r c ∧ (∀ u v,X u v≤b u v) ∧ t≤X i j := by
  rw [test,Bool.and_eq_true,guards_code,shifted_code,NetworkFeasibilityProgram.test_correct hEK]
  simpa only [and_assoc] using (BoundedCellShift.feasible_lower_iff r c b i j t).symm

end ContingencyTables.CellLowerTestProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_CellMaximumProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing an attained cell maximum by binary feasibility search

A finite maximum is used only to prove the result of the executed binary
search. The program never enumerates feasible tables.
-/

namespace ContingencyTables.CellMaximumProgram

open MatchingFPRAS.TreeTyped CellLowerTestProgram
open scoped Classical

def boundRealizer : Realizer bound :=
  composition (pair (composition first second) second) ResidualGraphProgram.capacityEntryRealizer

def maximum (z : Context) : ℕ := BinarySearchProgram.search test (z,bound z)

def maximumRealizer : Realizer maximum :=
  composition (f := fun z : Context=>(z,bound z))
    (g := BinarySearchProgram.search test)
    (pair identity boundRealizer) (BinarySearchProgram.searchRealizer test testRealizer)

/-- For every feasible instance the computed value is attained, and it
bounds the same coordinate of every other feasible table. -/
theorem maximum_correct {m n : ℕ} (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (i : Fin m) (j : Fin n)
    (hne : ∃ X,HasMargins X r c ∧ ∀ u v,X u v≤b u v) :
    ∃ X,HasMargins X r c ∧ (∀ u v,X u v≤b u v) ∧
      X i j=maximum (NetworkVertexCode.data r c b,(i.val,j.val)) ∧
      ∀ Y,HasMargins Y r c → (∀ u v,Y u v≤b u v) → Y i j≤X i j := by
  let S : Finset (BoundedTable r c b) := Finset.univ
  have hS : S.Nonempty := by
    obtain ⟨X,hm,hb⟩ := hne
    exact ⟨⟨⟨X,hm⟩,hb⟩,Finset.mem_univ _⟩
  obtain ⟨M,hM,hmax⟩ := Finset.exists_max_image S
    (fun X : BoundedTable r c b=>X.val.val i j) hS
  have ht (t : ℕ) :
      test ((NetworkVertexCode.data r c b,(i.val,j.val)),t)=true ↔ t≤M.val.val i j := by
    rw [CellLowerTestProgram.test_correct hEK]
    constructor
    · rintro ⟨X,hm,hb,hx⟩
      exact hx.trans (hmax ⟨⟨X,hm⟩,hb⟩ (Finset.mem_univ _))
    · intro hx
      exact ⟨M.val.val,M.val.property,M.property,hx⟩
  have he : maximum (NetworkVertexCode.data r c b,(i.val,j.val))=M.val.val i j := by
    unfold maximum
    rw [bound_code]
    exact BinarySearchProgram.search_eq test _ _ _ ht (M.property i j)
  exact ⟨M.val.val,M.val.property,M.property,he.symm,
    fun Y hm hb=>hmax ⟨⟨Y,hm⟩,hb⟩ (Finset.mem_univ _)⟩

end ContingencyTables.CellMaximumProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_CellMinimumProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing an attained minimum through the complementary table

Complementation changes the lower endpoint query to the
upper endpoint query and preserves every cell capacity.
-/

namespace ContingencyTables.CellMinimumProgram

open MatchingFPRAS.TreeTyped CellLowerTestProgram

def complementedRealizer : Realizer complemented :=
  pair (composition (f := fun z : Context=>z.1)
    (g := BoundedComplementProgram.complement) first BoundedComplementProgram.complementRealizer) second

def minimum (z : Context) : ℕ :=
  CellMaximumProgram.bound z-CellMaximumProgram.maximum (complemented z)

def minimumRealizer : Realizer minimum :=
  composition (f := fun z : Context=>
      (CellMaximumProgram.bound z,CellMaximumProgram.maximum (complemented z)))
    (g := fun z : ℕ×ℕ=>z.1-z.2)
    (pair CellMaximumProgram.boundRealizer
      (composition (f := complemented) (g := CellMaximumProgram.maximum)
        complementedRealizer CellMaximumProgram.maximumRealizer)) subtract

/-- The returned lower endpoint is attained and is no larger than the
selected coordinate of any feasible bounded table. -/
theorem minimum_correct {m n : ℕ} (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (i : Fin m) (j : Fin n)
    (hne : ∃ X,HasMargins X r c ∧ ∀ u v,X u v≤b u v) :
    ∃ X,HasMargins X r c ∧ (∀ u v,X u v≤b u v) ∧
      X i j=minimum (NetworkVertexCode.data r c b,(i.val,j.val)) ∧
      ∀ Y,HasMargins Y r c → (∀ u v,Y u v≤b u v) → X i j≤Y i j := by
  obtain ⟨X₀,hx,hxb⟩ := hne
  have hn : ∃ Y,HasMargins Y (BoundedTableComplement.rows b r)
      (BoundedTableComplement.columns b c) ∧ ∀ u v,Y u v≤b u v :=
    ⟨BoundedTableComplement.complement b X₀,
      BoundedTableComplement.complement_margins b X₀ r c hx hxb,
      BoundedTableComplement.complement_bounds b X₀⟩
  obtain ⟨Y,hy,hyb,hvalue,hmax⟩ := CellMaximumProgram.maximum_correct hEK
    (BoundedTableComplement.rows b r) (BoundedTableComplement.columns b c) b i j hn
  refine ⟨BoundedTableComplement.complement b Y,
    BoundedTableComplement.complement_reverse_margins b X₀ Y r c hx hxb hy hyb,
    BoundedTableComplement.complement_bounds b Y,?_,?_⟩
  · unfold minimum
    rw [CellMaximumProgram.bound_code,complemented_code,←hvalue]
    rfl
  · intro Z hz hzb
    have hb := hmax (BoundedTableComplement.complement b Z)
      (BoundedTableComplement.complement_margins b Z r c hz hzb)
      (BoundedTableComplement.complement_bounds b Z)
    change b i j-Y i j≤Z i j
    change b i j-Z i j≤Y i j at hb
    omega

end ContingencyTables.CellMinimumProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_BoxCompletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Enumerating tables through their free entries -/

namespace ContingencyTables.BoxCompletion
open DenseAffine DensePrograms
open scoped BigOperators Classical
noncomputable section

def decode {m n : ℕ} (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (htotal : ∑ i,R i=∑ j,P j) (N : ℕ) (z : Box m n N) : Option (Table R P) :=
  if hz : ∀ i j,0 ≤ integerTable R P (freeValues z) i j then
    some ⟨naturalTable R P (freeValues z),naturalTable_rows R P _ hz,
      naturalTable_columns R P _ hz htotal⟩
  else none

def encode {m n N : ℕ} (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (hN : (∑ i,R i)≤N) (X : Table R P) : Box m n N := fun k =>
  ⟨X.val (some (finProdFinEquiv.symm k).1) (some (finProdFinEquiv.symm k).2),
    Nat.lt_succ_of_le ((entry_le_total X.property _ _).trans hN)⟩

end
end ContingencyTables.BoxCompletion

end OAI
end


