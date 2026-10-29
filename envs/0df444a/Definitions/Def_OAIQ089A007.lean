-- Prove2me | Definitions.Def_OAIQ089A007
-- name    : OAIQ089A007
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T03:00:50.203657+00:00
-- url     : https://prove2.me/theorems/010a98e5-b355-4f65-8c55-0b1e8da5344b
-- title:
--   Definitions bundle OAIQ089A007 of the split of OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ContingencyTables.boundedSampling`, `OAI.ContingencyTables.counting` and `OAI.ContingencyTables.exactSampling`, carved from OpenAI's openai/math development (OpenAI, *Sampling and counting contingency tables with arbitrary margins (result family 115)*, OpenAI Math Release, September 24, 2026, result family 115, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 710 declarations of OpenAI's Lean: 588 definitions, 2 inductive types or structures, 13 instances and 107 theorems. The definitions and types are `OAI.ContingencyTables.CountingAmplifiedProgram.Request`, `OAI.ContingencyTables.CountingAmplifiedProgram.repeats`, `OAI.ContingencyTables.CountingAmplifiedProgram.repeatsRealizer`, `OAI.ContingencyTables.CountingBranchProgram.Request`, `OAI.ContingencyTables.CountingBranchProgram.feasible`, `OAI.ContingencyTables.CountingBranchProgram.feasibleRealizer`, `OAI.ContingencyTables.CountingBranchProgram.request`, `OAI.ContingencyTables.CountingBranchProgram.requestRealizer`, `OAI.ContingencyTables.CountingDirectProgram.Request`, `OAI.ContingencyTables.CountingDirectProgram.request`, `OAI.ContingencyTables.CountingInputParser.capacityFrameRealizer`, `OAI.ContingencyTables.CountingInputParser.cellsRealizer`, `OAI.ContingencyTables.CountingInputParser.decodeRealizer`, `OAI.ContingencyTables.CountingInputParser.fractionPairRealizer`, `OAI.ContingencyTables.CountingInputParser.offsetRealizer`, `OAI.ContingencyTables.CountingInputParser.parametersRealizer`, `OAI.ContingencyTables.CountingInputParser.publicRealizer`, `OAI.ContingencyTables.CountingInputParser.restRealizer`, `OAI.ContingencyTables.CountingPositiveProgram.Request`, `OAI.ContingencyTables.DensePrograms.acceptCompletionRealizer`, `OAI.ContingencyTables.DensePrograms.advance`, `OAI.ContingencyTables.DensePrograms.advanceRealizer`, `OAI.ContingencyTables.DensePrograms.axisNumberStepRealizer`, `OAI.ContingencyTables.DensePrograms.booleanWordsRealizer`, `OAI.ContingencyTables.DensePrograms.candidateCountInputRealizer`, `OAI.ContingencyTables.DensePrograms.candidateCountMeasure`, `OAI.ContingencyTables.DensePrograms.canonicalCounts`, `OAI.ContingencyTables.DensePrograms.canonicalDenseDraw`, `OAI.ContingencyTables.DensePrograms.canonicalDenseDrawRealizer`, `OAI.ContingencyTables.DensePrograms.canonicalFallback`, `OAI.ContingencyTables.DensePrograms.chunkIndicesRealizer`, `OAI.ContingencyTables.DensePrograms.clippedGridPowerInputRealizer`, `OAI.ContingencyTables.DensePrograms.clippedGridPowerRealizer`, `OAI.ContingencyTables.DensePrograms.completedEntryRealizer`, `OAI.ContingencyTables.DensePrograms.completedMatrixRealizer`, `OAI.ContingencyTables.DensePrograms.completedRowEntryRealizer`, `OAI.ContingencyTables.DensePrograms.completedRowRealizer`, `OAI.ContingencyTables.DensePrograms.completionCandidateRealizer`, `OAI.ContingencyTables.DensePrograms.completionCandidatesRealizer`, `OAI.ContingencyTables.DensePrograms.completionColumnsRealizer` and 550 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `ContingencyTables_Counting_CountingAmplifiedProgram`, `ContingencyTables_Counting_CountingBranchProgram`, `ContingencyTables_Counting_CountingDirectProgram`, `ContingencyTables_Counting_CountingDirectSemantics`, `ContingencyTables_Counting_CountingInputParser`, `ContingencyTables_Counting_CountingPositiveProgram`, `ContingencyTables_Dense_DenseBooleanWalkProgram`, `ContingencyTables_Dense_DenseCandidateCounts`, `ContingencyTables_Dense_DenseCanonicalProgram`, `ContingencyTables_Dense_DenseCanonicalSemantics`, `ContingencyTables_Dense_DenseCompletedMatrixProgram`, `ContingencyTables_Dense_DenseCompletionTest`, `ContingencyTables_Dense_DenseCountProgram`, `ContingencyTables_Dense_DenseDrawProgram`, `ContingencyTables_Dense_DenseDrawSemantics`, `ContingencyTables_Dense_DenseDrawTabulation`, `ContingencyTables_Dense_DenseEnumeratedMatrix`, `ContingencyTables_Dense_DenseExponentListProgram`, `ContingencyTables_Dense_DenseExponentProgram`, `ContingencyTables_Dense_DenseFlatExponentProgram`, `ContingencyTables_Dense_DenseGridExponentProgram`, `ContingencyTables_Dense_DenseMatrixProgram`, `ContingencyTables_Dense_DenseMatrixTable`, `ContingencyTables_Dense_DenseMatrixWalk`, `ContingencyTables_Dense_DenseMetropolisProgram`, `ContingencyTables_Dense_DenseNormalizeProgram`, `ContingencyTables_Dense_DenseNormalizeSemantics`, `ContingencyTables_Dense_DenseOffsetProgram`, `ContingencyTables_Dense_DenseReservedWord`, `ContingencyTables_Dense_DenseScaleCellProgram`, `ContingencyTables_Dense_DenseScaleMatrixProgram`, `ContingencyTables_Dense_DenseTableCoordinates`, `ContingencyTables_Dense_DenseTrialCountProgram`, `ContingencyTables_Dense_DenseTrialProgram`, `ContingencyTables_Dense_DenseTrialSemantics`, `ContingencyTables_Dense_DenseWalkProgram`, `ContingencyTables_Dense_DenseWalkTabulation`, `ContingencyTables_Dense_DenseWordProgram`, `ContingencyTables_Dense_GridIndexProgram`, `ContingencyTables_Machines_CachedProfileDecision`, `ContingencyTables_Machines_CachedTerminalSemantics`, `ContingencyTables_Machines_CompletionEnumerationProgram`, `ContingencyTables_Machines_DependentWordProgram`, `ContingencyTables_Machines_FiniteWordExecution`, `ContingencyTables_Machines_FiniteWordMachine`, `ContingencyTables_Machines_FirstSuccessProgram`, `ContingencyTables_Machines_FractionOutputProgram`, `ContingencyTables_Machines_FractionRepetitionProgram`, `ContingencyTables_Machines_LiteralProgram`, `ContingencyTables_Machines_MatrixCodeEquality`, `ContingencyTables_Machines_NatListEquality`, `ContingencyTables_Machines_OnlineIntegerRetry`, `ContingencyTables_Machines_OnlinePartialCall`, `ContingencyTables_Machines_PreparedDenseCount`, `ContingencyTables_Machines_PreparedOffsetCount`, `ContingencyTables_Machines_RepeatedFractionProgram`, `ContingencyTables_Machines_ResidualDenseProgram`, `ContingencyTables_Machines_ResidualWeightProgram`, `ContingencyTables_Machines_RetryNumeratorProgram`, `ContingencyTables_Machines_TableIndexProgram`, `ContingencyTables_Machines_TranslationDecisionProgram`, `ContingencyTables_Machines_VectorRetryProgram`, `ContingencyTables_Rooted_LargeMarginReference`, `ContingencyTables_Rooted_LargeMarginSemantics`, `ContingencyTables_Sampling_AllSamplingAccuracy`, `ContingencyTables_Sampling_AllSamplingProgram`, `ContingencyTables_Sampling_AllSamplingSemantics`, `ContingencyTables_Sampling_AllSmallInitialization`, `ContingencyTables_Sampling_AllSmallRational`, `ContingencyTables_Sampling_ExactIntegerOnline`, `ContingencyTables_Sampling_ExactIntegerProgram`, `ContingencyTables_Sampling_ExactIntegerRetry`, `ContingencyTables_Sampling_ExactMatrixTrial`, `ContingencyTables_Sampling_ExactPublicLaw`, `ContingencyTables_Sampling_FirstPaperBinaryParameters`, `ContingencyTables_Sampling_FirstPaperCodeNeighbors`, `ContingencyTables_Sampling_FirstPaperCodeProposal`, `ContingencyTables_Sampling_FirstPaperComputedCatalog`, `ContingencyTables_Sampling_FirstPaperContextTransport`, `ContingencyTables_Sampling_FirstPaperCorrectionBudget`, `ContingencyTables_Sampling_FirstPaperFeasibility`, `ContingencyTables_Sampling_FirstPaperFiniteSampler`, `ContingencyTables_Sampling_FirstPaperIdealRejection`, `ContingencyTables_Sampling_FirstPaperInitialization`, `ContingencyTables_Sampling_FirstPaperJointLaw`, `ContingencyTables_Sampling_FirstPaperPhysicalVariance`, `ContingencyTables_Sampling_FirstPaperPreparedProposal`, `ContingencyTables_Sampling_FirstPaperProposal`, `ContingencyTables_Sampling_FirstPaperSmallChain`, `ContingencyTables_Sampling_FirstPaperSuccessEvent`, `ContingencyTables_Sampling_GreedyPublicProgram`, `ContingencyTables_Sampling_OriginalBalancedJoint`, `ContingencyTables_Sampling_OriginalProfileEntries`, `ContingencyTables_Sampling_OriginalProfileProgram`, `ContingencyTables_Sampling_OriginalResidualVector`, `ContingencyTables_Sampling_OriginalTableCardinality`, `ContingencyTables_Sampling_OriginalTableCheck`, `ContingencyTables_Sampling_OriginalTableEnumeration`, `ContingencyTables_Sampling_OriginalTableIndex`, `ContingencyTables_Sampling_OuterTableProgram`, `ContingencyTables_Sampling_OuterTrialProgram`, `ContingencyTables_Sampling_PhysicalCompletionFibres`, `ContingencyTables_Sampling_PhysicalGraphDegree`, `ContingencyTables_Sampling_PhysicalGraphVertices`, `ContingencyTables_Sampling_PhysicalPaperCapacity`, `ContingencyTables_Sampling_PhysicalPrefixEnergies`, `ContingencyTables_Sampling_PhysicalRepairGraph`, `ContingencyTables_Sampling_PhysicalResidualMargins`, `ContingencyTables_Sampling_PhysicalSmallGraph`, `ContingencyTables_Sampling_ProfileBoxEnumeration`, `ContingencyTables_Sampling_ProfileBoxIndex`, `ContingencyTables_Sampling_ProfileCodeEquality`, `ContingencyTables_Sampling_ProfileExchangeCandidates`, `ContingencyTables_Sampling_ProfileInverseRepairProgram`, `ContingencyTables_Sampling_ProfilePublicProgram`, `ContingencyTables_Sampling_ProfileRepairProgram`, `ContingencyTables_Sampling_ProfileRetryProgram`, `ContingencyTables_Sampling_ProfileSamplingProgram`, `ContingencyTables_Sampling_ProfileScheduleProgram`, `ContingencyTables_Sampling_ProfileTransitionCountSemantics`, `ContingencyTables_Sampling_ProfileTransitionProgram`, `ContingencyTables_Sampling_ProfileTrialProgram`, `ContingencyTables_Sampling_ProfileWordProgram`, `ContingencyTables_Sampling_Repair`, `ContingencyTables_Sampling_RepairFibres`, `ContingencyTables_Sampling_RepairPrefixes`, `ContingencyTables_Sampling_SmallBalancedEncoding`, `ContingencyTables_Sampling_SmallBoundsProgram`, `ContingencyTables_Sampling_SmallCellCatalogProgram`, `ContingencyTables_Sampling_SmallContextCount`, `ContingencyTables_Sampling_SmallContextEnumeration`, `ContingencyTables_Sampling_SmallContextFibres`, `ContingencyTables_Sampling_SmallDefectCodeTest`, `ContingencyTables_Sampling_SmallExchangeListProgram`, `ContingencyTables_Sampling_SmallInverseRepairList`, `ContingencyTables_Sampling_SmallMarginTestProgram`, `ContingencyTables_Sampling_SmallProfileCode`, `ContingencyTables_Sampling_SmallProfileEncoding`, `ContingencyTables_Sampling_SmallProfileFlatCode`, `ContingencyTables_Sampling_SmallProfileRepair`, `ContingencyTables_Sampling_SmallProfileValidator`, `ContingencyTables_Sampling_SmallRepairCapacity`, `ContingencyTables_Sampling_SmallRepairCodeProgram`, `ContingencyTables_Sampling_SmallRepairGeometryProgram`, `ContingencyTables_Sampling_SmallRepairListProgram`, `ContingencyTables_Sampling_SmallRepairWords`, `ContingencyTables_Sampling_UnitFiniteLaw`, `ContingencyTables_Sampling_UnitIntegerLaw`, `ContingencyTables_Sampling_UnitProfileProgram`, `ContingencyTables_Sampling_UnitProfileSemantics`, `ContingencyTables_Sampling_UnitTrialProgram`, `ContingencyTables_Transport_AuxiliaryRepairMass`, `ContingencyTables_Transport_AxisProposalTest`, `ContingencyTables_Transport_BalancedCompletionMass`, `ContingencyTables_Transport_BalancedJointConstruction`, `ContingencyTables_Transport_BooleanEnumeration`, `ContingencyTables_Transport_BoundedProfileSemantics`, `ContingencyTables_Transport_BoundedProfileWalk`, `ContingencyTables_Transport_CanonicalIntegerLaw`, `ContingencyTables_Transport_ChoiceContextEnumeration`, `ContingencyTables_Transport_CompletionFibreTransport`, `ContingencyTables_Transport_DirectedBFSBounds`, `ContingencyTables_Transport_EqualityReindex`, `ContingencyTables_Transport_EqualitySoftening`, `ContingencyTables_Transport_ExcessContextDefects`, `ContingencyTables_Transport_ExcessContextProfiles`, `ContingencyTables_Transport_FiniteGridWords`, `ContingencyTables_Transport_IntegerLeafEnergy`, `ContingencyTables_Transport_IntegerMarginal`, `ContingencyTables_Transport_IntegerMatrixPoint`, `ContingencyTables_Transport_ListedBooleanDraw`, `ContingencyTables_Transport_ListedBooleanStep`, `ContingencyTables_Transport_ListedCompletion`, `ContingencyTables_Transport_ListedDenseDraw`, `ContingencyTables_Transport_ListedIntegerLaw`, `ContingencyTables_Transport_ListedKernelAccuracy`, `ContingencyTables_Transport_ListedReservedDraw`, `ContingencyTables_Transport_MeasuredMap`, `ContingencyTables_Transport_ProductIntegerSignature`, `ContingencyTables_Transport_RawSmallChoiceProperties`, `ContingencyTables_Transport_ReferenceCompletionBlock`, `ContingencyTables_Transport_ReferenceCompletionBounds`, `ContingencyTables_Transport_ReferenceDrawBounds`, `ContingencyTables_Transport_ReferenceFiniteDraw`, `ContingencyTables_Transport_SuccessfulJointBijection`, `ContingencyTables_Transport_UnaryMarkers`, `MatchingCount_Algorithm_OnlineScheduleNat`, `MatchingCount_Complexity_TreeChoiceCosts`, `MatchingCount_Machines_OnlineFold`, `MatchingCount_Machines_OnlineFrame`, `MatchingCount_Machines_OnlinePhysicalProgram`, `MatchingCount_Machines_OnlineTree`, `MatchingCount_Machines_TreeCanonical`, `MatchingCount_Machines_TreeListMore`, `MatchingCount_Tapes_Codec`, `MatchingCount_Tapes_OnlineWord`, `MatchingCount_Tapes_Packed`, `MatchingCount_Tapes_PackedExecution`, `MatchingCount_Tapes_PackedInverse`, `MatchingCount_Tapes_Parse`.
--
--   **Imports.** It imports the published bundle `Def_ContingencyTables`; the bundles `OAIQ089A003`, `OAIQ089A004` and `OAIQ089A005` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ089A009` and `OAIQ089A010`.
-- source:
--   OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 115; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Exact-Uniform-Sampling-of-Contingency-Tables-with-Arbitrary-Margins-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_ContingencyTables
import Definitions.Def_OAIQ089A003
import Definitions.Def_OAIQ089A004
import Definitions.Def_OAIQ089A005

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_IntegerMarginal
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Balanced marginalization of actual integer two-removal matrices

The new pair is summed subject to its exact total M. We identify every
old, fresh and cross entry with the balanced summation theorem; thus the
signature of the marginal is derived from signatures of the actual unsummed
integer matrices, rather than assumed for a binary encoding.
-/

namespace ContingencyTables.IntegerMarginal

open scoped BigOperators Classical Matrix
open CommonBasesFPRAS FactorialSignatures
open LinearMap (BilinForm)

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Equality-softening limits preserve the actual raw integer signature.
Only the finitely many displayed matrix entries are used. -/
theorem removal_signature_limit {K : Type*} {l : Filter K} [l.NeBot]
    (F : K → (I → ℕ) → ℝ) (f : (I → ℕ) → ℝ) (z : I → ℕ)
    (hlim : ∀ n, Filter.Tendsto (fun t => F t n) l (nhds (f n)))
    (hsig : ∀ᶠ t in l, OnePositiveDirection (integerRemovalMatrix (F t) z).toBilin') :
    OnePositiveDirection (integerRemovalMatrix f z).toBilin' := by
  apply (BinaryContraction.signature_iff _ (matrix_bilin_symm _ (integerRemoval_symm _ _))).mpr
  apply onePositive_of_tendsto (l := l) (fun t => integerRemovalMatrix (F t) z) (integerRemovalMatrix f z)
  · intro i j
    by_cases h : ValidPair z i j
    · simpa only [integerRemovalMatrix,h,ite_true, if_true] using hlim (removeTwo z i j)
    · simpa only [integerRemovalMatrix,h,ite_false] using
        (tendsto_const_nhds : Filter.Tendsto (fun _ : K => (0:ℝ)) l (nhds 0))
  · intro t
    exact integerRemoval_symm _ _
  · filter_upwards [hsig] with t ht
    exact (BinaryContraction.signature_iff _ (matrix_bilin_symm _ (integerRemoval_symm _ _))).mp ht

end ContingencyTables.IntegerMarginal

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ProductIntegerSignature
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Raw integer signatures of the actual line and unary product

The line groups are disjoint. Integer counts at zero are masked; a repeated
removal from a count below two uses a zero second-update factor. This
identifies the actual integer matrix, including its box boundaries, with a
congruence of the proved line/unary update matrix.
-/

namespace ContingencyTables.ProductIntegerSignature

open scoped BigOperators Classical Matrix
open CommonBasesFPRAS FactorialSignatures

variable {I G : Type*} [Fintype I] [Fintype G]

/-- The raw matrix is exactly the line/unary matrix with inactive integer
coordinates set to zero. Invalid repeated removals are also zero. -/
theorem integerRemoval_product_matrix (line : I → G) (a : G → ℕ → ℝ) (b : I → ℕ → ℝ)
    (z : I → ℕ) :
    integerRemovalMatrix (productWeight line a b) z =
      scaledMatrix (lineUnaryRemoval line
        (fun g => a g (lineTotal line z g))
        (fun g => a g (lineTotal line z g-1))
        (fun g => if 2 ≤ lineTotal line z g then a g (lineTotal line z g-2) else 0)
        (fun k => b k (z k)) (fun k => b k (z k-1))
        (fun k => if 2 ≤ z k then b k (z k-2) else 0)) (activeMask z) := by
  ext i j
  unfold integerRemovalMatrix scaledMatrix activeMask
  by_cases hv : ValidPair z i j
  · have hi : 0 < z i := hv.1
    have hj : 0 < z j := by dsimp [ValidPair] at hv; omega
    simp only [hv,ite_true, if_true,hi,hj,one_mul,mul_one]
    exact productWeight_removeTwo line a b z i j hv
  · rw [ite_eq_right hv]
    by_cases hi : 0 < z i
    · by_cases hj : 0 < z j
      · have hij : i = j := by by_contra h; exact hv ⟨hi,by simp [Ne.symm h,hj]⟩
        subst j
        have hn : ¬2 ≤ z i := by simp [ValidPair] at hv; omega
        simp only [hi,ite_true, if_true,one_mul,mul_one,lineUnaryRemoval]
        have hz : productTwoUpdates (fun k => b k (z k)) (fun k => b k (z k-1))
            (fun k => if 2 ≤ z k then b k (z k-2) else 0) i i = 0 := by
          apply Finset.prod_eq_zero (Finset.mem_univ i)
          simp [hn]
        rw [hz,mul_zero]
      · simp [hj]
    · simp [hi]

/-- Log-concavity of the actual scalar sequences gives the integer
signature required by factorial lifting and balanced marginalization. -/
theorem product_removal_onePositive (line : I → G) (a : G → ℕ → ℝ) (b : I → ℕ → ℝ)
    (z : I → ℕ)
    (ha : ∀ g n, n ≤ lineTotal line z g → 0 < a g n)
    (hb : ∀ i n, n ≤ z i → 0 < b i n)
    (halc : ∀ g, 2 ≤ lineTotal line z g →
      a g (lineTotal line z g) * a g (lineTotal line z g-2) ≤ a g (lineTotal line z g-1)^2)
    (hblc : ∀ i, 2 ≤ z i → b i (z i) * b i (z i-2) ≤ b i (z i-1)^2) :
    OnePositiveDirection (integerRemovalMatrix (productWeight line a b) z).toBilin' := by
  rw [integerRemoval_product_matrix]
  have hs := lineUnaryRemoval_onePositive line
    (fun g => a g (lineTotal line z g))
    (fun g => a g (lineTotal line z g-1))
    (fun g => if 2 ≤ lineTotal line z g then a g (lineTotal line z g-2) else 0)
    (fun i => b i (z i)) (fun i => b i (z i-1))
    (fun i => if 2 ≤ z i then b i (z i-2) else 0)
    (fun g => ha g _ le_rfl) (fun g => ha g _ (Nat.sub_le _ _))
    (fun g => by split_ifs; exact (ha g _ (Nat.sub_le _ _)).le; exact le_rfl)
    (fun i => hb i _ le_rfl) (fun i => hb i _ (Nat.sub_le _ _))
    (fun g => by split_ifs with h; exact halc g h; simp [sq_nonneg])
    (fun i => by split_ifs with h; exact hblc i h; simp [sq_nonneg])
  intro x hx y hxy
  rw [scaledMatrix_form] at hx hxy ⊢
  exact hs _ hx _ hxy

end ContingencyTables.ProductIntegerSignature

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_EqualitySoftening
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Root penalties and exact nonroot equations

Root lines carry their actual absolute-deviation penalty. Nonroot lines
carry a positive equality softener; its limit is the exact prescribed-line
indicator. Unary interval penalties include the companion's tree factors.
All balanced large-cell sums are performed before this finite limit.
-/

namespace ContingencyTables.EqualitySoftening

open scoped BigOperators Classical Matrix Topology
open Filter CommonBasesFPRAS FactorialSignatures ProductIntegerSignature
open ScalarPenalty IntegerMarginal BalancedBox BalancedFamily

variable {C G : Type*} [Fintype C] [Fintype G]

/-- The actual positive factors prove the raw signature; it is not an
assumption about a previously lifted binary weight. -/
theorem softenedWeight_removal (line : C → G) (root : G → Bool)
    (rate offset slope : G → ℝ) (urate ell uslope cap : C → ℝ) (L : ℝ)
    (hrate : ∀ g, 0 ≤ rate g) (hu : ∀ i, 0 ≤ urate i) (hL : 0 ≤ L) (z : C → ℕ) :
    OnePositiveDirection
      (integerRemovalMatrix (softenedWeight line root rate offset slope urate ell uslope cap L) z).toBilin' := by
  apply product_removal_onePositive line (lineFactor root rate offset slope L)
    (unaryFactor urate ell uslope cap) z
  · intro g n _; exact factor_positive _ _ _
  · intro i n _; exact factor_positive _ _ _
  · intro g hn
    apply abs_factor_logConcave _ _ _ _ _ hn
    split_ifs
    · exact hrate g
    · exact hL
  · intro i hn
    exact factor_logConcave (urate i) (hu i) _ _
      (affineDistance_convex (ell i) (uslope i) (cap i) _ hn)

omit [Fintype G] in
lemma lineFactor_tendsto (root : G → Bool) (rate offset slope : G → ℝ) (g : G) (n : ℕ) :
    Tendsto (fun L : ℝ => lineFactor root rate offset slope L g n) atTop
      (nhds (exactLineFactor root rate offset slope g n)) := by
  by_cases hroot : root g
  · simp [lineFactor,exactLineFactor,hroot]
  · simpa [lineFactor,exactLineFactor,hroot,factor] using
      factor_limit |offset g+(n:ℝ)*slope g| (abs_nonneg _)

theorem softenedWeight_tendsto (line : C → G) (root : G → Bool)
    (rate offset slope : G → ℝ) (urate ell uslope cap : C → ℝ) (z : C → ℕ) :
    Tendsto (fun L : ℝ => softenedWeight line root rate offset slope urate ell uslope cap L z) atTop
      (nhds (exactWeight line root rate offset slope urate ell uslope cap z)) := by
  apply Tendsto.mul_const
  apply tendsto_finsetProd
  intro g _
  exact lineFactor_tendsto root rate offset slope g (lineTotal line z g)

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- This is the actual finite balanced large-cell marginal with exact
nonroot equations. Positive softening is retained through every sum and
removed only after the last sum. -/
theorem exact_marginal_removal (Ms : List ℕ) (m : I → ℕ) (R : ℕ)
    (line : Coordinates I Ms → G) (root : G → Bool) (rate offset slope : G → ℝ)
    (urate ell uslope cap : Coordinates I Ms → ℝ)
    (hwidth : ∀ M ∈ Ms, 2 ≤ M) (hrate : ∀ g, 0 ≤ rate g) (hu : ∀ i, 0 ≤ urate i) :
    RemovalSlice (eliminate Ms (exactWeight line root rate offset slope urate ell uslope cap)) m R := by
  intro z hz htotal
  apply removal_signature_limit (l := (atTop : Filter ℝ))
    (fun L => eliminate Ms (softenedWeight line root rate offset slope urate ell uslope cap L))
    (eliminate Ms (exactWeight line root rate offset slope urate ell uslope cap)) z
  · intro x
    exact eliminate_tendsto Ms _ _
      (softenedWeight_tendsto line root rate offset slope urate ell uslope cap) x
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with L hL
    have hp : PositiveSlice (softenedWeight line root rate offset slope urate ell uslope cap L)
        (bounds m Ms) (R+Ms.sum) := by
      intro x _ _
      exact softenedWeight_positive line root rate offset slope urate ell uslope cap L x
    have hs : RemovalSlice (softenedWeight line root rate offset slope urate ell uslope cap L)
        (bounds m Ms) (R+Ms.sum) := by
      intro x _ _
      convert softenedWeight_removal line root rate offset slope urate ell uslope cap L hrate hu hL x using 1
      all_goals try with_reducible_and_instances rfl
      congr 2 <;> exact Subsingleton.elim _ _
    exact (eliminate_slices Ms m R _ hwidth hp hs).2 z hz htotal

end ContingencyTables.EqualitySoftening

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_EqualityReindex
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Equality factors under the actual physical coordinate bijection

A bijection of coordinates preserves the line totals and unary products.
Consequently the balanced marginal signature applies to the literal
physical factor family after all cell-index bookkeeping has been proved.
-/

namespace ContingencyTables.EqualityReindex

open scoped BigOperators Classical
open ProductIntegerSignature EqualitySoftening BalancedFamily BalancedBox

variable {C D G : Type*} [Fintype C] [Fintype D] [Fintype G]

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The application needs precisely the raw removal signature of the
actual physical factor marginal, rather than a hypothesis asserting it. -/
theorem physical_marginal_removal (Ms : List ℕ) (m : S → ℕ) (R : ℕ)
    (e : Coordinates S Ms ≃ D) (line : D → G) (root : G → Bool)
    (rate offset slope : G → ℝ) (urate ell uslope cap : D → ℝ)
    (hwidth : ∀ M ∈ Ms, 2≤M) (hrate : ∀ g, 0 ≤ rate g) (hu : ∀ d, 0≤urate d) :
    RemovalSlice (eliminate Ms (fun z =>
      exactWeight line root rate offset slope urate ell uslope cap (z ∘ e.symm))) m R := by
  have heq : (fun z => exactWeight line root rate offset slope urate ell uslope cap
      (z ∘ e.symm))=
      exactWeight (line ∘ e) root rate offset slope (urate ∘ e) (ell ∘ e) (uslope ∘ e) (cap ∘ e) := by
    funext z
    exact (exactWeight_reindex e line root rate offset slope urate ell uslope cap z).symm
  rw [heq]
  exact exact_marginal_removal Ms m R (line ∘ e) root rate offset slope
    (urate ∘ e) (ell ∘ e) (uslope ∘ e) (cap ∘ e) hwidth hrate (fun i => hu (e i))

end ContingencyTables.EqualityReindex

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_IntegerLeafEnergy
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual leaf energy as a finite sum of complete displays -/

namespace ContingencyTables.IntegerWeightedTransport

open scoped BigOperators Classical
open FactorialSignatures BalancedFamily BalancedEnumeration IntegerMarginal

universe u

noncomputable def integerGraphEnergy {C : Type*} [DecidableEq C]
    (V : Finset (C → ℕ)) (F H : (C → ℕ) → ℝ) : ℝ :=
  (∑ e ∈ (V ×ˢ V).filter (fun e => IntegerExchangeAdjacent e.1 e.2), edgeTerm F H e)/2

end ContingencyTables.IntegerWeightedTransport

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_TreeCanonical
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.TreeTyped.finsetCodec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

variable {A : Type} [Codec A]

def contains [DecidableEq A] (E : Realizer (fun x : A×A=>decide (x.1=x.2))) :
    Realizer (fun x : A×List A=>decide (x.1∈x.2)) :=
  (composition (mapWith E) any).congr (by
    intro x
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply,List.any_map,List.any_eq_true,id_eq,decide_eq_true_eq]
    constructor
    · rintro ⟨a,ha,he⟩; simpa [he] using ha
    · intro h; exact ⟨x.1,h,rfl⟩)
def dedupStepRealizer [DecidableEq A] (E : Realizer (fun x : A×A=>decide (x.1=x.2))) :
    Realizer (dedupStep (A:=A)) :=
  (choose (contains E) second listCons).congr (by intro x; simp [dedupStep])
omit [Codec A] in
lemma dedup_fold [DecidableEq A] (as : List A) :
    as.reverse.foldl (fun bs a=>dedupStep (a,bs)) []=as.dedup := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    rw [List.reverse_cons,List.foldl_append,List.foldl_cons,List.foldl_nil,ih]
    exact (List.dedup_cons' a as).symm
def dedup [DecidableEq A] (E : Realizer (fun x : A×A=>decide (x.1=x.2))) : Realizer (List.dedup (α:=A)) :=
  (composition (pair reverse (constant [])) (fold (dedupStepRealizer E))).congr dedup_fold
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileExchangeCandidates
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial binary program listing all coordinate exchanges -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped Polynomial

def profileIndices : Realizer (fun xs : List ℕ => List.range xs.length) :=
  composition listLength range

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperContextTransport
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Raw transport for the literal first-paper completion counts

An actual small-coordinate bijection isolates a fixed balanced prefix,
the special pair, and the remaining ordinary pairs. Large completions
are still the original physical finite sum; the prefix coordinates are
excluded from every exchange in the transport graph.
-/

namespace ContingencyTables.FirstPaperContextTransport

open scoped BigOperators Classical Topology
open FirstPaperPhysicalMarginal LargePairEnumeration IntegerWeightedTransport
open BalancedFamily BalancedBox

universe u

variable {I J C : Type u} [Fintype I] [Fintype J] [Fintype C]
  [DecidableEq C]

noncomputable def contextHard (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (Ms : List ℕ)
    (e : (C ⊕ Coordinates Bool Ms) ≃ SmallView (fun a : I×J => small a.1 a.2))
    (σ : C → ℕ) : (Coordinates Bool Ms → ℕ) → ℝ :=
  fun x => hardMarginal small B r c L ((Sum.elim σ x) ∘ e.symm)

end ContingencyTables.FirstPaperContextTransport

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_Repair
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Repair of a defect with its large completion

The two full matrices give the row and column views, agreeing at all
large cells. Moving one unit from the positive cell to the crossing cell
and resetting the column view preserves the enlarged margins. This is the
joint-object injection underlying the repair in paper 200-01.
-/

namespace ContingencyTables

open Finset

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

omit [Fintype I] [Fintype J] in
/-- Fixed defect labels make the repair injective on joint row/column
views, hence also on the state together with its large completion. -/
theorem repairMatrix_injective {x q y p : I → J → ℕ} {s t : I × J}
    (hx : IsDefect x q s t) (hy : IsDefect y p s t)
    (heq : repairMatrix x s t = repairMatrix y s t) : x = y ∧ q = p := by
  have hxy : x = y := by
    funext i j
    have h := congrArg (fun X : I → J → ℕ => (X i j : ℤ)) heq
    rw [repairMatrix_cast hx, repairMatrix_cast hy] at h
    simp only [transferInt] at h
    exact Int.natCast_inj.mp (by omega)
  refine ⟨hxy, ?_⟩
  funext i j
  apply Int.natCast_inj.mp
  rw [hx.2, hy.2, hxy]

end ContingencyTables

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_RepairPrefixes
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Literal repair values and row-major prefix preservation -/

namespace ContingencyTables

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

omit [Fintype I] [Fintype J] in
lemma repairMatrix_unchanged {x q : I → J → ℕ} {s t w : I×J}
    (h : IsDefect x q s t) (hwt : w ≠ t) (hwv : w ≠ (t.1,s.2)) :
    repairMatrix x s t w.1 w.2=x w.1 w.2 := by
  apply Int.natCast_inj.mp
  rw [repairMatrix_cast h]
  have h1 : ¬(w.1=t.1 ∧ w.2=t.2) := fun hw => hwt (Prod.ext hw.1 hw.2)
  have h2 : ¬(w.1=t.1 ∧ w.2=s.2) := fun hw => hwv (Prod.ext hw.1 hw.2)
  simp only [transferInt,h1,h2,↓reduceIte,sub_zero,add_zero]

end ContingencyTables

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_RepairFibres
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Joint state-completion repair injections, including fixed contexts

Full row and column views retain the large completion explicitly. Their
finite fibre cardinalities therefore count states with the correct
completion multiplicity. The target repair is a balanced full table.
-/

namespace ContingencyTables

open scoped BigOperators Classical
open PaddedCompletions

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

noncomputable instance jointDefectFintype (small : I → J → Bool) (r : I → ℕ) (c : J → ℕ)
    (rbar : I → ℕ) (cbar : J → ℕ) (s t : I×J) :
    Fintype (JointDefect small r c rbar cbar s t) := by unfold JointDefect; infer_instance

noncomputable instance residualTablesFintype (small : I → J → Bool) (r : I → ℕ) (c : J → ℕ)
    (rbar : I → ℕ) (cbar : J → ℕ) :
    Fintype (ResidualTables small r c rbar cbar) := by unfold ResidualTables; infer_instance

def jointRepair {small : I → J → Bool} {r : I → ℕ} {c : J → ℕ}
    {rbar : I → ℕ} {cbar : J → ℕ} {s t : I×J}
    (hs : small s.1 s.2=true) (ht : small t.1 t.2=true)
    (Z : JointDefect small r c rbar cbar s t) : ResidualTables small r c rbar cbar := by
  have hd := Z.property.1
  have hm := repairMatrix_margins hd rbar cbar Z.val.property.1 Z.val.property.2
  have hsmall := repairMatrix_small_sums hd hs ht
  exact ⟨⟨repairMatrix Z.val.val.1 s t,hm⟩,
    fun i => (hsmall.1 i).trans (Z.property.2.1 i),
    fun j => (hsmall.2 j).trans (Z.property.2.2 j)⟩

theorem jointRepair_injective {small : I → J → Bool} {r : I → ℕ} {c : J → ℕ}
    {rbar : I → ℕ} {cbar : J → ℕ} {s t : I×J}
    (hs : small s.1 s.2=true) (ht : small t.1 t.2=true) :
    Function.Injective (jointRepair (r := r) (c := c) (rbar := rbar) (cbar := cbar) hs ht) := by
  intro X Y he
  have hmatrix := congrArg (fun T => T.val.val) he
  have hviews := repairMatrix_injective X.property.1 Y.property.1 hmatrix
  exact Subtype.ext (Subtype.ext (Prod.ext hviews.1 hviews.2))

end ContingencyTables

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_PhysicalCompletionFibres
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
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

noncomputable instance completionFibreFintype (small : I → J → Bool) (B : I → J → ℕ)
    (r rbar : I → ℕ) (c cbar : J → ℕ) (z : SmallProfile small) :
    Fintype (CompletionFibre small B r rbar c cbar z) := by
  unfold CompletionFibre
  infer_instance

/-- Exact equality, including all completion multiplicities. -/
theorem hardMarginal_eq_fibre_card (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (z : SmallProfile small)
    (hz : ∀ u, z u ≤ B u.1.val.1 u.1.val.2) :
    hardMarginal small B r c L z=
      (Fintype.card (CompletionFibre small B r (fun i => r i+rowLargeCount small i*L)
        c (fun j => c j+columnLargeCount small j*L) z):ℝ) := by
  unfold hardMarginal fullHardFamily hardWeight
  rw [Finset.sum_boole,←Fintype.card_subtype]
  exact_mod_cast Fintype.card_congr (zeroPhysicalEquiv small B r c L z hz)

/-- Forgetting the retained profile loses no information on a bounded
injective family of profiles. In particular all later fibre sums count
full state/completion pairs exactly once. -/
theorem fibre_projection_injective {S : Type*}
    (small : I → J → Bool) (B : I → J → ℕ)
    (r rbar : I → ℕ) (c cbar : J → ℕ) (p : S → SmallProfile small)
    (hp : Function.Injective p) (hbox : ∀ s u, p s u ≤ B u.1.val.1 u.1.val.2) :
    Function.Injective (fun a : (s : S) × CompletionFibre small B r rbar c cbar (p s) =>
      a.2.val) := by
  rintro ⟨s,X⟩ ⟨t,Y⟩ he
  have hst : s=t := by
    apply hp
    funext u
    rcases u with ⟨⟨⟨i,j⟩,hs⟩,b⟩
    cases b
    · have hx := congrArg (fun Z : RowColumnPair rbar cbar => Z.val.1 i j) he
      rw [(X.property.2.2.1 i j hs).1,(Y.property.2.2.1 i j hs).1] at hx
      exact hx
    · have hq := congrArg (fun Z : RowColumnPair rbar cbar => Z.val.2 i j) he
      rw [(X.property.2.2.1 i j hs).2,(Y.property.2.2.1 i j hs).2] at hq
      have hx := hbox s (⟨(i,j),hs⟩,true)
      have hy := hbox t (⟨(i,j),hs⟩,true)
      dsimp only at hx hy
      omega
  subst t
  congr 1
  exact Subtype.ext he

end ContingencyTables.PhysicalCompletionFibres

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallContextFibres
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
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

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
lemma naturalProfile_injective (small : I → J → Bool) (B : I → J → ℕ) :
    Function.Injective (naturalProfile (small := small) (B := B)) := by
  intro x y he
  funext u
  exact Fin.ext (congrFun he u)

def BalancedProfiles [LT I] [LT J] (small : I → J → Bool) (B : I → J → ℕ)
    (s : I×J) (σ : I×J → ℕ) (k : ℕ) :=
  {z : BoundedProfile small B //
    (∀ i j, smallView small (naturalProfile z) false i j=smallQ small B (naturalProfile z) i j) ∧
    SmallPrefix small s σ (smallView small (naturalProfile z) false) ∧
    smallView small (naturalProfile z) false s.1 s.2=k}

def DefectProfiles [LT I] [LT J] (small : I → J → Bool) (B : I → J → ℕ)
    (s t : I×J) (σ : I×J → ℕ) (l : ℕ) :=
  {z : BoundedProfile small B //
    IsDefect (smallView small (naturalProfile z) false) (smallQ small B (naturalProfile z)) s t ∧
    SmallPrefix small s σ (smallView small (naturalProfile z) false) ∧
    smallView small (naturalProfile z) false s.1 s.2=l-1}

def SmallResidualChild [LT I] [LT J]
    (small : I → J → Bool) (r rbar : I → ℕ) (c cbar : J → ℕ)
    (s : I×J) (σ : I×J → ℕ) (k : ℕ) :=
  {T : ResidualTables small r c rbar cbar //
    SmallPrefix small s σ T.val.val ∧ T.val.val s.1 s.2=k}

noncomputable instance balancedProfilesFintype [LT I] [LT J]
    (small : I → J → Bool) (B : I → J → ℕ) (s : I×J) (σ : I×J → ℕ) (k : ℕ) :
    Fintype (BalancedProfiles small B s σ k) := by unfold BalancedProfiles; infer_instance

noncomputable instance defectProfilesFintype [LT I] [LT J]
    (small : I → J → Bool) (B : I → J → ℕ) (s t : I×J) (σ : I×J → ℕ) (l : ℕ) :
    Fintype (DefectProfiles small B s t σ l) := by unfold DefectProfiles; infer_instance

noncomputable instance smallResidualChildFintype [LT I] [LT J]
    (small : I → J → Bool) (r rbar : I → ℕ) (c cbar : J → ℕ)
    (s : I×J) (σ : I×J → ℕ) (k : ℕ) :
    Fintype (SmallResidualChild small r rbar c cbar s σ k) := by
  unfold SmallResidualChild
  infer_instance

noncomputable instance smallJointDefectContextFintype [LT I] [LT J]
    (small : I → J → Bool) (r rbar : I → ℕ) (c cbar : J → ℕ)
    (s t : I×J) (σ : I×J → ℕ) (l : ℕ) :
    Fintype (SmallJointDefectContext small r rbar c cbar s t σ l) := by
  unfold SmallJointDefectContext
  infer_instance

omit [DecidableEq I] [DecidableEq J] in
/-- A balanced small profile is balanced as a full pair of views. -/
lemma balanced_fibre_views {small : I → J → Bool} {B : I → J → ℕ}
    {r rbar : I → ℕ} {c cbar : J → ℕ} {z : SmallProfile small}
    (Z : CompletionFibre small B r rbar c cbar z)
    (hb : ∀ i j, smallView small z false i j=smallQ small B z i j) :
    Z.val.val.1=Z.val.val.2 := by
  funext i j
  cases hs : small i j
  · exact Z.property.2.2.2.1 i j hs
  · obtain ⟨hx,hq⟩ := Z.property.2.2.1 i j hs
    rw [hx,hq]
    simpa only [smallView,smallQ,hs,dite_eq_left] using hb i j

/-- The defect equation extends over the unchanged large completion. -/
lemma defect_fibre_views {small : I → J → Bool} {B : I → J → ℕ}
    {r rbar : I → ℕ} {c cbar : J → ℕ} {z : SmallProfile small} {s t : I×J}
    (Z : CompletionFibre small B r rbar c cbar z)
    (hs : small s.1 s.2=true) (ht : small t.1 t.2=true)
    (hd : IsDefect (smallView small z false) (smallQ small B z) s t) :
    IsDefect Z.val.val.1 Z.val.val.2 s t := by
  refine ⟨hd.1,?_⟩
  intro i j
  cases hij : small i j
  · have hns : ¬(i=s.1 ∧ j=s.2) := by rintro ⟨rfl,rfl⟩; rw [hs] at hij; contradiction
    have hnt : ¬(i=t.1 ∧ j=t.2) := by rintro ⟨rfl,rfl⟩; rw [ht] at hij; contradiction
    rw [←Z.property.2.2.2.1 i j hij]
    simp only [transferInt,hns,hnt,↓reduceIte,sub_zero,add_zero]
  · obtain ⟨hx,hq⟩ := Z.property.2.2.1 i j hij
    have he := hd.2 i j
    simp only [smallView,smallQ,hij,dite_eq_left,transferInt] at he
    simpa only [transferInt,hx,hq] using he

omit [DecidableEq I] [DecidableEq J] in
/-- Summing the literal hard weights is exactly counting the dependent
union of completion fibres. -/
theorem sum_hard_eq_sigma_card {S : Type*} [Fintype S]
    (small : I → J → Bool) (B : I → J → ℕ) (r : I → ℕ) (c : J → ℕ)
    (L : ℕ) (p : S → SmallProfile small)
    (hbox : ∀ s u, p s u ≤ B u.1.val.1 u.1.val.2) :
    (∑ s, hardMarginal small B r c L (p s))=
      (Fintype.card ((s : S) × CompletionFibre small B r
        (fun i => r i+rowLargeCount small i*L) c
        (fun j => c j+columnLargeCount small j*L) (p s)):ℝ) := by
  simp_rw [hardMarginal_eq_fibre_card small B r c L _ (hbox _)]
  rw [Fintype.card_sigma]
  simp only [Nat.cast_sum]

end ContingencyTables.SmallContextFibres

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallContextCount
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Literal contextual mass domination by repair

Finite sums of the actual hard completion weights, including all large
completions, are compared by the concrete repair injection.
-/

namespace ContingencyTables.SmallContextFibres

open scoped BigOperators Classical
open PaddedCompletions CompletionCounts FirstPaperProfiles
open PhysicalCompletionFibres FirstPaperPhysicalMarginal

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  [LinearOrder I] [LinearOrder J]

abbrev BalancedPairs (small : I → J → Bool) (B : I → J → ℕ)
    (r rbar : I → ℕ) (c cbar : J → ℕ) (s : I×J) (σ : I×J → ℕ) (k : ℕ) :=
  (z : BalancedProfiles small B s σ k) ×
    CompletionFibre small B r rbar c cbar (naturalProfile z.val)

noncomputable def balancedPairChild {small : I → J → Bool} {B : I → J → ℕ}
    {r rbar : I → ℕ} {c cbar : J → ℕ} {s : I×J} {σ : I×J → ℕ} {k : ℕ}
    (hs : small s.1 s.2=true)
    (a : BalancedPairs small B r rbar c cbar s σ k) :
    SmallResidualChild small r rbar c cbar s σ k := by
  have hq := balanced_fibre_views a.2 a.1.property.1
  refine ⟨⟨⟨a.2.val.val.1,a.2.val.property.1,?_⟩,a.2.property.1,?_⟩,?_,?_⟩
  · simpa only [hq] using a.2.val.property.2
  · simpa only [hq] using a.2.property.2.1
  · intro i j hs hbefore
    change a.2.val.val.1 i j=σ (i,j)
    rw [(a.2.property.2.2.1 i j hs).1]
    simpa only [smallView,hs,dite_eq_left] using a.1.property.2.1 i j hs hbefore
  · change a.2.val.val.1 s.1 s.2=k
    rw [(a.2.property.2.2.1 s.1 s.2 hs).1]
    simpa only [smallView,hs,dite_eq_left] using a.1.property.2.2

omit [DecidableEq I] [DecidableEq J] in
lemma balancedPairChild_injective {small : I → J → Bool} {B : I → J → ℕ}
    {r rbar : I → ℕ} {c cbar : J → ℕ} {s : I×J} {σ : I×J → ℕ} {k : ℕ}
    (hs : small s.1 s.2=true) :
    Function.Injective (balancedPairChild (B := B) (r := r) (rbar := rbar)
      (c := c) (cbar := cbar) (σ := σ) (k := k) hs) := by
  intro a b he
  apply fibre_projection_injective small B r rbar c cbar
    (fun z : BalancedProfiles small B s σ k => naturalProfile z.val)
    (fun x y h => Subtype.ext (naturalProfile_injective small B h))
    (fun z => naturalProfile_bounded z.val)
  apply Subtype.ext
  have hx := congrArg (fun T : SmallResidualChild small r rbar c cbar s σ k => T.val.val.val) he
  apply Prod.ext hx
  rw [←balanced_fibre_views a.2 a.1.property.1,←balanced_fibre_views b.2 b.1.property.1]
  exact hx

omit [DecidableEq I] [DecidableEq J] in
/-- Every residual table has exactly one balanced retained profile and
one large completion, provided the declared capacities exclude none. -/
lemma balancedPairChild_surjective {small : I → J → Bool} {B : I → J → ℕ}
    {r rbar : I → ℕ} {c cbar : J → ℕ} {s : I×J} {σ : I×J → ℕ} {k : ℕ}
    (hs : small s.1 s.2=true)
    (hcap : ∀ T : ResidualTables small r c rbar cbar, ∀ i j, T.val.val i j ≤ B i j) :
    Function.Surjective (balancedPairChild (B := B) (r := r) (rbar := rbar)
      (c := c) (cbar := cbar) (σ := σ) (k := k) hs) := by
  intro T
  let z : BoundedProfile small B := fun u =>
    if u.2 then ⟨B u.1.val.1 u.1.val.2-T.val.val.val u.1.val.1 u.1.val.2,
      Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
    else ⟨T.val.val.val u.1.val.1 u.1.val.2,
      Nat.lt_succ_of_le (hcap T.val _ _)⟩
  have hzfalse (i : I) (j : J) (hij : small i j=true) :
      smallView small (naturalProfile z) false i j=T.val.val.val i j := by
    simp only [smallView,hij,dite_eq_left,naturalProfile,z,Bool.false_eq_true,↓reduceIte]
  have hztrue (i : I) (j : J) (hij : small i j=true) :
      smallQ small B (naturalProfile z) i j=T.val.val.val i j := by
    simp only [smallQ,hij,dite_eq_left,naturalProfile,z,↓reduceIte]
    exact Nat.sub_sub_self (hcap T.val i j)
  have hbal : ∀ i j, smallView small (naturalProfile z) false i j=
      smallQ small B (naturalProfile z) i j := by
    intro i j
    cases hij : small i j
    · simp only [smallView,smallQ,hij,Bool.false_eq_true,↓reduceDIte]
    · rw [hzfalse i j hij,hztrue i j hij]
  let w : BalancedProfiles small B s σ k := ⟨z,hbal,
    (fun i j hij hbefore => by rw [hzfalse i j hij]; exact T.property.1 i j hij hbefore),
    by rw [hzfalse s.1 s.2 hs]; exact T.property.2⟩
  let Z : CompletionFibre small B r rbar c cbar (naturalProfile w.val) :=
    ⟨⟨(T.val.val.val,T.val.val.val),T.val.val.property⟩,T.val.property.1,T.val.property.2,
      (fun i j hij => ⟨by
        change T.val.val.val i j=naturalProfile z (⟨(i,j),hij⟩,false)
        simpa only [smallView,hij,dite_eq_left] using (hzfalse i j hij).symm,by
        change T.val.val.val i j=B i j-naturalProfile z (⟨(i,j),hij⟩,true)
        simpa only [smallQ,hij,dite_eq_left] using (hztrue i j hij).symm⟩),
      (fun _ _ _ => rfl),(fun i j _ => hcap T.val i j)⟩
  refine ⟨⟨w,Z⟩,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  rfl

/-- A contextual child mass is the exact cardinality of full residual
tables in that child, including all large completion multiplicities. -/
theorem balanced_mass_eq_child_card (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (s : I×J) (σ : I×J → ℕ) (k : ℕ)
    (hs : small s.1 s.2=true)
    (hcap : ∀ T : ResidualTables small r c
      (fun i => r i+rowLargeCount small i*L) (fun j => c j+columnLargeCount small j*L),
      ∀ i j, T.val.val i j ≤ B i j) :
    (∑ z : BalancedProfiles small B s σ k,
      hardMarginal small B r c L (naturalProfile z.val))=
      (Fintype.card (SmallResidualChild small r (fun i => r i+rowLargeCount small i*L)
        c (fun j => c j+columnLargeCount small j*L) s σ k):ℝ) := by
  rw [sum_hard_eq_sigma_card small B r c L
    (fun z : BalancedProfiles small B s σ k => naturalProfile z.val)
    (fun z => naturalProfile_bounded z.val)]
  exact_mod_cast Fintype.card_congr (Equiv.ofBijective (balancedPairChild hs)
    ⟨balancedPairChild_injective hs,balancedPairChild_surjective hs hcap⟩)

noncomputable def defectPairContext {small : I → J → Bool} {B : I → J → ℕ}
    {r rbar : I → ℕ} {c cbar : J → ℕ} {s t : I×J} {σ : I×J → ℕ} {l : ℕ}
    (hs : small s.1 s.2=true) (ht : small t.1 t.2=true)
    (a : (z : DefectProfiles small B s t σ l) ×
      CompletionFibre small B r rbar c cbar (naturalProfile z.val)) :
    SmallJointDefectContext small r rbar c cbar s t σ l := by
  refine ⟨⟨a.2.val,defect_fibre_views a.2 hs ht a.1.property.1,
    a.2.property.1,a.2.property.2.1⟩,?_,?_⟩
  · intro i j hij hbefore
    rw [(a.2.property.2.2.1 i j hij).1]
    simpa only [smallView,hij,dite_eq_left] using a.1.property.2.1 i j hij hbefore
  · rw [(a.2.property.2.2.1 s.1 s.2 hs).1]
    simpa only [smallView,hs,dite_eq_left] using a.1.property.2.2

lemma defectPairContext_injective {small : I → J → Bool} {B : I → J → ℕ}
    {r rbar : I → ℕ} {c cbar : J → ℕ} {s t : I×J} {σ : I×J → ℕ} {l : ℕ}
    (hs : small s.1 s.2=true) (ht : small t.1 t.2=true) :
    Function.Injective (defectPairContext (B := B) (r := r) (rbar := rbar)
      (c := c) (cbar := cbar) (σ := σ) (l := l) hs ht) := by
  intro a b he
  apply fibre_projection_injective small B r rbar c cbar
    (fun z : DefectProfiles small B s t σ l => naturalProfile z.val)
    (fun x y h => Subtype.ext (naturalProfile_injective small B h))
    (fun z => naturalProfile_bounded z.val)
  exact congrArg (fun Z : SmallJointDefectContext small r rbar c cbar s t σ l => Z.val.val) he

end ContingencyTables.SmallContextFibres

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallContextEnumeration
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallContextEnumeration.choiceContextFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Physical enumeration of a balanced exposure child

Every later small-cell choice occurs once, with the retained prefix fixed.
The large-cell capacities remain the original capacities throughout.
-/

namespace ContingencyTables.SmallContextEnumeration

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres
open LargePairEnumeration BalancedEnumeration BalancedFamily IntegerWeightedTransport
open FirstPaperContextTransport FirstPaperPhysicalMarginal FirstPaperProfiles

universe u

variable {I J : Type u} [LinearOrder I] [LinearOrder J]

noncomputable def choiceProfile (small : I → J → Bool) (B : I → J → ℕ) (U : ℕ)
    (hB : ∀ i j, small i j=true → B i j=U)
    (x : Cells small → Fin (U+1)) : BoundedProfile small B := fun a =>
  ⟨if a.2 then U-(x a.1).val else (x a.1).val,by
    rw [hB _ _ a.1.property]
    cases a.2
    · exact (x a.1).isLt
    · exact Nat.lt_succ_of_le (Nat.sub_le _ _)⟩

omit [LinearOrder I] [LinearOrder J] in
lemma choiceProfile_balanced (small : I → J → Bool) (B : I → J → ℕ) (U : ℕ)
    (hB : ∀ i j, small i j=true → B i j=U) (x : Cells small → Fin (U+1)) :
    ∀ i j, smallView small (naturalProfile (choiceProfile small B U hB x)) false i j=
      smallQ small B (naturalProfile (choiceProfile small B U hB x)) i j := by
  intro i j
  cases hij : small i j
  · simp only [smallView,smallQ,hij,Bool.false_eq_true,↓reduceDIte]
  · simp only [smallView,smallQ,hij,dite_eq_left,naturalProfile,choiceProfile,
      Bool.false_eq_true,↓reduceIte,hB i j hij]
    exact (Nat.sub_sub_self (Nat.le_of_lt_succ (x ⟨(i,j),hij⟩).isLt)).symm

noncomputable def balancedContext (small : I → J → Bool) (B : I → J → ℕ)
    (s : I×J) (hs : small s.1 s.2=true) (σ : I×J → ℕ) (U : ℕ)
    (hB : ∀ i j, small i j=true → B i j=U)
    (hσ : ∀ a : Earlier small s, σ a.val.val ≤ U) (k : Fin (U+1))
    (y : Later small s → Fin (U+1)) : BalancedProfiles small B s σ k.val := by
  let x := splitChoices small s hs U (prefixChoices small s σ U hσ) k y
  refine ⟨choiceProfile small B U hB x,choiceProfile_balanced small B U hB x,?_,?_⟩
  · intro i j hij hbefore
    simp only [smallView,hij,dite_eq_left,naturalProfile,choiceProfile,Bool.false_eq_true,↓reduceIte]
    change (x ⟨(i,j),hij⟩).val=σ (i,j)
    exact congrArg Fin.val (splitChoices_prefix small s hs U _ k y ⟨⟨(i,j),hij⟩,hbefore⟩)
  · simp only [smallView,hs,dite_eq_left,naturalProfile,choiceProfile,Bool.false_eq_true,↓reduceIte]
    change (x ⟨s,hs⟩).val=k.val
    exact congrArg Fin.val (splitChoices_special small s hs U _ k y)

lemma balanced_false_determines (small : I → J → Bool) (B : I → J → ℕ)
    (s : I×J) (σ : I×J → ℕ) (k : ℕ)
    (x y : BalancedProfiles small B s σ k)
    (he : ∀ a : Cells small, naturalProfile x.val (a,false)=naturalProfile y.val (a,false)) :
    x=y := by
  apply Subtype.ext
  apply naturalProfile_injective small B
  funext a
  rcases a with ⟨a,b⟩
  cases b
  · exact he a
  · have hx := x.property.1 a.val.1 a.val.2
    have hy := y.property.1 a.val.1 a.val.2
    simp only [smallView,smallQ,a.property,dite_eq_left] at hx hy
    change naturalProfile x.val (a,false)=B a.val.1 a.val.2-naturalProfile x.val (a,true) at hx
    change naturalProfile y.val (a,false)=B a.val.1 a.val.2-naturalProfile y.val (a,true) at hy
    have hbX := naturalProfile_bounded x.val (a,true)
    have hbY := naturalProfile_bounded y.val (a,true)
    dsimp only at hbX hbY
    have he' := he a
    omega

noncomputable def suffixChoices (small : I → J → Bool) (B : I → J → ℕ)
    (s : I×J) (σ : I×J → ℕ) (U : ℕ)
    (hB : ∀ i j, small i j=true → B i j=U) (k : Fin (U+1))
    (z : BalancedProfiles small B s σ k.val) : Later small s → Fin (U+1) := fun a =>
  ⟨naturalProfile z.val (a.val,false),by
    have h := naturalProfile_bounded z.val (a.val,false)
    rw [hB _ _ a.val.property] at h
    exact Nat.lt_succ_of_le h⟩

noncomputable def balancedContextEquiv (small : I → J → Bool) (B : I → J → ℕ)
    (s : I×J) (hs : small s.1 s.2=true) (σ : I×J → ℕ) (U : ℕ)
    (hB : ∀ i j, small i j=true → B i j=U)
    (hσ : ∀ a : Earlier small s, σ a.val.val ≤ U) (k : Fin (U+1)) :
    (Later small s → Fin (U+1)) ≃ BalancedProfiles small B s σ k.val where
  toFun := balancedContext small B s hs σ U hB hσ k
  invFun := suffixChoices small B s σ U hB k
  left_inv y := by
    funext a
    apply Fin.ext
    change (splitChoices small s hs U (prefixChoices small s σ U hσ) k y a.val).val=(y a).val
    rw [splitChoices_later]
  right_inv z := by
    apply balanced_false_determines small B s σ k.val
    intro a
    obtain ⟨q,rfl⟩ := (cellSplitEquiv small s hs).surjective a
    rcases q with p|(_|t)
    · change (splitChoices small s hs U (prefixChoices small s σ U hσ) k
        (suffixChoices small B s σ U hB k z) p.val).val=naturalProfile z.val (p.val,false)
      rw [splitChoices_prefix]
      simpa only [prefixChoices,smallView,p.val.property,dite_eq_left] using
        (z.property.2.1 _ _ p.val.property p.property).symm
    · change (splitChoices small s hs U (prefixChoices small s σ U hσ) k
        (suffixChoices small B s σ U hB k z) ⟨s,hs⟩).val=naturalProfile z.val (⟨s,hs⟩,false)
      rw [splitChoices_special]
      simpa only [smallView,hs,dite_eq_left] using z.property.2.2.symm
    · change (splitChoices small s hs U (prefixChoices small s σ U hσ) k
        (suffixChoices small B s σ U hB k z) t.val).val=naturalProfile z.val (t.val,false)
      rw [splitChoices_later]
      rfl

lemma physical_embedding_eq (small : I → J → Bool) (B : I → J → ℕ)
    (s : I×J) (hs : small s.1 s.2=true) (σ : I×J → ℕ) (U : ℕ)
    (hB : ∀ i j, small i j=true → B i j=U)
    (hσ : ∀ a : Earlier small s, σ a.val.val ≤ U) (k : Fin (U+1))
    {n : ℕ} (e : Fin n ≃ Later small s) (q : Assignments (widths (fun _ : Fin n => U))) :
    (Sum.elim (prefixRaw small s σ U)
      (embedding (widths (fun _ : Fin n => U)) (childProfile U k.val) q)) ∘
      (contextEquiv small s hs e U).symm=
    naturalProfile (balancedContext small B s hs σ U hB hσ k
      ((reindexChoices small s e) ((assignmentEquiv (fun _ : Fin n => U)) q))).val := by
  funext a
  obtain ⟨v,rfl⟩ := (contextEquiv small s hs e U).surjective a
  simp only [Function.comp_apply,Equiv.symm_apply_apply]
  cases v with
  | inl p =>
    rcases p with ⟨p,b⟩
    rw [contextEquiv_prefix]
    change (if b then U-σ p.val.val else σ p.val.val)=
      if b then U-(splitChoices small s hs U (prefixChoices small s σ U hσ) k _ p.val).val
      else (splitChoices small s hs U (prefixChoices small s σ U hσ) k _ p.val).val
    rw [splitChoices_prefix]
    rfl
  | inr v =>
    obtain ⟨w,rfl⟩ := (coordinateEquiv Bool (fun _ : Fin n => U)).symm.surjective v
    cases w with
    | inl b =>
      rw [contextEquiv_special]
      simp only [Sum.elim_inr]
      rw [embedding_coordinate_apply,Equiv.apply_symm_apply]
      change (if b then U-k.val else k.val)=
        if b then U-(splitChoices small s hs U (prefixChoices small s σ U hσ) k _ ⟨s,hs⟩).val
        else (splitChoices small s hs U (prefixChoices small s σ U hσ) k _ ⟨s,hs⟩).val
      rw [splitChoices_special]
    | inr p =>
      rcases p with ⟨i,b⟩
      rw [contextEquiv_later]
      simp only [Sum.elim_inr]
      rw [embedding_coordinate_apply,Equiv.apply_symm_apply]
      change (if b then U-((assignmentEquiv (fun _ : Fin n => U)) q i).val
        else ((assignmentEquiv (fun _ : Fin n => U)) q i).val)=
        if b then U-(splitChoices small s hs U (prefixChoices small s σ U hσ) k _ (e i).val).val
        else (splitChoices small s hs U (prefixChoices small s σ U hσ) k _ (e i).val).val
      rw [splitChoices_later]
      change (if b then U-((assignmentEquiv (fun _ : Fin n => U)) q i).val
        else ((assignmentEquiv (fun _ : Fin n => U)) q i).val)=
        if b then U-((assignmentEquiv (fun _ : Fin n => U)) q (e.symm (e i))).val
        else ((assignmentEquiv (fun _ : Fin n => U)) q (e.symm (e i))).val
      rw [Equiv.symm_apply_apply]

variable [Fintype I] [Fintype J]

/-- The recursive transport child is the literal sum over physical
bounded balanced profiles, retaining every large completion multiplicity. -/
theorem eliminate_context_eq_balanced_mass (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ)
    (s : I×J) (hs : small s.1 s.2=true) (σ : I×J → ℕ) (U : ℕ)
    (hB : ∀ i j, small i j=true → B i j=U)
    (hσ : ∀ a : Earlier small s, σ a.val.val ≤ U) (k : Fin (U+1))
    {n : ℕ} (e : Fin n ≃ Later small s) :
    eliminate (widths (fun _ : Fin n => U))
      (contextHard small B r c L _ (contextEquiv small s hs e U) (prefixRaw small s σ U))
      (childProfile U k.val)=
      ∑ z : BalancedProfiles small B s σ k.val, hardMarginal small B r c L (naturalProfile z.val) := by
  rw [eliminate_eq_sum]
  apply Fintype.sum_equiv (((assignmentEquiv (fun _ : Fin n => U)).trans
    (reindexChoices small s e)).trans (balancedContextEquiv small B s hs σ U hB hσ k))
  intro q
  unfold contextHard
  rw [physical_embedding_eq small B s hs σ U hB hσ k e q]
  rfl

end ContingencyTables.SmallContextEnumeration

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ExcessContextProfiles
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.SmallContextEnumeration.choiceContextFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Physical defect profiles in the auxiliary context kernel -/

namespace ContingencyTables.ExcessContextProfiles

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextEnumeration SmallContextFibres
open PhysicalCompletionFibres LargePairEnumeration BalancedFamily BalancedBox
open BalancedEnumeration IntegerWeightedTransport FirstPaperProfiles

universe u

variable {I J : Type u} [LinearOrder I] [LinearOrder J]

noncomputable def assemble (small : I → J → Bool) (s : I×J) (hs : small s.1 s.2=true)
    (σ : I×J → ℕ) (U : ℕ) {n : ℕ} (e : Fin n ≃ Later small s)
    (v : Coordinates Bool (widths (fun _ : Fin n => U)) → ℕ) : SmallProfile small :=
  (Sum.elim (prefixRaw small s σ U) v) ∘ (contextEquiv small s hs e U).symm

lemma assemble_apply (small : I → J → Bool) (s : I×J) (hs : small s.1 s.2=true)
    (σ : I×J → ℕ) (U : ℕ) {n : ℕ} (e : Fin n ≃ Later small s)
    (v : Coordinates Bool (widths (fun _ : Fin n => U)) → ℕ)
    (a : (Earlier small s×Bool) ⊕ Coordinates Bool (widths (fun _ : Fin n => U))) :
    assemble small s hs σ U e v (contextEquiv small s hs e U a)=
      Sum.elim (prefixRaw small s σ U) v a := by
  simp only [assemble,Function.comp_apply,Equiv.symm_apply_apply]

lemma assemble_prefix (small : I → J → Bool) (s : I×J) (hs : small s.1 s.2=true)
    (σ : I×J → ℕ) (U : ℕ) {n : ℕ} (e : Fin n ≃ Later small s)
    (v : Coordinates Bool (widths (fun _ : Fin n => U)) → ℕ)
    (a : Earlier small s) (b : Bool) :
    assemble small s hs σ U e v (a.val,b)=if b then U-σ a.val.val else σ a.val.val := by
  have h := assemble_apply small s hs σ U e v (.inl (a,b))
  simpa only [contextEquiv_prefix,Sum.elim_inl,prefixRaw] using h

lemma assemble_special (small : I → J → Bool) (s : I×J) (hs : small s.1 s.2=true)
    (σ : I×J → ℕ) (U : ℕ) {n : ℕ} (e : Fin n ≃ Later small s)
    (v : Coordinates Bool (widths (fun _ : Fin n => U)) → ℕ) (b : Bool) :
    assemble small s hs σ U e v (⟨s,hs⟩,b)=
      v ((coordinateEquiv Bool (fun _ : Fin n => U)).symm (.inl b)) := by
  have h := assemble_apply small s hs σ U e v
    (.inr ((coordinateEquiv Bool (fun _ : Fin n => U)).symm (.inl b)))
  simpa only [contextEquiv_special,Sum.elim_inr] using h

lemma assemble_later (small : I → J → Bool) (s : I×J) (hs : small s.1 s.2=true)
    (σ : I×J → ℕ) (U : ℕ) {n : ℕ} (e : Fin n ≃ Later small s)
    (v : Coordinates Bool (widths (fun _ : Fin n => U)) → ℕ) (i : Fin n) (b : Bool) :
    assemble small s hs σ U e v ((e i).val,b)=
      v ((coordinateEquiv Bool (fun _ : Fin n => U)).symm (.inr (i,b))) := by
  have h := assemble_apply small s hs σ U e v
    (.inr ((coordinateEquiv Bool (fun _ : Fin n => U)).symm (.inr (i,b))))
  simpa only [contextEquiv_later,Sum.elim_inr] using h

noncomputable def rawExcess (small : I → J → Bool) (s : I×J) (hs : small s.1 s.2=true)
    (σ : I×J → ℕ) (U l : ℕ) {n : ℕ} (e : Fin n ≃ Later small s)
    (q : ExcessAssignments (widths (fun _ : Fin n => U))) : SmallProfile small :=
  assemble small s hs σ U e (excessEmbedding _ (auxRoot U l) q)

lemma rawExcess_bounded (small : I → J → Bool) (s : I×J) (hs : small s.1 s.2=true)
    (σ : I×J → ℕ) (U l : ℕ) (hl : l ≤ U)
    (hσ : ∀ a : Earlier small s, σ a.val.val ≤ U) {n : ℕ} (e : Fin n ≃ Later small s)
    (q : ExcessAssignments (widths (fun _ : Fin n => U)))
    (hq : ValidExcess _ q) (a : SmallView (fun a : I×J => small a.1 a.2)) :
    rawExcess small s hs σ U l e q a ≤ U := by
  have hv := (excessEmbedding_inBox_iff _ _ _ (auxRoot_inBox U l hl) q).mpr hq
  obtain ⟨v,rfl⟩ := (contextEquiv small s hs e U).surjective a
  unfold rawExcess
  rw [assemble_apply]
  cases v with
  | inl p =>
    rcases p with ⟨p,b⟩
    cases b
    · exact hσ p
    · exact Nat.sub_le _ _
  | inr v =>
    rw [bounds_constant] at hv
    exact hv v

/-- The auxiliary profile has exactly the negative current pair and
one positive later pair required by the manuscript's conditional repair. -/
lemma rawExcess_pair_total (small : I → J → Bool) (s : I×J) (hs : small s.1 s.2=true)
    (σ : I×J → ℕ) (U l : ℕ) (hl0 : 1 ≤ l) (hlU : l ≤ U)
    (hσ : ∀ a : Earlier small s, σ a.val.val ≤ U) {n : ℕ} (e : Fin n ≃ Later small s)
    (q : ExcessAssignments (widths (fun _ : Fin n => U))) (a : Cells small) :
    rawExcess small s hs σ U l e q (a,false)+rawExcess small s hs σ U l e q (a,true)=
      if a=⟨s,hs⟩ then U-1 else
      if a=(e (excessIndex (fun _ : Fin n => U) q)).val then U+1 else U := by
  obtain ⟨v,rfl⟩ := (cellSplitEquiv small s hs).surjective a
  rcases v with p|(_|t)
  · have hps : p.val≠⟨s,hs⟩ := by
      intro he
      have h := p.property
      rw [he] at h
      exact h.ne rfl
    have hpt : p.val≠(e (excessIndex (fun _ : Fin n => U) q)).val := by
      intro he
      have h := p.property
      rw [he] at h
      exact (h.trans (e (excessIndex (fun _ : Fin n => U) q)).property).ne rfl
    change rawExcess small s hs σ U l e q (p.val,false)+rawExcess small s hs σ U l e q (p.val,true)=
      if p.val=⟨s,hs⟩ then U-1 else
      if p.val=(e (excessIndex (fun _ : Fin n => U) q)).val then U+1 else U
    simp only [rawExcess,assemble_prefix,Bool.false_eq_true,↓reduceIte,hps,hpt]
    have hb := hσ p
    omega
  · change rawExcess small s hs σ U l e q (⟨s,hs⟩,false)+rawExcess small s hs σ U l e q (⟨s,hs⟩,true)=
      if (⟨s,hs⟩ : Cells small)=⟨s,hs⟩ then U-1 else
      if (⟨s,hs⟩ : Cells small)=(e (excessIndex (fun _ : Fin n => U) q)).val then U+1 else U
    rw [ite_eq_left rfl]
    simp only [rawExcess,assemble_special,excessEmbedding_root,auxRoot,Bool.false_eq_true,↓reduceIte]
    omega
  · have hts : t.val≠⟨s,hs⟩ := by
      intro he
      have h := t.property
      rw [he] at h
      exact h.ne rfl
    have hte : t.val=(e (excessIndex (fun _ : Fin n => U) q)).val ↔
        e.symm t=excessIndex (fun _ : Fin n => U) q := by
      constructor
      · intro he
        have he' : t=e (excessIndex (fun _ : Fin n => U) q) := Subtype.ext he
        rw [he',Equiv.symm_apply_apply]
      · intro he
        have hh := congrArg e he
        simpa only [Equiv.apply_symm_apply] using congrArg Subtype.val hh
    have hh := excessEmbedding_pair_total (fun _ : Fin n => U) (auxRoot U l) q (e.symm t)
    change assemble small s hs σ U e (excessEmbedding _ (auxRoot U l) q) (t.val,false)+
      assemble small s hs σ U e (excessEmbedding _ (auxRoot U l) q) (t.val,true)=
      if t.val=⟨s,hs⟩ then U-1 else
      if t.val=(e (excessIndex (fun _ : Fin n => U) q)).val then U+1 else U
    have hf := assemble_later small s hs σ U e (excessEmbedding _ (auxRoot U l) q) (e.symm t) false
    have ht := assemble_later small s hs σ U e (excessEmbedding _ (auxRoot U l) q) (e.symm t) true
    simp only [Equiv.apply_symm_apply] at hf ht
    rw [hf,ht,ite_eq_right hts]
    by_cases h : e.symm t=excessIndex (fun _ : Fin n => U) q
    · rw [ite_eq_left (hte.mpr h)]
      simpa only [h,↓reduceIte] using hh
    · rw [ite_eq_right (fun he => h (hte.mp he))]
      simpa only [h,↓reduceIte,add_zero] using hh

end ContingencyTables.ExcessContextProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ExcessContextDefects
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.SmallContextEnumeration.choiceContextFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Auxiliary raw profiles satisfy the literal physical defect equation -/

namespace ContingencyTables.ExcessContextProfiles

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextEnumeration SmallContextFibres
open PhysicalCompletionFibres LargePairEnumeration BalancedFamily BalancedBox
open BalancedEnumeration IntegerWeightedTransport FirstPaperProfiles

universe u

variable {I J : Type u} [LinearOrder I] [LinearOrder J]

lemma defect_of_pair_totals (small : I → J → Bool) (B : I → J → ℕ) (U : ℕ)
    (hU : 1 ≤ U) (hB : ∀ i j, small i j=true → B i j=U)
    (s t : I×J) (hs : small s.1 s.2=true) (ht : small t.1 t.2=true) (hst : s≠t)
    (z : SmallProfile small) (hz : ∀ a, z a ≤ U)
    (hpair : ∀ a : Cells small, z (a,false)+z (a,true)=
      if a.val=s then U-1 else if a.val=t then U+1 else U) :
    IsDefect (smallView small z false) (smallQ small B z) s t := by
  refine ⟨hst,?_⟩
  intro i j
  cases hij : small i j
  · have hns : ¬(i=s.1 ∧ j=s.2) := by
      rintro ⟨rfl,rfl⟩
      rw [hs] at hij
      contradiction
    have hnt : ¬(i=t.1 ∧ j=t.2) := by
      rintro ⟨rfl,rfl⟩
      rw [ht] at hij
      contradiction
    simp only [transferInt,smallView,smallQ,hij,Bool.false_eq_true,↓reduceDIte,
      hns,hnt,↓reduceIte]
    norm_num
  · have hp := hpair ⟨(i,j),hij⟩
    have hx := hz (⟨(i,j),hij⟩,false)
    have hy := hz (⟨(i,j),hij⟩,true)
    dsimp only at hp
    by_cases his : i=s.1 ∧ j=s.2
    · have his' : (i,j)=s := Prod.ext his.1 his.2
      have hit : ¬(i=t.1 ∧ j=t.2) := by
        intro hit
        exact hst (his'.symm.trans (Prod.ext hit.1 hit.2))
      rw [ite_eq_left his'] at hp
      simp only [transferInt,smallView,smallQ,hij,dite_eq_left,hB i j hij,
        ite_eq_left his,ite_eq_right hit]
      omega
    · have his' : (i,j)≠s := fun h => his (Prod.ext_iff.mp h)
      rw [ite_eq_right his'] at hp
      by_cases hit : i=t.1 ∧ j=t.2
      · have hit' : (i,j)=t := Prod.ext hit.1 hit.2
        rw [ite_eq_left hit'] at hp
        simp only [transferInt,smallView,smallQ,hij,dite_eq_left,hB i j hij,
          ite_eq_right his,ite_eq_left hit]
        omega
      · have hit' : (i,j)≠t := fun h => hit (Prod.ext_iff.mp h)
        rw [ite_eq_right hit'] at hp
        simp only [transferInt,smallView,smallQ,hij,dite_eq_left,hB i j hij,
          ite_eq_right his,ite_eq_right hit]
        omega

noncomputable def boundedExcess (small : I → J → Bool) (B : I → J → ℕ)
    (s : I×J) (hs : small s.1 s.2=true) (σ : I×J → ℕ) (U l : ℕ)
    (hl : l ≤ U) (hB : ∀ i j, small i j=true → B i j=U)
    (hσ : ∀ a : Earlier small s, σ a.val.val ≤ U) {n : ℕ} (e : Fin n ≃ Later small s)
    (q : ExcessAssignments (widths (fun _ : Fin n => U)))
    (hq : ValidExcess _ q) : BoundedProfile small B := fun a =>
  ⟨rawExcess small s hs σ U l e q a,by
    rw [hB _ _ a.1.property]
    exact Nat.lt_succ_of_le (rawExcess_bounded small s hs σ U l hl hσ e q hq a)⟩

lemma naturalProfile_boundedExcess (small : I → J → Bool) (B : I → J → ℕ)
    (s : I×J) (hs : small s.1 s.2=true) (σ : I×J → ℕ) (U l : ℕ)
    (hl : l ≤ U) (hB : ∀ i j, small i j=true → B i j=U)
    (hσ : ∀ a : Earlier small s, σ a.val.val ≤ U) {n : ℕ} (e : Fin n ≃ Later small s)
    (q : ExcessAssignments (widths (fun _ : Fin n => U))) (hq : ValidExcess _ q) :
    naturalProfile (boundedExcess small B s hs σ U l hl hB hσ e q hq)=
      rawExcess small s hs σ U l e q := rfl

noncomputable def excessDefectProfile (small : I → J → Bool) (B : I → J → ℕ)
    (s : I×J) (hs : small s.1 s.2=true) (σ : I×J → ℕ) (U l : ℕ)
    (hl0 : 1 ≤ l) (hlU : l ≤ U) (hB : ∀ i j, small i j=true → B i j=U)
    (hσ : ∀ a : Earlier small s, σ a.val.val ≤ U) {n : ℕ} (e : Fin n ≃ Later small s)
    (q : ExcessAssignments (widths (fun _ : Fin n => U))) (hq : ValidExcess _ q) :
    DefectProfiles small B s (e (excessIndex (fun _ : Fin n => U) q)).val.val σ l := by
  let t := e (excessIndex (fun _ : Fin n => U) q)
  refine ⟨boundedExcess small B s hs σ U l hlU hB hσ e q hq,?_,?_,?_⟩
  · rw [naturalProfile_boundedExcess]
    apply defect_of_pair_totals small B U (by omega) hB s t.val.val hs t.val.property
      t.property.ne (rawExcess small s hs σ U l e q)
      (rawExcess_bounded small s hs σ U l hlU hσ e q hq)
    intro a
    have hh := rawExcess_pair_total small s hs σ U l hl0 hlU hσ e q a
    simpa only [Subtype.ext_iff] using hh
  · intro i j hij hbefore
    simp only [naturalProfile_boundedExcess,smallView,hij,dite_eq_left]
    have hh := assemble_prefix small s hs σ U e
      (excessEmbedding _ (auxRoot U l) q) ⟨⟨(i,j),hij⟩,hbefore⟩ false
    exact hh
  · simp only [naturalProfile_boundedExcess,smallView,hs,dite_eq_left,rawExcess,
      assemble_special,excessEmbedding_root,auxRoot,Bool.false_eq_true,↓reduceIte]

end ContingencyTables.ExcessContextProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_AuxiliaryRepairMass
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.SmallContextEnumeration.choiceContextFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conditional repair bounds the literal auxiliary kernel mass -/

namespace ContingencyTables.ExcessContextProfiles

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextEnumeration SmallContextFibres
open PhysicalCompletionFibres LargePairEnumeration BalancedFamily BalancedBox
open BalancedEnumeration IntegerWeightedTransport FirstPaperProfiles
open FirstPaperContextTransport FirstPaperPhysicalMarginal IntegerBoxTruncation
open PaddedCompletions CompletionCounts

universe u

variable {I J : Type u} [LinearOrder I] [LinearOrder J]

lemma rawExcess_injective (small : I → J → Bool) (s : I×J) (hs : small s.1 s.2=true)
    (σ : I×J → ℕ) (U l : ℕ) {n : ℕ} (e : Fin n ≃ Later small s) :
    Function.Injective (rawExcess small s hs σ U l e) := by
  intro q q' he
  apply excessEmbedding_injective _ (auxRoot U l)
  funext a
  have hh := congrFun he (contextEquiv small s hs e U (.inr a))
  simpa only [rawExcess,assemble,Function.comp_apply,Equiv.symm_apply_apply,Sum.elim_inr] using hh

variable [Fintype I] [Fintype J]

/-- Every truncated auxiliary assignment maps injectively into one
actual conditional defect profile. The hard weights retain all completions. -/
theorem auxiliary_mass_le_defect_sum (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (s : I×J) (hs : small s.1 s.2=true)
    (σ : I×J → ℕ) (U l : ℕ) (hl0 : 1 ≤ l) (hlU : l ≤ U)
    (hB : ∀ i j, small i j=true → B i j=U)
    (hσ : ∀ a : Earlier small s, σ a.val.val ≤ U) {n : ℕ} (e : Fin n ≃ Later small s) :
    let Ms := widths (fun _ : Fin n => U)
    let f := contextHard small B r c L Ms (contextEquiv small s hs e U) (prefixRaw small s σ U)
    auxiliaryKernel Ms (truncate f (bounds (fun _ : Bool => U) Ms) (U+Ms.sum)) (auxRoot U l) ≤
      ∑ t : Later small s, ∑ z : DefectProfiles small B s t.val.val σ l,
        hardMarginal small B r c L (naturalProfile z.val) := by
  dsimp only
  rw [auxiliaryKernel_truncate_eq_valid_sum _ _ _ _ _ (auxRoot_inBox U l hlU) (by
    simp only [auxRoot,Fintype.sum_bool,Bool.false_eq_true,↓reduceIte]
    omega)]
  rw [Finset.sum_subtype (p := ValidExcess (widths (fun _ : Fin n => U))) _ (by simp)]
  let j : ValidAssignments U n → (t : Later small s) × DefectProfiles small B s t.val.val σ l :=
    fun q => ⟨e (excessIndex (fun _ : Fin n => U) q.val),
      excessDefectProfile small B s hs σ U l hl0 hlU hB hσ e q.val q.property⟩
  have hj : Function.Injective j := by
    intro q q' he
    apply Subtype.ext
    apply rawExcess_injective small s hs σ U l e
    exact congrArg (fun a : (t : Later small s) × DefectProfiles small B s t.val.val σ l =>
      naturalProfile a.2.val) he
  have hg (a : (t : Later small s) × DefectProfiles small B s t.val.val σ l) :
      0 ≤ hardMarginal small B r c L (naturalProfile a.2.val) := by
    rw [hardMarginal_eq_fibre_card small B r c L _ (naturalProfile_bounded a.2.val)]
    positivity
  have hh := finite_injective_sum_le j hj
    (fun a => hardMarginal small B r c L (naturalProfile a.2.val)) hg
  rw [Fintype.sum_sigma] at hh
  exact hh

end ContingencyTables.ExcessContextProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_PhysicalGraphVertices
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite physical vertices containing every contextual transport leaf -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextEnumeration SmallContextFibres
open PhysicalCompletionFibres LargePairEnumeration BalancedFamily BalancedBox
open IntegerWeightedTransport FirstPaperProfiles ExcessContextProfiles

universe u

variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

noncomputable instance profilesFintype (small : I → J → Bool) (B : I → J → ℕ) :
    Fintype (Profiles small B) := by unfold Profiles; infer_instance

noncomputable def vertices (small : I → J → Bool) (B : I → J → ℕ) : Finset (SmallProfile small) :=
  Finset.univ.image (fun z : Profiles small B => naturalProfile z.val)

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallProfileRepair
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Literal small-profile repair and its typewise inverse -/

namespace ContingencyTables.SmallGraphProfiles

open scoped Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres FirstPaperProfiles

universe u

variable {I J : Type u} [LinearOrder I] [LinearOrder J]

noncomputable def repairedProfile (small : I → J → Bool) (B : I → J → ℕ)
    (z : SmallProfile small) (s t : I×J) : SmallProfile small := fun a =>
  if a.2 then B a.1.val.1 a.1.val.2-repairMatrix (smallView small z false) s t a.1.val.1 a.1.val.2
  else repairMatrix (smallView small z false) s t a.1.val.1 a.1.val.2

/-- Fixed ordered defect labels recover both old views from the literal
repaired profile; this does not forget the column-view complement. -/
theorem repairedProfile_injective (small : I → J → Bool) (B : I → J → ℕ)
    (s t : I×J) (z w : SmallProfile small)
    (hz : ∀ a,z a ≤ B a.1.val.1 a.1.val.2) (hw : ∀ a,w a ≤ B a.1.val.1 a.1.val.2)
    (hdz : IsDefect (smallView small z false) (smallQ small B z) s t)
    (hdw : IsDefect (smallView small w false) (smallQ small B w) s t)
    (he : repairedProfile small B z s t=repairedProfile small B w s t) : z=w := by
  have hx (a : Cells small) : z (a,false)=w (a,false) := by
    have heta : (⟨(a.val.1,a.val.2),a.property⟩ : Cells small)=a := Subtype.ext (Prod.eta a.val)
    have hh := congrArg (fun p : SmallProfile small => (p (a,false):ℤ)) he
    change (repairMatrix (smallView small z false) s t a.val.1 a.val.2:ℤ)=
      (repairMatrix (smallView small w false) s t a.val.1 a.val.2:ℤ) at hh
    rw [repairMatrix_cast hdz,repairMatrix_cast hdw] at hh
    simp only [transferInt,smallView,a.property,dite_eq_left] at hh
    simp only [heta] at hh
    omega
  funext a
  rcases a with ⟨a,b⟩
  cases b
  · exact hx a
  · have hdz' := hdz.2 a.val.1 a.val.2
    have hdw' := hdw.2 a.val.1 a.val.2
    have heta : (⟨(a.val.1,a.val.2),a.property⟩ : Cells small)=a := Subtype.ext (Prod.eta a.val)
    simp only [smallQ,smallView,a.property,dite_eq_left,transferInt] at hdz' hdw'
    simp only [heta,hx a] at hdz' hdw'
    have hzb := hz (a,true)
    have hwb := hw (a,true)
    dsimp only at hzb hwb
    omega

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileRepairProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial binary program for the literal small-profile repair -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped Polynomial

def differenceEntryRealizer : Realizer differenceEntry :=
  composition (pair
    (composition (pair (composition first first) second) (getDFast 0))
    (composition (pair (composition first second) second) (getDFast 0))) subtract

def listDifferenceRealizer : Realizer listDifference :=
  composition (pair identity (composition (composition second listLength) range))
    (mapWith differenceEntryRealizer)

def repairRowsRealizer : Realizer (fun z : RepairInput =>
    listExchange (z.1,(z.2.2.2,z.2.2.1))) :=
  composition (pair first (pair
    (composition (composition second second) second)
    (composition (composition second second) first))) listExchangeRealizer

def repairedViewsRealizer : Realizer repairedViews :=
  pair repairRowsRealizer (composition
    (pair (composition second first) repairRowsRealizer) listDifferenceRealizer)

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallCellCatalogProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Enumerating the actual small cells from binary margins -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped Polynomial

def smallCellTestRealizer : Realizer smallCellTest := by
  let R : Realizer (fun z : CellCatalogInput×(ℕ×ℕ) => z.1.1.1.getD z.2.1 0) :=
    composition (pair (composition (composition first first) first)
      (composition second first)) (getDFast 0)
  let C : Realizer (fun z : CellCatalogInput×(ℕ×ℕ) => z.1.1.2.getD z.2.2 0) :=
    composition (pair (composition (composition first first) second)
      (composition second second)) (getDFast 0)
  let U : Realizer (fun z : CellCatalogInput×(ℕ×ℕ) => z.1.2) := composition first second
  exact (choose (composition (pair R U) less) (constant true)
    (composition (pair C U) less)).congr (by
      intro z
      apply Bool.eq_iff_iff.mpr
      simp only [Function.comp_apply,decide_eq_true_eq,smallCellTest]
      split_ifs <;> simp_all)

def smallCellCatalogRealizer : Realizer smallCellCatalog :=
  composition (pair identity (composition first cellPairsRealizer)) (filterWith smallCellTestRealizer)

theorem mem_smallCellCatalog (r c : List ℕ) (U i j : ℕ) :
    (i,j)∈smallCellCatalog ((r,c),U) ↔
      i < r.length ∧ j < c.length ∧ (r.getD i 0<U ∨ c.getD j 0<U) := by
  simp only [smallCellCatalog,List.mem_filter,mem_cellPairs,smallCellTest,decide_eq_true_eq]
  tauto

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_PhysicalPrefixEnergies
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Physical prefix contexts use each exchange edge at most once -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextEnumeration SmallContextFibres
open PhysicalCompletionFibres LargePairEnumeration IntegerWeightedTransport

universe u

variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

noncomputable def physicalEdges (small : I → J → Bool) (B : I → J → ℕ) :
    Finset (SmallProfile small×SmallProfile small) :=
  ((vertices small B) ×ˢ (vertices small B)).filter (fun p => IntegerExchangeAdjacent p.1 p.2)

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ChoiceContextEnumeration
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Literal finite choice fibres equal the transport child sums -/

namespace ContingencyTables.SmallContextEnumeration

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres
open LargePairEnumeration BalancedEnumeration BalancedFamily
open FirstPaperContextTransport FirstPaperPhysicalMarginal ExcessContextProfiles SmallGraphProfiles
open FiniteExposureVariance
open IntegerWeightedTransport

universe u

variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

def rawChoice (small : I → J → Bool) (U : ℕ) (x : Cells small → Fin (U+1)) :
    SmallProfile small := fun p => if p.2 then U-(x p.1).val else (x p.1).val

end ContingencyTables.SmallContextEnumeration

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallRepairCapacity
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A positive physical defect repairs inside the literal small box -/

namespace ContingencyTables.SmallGraphProfiles

open scoped Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres FirstPaperProfiles
open FirstPaperPhysicalMarginal PaddedCompletions CompletionCounts

universe u

variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

/-- Positive hard marginal supplies an actual full completion. Its
preserved residual bounds force each repaired small entry below U. -/
theorem repair_small_capacity (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (hB : ∀ i j,firstPaperSmall r c U i j=true → B i j=U)
    (z : SmallProfile (firstPaperSmall r c U))
    (hz : ∀ a,z a ≤ B a.1.val.1 a.1.val.2) (s t : I×J)
    (hs : firstPaperSmall r c U s.1 s.2=true) (ht : firstPaperSmall r c U t.1 t.2=true)
    (hd : IsDefect (smallView (firstPaperSmall r c U) z false)
      (smallQ (firstPaperSmall r c U) B z) s t)
    (hf : 0 < hardMarginal (firstPaperSmall r c U) B r c L z) :
    ∀ a : Cells (firstPaperSmall r c U),
      repairMatrix (smallView (firstPaperSmall r c U) z false) s t a.val.1 a.val.2 ≤ B a.val.1 a.val.2 := by
  have hcard : 0 < Fintype.card (CompletionFibre (firstPaperSmall r c U) B r
      (fun i => r i+rowLargeCount (firstPaperSmall r c U) i*L) c
      (fun j => c j+columnLargeCount (firstPaperSmall r c U) j*L) z) := by
    have h := hf
    rw [hardMarginal_eq_fibre_card _ _ _ _ _ z hz] at h
    exact_mod_cast h
  obtain ⟨Z⟩ := Fintype.card_pos_iff.mp hcard
  have hfull := defect_fibre_views Z hs ht hd
  intro a
  have hcap := repairMatrix_small_capacity r c U hfull hs ht Z.property.1 Z.property.2.1
    a.val.1 a.val.2 a.property
  have he : repairMatrix Z.val.val.1 s t a.val.1 a.val.2=
      repairMatrix (smallView (firstPaperSmall r c U) z false) s t a.val.1 a.val.2 := by
    apply repairMatrix_pointwise
    have hx := (Z.property.2.2.1 a.val.1 a.val.2 a.property).1
    simpa only [smallView,a.property,dite_eq_left] using hx
  rw [he] at hcap
  rw [hB _ _ a.property]
  exact Nat.le_of_lt hcap

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallRepairWords
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual positive defects repair to the physical transversal words -/

namespace ContingencyTables.SmallGraphProfiles

open scoped Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres FirstPaperProfiles
open FirstPaperPhysicalMarginal PaddedCompletions CompletionCounts
open SmallContextEnumeration RowMajorEnumeration

universe u

variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

def PositiveDefects (small : I → J → Bool) (B : I → J → ℕ) (r : I → ℕ) (c : J → ℕ) (L : ℕ) :=
  {z : BoundedProfile small B // SingleDefect small B (naturalProfile z) ∧
    0 < hardMarginal small B r c L (naturalProfile z)}

noncomputable instance positiveDefectsFintype (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) : Fintype (PositiveDefects small B r c L) := by
  unfold PositiveDefects
  infer_instance

lemma defect_labels_exist (small : I → J → Bool) (B : I → J → ℕ) (r : I → ℕ) (c : J → ℕ) (L : ℕ)
    (z : PositiveDefects small B r c L) :
    ∃ st : Cells small×Cells small,IsDefect (smallView small (naturalProfile z.val) false)
      (smallQ small B (naturalProfile z.val)) st.1.val st.2.val := by
  obtain ⟨s,t,hs,ht,hd⟩ := z.property.1
  exact ⟨(⟨s,hs⟩,⟨t,ht⟩),hd⟩

noncomputable def defectLabels (small : I → J → Bool) (B : I → J → ℕ) (r : I → ℕ) (c : J → ℕ) (L : ℕ)
    (z : PositiveDefects small B r c L) : Cells small×Cells small :=
  Classical.choose (defect_labels_exist small B r c L z)

lemma defectLabels_spec (small : I → J → Bool) (B : I → J → ℕ) (r : I → ℕ) (c : J → ℕ) (L : ℕ)
    (z : PositiveDefects small B r c L) :
    IsDefect (smallView small (naturalProfile z.val) false) (smallQ small B (naturalProfile z.val))
      (defectLabels small B r c L z).1.val (defectLabels small B r c L z).2.val :=
  Classical.choose_spec (defect_labels_exist small B r c L z)

noncomputable def repairWord (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (hB : ∀ i j,firstPaperSmall r c U i j=true → B i j=U)
    (z : PositiveDefects (firstPaperSmall r c U) B r c L) :
    Fin (Fintype.card (Cells (firstPaperSmall r c U))) → Fin (U+1) := fun j =>
  let st := defectLabels _ B r c L z
  let a := enumeration (firstPaperSmall r c U) j
  ⟨repairMatrix (smallView (firstPaperSmall r c U) (naturalProfile z.val) false)
      st.1.val st.2.val a.val.1 a.val.2,Nat.lt_succ_of_le (by
    exact (repair_small_capacity r c U L B hB (naturalProfile z.val)
      (naturalProfile_bounded z.val) st.1.val st.2.val st.1.property st.2.property
      (defectLabels_spec _ B r c L z) z.property.2 a).trans_eq (hB _ _ a.property))⟩

lemma repairWord_profile (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (hB : ∀ i j,firstPaperSmall r c U i j=true → B i j=U)
    (z : PositiveDefects (firstPaperSmall r c U) B r c L) :
    rawChoice (firstPaperSmall r c U) U
      (wordChoices (firstPaperSmall r c U) U (repairWord r c U L B hB z))=
      repairedProfile (firstPaperSmall r c U) B (naturalProfile z.val)
        (defectLabels _ B r c L z).1.val (defectLabels _ B r c L z).2.val := by
  funext p
  rcases p with ⟨a,b⟩
  have he : (wordChoices (firstPaperSmall r c U) U (repairWord r c U L B hB z) a).val=
      repairMatrix (smallView (firstPaperSmall r c U) (naturalProfile z.val) false)
        (defectLabels _ B r c L z).1.val (defectLabels _ B r c L z).2.val a.val.1 a.val.2 := by
    change repairMatrix (smallView (firstPaperSmall r c U) (naturalProfile z.val) false)
      (defectLabels _ B r c L z).1.val (defectLabels _ B r c L z).2.val
      (enumeration (firstPaperSmall r c U) ((enumeration (firstPaperSmall r c U)).symm a)).val.1
      (enumeration (firstPaperSmall r c U) ((enumeration (firstPaperSmall r c U)).symm a)).val.2=_
    rw [Equiv.apply_symm_apply]
  cases b
  · exact he
  · change U-_ = B a.val.1 a.val.2-_
    rw [he,hB _ _ a.property]

theorem repairWord_type_injective (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (hB : ∀ i j,firstPaperSmall r c U i j=true → B i j=U) :
    Function.Injective (fun z : PositiveDefects (firstPaperSmall r c U) B r c L =>
      (defectLabels _ B r c L z,repairWord r c U L B hB z)) := by
  intro x y he
  have hl := congrArg Prod.fst he
  dsimp only at hl
  have hr := congrArg (fun a => rawChoice (firstPaperSmall r c U) U
    (wordChoices (firstPaperSmall r c U) U a)) (congrArg Prod.snd he)
  rw [repairWord_profile,repairWord_profile,hl] at hr
  have hdx := defectLabels_spec (firstPaperSmall r c U) B r c L x
  rw [hl] at hdx
  apply Subtype.ext
  apply naturalProfile_injective (firstPaperSmall r c U) B
  exact repairedProfile_injective (firstPaperSmall r c U) B _ _ _ _
    (naturalProfile_bounded x.val) (naturalProfile_bounded y.val) hdx
    (defectLabels_spec _ B r c L y) hr

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_RawSmallChoiceProperties
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Balanced words are literal bounded physical transversal profiles -/

namespace ContingencyTables.SmallContextEnumeration

open scoped Classical
open SmallContextCoordinates SmallContextFibres SmallGraphProfiles

universe u

variable {I J : Type u}

lemma rawChoice_bounded (small : I → J → Bool) (B : I → J → ℕ) (U : ℕ)
    (hB : ∀ i j,small i j=true → B i j=U) (x : Cells small → Fin (U+1)) :
    ∀ a,rawChoice small U x a ≤ B a.1.val.1 a.1.val.2 :=
  naturalProfile_bounded (choiceProfile small B U hB x)

lemma rawChoice_balanced (small : I → J → Bool) (B : I → J → ℕ) (U : ℕ)
    (hB : ∀ i j,small i j=true → B i j=U) (x : Cells small → Fin (U+1)) :
    Balanced small B (rawChoice small U x) := choiceProfile_balanced small B U hB x

lemma rawChoice_injective (small : I → J → Bool) (U : ℕ) : Function.Injective (rawChoice small U) := by
  intro x y he
  funext a
  exact Fin.ext (congrFun he (a,false))

end ContingencyTables.SmallContextEnumeration

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_PhysicalRepairGraph
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual small graph contains its exchanges and designated repairs -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres FirstPaperProfiles
open FirstPaperPhysicalMarginal PaddedCompletions CompletionCounts
open SmallContextEnumeration RowMajorEnumeration IntegerWeightedTransport

universe u

variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

noncomputable def repairEdges (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (hB : ∀ i j,firstPaperSmall r c U i j=true → B i j=U) :
    Finset (SmallProfile (firstPaperSmall r c U)×SmallProfile (firstPaperSmall r c U)) :=
  let target := fun z => rawChoice (firstPaperSmall r c U) U
    (wordChoices (firstPaperSmall r c U) U (repairWord r c U L B hB z))
  (Finset.univ.image (fun z : PositiveDefects (firstPaperSmall r c U) B r c L =>
    (naturalProfile z.val,target z))) ∪
  (Finset.univ.image (fun z : PositiveDefects (firstPaperSmall r c U) B r c L =>
    (target z,naturalProfile z.val)))

noncomputable def fullEdges (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (hB : ∀ i j,firstPaperSmall r c U i j=true → B i j=U) :=
  physicalEdges (firstPaperSmall r c U) B ∪ repairEdges r c U L B hB

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallBalancedEncoding
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Every bounded balanced small profile has its literal word encoding -/

namespace ContingencyTables.SmallGraphProfiles

open scoped Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres FirstPaperProfiles
open SmallContextEnumeration RowMajorEnumeration

universe u

variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

noncomputable def balancedChoices (small : I → J → Bool) (B : I → J → ℕ) (U : ℕ)
    (hB : ∀ i j,small i j=true → B i j=U) (z : BoundedProfile small B) :
    Cells small → Fin (U+1) := fun a =>
  ⟨(z (a,false)).val,(z (a,false)).isLt.trans_le (by rw [hB _ _ a.property])⟩

omit [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J] in
lemma balancedChoices_profile (small : I → J → Bool) (B : I → J → ℕ) (U : ℕ)
    (hB : ∀ i j,small i j=true → B i j=U) (z : BoundedProfile small B)
    (hz : Balanced small B (naturalProfile z)) :
    rawChoice small U (balancedChoices small B U hB z)=naturalProfile z := by
  funext p
  rcases p with ⟨a,b⟩
  cases b
  · rfl
  · have h := hz a.val.1 a.val.2
    have heta : (⟨(a.val.1,a.val.2),a.property⟩ : Cells small)=a := Subtype.ext (Prod.eta a.val)
    simp only [smallView,smallQ,a.property,dite_eq_left] at h
    rw [heta] at h
    dsimp only [naturalProfile] at h
    have hy := (z (a,true)).isLt
    have hb := hB _ _ a.property
    change U-(z (a,false)).val=(z (a,true)).val
    change (z (a,true)).val < B a.val.1 a.val.2+1 at hy
    omega

noncomputable def balancedWord (small : I → J → Bool) (B : I → J → ℕ) (U : ℕ)
    (hB : ∀ i j,small i j=true → B i j=U) (z : BoundedProfile small B) :
    Fin (Fintype.card (Cells small)) → Fin (U+1) :=
  (wordChoices small U).symm (balancedChoices small B U hB z)

lemma balancedWord_profile (small : I → J → Bool) (B : I → J → ℕ) (U : ℕ)
    (hB : ∀ i j,small i j=true → B i j=U) (z : BoundedProfile small B)
    (hz : Balanced small B (naturalProfile z)) :
    rawChoice small U (wordChoices small U (balancedWord small B U hB z))=naturalProfile z := by
  unfold balancedWord
  rw [Equiv.apply_symm_apply]
  exact balancedChoices_profile small B U hB z hz

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallProfileEncoding
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The variance encoding retains exactly the positive physical states -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres FirstPaperProfiles
open FirstPaperPhysicalMarginal SmallContextEnumeration RowMajorEnumeration FiniteExposureVariance

universe u

variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

abbrev VarianceEncoding (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L U : ℕ) :=
  (Fin (Fintype.card (Cells small)) → Fin (U+1)) ⊕ PositiveDefects small B r c L

noncomputable def encodeProfile (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L U : ℕ)
    (hB : ∀ i j,small i j=true → B i j=U) :
    VarianceEncoding small B r c L U → Profiles small B
  | .inl x => ⟨choiceProfile small B U hB (wordChoices small U x),
      Or.inl (choiceProfile_balanced small B U hB _)⟩
  | .inr z => ⟨z.val,Or.inr z.property.1⟩

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperPhysicalVariance
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The Poincare inequality on the actual feasible small states -/

namespace ContingencyTables.SmallGraphProfiles

open scoped Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres FirstPaperProfiles
open FirstPaperPhysicalMarginal CompletionCounts SmallContextEnumeration FiniteExposureVariance

universe u

variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

noncomputable instance physicalStatesFintype (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) : Fintype (PhysicalStates small B r c L) := by
  unfold PhysicalStates
  infer_instance

lemma physicalProfile_injective (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) :
    Function.Injective (physicalProfile small B r c L) := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact naturalProfile_injective small B h

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_PhysicalResidualMargins
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
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

lemma physical_residual_totals (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ)
    (z : PhysicalStates small B r c L)
    (hcap : ∀ i j,small i j=false → (∑ k,residualRows small B r c L z k) ≤ B i j) :
    (∑ i,residualRows small B r c L z i)=∑ j,residualColumns small B r c L z j := by
  obtain ⟨A⟩ := physical_completions_nonempty small B r c L z hcap
  calc
    _ = ∑ i,∑ j,A.val.val i j := by simp_rw [A.val.property.1]
    _ = ∑ j,∑ i,A.val.val i j := Finset.sum_comm
    _ = _ := by simp_rw [A.val.property.2]

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_PhysicalPaperCapacity
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The manuscript capacity bounds every physical residual completion -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open PhysicalCompletionFibres FirstPaperProfiles FirstPaperPhysicalMarginal CompletionCounts

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

lemma physical_paper_capacity (small : I → J → Bool) (r : I → ℕ) (c : J → ℕ)
    (d L U : ℕ) (hd : Fintype.card I*Fintype.card J ≤ d)
    (z : PhysicalStates small (paperCapacity small r d L U) r c L) :
    ∀ i j,small i j=false →
      (∑ k,residualRows small (paperCapacity small r d L U) r c L z k) ≤
        paperCapacity small r d L U i j :=
  paper_capacity_excludes_none small
    (smallView small (physicalProfile small (paperCapacity small r d L U) r c L z) false)
    r d L U hd

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_PhysicalGraphDegree
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The manuscript's finite neighbor bound on the physical small graph -/

namespace ContingencyTables.SmallGraphProfiles

open scoped Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres FirstPaperProfiles
open CompletionCounts SmallContextEnumeration RowMajorEnumeration IntegerWeightedTransport

universe u

variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

noncomputable def fullNeighbors (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (hB : ∀ i j,firstPaperSmall r c U i j=true → B i j=U)
    (v : SmallProfile (firstPaperSmall r c U)) :=
  ((fullEdges r c U L B hB).filter (fun p => p.1=v)).image Prod.snd

lemma fullNeighbors_subset (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (hB : ∀ i j,firstPaperSmall r c U i j=true → B i j=U)
    (v : SmallProfile (firstPaperSmall r c U)) :
    fullNeighbors r c U L B hB v ⊆ exchangeCandidates v ∪
      repairNeighbors
        (fun z : PositiveDefects (firstPaperSmall r c U) B r c L => naturalProfile z.val)
        (fun z => rawChoice (firstPaperSmall r c U) U
          (wordChoices (firstPaperSmall r c U) U (repairWord r c U L B hB z))) v := by
  intro y hy
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨he,hv⟩ := Finset.mem_filter.mp hp
  rcases Finset.mem_union.mp he with he|he
  · apply Finset.mem_union_left
    have ha := (Finset.mem_filter.mp he).2
    rw [hv] at ha
    exact adjacent_mem_candidates ha
  · apply Finset.mem_union_right
    rcases Finset.mem_union.mp he with he|he
    · obtain ⟨z,_,hz⟩ := Finset.mem_image.mp he
      subst p
      exact mem_repairNeighbors_forward _ _ v z hv
    · obtain ⟨z,_,hz⟩ := Finset.mem_image.mp he
      subst p
      exact mem_repairNeighbors_reverse _ _ v z hv

/-- Counting distinct neighbors, with repeated exchange/repair edges
removed by the finite-set union, gives exactly the source bound. -/
theorem fullNeighbors_card_le (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (hB : ∀ i j,firstPaperSmall r c U i j=true → B i j=U)
    (v : SmallProfile (firstPaperSmall r c U)) :
    (fullNeighbors r c U L B hB v).card ≤ 5*(Fintype.card (Cells (firstPaperSmall r c U)))^2+1 := by
  let x := fun z : PositiveDefects (firstPaperSmall r c U) B r c L => naturalProfile z.val
  let y := fun z : PositiveDefects (firstPaperSmall r c U) B r c L =>
    rawChoice (firstPaperSmall r c U) U (wordChoices (firstPaperSmall r c U) U (repairWord r c U L B hB z))
  have hx : Function.Injective x := by
    intro a b he
    apply Subtype.ext
    exact naturalProfile_injective _ B he
  have hy : Function.Injective (fun z => (defectLabels _ B r c L z,y z)) := by
    intro a b he
    have hl := congrArg Prod.fst he
    have hr := congrArg Prod.snd he
    dsimp only at hl hr
    have hw : repairWord r c U L B hB a=repairWord r c U L B hB b :=
      (wordChoices (firstPaperSmall r c U) U).injective
        (rawChoice_injective (firstPaperSmall r c U) U hr)
    exact repairWord_type_injective r c U L B hB (Prod.ext hl hw)
  have hr := repairNeighbors_card_le x y hx (defectLabels _ B r c L) hy v
  have hc := exchangeCandidates_card_le v
  have hs := (Finset.card_le_card (fullNeighbors_subset r c U L B hB v)).trans (Finset.card_union_le _ _)
  change (fullNeighbors r c U L B hB v).card ≤ (exchangeCandidates v).card+(repairNeighbors x y v).card at hs
  have hcoord : Fintype.card (LargePairEnumeration.SmallView (fun a : I×J => firstPaperSmall r c U a.1 a.2))=
      2*Fintype.card (Cells (firstPaperSmall r c U)) := by
    change Fintype.card (Cells (firstPaperSmall r c U)×Bool)=_
    rw [Fintype.card_prod,Fintype.card_bool]
    omega
  rw [Fintype.card_prod] at hr
  change (repairNeighbors x y v).card ≤ _ at hr
  rw [hcoord] at hc
  nlinarith

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_PhysicalSmallGraph
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite graph on positive-weight physical states -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres FirstPaperProfiles
open CompletionCounts SmallContextEnumeration IntegerWeightedTransport

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

noncomputable def physicalAdjacent (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (hB : ∀ i j,firstPaperSmall r c U i j=true → B i j=U)
    (x y : PhysicalStates (firstPaperSmall r c U) B r c L) : Prop :=
  (physicalProfile _ B r c L x,physicalProfile _ B r c L y) ∈ fullEdges r c U L B hB

lemma physicalAdjacent_degree (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (hB : ∀ i j,firstPaperSmall r c U i j=true → B i j=U)
    (x : PhysicalStates (firstPaperSmall r c U) B r c L) :
    (Finset.univ.filter (physicalAdjacent r c U L B hB x)).card ≤
      5*(Fintype.card (Cells (firstPaperSmall r c U)))^2+1 := by
  let p := physicalProfile (firstPaperSmall r c U) B r c L
  have hsub : (Finset.univ.filter (physicalAdjacent r c U L B hB x)).image p ⊆
      fullNeighbors r c U L B hB (p x) := by
    intro y hy
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_image.mpr ⟨(p x,p z),Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hz).2,rfl⟩,rfl⟩
  calc
    _ = ((Finset.univ.filter (physicalAdjacent r c U L B hB x)).image p).card :=
      (Finset.card_image_of_injective _ (physicalProfile_injective _ B r c L)).symm
    _ ≤ (fullNeighbors r c U L B hB (p x)).card := Finset.card_le_card hsub
    _ ≤ _ := fullNeighbors_card_le r c U L B hB (p x)

lemma physicalAdjacent_degree_allowance (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (hB : ∀ i j,firstPaperSmall r c U i j=true → B i j=U)
    (x : PhysicalStates (firstPaperSmall r c U) B r c L) :
    (Finset.univ.filter (physicalAdjacent r c U L B hB x)).card ≤
      5*(dimensionAllowance (I := I) (J := J))^2+1 := by
  have hc : Fintype.card (Cells (firstPaperSmall r c U)) ≤ dimensionAllowance (I := I) (J := J) := by
    calc
      _ ≤ Fintype.card (I×J) := Fintype.card_subtype_le _
      _ = Fintype.card I*Fintype.card J := Fintype.card_prod _ _
      _ ≤ _ := dimension_le_allowance
  exact (physicalAdjacent_degree r c U L B hB x).trans (by gcongr)

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ReferenceCompletionBlock
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
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

lemma reference_totals (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U)
    (z : PhysicalStates (firstPaperSmall r c U) B r c L)
    (hcap : ∀ i j,firstPaperSmall r c U i j=false →
      (∑ k,residualRows (firstPaperSmall r c U) B r c L z k) ≤ B i j) :
    (∑ i,referenceRows r c U L B i₀ z i)=∑ j,referenceColumns r c U L B j₀ z j := by
  unfold referenceRows referenceColumns
  rw [(Equiv.optionSubtypeNe i₀).sum_comp
    (fun i : LargeRows r U => residualRows (firstPaperSmall r c U) B r c L z i.val),
    (Equiv.optionSubtypeNe j₀).sum_comp
    (fun j : LargeColumns c U => residualColumns (firstPaperSmall r c U) B r c L z j.val)]
  have hr : (∑ i : LargeRows r U,residualRows (firstPaperSmall r c U) B r c L z i.val)=
      ∑ i,residualRows (firstPaperSmall r c U) B r c L z i := by
    convert sum_subtype_eq_of_zero (fun i => U ≤ r i)
      (residualRows (firstPaperSmall r c U) B r c L z)
      (physical_residual_row_zero r c U L B z hcap) using 1
    all_goals try with_reducible_and_instances rfl
    congr 2
    exact Subsingleton.elim _ _
  have hc : (∑ j : LargeColumns c U,residualColumns (firstPaperSmall r c U) B r c L z j.val)=
      ∑ j,residualColumns (firstPaperSmall r c U) B r c L z j := by
    convert sum_subtype_eq_of_zero (fun j => U ≤ c j)
      (residualColumns (firstPaperSmall r c U) B r c L z)
      (physical_residual_column_zero r c U L B z hcap) using 1
    all_goals try with_reducible_and_instances rfl
    congr 2
    exact Subsingleton.elim _ _
  rw [hr,hc]
  exact physical_residual_totals _ B r c L z hcap

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ReferenceCompletionBounds
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Padding and dimension bounds for the actual reference completion block -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open PhysicalCompletionFibres FirstPaperPhysicalMarginal CompletionCounts PaddedCompletions

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

lemma large_row_padding (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (z : PhysicalStates (firstPaperSmall r c U) B r c L)
    (i : LargeRows r U) (j : LargeColumns c U) :
    L ≤ residualRows (firstPaperSmall r c U) B r c L z i.val := by
  have hs := (firstPaperSmall_false_iff r c U i.val j.val).mpr ⟨i.property,j.property⟩
  have hh := Finset.single_le_sum
    (f := fun j' => if firstPaperSmall r c U i.val j' then 0 else 1)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ j.val)
  have hc : 1 ≤ rowLargeCount (firstPaperSmall r c U) i.val := by
    simpa only [rowLargeCount,hs,Bool.false_eq_true,ite_false] using hh
  unfold residualRows
  nlinarith

lemma large_column_padding (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (z : PhysicalStates (firstPaperSmall r c U) B r c L)
    (i : LargeRows r U) (j : LargeColumns c U) :
    L ≤ residualColumns (firstPaperSmall r c U) B r c L z j.val := by
  have hs := (firstPaperSmall_false_iff r c U i.val j.val).mpr ⟨i.property,j.property⟩
  have hh := Finset.single_le_sum
    (f := fun i' => if firstPaperSmall r c U i' j.val then 0 else 1)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i.val)
  have hc : 1 ≤ columnLargeCount (firstPaperSmall r c U) j.val := by
    simpa only [columnLargeCount,hs,Bool.false_eq_true,ite_false] using hh
  unfold residualColumns
  nlinarith

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperSmallChain
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal first-paper completion chain has the stated Poincare bound -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open CommonBasesFPRAS PhysicalCompletionFibres FirstPaperPhysicalMarginal CompletionCounts
open CompletionTranslation FiniteExposureVariance

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

/-- Keep one public enumeration instance for the paper's state type, so
rational laws and generic finite kernels share the same index. -/
noncomputable instance paperStatesFintype (r : I → ℕ) (c : J → ℕ) :
    Fintype (PaperStates r c) :=
  physicalStatesFintype (paperSmall r c) (stateCapacity r c) r c
    ((dimensionAllowance (I := I) (J := J))^12)

noncomputable def stateWeight (r : I → ℕ) (c : J → ℕ) (z : PaperStates r c) : ℝ :=
  hardMarginal (paperSmall r c) (stateCapacity r c) r c
    ((dimensionAllowance (I := I) (J := J))^12)
    (physicalProfile _ (stateCapacity r c) r c _ z)

lemma stateWeight_positive (r : I → ℕ) (c : J → ℕ) (z : PaperStates r c) :
    0 < stateWeight r c z := z.property

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperJointLaw
attribute [-instance] _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniformity of the actual state/completion joint law -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open PhysicalCompletionFibres FirstPaperPhysicalMarginal CompletionCounts PaddedCompletions
open ResidualMixture FirstSuccess CompletionTranslation SmallContextFibres

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

abbrev PaperFibre (r : I → ℕ) (c : J → ℕ) (z : PaperStates r c) :=
  CompletionFibre (paperSmall r c) (stateCapacity r c) r
    (fun i => r i+rowLargeCount (paperSmall r c) i*((dimensionAllowance (I := I) (J := J))^12)) c
    (fun j => c j+columnLargeCount (paperSmall r c) j*((dimensionAllowance (I := I) (J := J))^12))
    (physicalProfile _ (stateCapacity r c) r c _ z)

noncomputable instance paperFibreNonempty (r : I → ℕ) (c : J → ℕ) (z : PaperStates r c) :
    Nonempty (PaperFibre r c z) := by
  apply Fintype.card_pos_iff.mp
  have hp := stateWeight_positive r c z
  change 0 < hardMarginal _ _ _ _ _ _ at hp
  rw [hardMarginal_eq_fibre_card (paperSmall r c) (stateCapacity r c) r c
    ((dimensionAllowance (I := I) (J := J))^12)
    (physicalProfile _ (stateCapacity r c) r c _ z) (naturalProfile_bounded z.val.val)] at hp
  exact_mod_cast hp

abbrev PaperStateJoint (r : I → ℕ) (c : J → ℕ) := (z : PaperStates r c) × PaperFibre r c z

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_CompletionFibreTransport
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Changing a retained profile by an equality keeps the literal views -/

namespace ContingencyTables.PhysicalCompletionFibres

variable {I J : Type*} [Fintype I] [Fintype J]
variable {small : I → J → Bool} {B : I → J → ℕ}
variable {r rbar : I → ℕ} {c cbar : J → ℕ} {z w : SmallProfile small}

def withProfile (h : z=w) (Z : CompletionFibre small B r rbar c cbar z) :
    CompletionFibre small B r rbar c cbar w :=
  ⟨Z.val,by rw [←h]; exact Z.property⟩

lemma withProfile_val (h : z=w) (Z : CompletionFibre small B r rbar c cbar z) :
    (withProfile h Z).val=Z.val := rfl

end ContingencyTables.PhysicalCompletionFibres

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_BalancedCompletionMass
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Balanced profile/completion pairs inject into padded tables -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open PhysicalCompletionFibres FirstPaperPhysicalMarginal FirstPaperProfiles
open SmallContextFibres SmallContextCoordinates SmallContextEnumeration RowMajorEnumeration
open PaddedCompletions CompletionCounts

universe u
variable {I J : Type u} [Fintype I] [Fintype J]

lemma balanced_fibre_views_eq (small : I → J → Bool) (B : I → J → ℕ)
    (r rbar : I → ℕ) (c cbar : J → ℕ) (z : SmallProfile small)
    (hz : Balanced small B z) (Z : CompletionFibre small B r rbar c cbar z) :
    Z.val.val.1=Z.val.val.2 := by
  funext i j
  cases hs : small i j with
  | false => exact Z.property.2.2.2.1 i j hs
  | true =>
    rw [(Z.property.2.2.1 i j hs).1,(Z.property.2.2.1 i j hs).2]
    have h := hz i j
    simpa only [smallView,smallQ,hs,dite_eq_left] using h

noncomputable def balancedFibreTable (small : I → J → Bool) (B : I → J → ℕ)
    (r rbar : I → ℕ) (c cbar : J → ℕ) (z : SmallProfile small)
    (hz : Balanced small B z) (Z : CompletionFibre small B r rbar c cbar z) :
    Table rbar cbar :=
  ⟨Z.val.val.1,Z.val.property.1,by
    rw [balanced_fibre_views_eq small B r rbar c cbar z hz Z]
    exact Z.val.property.2⟩

variable [LinearOrder I] [LinearOrder J]

abbrev BalancedJoint (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L U : ℕ) :=
  (a : Fin (Fintype.card (Cells small)) → Fin (U+1)) ×
    CompletionFibre small B r (fun i => r i+rowLargeCount small i*L)
      c (fun j => c j+columnLargeCount small j*L) (rawChoice small U (wordChoices small U a))

noncomputable def balancedJointTable (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L U : ℕ)
    (hB : ∀ i j,small i j=true → B i j=U) (a : BalancedJoint small B r c L U) :
    Table (fun i => r i+rowLargeCount small i*L) (fun j => c j+columnLargeCount small j*L) :=
  balancedFibreTable small B r _ c _ _ (rawChoice_balanced small B U hB _) a.2

lemma balancedJointTable_injective (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L U : ℕ)
    (hB : ∀ i j,small i j=true → B i j=U) :
    Function.Injective (balancedJointTable small B r c L U hB) := by
  intro a b hab
  apply fibre_projection_injective small B r _ c _
    (fun a => rawChoice small U (wordChoices small U a))
    ((rawChoice_injective small U).comp (wordChoices small U).injective)
    (fun a => rawChoice_bounded small B U hB _) 
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg Subtype.val hab
  · have ha := balanced_fibre_views_eq small B r _ c _ _ (rawChoice_balanced small B U hB _) a.2
    have hb := balanced_fibre_views_eq small B r _ c _ _ (rawChoice_balanced small B U hB _) b.2
    rw [← ha,← hb]
    exact congrArg Subtype.val hab

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_BalancedJointConstruction
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Recover the unique balanced joint object from its full padded table -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open PhysicalCompletionFibres FirstPaperPhysicalMarginal FirstPaperProfiles
open SmallContextFibres SmallContextCoordinates SmallContextEnumeration RowMajorEnumeration
open PaddedCompletions CompletionCounts

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

lemma tableWord_false (small : I → J → Bool) (U : ℕ) (Y : I → J → ℕ)
    (hY : ∀ i j,small i j=true → Y i j ≤ U) (a : Cells small) :
    rawChoice small U (wordChoices small U (tableWord small U Y hY)) (a,false)=Y a.val.1 a.val.2 := by
  unfold tableWord
  rw [Equiv.apply_symm_apply]
  rfl

lemma tableWord_true (small : I → J → Bool) (U : ℕ) (Y : I → J → ℕ)
    (hY : ∀ i j,small i j=true → Y i j ≤ U) (a : Cells small) :
    rawChoice small U (wordChoices small U (tableWord small U Y hY)) (a,true)=U-Y a.val.1 a.val.2 := by
  unfold tableWord
  rw [Equiv.apply_symm_apply]
  rfl

/-- Residual feasibility and the literal small-cell bound suffice to
construct the balanced profile together with every retained large entry. -/
noncomputable def jointOfTable (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L U : ℕ)
    (hB : ∀ i j,small i j=true → B i j=U)
    (Y : Table (fun i => r i+rowLargeCount small i*L) (fun j => c j+columnLargeCount small j*L))
    (hY : ∀ i j,small i j=true → Y.val i j ≤ U)
    (hR : ∀ i,smallRow small Y.val i ≤ r i)
    (hC : ∀ j,smallColumnView small Y.val j ≤ c j)
    (hlarge : ∀ i j,small i j=false → Y.val i j ≤ B i j) : BalancedJoint small B r c L U :=
  ⟨tableWord small U Y.val hY,
    ⟨⟨(Y.val,Y.val),Y.property⟩,hR,hC,by
      intro i j hs
      constructor
      · exact (tableWord_false small U Y.val hY ⟨(i,j),hs⟩).symm
      · rw [tableWord_true,hB i j hs,Nat.sub_sub_self (hY i j hs)]
    ,fun _ _ _ => rfl,hlarge⟩⟩

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_OriginalBalancedJoint
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Every original table supplies its literal balanced padded joint object -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open PhysicalCompletionFibres FirstPaperPhysicalMarginal FirstPaperProfiles
open SmallContextFibres SmallContextCoordinates SmallContextEnumeration RowMajorEnumeration
open PaddedCompletions CompletionCounts

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

noncomputable def paperOriginalJoint (r : I → ℕ) (c : J → ℕ) (X : Table r c) :
    BalancedJoint (paperSmall r c) (stateCapacity r c) r c
      ((dimensionAllowance (I := I) (J := J))^12) ((dimensionAllowance (I := I) (J := J))^20) := by
  let d := dimensionAllowance (I := I) (J := J)
  let small := paperSmall r c
  let Y := paddedOriginal small (d^12) X
  have hR := paddedOriginal_small_rows small (d^12) X
  have hC := paddedOriginal_small_columns small (d^12) X
  refine jointOfTable small (stateCapacity r c) r c (d^12) (d^20)
    (stateCapacity_small r c) Y ?_ hR hC ?_
  · intro i j hs
    change X.val i j+(if small i j then 0 else d^12) ≤ d^20
    simpa only [hs,ite_true, if_true,Nat.add_zero] using original_small_entry_le r c (d^20) X i j hs
  · intro i j _
    exact paper_residual_capacity r c d (d^12) (d^20) dimension_le_allowance ⟨Y,hR,hC⟩ i j

lemma paperOriginalJoint_projection (r : I → ℕ) (c : J → ℕ) (X : Table r c) :
    balancedJointTable (paperSmall r c) (stateCapacity r c) r c
      ((dimensionAllowance (I := I) (J := J))^12) ((dimensionAllowance (I := I) (J := J))^20)
      (stateCapacity_small r c) (paperOriginalJoint r c X)=
        paddedOriginal (paperSmall r c) ((dimensionAllowance (I := I) (J := J))^12) X := by
  apply Subtype.ext
  rfl

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_SuccessfulJointBijection
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal successful balanced pairs are exactly the original tables -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open PhysicalCompletionFibres FirstPaperPhysicalMarginal PaddedCompletions CompletionCounts

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

abbrev PaperJoint (r : I → ℕ) (c : J → ℕ) :=
  BalancedJoint (paperSmall r c) (stateCapacity r c) r c
    ((dimensionAllowance (I := I) (J := J))^12) ((dimensionAllowance (I := I) (J := J))^20)

noncomputable def jointTable (r : I → ℕ) (c : J → ℕ) (a : PaperJoint r c) :=
  balancedJointTable (paperSmall r c) (stateCapacity r c) r c
    ((dimensionAllowance (I := I) (J := J))^12) ((dimensionAllowance (I := I) (J := J))^20)
    (stateCapacity_small r c) a

abbrev SuccessfulJoint (r : I → ℕ) (c : J → ℕ) :=
  {a : PaperJoint r c // ∀ i j,paperSmall r c i j=false →
    (dimensionAllowance (I := I) (J := J))^12 ≤ (jointTable r c a).val i j}

noncomputable def originalSuccessfulJoint (r : I → ℕ) (c : J → ℕ) (X : Table r c) :
    SuccessfulJoint r c := by
  refine ⟨paperOriginalJoint r c X,?_⟩
  intro i j hs
  unfold jointTable
  rw [paperOriginalJoint_projection]
  simp only [paddedOriginal,hs,Bool.false_eq_true,ite_false]
  omega

noncomputable def unpadSuccessfulJoint (r : I → ℕ) (c : J → ℕ)
    (a : SuccessfulJoint r c) : Table r c := by
  let L := (dimensionAllowance (I := I) (J := J))^12
  let P := largePadding (paperLarge r c) L
  let Y := jointTable r c a.val
  have hm : HasMargins Y.val (paddedRows r P) (paddedColumns c P) := by
    dsimp only [P,paperLarge]
    rw [large_padding_rows,large_padding_columns]
    exact Y.property
  exact unpadTable P ⟨Y.val,hm⟩ (by
    intro i j
    cases hs : paperSmall r c i j with
    | false => simpa only [P,paperLarge,largePadding,Finset.mem_filter,Finset.mem_univ,
        true_and,hs,ite_true, if_true] using a.property i j hs
    | true => simp [P,paperLarge,largePadding,hs])

lemma unpadSuccessfulJoint_val (r : I → ℕ) (c : J → ℕ) (a : SuccessfulJoint r c) (i : I) (j : J) :
    (unpadSuccessfulJoint r c a).val i j=(jointTable r c a.val).val i j-
      largePadding (paperLarge r c) ((dimensionAllowance (I := I) (J := J))^12) i j := rfl

/-- Each success produces exactly one original table, and every original
table has exactly one successful state/completion preimage. -/
noncomputable def successfulJointEquiv (r : I → ℕ) (c : J → ℕ) :
    Table r c ≃ SuccessfulJoint r c where
  toFun := originalSuccessfulJoint r c
  invFun := unpadSuccessfulJoint r c
  left_inv X := by
    apply Subtype.ext
    funext i j
    rw [unpadSuccessfulJoint_val]
    change (jointTable r c (paperOriginalJoint r c X)).val i j-_=X.val i j
    unfold jointTable
    rw [paperOriginalJoint_projection]
    cases hs : paperSmall r c i j <;> simp [paddedOriginal,paperLarge,largePadding,hs]
  right_inv a := by
    apply Subtype.ext
    apply balancedJointTable_injective (paperSmall r c) (stateCapacity r c) r c
      ((dimensionAllowance (I := I) (J := J))^12) ((dimensionAllowance (I := I) (J := J))^20)
      (stateCapacity_small r c)
    change jointTable r c (paperOriginalJoint r c (unpadSuccessfulJoint r c a))=jointTable r c a.val
    unfold jointTable at ⊢
    rw [paperOriginalJoint_projection]
    apply Subtype.ext
    funext i j
    change (unpadSuccessfulJoint r c a).val i j+
      (if paperSmall r c i j then 0 else (dimensionAllowance (I := I) (J := J))^12)=_
    rw [unpadSuccessfulJoint_val]
    cases hs : paperSmall r c i j with
    | false =>
      have ha := a.property i j hs
      simpa only [paperLarge,largePadding,Finset.mem_filter,Finset.mem_univ,true_and,
        hs,ite_true, if_true,Bool.false_eq_true,ite_false,jointTable] using Nat.sub_add_cancel ha
    | true => simp [paperLarge,largePadding,hs,jointTable]

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperSuccessEvent
attribute [-instance] _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual joint-law success event counts every original table once -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open PhysicalCompletionFibres FirstPaperPhysicalMarginal FirstPaperProfiles
open SmallContextFibres SmallContextCoordinates SmallContextEnumeration RowMajorEnumeration
open PaddedCompletions CompletionCounts

noncomputable section
universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]
variable (r : I → ℕ) (c : J → ℕ)

local notation "d" => dimensionAllowance (I := I) (J := J)
local notation "small" => paperSmall r c
local notation "B" => stateCapacity r c

/-- Forget the redundant small-profile coordinate while retaining both
full margin views. This projection is injective on all actual joint pairs. -/
def stateJointProjection (a : PaperStateJoint r c) := a.2.val

lemma stateJointProjection_injective : Function.Injective (stateJointProjection r c) :=
  fibre_projection_injective small B r _ c _ (physicalProfile small B r c (d^12))
    (physicalProfile_injective small B r c (d^12))
    (fun z => naturalProfile_bounded z.val.val)

def paperJointState (a : PaperJoint r c) : PaperStates r c := by
  have hp : 0 < hardMarginal small B r c (d^12)
      (rawChoice small (d^20) (wordChoices small (d^20) a.1)) := by
    rw [hardMarginal_eq_fibre_card small B r c (d^12) _
      (rawChoice_bounded small B (d^20) (stateCapacity_small r c) _)]
    exact_mod_cast Fintype.card_pos_iff.mpr (⟨a.2⟩ : Nonempty _)
  exact ⟨encodeProfile small B r c (d^12) (d^20) (stateCapacity_small r c) (.inl a.1),hp⟩

def paperJointEmbedding (a : PaperJoint r c) : PaperStateJoint r c :=
  ⟨paperJointState r c a,a.2⟩

lemma paperJointEmbedding_injective : Function.Injective (paperJointEmbedding r c) := by
  intro a b hab
  apply balancedJointTable_injective small B r c (d^12) (d^20) (stateCapacity_small r c)
  apply Subtype.ext
  exact congrArg (fun z : PaperStateJoint r c => z.2.val.val.1) hab

lemma paperJointEmbedding_balanced (a : PaperJoint r c) :
    Balanced small B (physicalProfile small B r c (d^12) (paperJointEmbedding r c a).1) :=
  rawChoice_balanced small B (d^20) (stateCapacity_small r c) _

def balancedJointFromState (a : PaperStateJoint r c)
    (hb : Balanced small B (physicalProfile small B r c (d^12) a.1)) : PaperJoint r c :=
  ⟨balancedWord small B (d^20) (stateCapacity_small r c) a.1.val.val,
    withProfile (balancedWord_profile small B (d^20) (stateCapacity_small r c) a.1.val.val hb).symm a.2⟩

lemma balancedJointFromState_projection (a : PaperStateJoint r c)
    (hb : Balanced small B (physicalProfile small B r c (d^12) a.1)) :
    (balancedJointFromState r c a hb).2.val=a.2.val := by
  exact withProfile_val
    (balancedWord_profile small B (d^20) (stateCapacity_small r c) a.1.val.val hb).symm a.2

lemma embedding_fromState (a : PaperStateJoint r c)
    (hb : Balanced small B (physicalProfile small B r c (d^12) a.1)) :
    paperJointEmbedding r c (balancedJointFromState r c a hb)=a := by
  apply stateJointProjection_injective r c
  exact balancedJointFromState_projection r c a hb

lemma fromState_embedding (a : PaperJoint r c) :
    balancedJointFromState r c (paperJointEmbedding r c a) (paperJointEmbedding_balanced r c a)=a := by
  apply paperJointEmbedding_injective r c
  exact embedding_fromState r c _ _

/-- The success test reads precisely balance and the lower padding bound. -/
def StateJointSuccess (a : PaperStateJoint r c) : Prop :=
  Balanced small B (physicalProfile small B r c (d^12) a.1) ∧
    ∀ i j,small i j=false → d^12 ≤ a.2.val.val.1 i j

abbrev SuccessfulStateJoint := {a : PaperStateJoint r c // StateJointSuccess r c a}

def successStateEquiv : SuccessfulJoint r c ≃ SuccessfulStateJoint r c where
  toFun a := ⟨paperJointEmbedding r c a.val,paperJointEmbedding_balanced r c a.val,a.property⟩
  invFun a := ⟨balancedJointFromState r c a.val a.property.1,a.property.2⟩
  left_inv a := by
    apply Subtype.ext
    exact fromState_embedding r c a.val
  right_inv a := by
    apply Subtype.ext
    exact embedding_fromState r c a.val a.property.1

/-- Every accepted actual state/completion pair unpads to one original
table, and every original table has one such pair. -/
def originalStateSuccessEquiv : Table r c ≃ SuccessfulStateJoint r c :=
  (successfulJointEquiv r c).trans (successStateEquiv r c)

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ReferenceDrawBounds
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform size bounds for the state-dependent dense completion call -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open PhysicalCompletionFibres FirstPaperPhysicalMarginal CompletionCounts PaddedCompletions

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

lemma reference_row_le_stateBound (r : I → ℕ) (c : J → ℕ)
    (i₀ : LargeRows r ((dimensionAllowance (I := I) (J := J))^20))
    (z : PaperStates r c) (i : Option {i : LargeRows r ((dimensionAllowance (I := I) (J := J))^20) // i≠i₀}) :
    referenceRows r c _ _ (stateCapacity r c) i₀ z i ≤ stateBound r c := by
  let k := ((Equiv.optionSubtypeNe i₀) i).val
  have hr : r k ≤ ∑ a,r a := Finset.single_le_sum (f := r) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  have hcount : rowLargeCount (paperSmall r c) k ≤ Fintype.card J := by
    unfold rowLargeCount
    calc
      _ ≤ ∑ _j : J,(1:ℕ) := Finset.sum_le_sum (fun j _ => by split_ifs <;> omega)
      _ = _ := by simp
  have hdim : Fintype.card J ≤ dimensionAllowance (I := I) (J := J) := by
    unfold dimensionAllowance
    nlinarith
  have hm := Nat.mul_le_mul_right ((dimensionAllowance (I := I) (J := J))^12) (hcount.trans hdim)
  have hs := Nat.sub_le (r k)
    (smallRow (paperSmall r c) (FirstPaperProfiles.smallView (paperSmall r c)
      (physicalProfile _ (stateCapacity r c) r c _ z) false) k)
  unfold referenceRows residualRows stateBound
  change r k-_+rowLargeCount (paperSmall r c) k*((dimensionAllowance (I := I) (J := J))^12) ≤ _
  omega

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ReferenceFiniteDraw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A finite Boolean draw of the actual state-dependent completion fibre -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open PhysicalCompletionFibres FirstPaperPhysicalMarginal CompletionCounts PaddedCompletions
open ResidualMixture FirstSuccess GridBoundary FairBits

noncomputable section
universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]
variable (r : I → ℕ) (c : J → ℕ)
variable (i₀ : LargeRows r ((dimensionAllowance (I := I) (J := J))^20))
variable (j₀ : LargeColumns c ((dimensionAllowance (I := I) (J := J))^20))
variable {q : ℕ}
variable (e : ({i : LargeRows r ((dimensionAllowance (I := I) (J := J))^20) // i≠i₀} ×
  {j : LargeColumns c ((dimensionAllowance (I := I) (J := J))^20) // j≠j₀}) ≃ Fin q)

local notation "d" => dimensionAllowance (I := I) (J := J)
local notation "R" => referenceRows r c (d^20) (d^12) (stateCapacity r c) i₀
local notation "P" => referenceColumns r c (d^20) (d^12) (stateCapacity r c) j₀

abbrev paperReferenceEquiv (z : PaperStates r c) : PaperFibre r c z ≃ Table (R z) (P z) :=
  referenceFibreEquiv r c _ _ (stateCapacity r c) i₀ j₀ z
    (physical_paper_capacity _ r c _ _ _ dimension_le_allowance z)

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperInitialization
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete initial state and completion fallbacks -/

namespace ContingencyTables.GreedyFeasibleTable

open scoped BigOperators

/-- Reindex the row/column recursion without changing its arithmetic. -/
noncomputable def reindexed {I J : Type*} [Fintype I] [Fintype J]
    (r : I → ℕ) (c : J → ℕ) (h : (∑ i,r i)=∑ j,c j) : Table r c :=
  (tableReindex (Fintype.equivFin I).symm (Fintype.equivFin J).symm r c).symm
    (table (fun i => r ((Fintype.equivFin I).symm i))
      (fun j => c ((Fintype.equivFin J).symm j)) (by
        rw [(Fintype.equivFin I).symm.sum_comp,(Fintype.equivFin J).symm.sum_comp]
        exact h))

end ContingencyTables.GreedyFeasibleTable

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperFeasibility
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Arithmetic tests for the positive small-profile state space

Feasibility is decided by coordinate bounds, the allowed local pattern,
and residual margin equations. No completion count is evaluated.
-/

namespace ContingencyTables.SmallGraphProfiles
open scoped BigOperators Classical
open PhysicalCompletionFibres SmallContextFibres FirstPaperPhysicalMarginal
open CompletionCounts PaddedCompletions FirstPaperProfiles

noncomputable section
universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]
omit [LinearOrder I] [LinearOrder J] in
/-- Equal residual totals and zero margins outside a rectangle suffice
for a supported completion, including empty row or column types. -/
lemma supported_completion_nonempty (small : I → J → Bool)
    (p : I → Prop) (q : J → Prop)
    (hrect : ∀ i j,small i j=false ↔ p i ∧ q j)
    (R : I → ℕ) (C : J → ℕ) (ht : (∑ i,R i)=∑ j,C j)
    (hR : ∀ i,¬p i → R i=0) (hC : ∀ j,¬q j → C j=0) :
    Nonempty (LargeCompletion small R C) := by
  obtain ⟨A⟩ : Nonempty (Table R C) := ⟨GreedyFeasibleTable.reindexed R C ht⟩
  refine ⟨⟨A,?_⟩⟩
  intro i j hs
  by_cases hi : p i
  · have hj : ¬q j := by
      intro hj
      exact Bool.noConfusion (hs.symm.trans ((hrect i j).mpr ⟨hi,hj⟩))
    have he : A.val i j ≤ C j := by
      rw [←A.property.2 j]
      exact Finset.single_le_sum (f := fun k => A.val k j)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    exact Nat.eq_zero_of_le_zero (he.trans_eq (hC j hj))
  · have he : A.val i j ≤ R i := by
      rw [←A.property.1 i]
      exact Finset.single_le_sum (f := fun k => A.val i k)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    exact Nat.eq_zero_of_le_zero (he.trans_eq (hR i hi))

variable (r : I → ℕ) (c : J → ℕ)
local notation "d" => dimensionAllowance (I := I) (J := J)
local notation "U" => d^20
local notation "L" => d^12
local notation "small" => paperSmall r c
local notation "B" => stateCapacity r c

/-- Padded residual margins can be computed before establishing feasibility. -/
def profileRows (z : SmallProfile small) (i : I) : ℕ :=
  r i-smallRow small (smallView small z false) i+rowLargeCount small i*L

def profileColumns (z : SmallProfile small) (j : J) : ℕ :=
  c j-smallColumn small B (smallView small z true) j+columnLargeCount small j*L

/-- Each field is a finite integer test on the candidate profile. -/
structure ProfileFeasible (z : SmallProfile small) : Prop where
  bounded : ∀ a,z a ≤ B a.1.val.1 a.1.val.2
  pattern : Pattern small B z
  residuals : OriginalResidualsNonnegative small B (smallView small z false) (smallView small z true) r c
  rows_outside : ∀ i,¬U ≤ r i → profileRows r c z i=0
  columns_outside : ∀ j,¬U ≤ c j → profileColumns r c z j=0
  totals : (∑ i,profileRows r c z i)=∑ j,profileColumns r c z j

omit [LinearOrder I] [LinearOrder J] in
lemma profile_capacity (z : SmallProfile small) :
    ∀ i j,small i j=false → (∑ k,profileRows r c z k) ≤ B i j :=
  paper_capacity_excludes_none small (smallView small z false) r d L U dimension_le_allowance

lemma physicalProfile_feasible (x : PaperStates r c) :
    ProfileFeasible r c (physicalProfile small B r c L x) := by
  have hcap := profile_capacity r c (physicalProfile small B r c L x)
  exact ⟨naturalProfile_bounded x.val.val,x.val.property,
    physical_original_residuals small B r c L x hcap,
    physical_residual_row_zero r c U L B x hcap,
    physical_residual_column_zero r c U L B x hcap,
    physical_residual_totals small B r c L x hcap⟩

/-- A passing arithmetic test constructs a completion by the greedy
rectangle algorithm, proving that its weight is strictly positive. -/
lemma profileFeasible_positive (z : SmallProfile small) (h : ProfileFeasible r c z) :
    0 < hardMarginal small B r c L z := by
  have hne := supported_completion_nonempty small
    (fun i => U ≤ r i) (fun j => U ≤ c j) (firstPaperSmall_false_iff r c U)
    (profileRows r c z) (profileColumns r c z) h.totals h.rows_outside h.columns_outside
  have hc := hardMarginal_eq_completionCount small B r c L z h.bounded (profile_capacity r c z)
  rw [ite_eq_left h.residuals] at hc
  rw [hc]
  exact Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr hne)

/-- The successful integer tests recover an actual state without
searching the completion space. -/
def stateOfFeasible (z : SmallProfile small) (h : ProfileFeasible r c z) : PaperStates r c :=
  ⟨⟨(fun a => ⟨z a,Nat.lt_succ_of_le (h.bounded a)⟩),h.pattern⟩,
    profileFeasible_positive r c z h⟩

/-- Failed candidates are discarded. Passing candidates retain all
completion multiplicity through the original physical state type. -/
def decodeProfile (z : SmallProfile small) : Option (PaperStates r c) :=
  if h : ProfileFeasible r c z then some (stateOfFeasible r c z h) else none

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_TreeListMore
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
variable {A B X : Type} [Codec A] [Codec B] [Codec X]

def listMinRealizer : Realizer listMin :=
  (fold minimum).congr (by intro x; dsimp only [listMin]; congr 1; funext a b; exact Nat.min_comm b a)

end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Complexity_TreeChoiceCosts
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeFraction
open TreeTyped

def cumulativeFast : Realizer cumulativeFraction := composition takeFast sumRealizer
end MatchingFPRAS.TreeFraction

namespace MatchingFPRAS.ExecutableChoice
open TreeTyped TreeFraction Polynomial

def predicateFast : Realizer predicate := by
  let C : Realizer (fun x : (List Fraction×Fraction)×ℕ=>cumulativeFraction (x.1.1,x.2+1)) :=
    (composition (pair first.fst (composition second successor)) cumulativeFast).congr (fun _=>rfl)
  exact (composition (pair first.snd C) lessRealizer).congr (fun _=>rfl)

def chooseFast : Realizer choose := by
  let rs : Realizer (fun x : List Fraction×Fraction=>List.range x.1.length) :=
    composition (composition first listLength) range
  let good:=composition (pair identity rs) (filterWith predicateFast)
  exact (composition (pair good (composition first listLength)) listMinRealizer).congr (fun _=>rfl)
end MatchingFPRAS.ExecutableChoice

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallBoundsProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A binary program checking every stored coordinate bound -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

def boundedValuesRealizer : Realizer boundedValues :=
  (composition (mapWith (composition (pair second first) leNat)) all).congr (by
    intro z
    simp only [Function.comp_apply,List.all_map,Function.comp_def,id_eq,boundedValues])

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallMarginTestProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial residual-margin inequality and equality tests -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped Polynomial

def validMarginAtRealizer (row : Bool) : Realizer (validMarginAt row) :=
  (composition (pair
    (composition (pair (lineValueRealizer row) (marginValueRealizer row)) leNat)
    (choose (composition (pair (marginValueRealizer row) (composition first second)) less)
      (composition (pair (lineValueRealizer row) (marginValueRealizer row)) natEqual)
      (constant true))) boolAnd).congr (by
        intro z
        apply Bool.eq_iff_iff.mpr
        simp only [Function.comp_apply,Bool.and_eq_true,decide_eq_true_eq,validMarginAt]
        by_cases h : (marginList row z.1).getD z.2 0<z.1.2 <;>
          simp only [List.getD_eq_getElem?_getD] at h <;> simp [h])

def validMarginsRealizer (row : Bool) : Realizer (validMargins row) :=
  (composition (composition (pair identity (marginIndices row))
    (mapWith (validMarginAtRealizer row))) all).congr (by
      intro z
      simp only [Function.comp_apply,List.all_map,Function.comp_def,id_eq,validMargins])

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

def profileBound (row : Bool) : Realizer (fun z : ProfileCheckData =>
    boundedValues (z.2,if row then z.1.1.2.1 else z.1.1.2.2)) :=
  composition (pair second (profileView row)) boundedValuesRealizer

def profileShape (row : Bool) : Realizer (fun z : ProfileCheckData =>
    decide ((if row then z.1.1.2.1 else z.1.1.2.2).length=z.1.1.1.length)) :=
  composition (pair (composition (profileView row) listLength)
    (composition profileCatalog listLength)) natEqual

def profileLineTest (row : Bool) : Realizer (fun z : ProfileCheckData =>
    validMargins row (((z.1.1.1,
      if row then z.1.1.2.1 else complementValues (z.2,z.1.1.2.2)),z.1.2),z.2)) :=
  composition (profileLineData row) (validMarginsRealizer row)

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

def profileOfCode (v : List ℕ×List ℕ) : SmallProfile small :=
  fun a => (if a.2 then v.2 else v.1).getD (e.symm a.1).val 0

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallProfileFlatCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Flattening the two stored views for coordinate exchanges -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

def flattenViewsRealizer : Realizer flattenViews := append

def splitViewsRealizer : Realizer splitViews :=
  pair (composition (pair second first) takeFast) (composition (pair second first) dropFast)

def codeExchangeRealizer : Realizer codeExchange :=
  composition (pair (composition (composition first first) listLength)
    (composition (pair (composition first flattenViewsRealizer) second) listExchangeRealizer))
      splitViewsRealizer

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallExchangeListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Enumerating all directed unit exchanges of a stored profile -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

def positiveExchangeTestRealizer : Realizer positiveExchangeTest :=
  (composition (pair (composition (composition second natEqual) boolNot)
    (composition (pair (constant 0)
      (composition (pair first (composition second second)) (getDFast 0))) less)) boolAnd).congr (by
        intro z
        apply Bool.eq_iff_iff.mpr
        simp only [Function.comp_apply,Bool.and_eq_true,Bool.not_eq_true',
          decide_eq_false_iff_not,decide_eq_true_eq,positiveExchangeTest])

def positiveExchangeIndicesRealizer : Realizer positiveExchangeIndices :=
  composition (pair identity (composition (pair identity identity) cellPairsRealizer))
    (filterWith positiveExchangeTestRealizer)

def codeExchangeListRealizer : Realizer codeExchangeList :=
  composition (pair identity (composition flattenViewsRealizer positiveExchangeIndicesRealizer))
    (mapWith codeExchangeRealizer)

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileCodeEquality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial equality and duplicate removal for profile codes -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped Polynomial

def listEntryEqualRealizer : Realizer listEntryEqual :=
  composition (pair
    (composition (pair (composition first first) second) (getDFast 0))
    (composition (pair (composition first second) second) (getDFast 0))) natEqual

def equalityIndices : Realizer (fun z : List ℕ×List ℕ => List.range z.1.length) :=
  composition first profileIndices

def listNatTestRealizer : Realizer listNatTest :=
  (composition (pair
    (composition (pair (composition first listLength) (composition second listLength)) natEqual)
    (composition (composition (pair identity equalityIndices) (mapWith listEntryEqualRealizer)) all))
      boolAnd).congr (by
        intro z
        simp only [Function.comp_apply,List.all_map,Function.comp_def,id_eq,listNatTest])

def listNatEqual : Realizer (fun z : List ℕ×List ℕ => decide (z.1=z.2)) :=
  listNatTestRealizer.congr (fun z => Bool.eq_iff_iff.mpr (by simp only [listNatTest_iff,decide_eq_true_eq]))

def profileCodeEqual : Realizer (fun z : (List ℕ×List ℕ)×(List ℕ×List ℕ) =>
    decide (z.1=z.2)) := pairEqual listNatEqual listNatEqual

def profileCodeDedup : Realizer (List.dedup (α := List ℕ×List ℕ)) := dedup profileCodeEqual

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileInverseRepairProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial binary program for each labelled inverse repair -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

def backwardRowsRealizer : Realizer backwardRows :=
  composition (pair first (composition (composition second second) second)) listExchangeRealizer

def backwardColumnsRealizer : Realizer backwardColumns :=
  composition (pair backwardRowsRealizer (pair
    (composition (composition second second) first)
    (composition (composition (composition second second) second) first))) listExchangeRealizer

def backwardViewsRealizer : Realizer backwardViews :=
  pair backwardRowsRealizer (composition
    (pair (composition second first) backwardColumnsRealizer) listDifferenceRealizer)

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallRepairGeometryProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary computation of repair crossing cells and capacities -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

def sourceCell : Realizer (fun z : RepairGeometry => z.1.getD z.2.1 (0,0)) :=
  composition (pair first (composition second first)) (getDFast (0,0))

def targetCell : Realizer (fun z : RepairGeometry => z.1.getD z.2.2 (0,0)) :=
  composition (pair first (composition second second)) (getDFast (0,0))

def crossingIndexRealizer : Realizer crossingIndex :=
  composition (pair (pair (composition targetCell first) (composition sourceCell second)) first)
    cellLookupRealizer

def capacityListRealizer : Realizer capacityList := mapWith first

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallRepairCodeProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Forward and inverse repairs on the stored pair of integer lists -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

def repairDataCatalog : Realizer (fun z : LabelledRepairData => z.1.1.1) :=
  composition (composition first first) first

def repairDataRows : Realizer (fun z : LabelledRepairData => z.1.1.2.1) :=
  composition (composition (composition first first) second) first

def repairDataCaps : Realizer (fun z : LabelledRepairData =>
    capacityList (z.1.2,z.1.1.2.1)) :=
  composition (pair (composition first second) repairDataRows) capacityListRealizer

def repairDataCross : Realizer (fun z : LabelledRepairData =>
    crossingIndex (z.1.1.1,z.2)) :=
  composition (pair repairDataCatalog second) crossingIndexRealizer

def forwardRepairCodeRealizer : Realizer forwardRepairCode :=
  composition (pair repairDataRows (pair repairDataCaps
    (pair (composition second second) repairDataCross))) repairedViewsRealizer

def inverseRepairCodeRealizer : Realizer inverseRepairCode :=
  composition (pair repairDataRows (pair repairDataCaps
    (pair (composition second first) (pair (composition second second) repairDataCross))))
      backwardViewsRealizer

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallDefectCodeTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The labelled defect predicate on two binary-coded views -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

def repairLabelTestRealizer : Realizer repairLabelTest :=
  composition (pair (pair (composition (composition first first) second)
    (composition first second)) second) defectTestRealizer

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallRepairListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial lists of encoded forward and inverse repairs -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

def repairRows : Realizer (fun z : RepairData => z.1.2.1) :=
  composition (composition first second) first

def repairPairsRealizer : Realizer repairPairs :=
  composition (pair repairRows repairRows) cellPairsRealizer

def forwardRepairLabelsRealizer : Realizer forwardRepairLabels :=
  composition (pair identity repairPairsRealizer) (filterWith repairLabelTestRealizer)

def forwardRepairListRealizer : Realizer forwardRepairList :=
  composition (pair identity forwardRepairLabelsRealizer) (mapWith forwardRepairCodeRealizer)

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallInverseRepairList
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Checking inverse repair candidates against their forward image -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

def inverseLabelInputRealizer : Realizer inverseLabelInput :=
  pair (pair (pair repairDataCatalog inverseRepairCodeRealizer)
    (composition first second)) second

def inverseLabelTestRealizer : Realizer inverseLabelTest :=
  composition (pair
    (composition inverseLabelInputRealizer repairLabelTestRealizer)
    (composition (pair (composition inverseLabelInputRealizer forwardRepairCodeRealizer)
      (composition (composition first first) second)) profileCodeEqual)) boolAnd

def inverseRepairLabelsRealizer : Realizer inverseRepairLabels :=
  composition (pair identity repairPairsRealizer) (filterWith inverseLabelTestRealizer)

def checkedInverseRepairListRealizer : Realizer checkedInverseRepairList :=
  composition (pair identity inverseRepairLabelsRealizer) (mapWith inverseRepairCodeRealizer)

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperCodeNeighbors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A binary program for the full physical neighbor list -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

def repairInput : Realizer (fun z : ProfileCheckData => (z.1.1,z.2)) :=
  pair (composition first first) second

def rawCodeNeighborsRealizer : Realizer rawCodeNeighbors :=
  composition (pair (composition profileViews codeExchangeListRealizer)
    (composition (pair (composition repairInput forwardRepairListRealizer)
      (composition repairInput checkedInverseRepairListRealizer)) append)) append

def candidateDataRealizer : Realizer candidateData :=
  pair (pair (pair (composition (f := fun z : ProfileCheckData×(List ℕ×List ℕ) => z.1)
    (g := fun z : ProfileCheckData => z.1.1.1) first profileCatalog) second)
    (composition (f := fun z : ProfileCheckData×(List ℕ×List ℕ) => z.1)
      (g := fun z : ProfileCheckData => z.1.2) first profileMargins)) (composition first second)

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperProposal
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The explicit small-state proposal realizes the proved ideal kernel -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open ResidualMixture FirstSuccess CompletionTranslation CompletionCounts

noncomputable section
universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]
variable (r : I → ℕ) (c : J → ℕ)

local notation "d" => dimensionAllowance (I := I) (J := J)

def proposalWeights (x y : PaperStates r c) : ℚ :=
  if physicalAdjacent r c _ _ (stateCapacity r c) (stateCapacity_small r c) x y
  then smallProposalRat d else 0

lemma proposalWeights_nonnegative (x y : PaperStates r c) : 0 ≤ proposalWeights r c x y := by
  unfold proposalWeights
  split_ifs
  · unfold smallProposalRat
    positivity
  · rfl

lemma proposalWeights_total (x : PaperStates r c) : ∑ y,proposalWeights r c x y ≤ 1 := by
  let Adj := physicalAdjacent r c (d^20) (d^12) (stateCapacity r c) (stateCapacity_small r c) x
  have he : (∑ y,proposalWeights r c x y)=
      ((Finset.univ.filter Adj).card:ℚ)*smallProposalRat d := by
    change (∑ y,if Adj y then smallProposalRat d else 0)=_
    rw [←Finset.sum_filter]
    simp only [Finset.sum_const,nsmul_eq_mul]
  rw [he]
  have hb : ((5*d^2+1:ℕ):ℝ)*smallProposal d ≤ 1/2 :=
    smallProposal_degree d (by unfold dimensionAllowance; omega)
  have hd := physicalAdjacent_degree_allowance r c (d^20) (d^12)
    (stateCapacity r c) (stateCapacity_small r c) x
  have hp : 0 ≤ smallProposal d := (smallProposal_bounds d (by unfold dimensionAllowance; omega)).1.le
  have hh : ((Finset.univ.filter Adj).card:ℝ)*smallProposal d ≤ 1 :=
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hd) hp).trans (hb.trans (by norm_num))
  apply (Rat.cast_le (K := ℝ)).mp
  simpa only [Rat.cast_mul,Rat.cast_natCast,smallProposalRat_cast,Rat.cast_one] using hh

def smallProposalLaw (x : PaperStates r c) : RationalLaw (Option (PaperStates r c)) :=
  proposalLaw (proposalWeights r c x) (proposalWeights_nonnegative r c x) (proposalWeights_total r c x)

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperCodeProposal
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The compiled neighbor draw has the small-chain proposal law -/

namespace ContingencyTables.SmallGraphProfiles
open scoped BigOperators Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres FirstPaperProfiles
open ProfilePrograms FirstPaperPhysicalMarginal CompletionCounts FirstSuccess FairBits

noncomputable section
variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c))
local notation "small" => paperSmall r c
local notation "s" => smallProposalBits (I := Fin m) (J := Fin n)

def decodeStateCode (v : List ℕ×List ℕ) : Option (PaperStates r c) :=
  if v.1.length=q ∧ v.2.length=q then decodeProfile r c (profileOfCode small e v) else none

def decodedCodeProposal (x : PaperStates r c) (bits : Fin s → Bool) : Option (PaperStates r c) :=
  (codeNeighborProposal (stateCodeData r c e x,List.ofFn bits)).bind (decodeStateCode r c e)

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperComputedCatalog
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The small-cell ordering is computed from the encoded margins -/

namespace ContingencyTables.SmallGraphProfiles
open scoped Classical
open SmallContextCoordinates ProfilePrograms FirstPaperPhysicalMarginal CompletionCounts

noncomputable section
variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "U" => d^20
local notation "small" => paperSmall r c

def computedCatalog : List (ℕ×ℕ) := smallCellCatalog ((List.ofFn r,List.ofFn c),U)

lemma computedCatalog_nodup : (computedCatalog r c).Nodup :=
  (cellPairs_nodup (List.ofFn r) (List.ofFn c)).filter _

lemma mem_computedCatalog (ij : ℕ×ℕ) :
    ij∈computedCatalog r c ↔ ∃ a : Cells small,((a.val.1.val,a.val.2.val):ℕ×ℕ)=ij := by
  rw [computedCatalog,mem_smallCellCatalog]
  simp only [List.length_ofFn]
  constructor
  · rintro ⟨hi,hj,hsmall⟩
    let i : Fin m := ⟨ij.1,hi⟩
    let j : Fin n := ⟨ij.2,hj⟩
    have hs : small i j=true := by
      apply decide_eq_true
      simpa only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,hi,hj,dite_true,
        Option.getD_some] using hsmall
    exact ⟨⟨(i,j),hs⟩,rfl⟩
  · rintro ⟨a,rfl⟩
    refine ⟨a.val.1.isLt,a.val.2.isLt,?_⟩
    have hs : r a.val.1<U ∨ c a.val.2<U := of_decide_eq_true a.property
    simpa only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,a.val.1.isLt,a.val.2.isLt,
      dite_true,Option.getD_some,Fin.eta] using hs

def catalogCell (i : Fin (computedCatalog r c).length) : Cells small :=
  Classical.choose ((mem_computedCatalog r c ((computedCatalog r c)[i.val])).mp
    (List.getElem_mem i.isLt))

lemma catalogCell_coordinates (i : Fin (computedCatalog r c).length) :
    ((catalogCell r c i).val.1.val,(catalogCell r c i).val.2.val)=
      (computedCatalog r c)[i.val] :=
  Classical.choose_spec ((mem_computedCatalog r c ((computedCatalog r c)[i.val])).mp
    (List.getElem_mem i.isLt))

lemma catalogCell_bijective : Function.Bijective (catalogCell r c) := by
  constructor
  · intro i j h
    have he := congrArg (fun a : Cells small => (a.val.1.val,a.val.2.val)) h
    rw [catalogCell_coordinates,catalogCell_coordinates] at he
    exact Fin.ext ((computedCatalog_nodup r c).getElem_inj_iff.mp he)
  · intro a
    have hm : (a.val.1.val,a.val.2.val)∈computedCatalog r c :=
      (mem_computedCatalog r c _).mpr ⟨a,rfl⟩
    obtain ⟨i,hi,hval⟩ := List.mem_iff_getElem.mp hm
    refine ⟨⟨i,hi⟩,?_⟩
    have he := (catalogCell_coordinates r c ⟨i,hi⟩).trans hval
    apply Subtype.ext
    exact Prod.ext (Fin.ext (congrArg Prod.fst he)) (Fin.ext (congrArg Prod.snd he))

def computedCellEquiv : Fin (computedCatalog r c).length ≃ Cells small :=
  Equiv.ofBijective (catalogCell r c) (catalogCell_bijective r c)

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

def twentiethPower : Realizer (fun n : ℕ => n^20) :=
  (composition fifthPower fourthPower).congr (by
    intro n
    simp only [Function.comp_apply,←pow_mul])

def marginDimensionRealizer : Realizer marginDimension :=
  composition (f := fun z : List ℕ×List ℕ => (10,(z.1.length+1)*(z.2.length+1)))
    (g := fun z : ℕ×ℕ => z.1+z.2) (pair (constant 10)
    (composition (f := fun z : List ℕ×List ℕ => (z.1.length+1,z.2.length+1))
      (g := fun z : ℕ×ℕ => z.1*z.2)
      (pair (composition (composition first listLength) successor)
      (composition (composition second listLength) successor)) multiply)) add

def marginThresholdRealizer : Realizer marginThreshold :=
  composition (f := marginDimension) (g := fun n : ℕ => n^20) marginDimensionRealizer twentiethPower

def marginCatalogRealizer : Realizer marginCatalog :=
  composition (pair identity marginThresholdRealizer) smallCellCatalogRealizer

def prepareProfileInput (z : RawProfileInput) : ProfileCheckData :=
  (((marginCatalog z.1,z.2),z.1),marginThreshold z.1)

def prepareProfileInputRealizer : Realizer prepareProfileInput :=
  pair (pair (pair (composition (f := fun z : RawProfileInput => z.1) (g := marginCatalog) first marginCatalogRealizer) second) first)
    (composition (f := fun z : RawProfileInput => z.1) (g := marginThreshold) first marginThresholdRealizer)

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

def componentRealizer : Realizer componentValue := by
  let D : Realizer (fun z : ComponentData => z.1.1) := composition first first
  let S : Realizer (fun z : ComponentData => z.1.2) := composition first second
  let P : Realizer (fun z : ComponentData => z.2.1) := composition second first
  let N : Realizer (fun z : ComponentData => z.2.2) := composition second second
  let D4 := composition D fourthPower
  let D8 := composition D eighthPower
  let pos := composition (pair D4
    (composition (pair (composition (pair D8 P) multiply)
      (composition (pair D S) multiply)) add)) multiply
  let neg := composition (pair (composition (pair D4 D8) multiply) N) multiply
  let den := composition (pair S D8) multiply
  exact (composition (pair (composition (pair neg pos) subtract) den) quotient).congr
    (by intro z; rfl)

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

def exponentCellRealizer : Realizer exponentCell :=
  composition exponentCellDataRealizer componentRealizer

def exponentCellsRealizer : Realizer exponentCells :=
  composition (composition first first) cellPairsRealizer

def exponentValuesRealizer : Realizer exponentValues :=
  composition (pair identity exponentCellsRealizer) (mapWith exponentCellRealizer)

def fullExponentRealizer : Realizer fullExponent :=
  composition (pair exponentValuesRealizer (constant 0)) listMaximumRealizer

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

def gridCellValueRealizer : Realizer gridCellValue :=
  composition (pair gridCellWidthRealizer
    (composition (pair (composition (composition first first) second) second) matrixEntryRealizer))
    multiply

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseScaleMatrixProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Scaling a binary grid matrix to its integer bin corner -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped Polynomial GridBoundary

def scaleRowsRealizer : Realizer scaleRows :=
  composition (composition (composition (composition (composition first first) first) tail)
    listLength) range

def scaleColumnsRealizer : Realizer scaleColumns :=
  composition (composition (composition (composition (composition first first) second) tail)
    listLength) range

def scaleRowEntryRealizer : Realizer scaleRowEntry :=
  composition (pair (composition first first) (pair (composition first second) second))
    gridCellValueRealizer

def scaleRowRealizer : Realizer scaleRow :=
  composition (pair identity (composition first scaleColumnsRealizer)) (mapWith scaleRowEntryRealizer)

def scaleMatrixRealizer : Realizer scaleMatrix :=
  composition (pair identity scaleRowsRealizer) (mapWith scaleRowRealizer)

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseOffsetProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary quotient offsets and the resulting free matrix -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped ProfilePrograms GridBoundary

def offsetBitsRealizer : Realizer offsetBits := by
  let N : Realizer (fun z : OffsetData×(ℕ×ℕ) => z.1.1.1.1.2.tail) :=
    composition (composition (composition (composition
    (composition first first) first) first) second) tail
  let width := composition N listLength
  let index := composition (pair
    (composition (pair (composition second first) width) multiply)
    (composition second second)) add
  exact composition (pair (composition first second) index) (getDFast [])

def offsetFreeEntryRealizer : Realizer offsetFreeEntry := by
  let cell : Realizer (fun z : OffsetData×(ℕ×ℕ) => (z.1.1,z.2)) :=
    pair (composition first first) second
  exact composition (pair (composition cell gridCellValueRealizer)
    (composition (pair (composition cell gridCellWidthRealizer) offsetBitsRealizer)
      scaledWordRealizer)) add

def offsetRowEntryRealizer : Realizer offsetRowEntry :=
  composition (pair (composition first first) (pair (composition first second) second))
    offsetFreeEntryRealizer

def offsetRowRealizer : Realizer offsetRow :=
  composition (pair identity (composition (composition first first) scaleColumnsRealizer))
    (mapWith offsetRowEntryRealizer)

def offsetMatrixRealizer : Realizer offsetMatrix :=
  composition (pair identity (composition first scaleRowsRealizer)) (mapWith offsetRowRealizer)

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseGridExponentProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing the dense exponent directly from a binary grid matrix -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped GridBoundary

def scaledDataRealizer : Realizer scaledData :=
  pair (pair (composition first first) scaleMatrixRealizer) second

def gridExponentRealizer : Realizer gridExponent :=
  composition scaledDataRealizer fullExponentRealizer

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

def flatExponentRealizer : Realizer flatExponent := composition flatToGridDataRealizer gridExponentRealizer

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseMetropolisProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial binary program for a full dense Metropolis step -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped

def replaceFlatRealizer : Realizer replaceFlat :=
  pair (pair (composition (composition first first) first) second) (composition first second)

def flatAcceptCandidate (z : FlatStepData×List ℕ) : List ℕ :=
  if dyadicWordAccept (z.1.2.2,
    flatExponent (replaceFlat (z.1.1,z.2))-flatExponent z.1.1) then z.2 else z.1.1.1.2

def flatAcceptCandidateRealizer : Realizer flatAcceptCandidate := by
  let data : Realizer (fun z : FlatStepData×List ℕ => z.1.1) := composition first first
  let candidate := composition (composition (pair data second) replaceFlatRealizer) flatExponentRealizer
  let current := composition data flatExponentRealizer
  let gap := composition (pair candidate current) subtract
  let coins : Realizer (fun z : FlatStepData×List ℕ => z.1.2.2) :=
    composition (composition first second) second
  exact choose (composition (pair coins gap) dyadicWordAcceptRealizer) second
    (composition (composition data first) second)

def flatStepCandidate (z : FlatStepData) : Option (List ℕ) :=
  axisWordStep ((4*z.1.2^8,z.1.1.2),z.2.1)

def flatStepCandidateRealizer : Realizer flatStepCandidate := by
  let d : Realizer (fun z : FlatStepData => z.1.2) := composition first second
  let K := composition (pair (constant 4) (composition d eighthPower)) multiply
  let xs : Realizer (fun z : FlatStepData => z.1.1.2) :=
    composition (composition first first) second
  exact composition (pair (pair K xs) (composition second first)) axisWordStepRealizer

def flatMetropolisStep (z : FlatStepData) : List ℕ :=
  (flatStepCandidate z).elim z.1.1.2 (fun xs => flatAcceptCandidate (z,xs))

def flatMetropolisStepRealizer : Realizer flatMetropolisStep :=
  composition (pair identity flatStepCandidateRealizer)
    (optionCases (composition (composition first first) second) flatAcceptCandidateRealizer)

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

def proposalWidthRealizer : Realizer proposalWidth := by
  let D : Realizer (fun z : FlatExponentData×List Bool => z.1.2) := composition first second
  let M := composition (pair (constant 8) D) multiply
  exact composition M ceilLogTwoRealizer

def flatWordStep (z : FlatExponentData×List Bool) : List ℕ :=
  flatMetropolisStep (z.1,
    (z.2.take (proposalWidth z),z.2.drop (proposalWidth z)))

def flatWordStepRealizer : Realizer flatWordStep :=
  composition (pair first (pair
    (composition (pair second proposalWidthRealizer) takeFast)
    (composition (pair second proposalWidthRealizer) dropFast))) flatMetropolisStepRealizer

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

def chunkIndicesRealizer : Realizer chunkIndices := composition (composition first listLength) range

def dependentChunksRealizer : Realizer dependentChunks :=
  composition (pair identity chunkIndicesRealizer) (mapWith dependentChunkRealizer)

open scoped BigOperators

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_DirectedBFSBounds
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial size of the materialized BFS path store -/

namespace ContingencyTables.DirectedBFSBounds

open MatchingFPRAS.TreeTyped DirectedBFSCode

def Bounded (P : Store) (B : ℕ) : Prop := ∀ o∈P,weight o≤B

end ContingencyTables.DirectedBFSBounds

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FirstSuccessProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial first-success selection for a supplied list of trial words -/

namespace ContingencyTables.FirstSuccessProgram
open MatchingFPRAS.TreeTyped

variable {A B W : Type} [Codec A] [Codec B] [Codec W] [Inhabited B]

def isSomeRealizer : Realizer (Option.isSome : Option B → Bool) :=
  (composition (pair (constant false) identity)
    (optionCases (constant false) (constant true))).congr (by intro o; cases o <;> rfl)

omit [Codec B] [Inhabited B] in
lemma firstSome_filter (xs : List (Option B)) :
    (xs.filter Option.isSome).headD none=firstSome xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases x with
    | none => exact ih
    | some b => rfl

def firstSomeRealizer : Realizer (firstSome (B := B)) :=
  (composition (filter isSomeRealizer) (head none)).congr firstSome_filter

def defaultRealizer : Realizer (fun z : B×Option B => z.2.getD z.1) :=
  (optionCases identity second).recode id (fun z : B×Option B => z.2.getD z.1)
    (fun _ => rfl) (by rintro ⟨b,o⟩; cases o <;> rfl)

def retryRealizer {f : A×W → Option B} (F : Realizer f) : Realizer (retry f) := by
  let inputs : Realizer (fun z : (A×B)×List W => (z.1.1,z.2)) :=
    pair (composition first first) second
  let results := composition inputs (mapWith F)
  exact composition (pair (composition first second) (composition results firstSomeRealizer)) defaultRealizer

end ContingencyTables.FirstSuccessProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FractionRepetitionProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executing the confidence repetition count on a rational input -/
namespace ContingencyTables.FractionRepetitionProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped

def countRealizer : Realizer count :=
  composition (f := fun x : TreeFraction.Fraction => (64,(TreeFraction.normalize x).2.bits.length+1))
    (g := fun p : ℕ×ℕ => p.1*p.2)
    (pair (constant 64) (composition
      (composition (composition (composition TreeFraction.normalizeRealizer second) toBits) listLength)
      successor)) multiply
end ContingencyTables.FractionRepetitionProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingDirectProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The direct estimator for the zero-label branch

The same finite-word median evaluator handles this branch. The confidence
parameter controls the outer repetition count independently of its relative
accuracy, which is one quarter of the public accuracy.
-/
namespace ContingencyTables.CountingDirectProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms


abbrev Request := CountingBaseProgram.Input×TreeFraction.Fraction

end ContingencyTables.CountingDirectProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_RepeatedFractionProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independent repetition of a finite-word rational program

The public confidence amplification only groups bits already supplied
on the tape. Its binary count cannot cause an unbounded allocation.
-/

namespace ContingencyTables.RepeatedFractionProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms

variable {X : Type} [Codec X]
def wordsRealizer : Realizer (words (X:=X)) :=
  composition (f := fun z : Input X => (wordChunks (z.1.2.2,z.2),z.1.2.1))
    (g := fun p : List (List Bool)×ℕ => p.1.take p.2)
    (pair
      (composition (f := fun z : Input X => (z.1.2.2,z.2)) (g := wordChunks)
        (pair (composition (composition first second) second) second) wordChunksRealizer)
      (composition (composition first second) first)) takeFast

variable {f : X×List Bool→TreeFraction.Fraction}

def sampleRealizer (F : Realizer f) : Realizer (sample f) :=
  composition (f := fun z : Input X×List Bool => (z.1.1.1,z.2)) (g := f)
    (pair (composition (composition first first) first) second) F
def samplesRealizer (F : Realizer f) : Realizer (samples f) :=
  composition (pair identity wordsRealizer) (mapWith (sampleRealizer F))

attribute [local irreducible] samples

def outputRealizer (F : Realizer f) : Realizer (output f) :=
  composition (f := samples f) (g := MedianFractionProgram.median)
    (samplesRealizer F) MedianFractionProgram.medianRealizer

open GridBoundary CommonBasesFPRAS

end ContingencyTables.RepeatedFractionProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingAmplifiedProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Outer confidence repetition of the executed counting program -/
namespace ContingencyTables.CountingAmplifiedProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped CommonBasesFPRAS GridBoundary
abbrev Request := CountingDirectProgram.Request
variable (width : Request→ℕ) (N : Realizer width)

def repeats (req : Request) : ℕ := FractionRepetitionProgram.count req.2
def repeatsRealizer : Realizer repeats :=
  composition (f := fun req : Request => req.2) (g := FractionRepetitionProgram.count)
    second FractionRepetitionProgram.countRealizer

end ContingencyTables.CountingAmplifiedProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Algorithm_OnlineScheduleNat
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
variable {A : Type} [Codec A]
def Realizer.addNat {f g : A→ℕ} (F : Realizer f) (G : Realizer g) :
    Realizer (fun a=>f a+g a) := composition (pair F G) add
def Realizer.mulNat {f g : A→ℕ} (F : Realizer f) (G : Realizer g) :
    Realizer (fun a=>f a*g a) := composition (pair F G) multiply
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_Codec
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
variable {A B A' B' : Type} [Codec A] [Codec B] [Codec A'] [Codec B']
def Realizer.reencode {f : A→B} (F : Realizer f) (i : A'→A) (g : A'→B')
    (hi : ∀ a,encode (i a)=encode a) (hg : ∀ a,encode (g a)=encode (f (i a))) : Realizer g where
  program := F.program
  cost a := F.cost (i a)
  correct := by
    intro a s
    have h:=F.correct (i a) s
    rw [hi a,←hg a] at h
    exact h
end MatchingFPRAS.TreeTyped

namespace MatchingFPRAS.LiteralCodec
open TreeTyped TreeData TreeFunction

instance instCodecSymbol : Codec Symbol := ⟨fun a=>TreeTyped.encode (parts a)⟩
lemma encode_parts (a : Symbol) : TreeTyped.encode (parts a)=TreeTyped.encode a := rfl

def valRealizer : Realizer (Fin.val : Symbol→ℕ) :=
  (composition first listLength).reencode parts Fin.val encode_parts (fun a=>by simp [parts])
def fromBitRealizer : Realizer fromBit := choose identity (constant 2) (constant 1)
def natWordRealizer : Realizer natWord :=
  (composition (pair (composition toBits (map fromBitRealizer)) (constant [3])) append).congr (fun _=>rfl)
def ratWordRealizer : Realizer ratWord :=
  (composition (pair (constant 4) (composition (pair (composition first natWordRealizer)
    (composition second natWordRealizer)) append)) listCons).congr (fun _=>rfl)
end MatchingFPRAS.LiteralCodec

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_Parse
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.LiteralParse
open TreeTyped TreeData TreeFunction Polynomial LiteralCodec

def eqSymbol (a : Symbol) : Realizer (fun b : Symbol=>decide (b=a)) :=
  (composition (pair valRealizer (constant a.val)) natEqual).congr
    (fun b=>by simp only [Function.comp_apply,Fin.ext_iff])

def numStepRealizer : Realizer numStep :=
  (choose (composition first (eqSymbol 3))
    (composition (pair (constant 0) second) listCons)
    (choose (composition first (eqSymbol 1))
      (composition (pair ((constant 2).mulNat (composition second (head 0))) (composition second tail)) listCons)
      (choose (composition first (eqSymbol 2))
        (composition (pair (((constant 2).mulNat (composition second (head 0))).addNat (constant 1)) (composition second tail)) listCons)
        second))).congr (fun x=>by simp only [Function.comp_apply,decide_eq_true_eq,numStep])
def parseRealizer : Realizer parse :=
  (composition (pair reverse (constant [])) (fold numStepRealizer)).congr (fun as=>by
    simp only [Function.comp_apply,List.foldl_reverse,parse])
end MatchingFPRAS.LiteralParse

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_GreedyPublicProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Parsing the public margins and printing the greedy matrix

All operations are existing binary list programs. The bounded take and
drop operations also terminate polynomially on malformed headers.
-/

namespace ContingencyTables.GreedyFeasibleTable
open MatchingFPRAS TreeTyped LiteralCodec LiteralParse
open scoped BigOperators

def marginListsRealizer : Realizer marginLists := by
  let M : Realizer (fun ns : List ℕ => ns.headD 0) := head 0
  let N : Realizer (fun ns : List ℕ => ns.tail.headD 0) := composition tail (head 0)
  let D : Realizer (fun ns : List ℕ => ns.tail.tail) := composition tail tail
  exact (pair (composition (pair D M) takeFast)
    (composition (pair (composition (pair D M) dropFast) N) takeFast)).congr (fun _ => rfl)

def printMatrixRealizer : Realizer printMatrix :=
  flatMapPoly (flatMapPoly natWordRealizer)

end ContingencyTables.GreedyFeasibleTable

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingInputParser
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Parsing the public cell-bounded counting input

Dimensions only delimit bounded list slices. The matrix layout uses the
lengths of the parsed margin lists, so malformed headers do not create
unbounded numeric loops. Positive rational parameters use their natural
numerator and denominator, exactly as in the public tape encoding.
-/

namespace ContingencyTables.CountingInputParser
open MatchingFPRAS MatchingFPRAS.TreeTyped MatchingFPRAS.LiteralParse
open MatchingFPRAS.TreeFraction DensePrograms

def offsetRealizer : Realizer offset :=
  composition (pair (composition (pair (constant 2) (head 0)) add)
    (composition tail (head 0))) add
def restRealizer : Realizer rest := composition (pair identity offsetRealizer) dropFast
def cellsRealizer : Realizer cells :=
  composition (pair (composition (composition GreedyFeasibleTable.marginListsRealizer first) listLength)
    (composition (composition GreedyFeasibleTable.marginListsRealizer second) listLength)) multiply
def capacityFrameRealizer : Realizer capacityFrame :=
  pair (pair
    (composition (f := fun ns : List ℕ => (0,(GreedyFeasibleTable.marginLists ns).1))
      (g := fun z : ℕ×List ℕ => z.1::z.2)
      (pair (constant 0) (composition GreedyFeasibleTable.marginListsRealizer first)) listCons)
    (composition (f := fun ns : List ℕ => (0,(GreedyFeasibleTable.marginLists ns).2))
      (g := fun z : ℕ×List ℕ => z.1::z.2)
      (pair (constant 0) (composition GreedyFeasibleTable.marginListsRealizer second)) listCons))
    (composition (pair restRealizer cellsRealizer) takeFast)
def parametersRealizer : Realizer parameters :=
  composition (pair restRealizer cellsRealizer) dropFast
def fractionPairRealizer : Realizer fractionPair :=
  pair (pair (head 0) (composition tail (head 1)))
    (pair (composition (composition tail tail) (head 0))
      (composition (composition (composition tail tail) tail) (head 1)))
def decodeRealizer : Realizer decode :=
  pair (pair GreedyFeasibleTable.marginListsRealizer
    (composition (f := capacityFrame) (g := unflattenGrid) capacityFrameRealizer unflattenGridRealizer))
    (composition (f := parameters) (g := fractionPair) parametersRealizer fractionPairRealizer)
def publicRealizer : Realizer parseInput :=
  composition (f := parse) (g := decode) parseRealizer decodeRealizer

end ContingencyTables.CountingInputParser

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FractionOutputProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Canonical nonnegative rational output on the public tape -/

namespace ContingencyTables.FractionOutputProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped MatchingFPRAS.LiteralCodec

def outputRealizer : Realizer output :=
  composition (f := TreeFraction.normalize) (g := ratWord)
    TreeFraction.normalizeRealizer ratWordRealizer

end ContingencyTables.FractionOutputProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingBranchProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Public dispatch for the two counting branches

The positive-label evaluator is a program parameter, instantiated by the
adaptive estimator. Feasibility and the zero-label branch are computed from
the same parsed input used by the complete public machine.
-/
namespace ContingencyTables.CountingBranchProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped
abbrev Request := CountingDirectProgram.Request

/-- Reassociate the two rational parameters without re-encoding them. -/
def request (z : CountingInputParser.Input) : Request := ((z.1,z.2.1),z.2.2)
def requestRealizer : Realizer request :=
  pair (pair first (composition second first)) (composition second second)

def feasible (z : Request) : Bool := NetworkFeasibilityProgram.test z.1.1
def feasibleRealizer : Realizer feasible :=
  composition (f := fun z : Request => z.1.1) (g := NetworkFeasibilityProgram.test)
    (composition first first) NetworkFeasibilityProgram.testRealizer

attribute [local irreducible] feasible

end ContingencyTables.CountingBranchProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingDirectSemantics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The direct binary evaluator uses the original counting parameters -/
namespace ContingencyTables.CountingDirectProgram
open MatchingFPRAS CompanionFactorialApplication GridBoundary CompanionOracleDensity
open scoped Classical
noncomputable section
variable {m n : ℕ}

def request (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ) (epsilon delta : ℚ) : Request :=
  ((NetworkVertexCode.data r c b,TreeFraction.repr epsilon),TreeFraction.repr delta)

end
end ContingencyTables.CountingDirectProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseWalkProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial loop of binary dense transition words -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped Polynomial

def advance (z : List Bool×FlatExponentData) : FlatExponentData :=
  replaceFlat (z.2,flatWordStep (z.2,z.1))

def advanceRealizer : Realizer advance := by
  let swap : Realizer (fun z : List Bool×FlatExponentData => (z.2,z.1)) := pair second first
  let next := composition swap flatWordStepRealizer
  exact composition (pair second next) replaceFlatRealizer

def walkWords (z : FlatExponentData×List (List Bool)) : FlatExponentData :=
  z.2.foldl (fun data bits => advance (bits,data)) z.1

def walkWordsRealizer : Realizer walkWords :=
  composition (pair second first) (fold advanceRealizer)

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseBooleanWalkProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial program for the complete flat-word dense walk -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped GridBoundary ProfilePrograms

def flatWordWalk (z : FlatExponentData×List Bool) : FlatExponentData :=
  walkWords (z.1,wordChunks (denseStepBits z.1.2,z.2))

def flatWordWalkRealizer : Realizer flatWordWalk :=
  composition (pair first (composition (pair
    (composition (composition first second) denseWidthRealizer) second) wordChunksRealizer))
    walkWordsRealizer

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseCompletionTest
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial exact acceptance test for a free integer matrix -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped ProfilePrograms

def completionNonnegativeRealizer : Realizer completionNonnegative :=
  composition (composition completionPartsRealizer (pair second first)) leNat

def completionValidRealizer : Realizer completionValid :=
  (composition (composition (pair identity (composition first cellPairsRealizer))
    (mapWith completionNonnegativeRealizer)) all).congr (by
      intro z
      simp only [Function.comp_apply,List.all_map,Function.comp_def,id_eq,completionValid])

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseCompletedMatrixProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary construction of the completed integer matrix -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped Polynomial

def completedEntryRealizer : Realizer completedEntry :=
  composition (composition completionPartsRealizer (pair first second)) subtract

def completionRowsRealizer : Realizer completionRows :=
  composition (composition (composition first first) listLength) range
def completionColumnsRealizer : Realizer completionColumns :=
  composition (composition (composition first second) listLength) range

def completedRowEntryRealizer : Realizer completedRowEntry :=
  composition (pair (composition first first) (pair (composition first second) second)) completedEntryRealizer

def completedRowRealizer : Realizer completedRow :=
  composition (pair identity (composition first completionColumnsRealizer)) (mapWith completedRowEntryRealizer)

def completedMatrixRealizer : Realizer completedMatrix :=
  composition (pair identity completionRowsRealizer) (mapWith completedRowRealizer)

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseTrialProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The complete dense trial as a polynomial binary program -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped ProfilePrograms

def trialGrid (z : DenseTrialData) : ExponentData :=
  flatToGridData (flatWordWalk (z.1.1,z.2.take (trialWalkBits z)))

def trialGridRealizer : Realizer trialGrid := by
  let data : Realizer (fun z : DenseTrialData => z.1.1) := composition first first
  let bits := composition (pair (second (A := FlatExponentData×ℕ) (B := List Bool))
    trialWalkBitsRealizer) takeFast
  let source := pair data bits
  let walk := composition source flatWordWalkRealizer
  let result := composition walk flatToGridDataRealizer
  exact result

def trialOffsets (z : DenseTrialData) : List (List Bool) :=
  dependentChunks (offsetLengths (trialGrid z,z.1.2),z.2.drop (trialWalkBits z))

def trialOffsetsRealizer : Realizer trialOffsets :=
  composition (pair
    (composition (pair trialGridRealizer (composition first second)) offsetLengthsRealizer)
    (composition (pair second trialWalkBitsRealizer) dropFast)) dependentChunksRealizer

def trialCompletion (z : DenseTrialData) : CompletionData :=
  ((trialGrid z).1.1,offsetMatrix (trialGrid z,trialOffsets z))

def trialCompletionRealizer : Realizer trialCompletion :=
  pair (composition (composition trialGridRealizer first) first)
    (composition (pair trialGridRealizer trialOffsetsRealizer) offsetMatrixRealizer)

def acceptCompletionRealizer : Realizer acceptCompletion :=
  choose completionValidRealizer (composition completedMatrixRealizer MatchingFPRAS.TreeTyped.some) (constant none)

def denseTrialCode (z : DenseTrialData) : Option MatrixCode := acceptCompletion (trialCompletion z)

def denseTrialCodeRealizer : Realizer denseTrialCode :=
  composition trialCompletionRealizer acceptCompletionRealizer

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseDrawProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The bounded dense draw as a single polynomial binary program -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped ProfilePrograms

def drawChunksRealizer : Realizer drawChunks :=
  composition (pair (composition (composition first first) trialWidthRealizer) second)
    wordChunksRealizer

def denseDrawCode (z : DenseDrawData) : MatrixCode :=
  FirstSuccessProgram.retry denseTrialCode (z.1,drawChunks z)

def denseDrawCodeRealizer : Realizer denseDrawCode :=
  composition (pair first drawChunksRealizer) (FirstSuccessProgram.retryRealizer denseTrialCodeRealizer)

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseTrialSemantics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The complete trial program uses the manuscript's finite-bit experiment -/

namespace ContingencyTables.DensePrograms
open GridBoundary FairBits
open scoped BigOperators Classical

noncomputable section

def tableOutput {m n : ℕ} {R : Option (Fin m) → ℕ} {P : Option (Fin n) → ℕ}
    (X : Table R P) : MatrixCode :=
  matrixCode (fun i : Fin (m+1) => fun j : Fin (n+1) =>
    X.val (finSuccEquiv m i) (finSuccEquiv n j))

end
end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseDrawSemantics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The bounded binary draw is exactly the analyzed Boolean sampler -/

namespace ContingencyTables.DensePrograms
open GridBoundary FairBits
open scoped BigOperators Classical

noncomputable section

def drawInput {m n d : ℕ} (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (h : ℕ) (a : Grid (I := Fin (m*n)) (4*d^8)) (fallback : Table R P)
    (bits : List Bool) : DenseDrawData :=
  ((((((marginCode R,marginCode P),gridNatCode a),d),h),tableOutput fallback),bits)

end
end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseNormalizeProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Moving maximal margins into the distinguished positions -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped

def normalizedDraw (z : DenseDrawData) : MatrixCode := denseDrawCode (preparedDraw z)

def normalizedDrawRealizer : Realizer normalizedDraw :=
  composition preparedDrawRealizer denseDrawCodeRealizer

def normalizedDenseCode (z : DenseDrawData) : MatrixCode :=
  swapMatrix (drawIndices z,normalizedDraw z)

def normalizedDenseCodeRealizer : Realizer normalizedDenseCode :=
  composition (pair drawIndicesRealizer normalizedDrawRealizer) swapMatrixRealizer

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseNormalizeSemantics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Correctness of computed maximal-margin normalization -/

namespace ContingencyTables.DensePrograms
open GridBoundary FairBits ResidualMixture FirstSuccess
open scoped BigOperators Classical

noncomputable section

def normalizedBooleanDraw {m n d : ℕ} (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (hd : 14≤d) (hR : ∀ i,d^12≤R i) (hP : ∀ j,d^12≤P j)
    (htotal : ∑ i,R i=∑ j,P j) (h : ℕ)
    (a : Grid (I := Fin (m*n)) (4*d^8)) (fallback : Table R P)
    (bits : Fin (normalizedDrawBits R P d h) → Bool) : Table R P :=
  let E : Table R P ≃ Table (normalizedMargin R) (normalizedMargin P) :=
    tableReindex (indexPermutation (marginPosition R)) (indexPermutation (marginPosition P)) R P
  E.symm (denseBooleanDraw (normalizedMargin R) (normalizedMargin P) d hd
    (normalizedMargin_lower R _ hR) (normalizedMargin_lower P _ hP) finProdFinEquiv
    (by rw [normalizedMargin_total,normalizedMargin_total]; exact htotal) h a (E fallback) bits)

/-- The computed choice of maximal rows and columns retains the dense
sampler's uniform-error guarantee for arbitrary original row order. -/
theorem normalizedBooleanDraw_variation {m n d : ℕ}
    (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (hd : 14≤d) (hR : ∀ i,d^12≤R i) (hP : ∀ j,d^12≤P j)
    (hdimR : Fintype.card (Option (Fin m))≤d) (hdimP : Fintype.card (Option (Fin n))≤d)
    (hfree : Fintype.card (Fin m×Fin n)≤d) (htotal : ∑ i,R i=∑ j,P j)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (m*n))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (m*n)) (4*d^8)))
    (h : ℕ) (a : Grid (I := Fin (m*n)) (4*d^8)) (fallback : Table R P) :
    let _ : Nonempty (Table R P) := ⟨fallback⟩
    (variation (mapLaw (uniformLaw (α := Fin (normalizedDrawBits R P d h) → Bool))
      (normalizedBooleanDraw R P hd hR hP htotal h a fallback))
      (uniformLaw (α := Table R P)) : ℝ)≤(2:ℝ)^(-(h:ℝ)) := by
  let E : Table R P ≃ Table (normalizedMargin R) (normalizedMargin P) :=
    tableReindex (indexPermutation (marginPosition R)) (indexPermutation (marginPosition P)) R P
  let : Nonempty (Table R P) := ⟨fallback⟩
  let : Nonempty (Table (normalizedMargin R) (normalizedMargin P)) := ⟨E fallback⟩
  have ht : (∑ i,normalizedMargin R i)=∑ j,normalizedMargin P j := by
    rw [normalizedMargin_total,normalizedMargin_total]
    exact htotal
  have he := denseBooleanDraw_variation (normalizedMargin R) (normalizedMargin P) d hd
    (normalizedMargin_lower R _ hR) (normalizedMargin_lower P _ hP)
    (normalizedMargin_max R) (normalizedMargin_max P) hdimR hdimP hfree ht
    finProdFinEquiv hPL hCheeger h a (E fallback)
  dsimp only at ⊢
  change (variation (mapLaw (uniformLaw (α := Fin (denseDrawBits (normalizedMargin R)
    (normalizedMargin P) d finProdFinEquiv h) → Bool))
    (fun bits => E.symm (denseBooleanDraw (normalizedMargin R) (normalizedMargin P) d hd
      (normalizedMargin_lower R _ hR) (normalizedMargin_lower P _ hP)
      finProdFinEquiv ht h a (E fallback) bits))) (uniformLaw (α := Table R P)) : ℝ)≤_
  rw [mapLaw_equiv_output]
  change (variation (equivLaw E.symm (denseBooleanDrawLaw (normalizedMargin R) (normalizedMargin P)
    d hd (normalizedMargin_lower R _ hR) (normalizedMargin_lower P _ hP)
    finProdFinEquiv ht h a (E fallback))) (uniformLaw (α := Table R P)) : ℝ)≤_
  rw [←uniform_equiv E.symm,variation_equiv]
  exact he

end
end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseCanonicalProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Dense sampling from margins with a computed grid and fallback -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped ProfilePrograms

def canonicalDenseDraw (z : CanonicalDrawData) : MatrixCode :=
  normalizedDenseCode (canonicalInput z)

def canonicalDenseDrawRealizer : Realizer canonicalDenseDraw :=
  composition canonicalInputRealizer normalizedDenseCodeRealizer

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseCanonicalSemantics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Correctness of dense sampling with computed initialization -/

namespace ContingencyTables.DensePrograms
open GridBoundary FairBits ResidualMixture FirstSuccess
open scoped BigOperators Classical

noncomputable section

def canonicalFallback {m n : ℕ} (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (htotal : (∑ i,R i)=∑ j,P j) : Table R P :=
  (tableReindex (finSuccEquiv m) (finSuccEquiv n) R P).symm
    (GreedyFeasibleTable.table (fun i => R (finSuccEquiv m i))
      (fun j => P (finSuccEquiv n j)) (by
        rw [(finSuccEquiv m).sum_comp,(finSuccEquiv n).sum_comp]
        exact htotal))

/-- The initialized dense call retains the stated error for every
margin ordering and uses only the published analytic inputs. -/
theorem canonicalDenseDraw_variation {m n d : ℕ}
    (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (hd : 14≤d) (hR : ∀ i,d^12≤R i) (hP : ∀ j,d^12≤P j)
    (hdimR : Fintype.card (Option (Fin m))≤d) (hdimP : Fintype.card (Option (Fin n))≤d)
    (hfree : Fintype.card (Fin m×Fin n)≤d) (htotal : (∑ i,R i)=∑ j,P j)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (m*n))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (m*n)) (4*d^8))) (h : ℕ) :
    let _ : Nonempty (Table R P) := ⟨canonicalFallback R P htotal⟩
    (variation (mapLaw (uniformLaw (α := Fin (normalizedDrawBits R P d h) → Bool))
      (normalizedBooleanDraw R P hd hR hP htotal h
        (canonicalOrigin (m*n) d (by omega)) (canonicalFallback R P htotal)))
      (uniformLaw (α := Table R P)) : ℝ)≤(2:ℝ)^(-(h:ℝ)) :=
  normalizedBooleanDraw_variation R P hd hR hP hdimR hdimP hfree htotal hPL hCheeger h _ _

end
end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseReservedWord
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing and consuming the exact dense-word prefix -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped ProfilePrograms FirstSuccess

def reservedCanonicalDraw (z : CanonicalDrawData) : MatrixCode :=
  canonicalDenseDraw (z.1,z.2.take (canonicalBitCount z.1))

def reservedCanonicalDrawRealizer : Realizer reservedCanonicalDraw :=
  composition (pair first (composition (pair second
    (composition first canonicalBitCountRealizer)) takeFast)) canonicalDenseDrawRealizer

open GridBoundary
open scoped BigOperators Classical
end ContingencyTables.DensePrograms

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

abbrev ResidualDrawData := ResidualParameters×List Bool

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_LargeMarginSemantics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact indexing of the computed large residual margins -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms PaddedCompletions SmallContextCoordinates SmallContextFibres
open PhysicalCompletionFibres FirstPaperProfiles CompletionCounts
open scoped BigOperators Classical

noncomputable section
variable {m n q : ℕ}

def largeMemberEquiv (r : Fin m → ℕ) (U : ℕ) :
    {i // i∈largeIndices (U,List.ofFn r)} ≃ LargeRows r U where
  toFun x := by
    have hm := (mem_largeIndices U (List.ofFn r) x.val).mp x.property
    have hi : x.val < m := by simpa only [List.length_ofFn] using hm.1
    exact ⟨⟨x.val,hi⟩,(largeIndices_ofFn_mem r U ⟨x.val,hi⟩).mp x.property⟩
  invFun i := ⟨i.val.val,(largeIndices_ofFn_mem r U i.val).mpr i.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Increasing list order gives a fixed, computed indexing of every
large row. The same construction is used for columns. -/
def largeIndexEquiv (r : Fin m → ℕ) (U : ℕ) :
    Fin (largeIndices (U,List.ofFn r)).length ≃ LargeRows r U :=
  (List.Nodup.getEquiv _ (largeIndices_nodup U (List.ofFn r))).trans (largeMemberEquiv r U)

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_LargeMarginReference
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computed reference coordinates for the large completion rectangle -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms SmallContextCoordinates SmallContextFibres
open PhysicalCompletionFibres FirstPaperProfiles PaddedCompletions CompletionCounts
open scoped BigOperators Classical

noncomputable section
variable {m n q : ℕ}

def largeOptionEquiv (r : Fin m → ℕ) (U : ℕ)
    (hr : 0 < (largeIndices (U,List.ofFn r)).length) :
    Option (Fin ((largeIndices (U,List.ofFn r)).length-1)) ≃ LargeRows r U :=
  (optionIndexEquiv _ hr).trans (largeIndexEquiv r U)

def listedRows (r : Fin m → ℕ) (c : Fin n → ℕ) (U L : ℕ)
    (B : Fin m → Fin n → ℕ) (hr : 0 < (largeIndices (U,List.ofFn r)).length)
    (z : PhysicalStates (firstPaperSmall r c U) B r c L) :
    Option (Fin ((largeIndices (U,List.ofFn r)).length-1)) → ℕ :=
  fun i => residualRows (firstPaperSmall r c U) B r c L z (largeOptionEquiv r U hr i).val

def listedColumns (r : Fin m → ℕ) (c : Fin n → ℕ) (U L : ℕ)
    (B : Fin m → Fin n → ℕ) (hc : 0 < (largeIndices (U,List.ofFn c)).length)
    (z : PhysicalStates (firstPaperSmall r c U) B r c L) :
    Option (Fin ((largeIndices (U,List.ofFn c)).length-1)) → ℕ :=
  fun j => residualColumns (firstPaperSmall r c U) B r c L z (largeOptionEquiv c U hc j).val

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ListedCompletion
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Entry-preserving completion coordinates in computed list order -/

namespace ContingencyTables.SmallGraphProfiles
open PhysicalCompletionFibres FirstPaperPhysicalMarginal CompletionCounts PaddedCompletions
open DensePrograms
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ}
variable (r : Fin m → ℕ) (c : Fin n → ℕ) (U L : ℕ) (B : Fin m → Fin n → ℕ)
variable (hr : 0 < (ProfilePrograms.largeIndices (U,List.ofFn r)).length)
variable (hc : 0 < (ProfilePrograms.largeIndices (U,List.ofFn c)).length)

def listedReferenceIndex (r : Fin m → ℕ) (U : ℕ)
    (hr : 0 < (ProfilePrograms.largeIndices (U,List.ofFn r)).length) :
    Option (Fin ((ProfilePrograms.largeIndices (U,List.ofFn r)).length-1)) ≃
      Option {i : LargeRows r U // i≠largeOptionEquiv r U hr none} :=
  (largeOptionEquiv r U hr).trans (Equiv.optionSubtypeNe (largeOptionEquiv r U hr none)).symm

lemma listedReference_row
    (z : PhysicalStates (firstPaperSmall r c U) B r c L) :
    (fun i => referenceRows r c U L B (largeOptionEquiv r U hr none) z
      (listedReferenceIndex r U hr i))=listedRows r c U L B hr z := by
  funext i
  simp only [referenceRows,listedReferenceIndex,Equiv.trans_apply,Equiv.apply_symm_apply,listedRows]

lemma listedReference_column
    (z : PhysicalStates (firstPaperSmall r c U) B r c L) :
    (fun j => referenceColumns r c U L B (largeOptionEquiv c U hc none) z
      (listedReferenceIndex c U hc j))=listedColumns r c U L B hc z := by
  funext j
  simp only [referenceColumns,listedReferenceIndex,Equiv.trans_apply,Equiv.apply_symm_apply,listedColumns]

def listedFibreEquiv (z : PhysicalStates (firstPaperSmall r c U) B r c L)
    (hcap : ∀ i j,firstPaperSmall r c U i j=false →
      (∑ k,residualRows (firstPaperSmall r c U) B r c L z k)≤B i j) :
    CompletionFibre (firstPaperSmall r c U) B r
      (fun i => r i+rowLargeCount (firstPaperSmall r c U) i*L) c
      (fun j => c j+columnLargeCount (firstPaperSmall r c U) j*L)
      (physicalProfile _ B r c L z) ≃ Table (listedRows r c U L B hr z) (listedColumns r c U L B hc z) := by
  let i₀ := largeOptionEquiv r U hr none
  let j₀ := largeOptionEquiv c U hc none
  have E := (referenceFibreEquiv r c U L B i₀ j₀ z hcap).trans
    (tableReindex (listedReferenceIndex r U hr) (listedReferenceIndex c U hc)
      (referenceRows r c U L B i₀ z) (referenceColumns r c U L B j₀ z))
  exact E.trans (tableMarginTransport _ _ _ _
    (listedReference_row r c U L B hr z) (listedReference_column r c U L B hc z))

theorem listed_totals (z : PhysicalStates (firstPaperSmall r c U) B r c L)
    (hcap : ∀ i j,firstPaperSmall r c U i j=false →
      (∑ k,residualRows (firstPaperSmall r c U) B r c L z k)≤B i j) :
    (∑ i,listedRows r c U L B hr z i)=∑ j,listedColumns r c U L B hc z j := by
  have h := reference_totals r c U L B (largeOptionEquiv r U hr none)
    (largeOptionEquiv c U hc none) z hcap
  rw [←(listedReferenceIndex r U hr).sum_comp
      (referenceRows r c U L B (largeOptionEquiv r U hr none) z),
    ←(listedReferenceIndex c U hc).sum_comp
      (referenceColumns r c U L B (largeOptionEquiv c U hc none) z)] at h
  simpa only [listedReference_row,listedReference_column] using h

include hc in
theorem listed_row_padding (z : PhysicalStates (firstPaperSmall r c U) B r c L)
    (i : Option (Fin ((ProfilePrograms.largeIndices (U,List.ofFn r)).length-1))) :
    L≤listedRows r c U L B hr z i :=
  large_row_padding r c U L B z (largeOptionEquiv r U hr i) (largeOptionEquiv c U hc none)

include hr in
theorem listed_column_padding (z : PhysicalStates (firstPaperSmall r c U) B r c L)
    (j : Option (Fin ((ProfilePrograms.largeIndices (U,List.ofFn c)).length-1))) :
    L≤listedColumns r c U L B hc z j :=
  large_column_padding r c U L B z (largeOptionEquiv r U hr none) (largeOptionEquiv c U hc j)

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ListedDenseDraw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A canonical dense draw in the actual retained completion fibre -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal
open CompletionCounts PaddedCompletions ResidualMixture FirstSuccess FairBits
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ}
variable (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (hr : 0 < (largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn r)).length)
variable (hc : 0 < (largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn c)).length)

abbrev largeTailCount {m : ℕ} (r : Fin m → ℕ) (V : ℕ) : ℕ :=
  (largeIndices (V,List.ofFn r)).length-1

local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "U" => d^20
local notation "L" => d^12
local notation "R" => listedRows r c U L (stateCapacity r c) hr
local notation "P" => listedColumns r c U L (stateCapacity r c) hc
local notation "nr" => largeTailCount r U
local notation "nc" => largeTailCount c U

lemma largeIndices_length_le {m : ℕ} (r : Fin m → ℕ) (V : ℕ) :
    (largeIndices (V,List.ofFn r)).length ≤ m := by
  have h := Fintype.card_congr (largeIndexEquiv r V)
  rw [Fintype.card_fin] at h
  rw [h]
  exact (Fintype.card_subtype_le _).trans_eq (Fintype.card_fin m)

include hr hc in
lemma listed_dimensions :
    Fintype.card (Option (Fin nr)) ≤ d ∧
    Fintype.card (Option (Fin nc)) ≤ d ∧ Fintype.card (Fin nr×Fin nc) ≤ d := by
  have hm := largeIndices_length_le r U
  have hn := largeIndices_length_le c U
  simp only [Fintype.card_option,Fintype.card_fin,Fintype.card_prod,largeTailCount]
  have hmul := Nat.mul_le_mul ((Nat.sub_le (largeIndices (U,List.ofFn r)).length 1).trans hm)
    ((Nat.sub_le (largeIndices (U,List.ofFn c)).length 1).trans hn)
  have hd := dimension_le_allowance (I := Fin m) (J := Fin n)
  simp only [Fintype.card_fin] at hd
  have hdr : m ≤ d := by unfold dimensionAllowance; simp only [Fintype.card_fin]; nlinarith
  have hdc : n ≤ d := by unfold dimensionAllowance; simp only [Fintype.card_fin]; nlinarith
  exact ⟨by omega,by omega,hmul.trans hd⟩

include hr hc in
lemma listed_dimension_fourteen : 14 ≤ d :=
  reference_dimension_fourteen r c U (largeOptionEquiv r U hr none) (largeOptionEquiv c U hc none)

abbrev paperListedEquiv (z : PaperStates r c) : PaperFibre r c z ≃ Table (R z) (P z) :=
  listedFibreEquiv r c U L (stateCapacity r c) hr hc z
    (physical_paper_capacity _ r c _ _ _ dimension_le_allowance z)

lemma listed_paper_totals (z : PaperStates r c) : (∑ i,R z i)=∑ j,P z j :=
  listed_totals r c U L (stateCapacity r c) hr hc z
    (physical_paper_capacity _ r c _ _ _ dimension_le_allowance z)

lemma listed_row_bound (z : PaperStates r c) (i : Option (Fin nr)) : R z i ≤ stateBound r c := by
  have h := reference_row_le_stateBound r c (largeOptionEquiv r U hr none) z
    (listedReferenceIndex r U hr i)
  have he := congrFun (listedReference_row r c U L (stateCapacity r c) hr z) i
  exact he ▸ h

abbrev listedDrawBits (h : ℕ) (z : PaperStates r c) := normalizedDrawBits (R z) (P z) d h

def listedDenseDraw (h : ℕ) (z : PaperStates r c)
    (bits : Fin (listedDrawBits r c hr hc h z) → Bool) : PaperFibre r c z :=
  (paperListedEquiv r c hr hc z).symm
    (normalizedBooleanDraw (R z) (P z) (listed_dimension_fourteen r c hr hc)
      (listed_row_padding r c U L (stateCapacity r c) hr hc z)
      (listed_column_padding r c U L (stateCapacity r c) hr hc z)
      (listed_paper_totals r c hr hc z) h
      (canonicalOrigin (nr*nc) d (by have := listed_dimension_fourteen r c hr hc; omega))
      (canonicalFallback (R z) (P z) (listed_paper_totals r c hr hc z)) bits)

theorem listedDrawBits_le (b h : ℕ) (hb : Nat.clog 2 (stateBound r c+2) ≤ b)
    (z : PaperStates r c) : listedDrawBits r c hr hc h z ≤ 25*(d+b+h+1)^62 := by
  apply normalizedDrawBits_polynomial (R z) (P z) d (stateBound r c) b h
  · simpa only [Fintype.card_prod,Fintype.card_fin] using (listed_dimensions r c hr hc).2.2
  · exact listed_row_bound r c hr z
  · exact hb

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ListedReservedDraw
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A common fixed word for all computed residual completion draws -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

def reservedResidualDraw (z : ResidualDrawData) : DensePrograms.MatrixCode :=
  DensePrograms.reservedCanonicalDraw (residualParameters z.1,z.2)

def reservedResidualDrawRealizer : Realizer reservedResidualDraw :=
  composition (pair (composition first residualParametersRealizer) second)
    DensePrograms.reservedCanonicalDrawRealizer

end ContingencyTables.ProfilePrograms

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal
open SmallContextCoordinates CompletionCounts ResidualMixture FirstSuccess FairBits
open scoped BigOperators Classical

noncomputable section
variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (hr : 0 < (largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn r)).length)
variable (hc : 0 < (largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn c)).length)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)

def listedPaddedDraw (b h : ℕ) (hb : Nat.clog 2 (stateBound r c+2) ≤ b)
    (z : PaperStates r c) (bits : Fin (25*(d+b+h+1)^62) → Bool) : PaperFibre r c z :=
  listedDenseDraw r c hr hc h z (prefixWord (listedDrawBits_le r c hr hc b h hb z) bits)

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_TranslationDecisionProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary arithmetic for the completion translation test -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped ProfilePrograms CompletionTranslation
open scoped BigOperators

def starPartsRealizer : Realizer starParts :=
  composition (pair (pair first (constant [])) second) completionPartsRealizer

def translationPartsRealizer : Realizer translationParts := by
  let old : Realizer (fun z : TranslationCell => starParts (z.1.1,z.2)) :=
    composition (f := fun z : TranslationCell => (z.1.1,z.2)) (g := starParts)
      (pair (composition first first) second) starPartsRealizer
  let new : Realizer (fun z : TranslationCell => starParts (z.1.2,z.2)) :=
    composition (f := fun z : TranslationCell => (z.1.2,z.2)) (g := starParts)
      (pair (composition first second) second) starPartsRealizer
  exact pair (composition (pair (composition new first) (composition old second)) add)
    (composition (pair (composition new second) (composition old first)) add)

def translatedCellRealizer : Realizer translatedCell := by
  let parts : Realizer (fun z : TranslationData×(ℕ×ℕ) => translationParts (z.1.1,z.2)) :=
    composition (pair (composition first first) second) translationPartsRealizer
  let entry : Realizer (fun z : TranslationData×(ℕ×ℕ) => matrixEntry (z.1.2,z.2)) :=
    composition (pair (composition first second) second) matrixEntryRealizer
  exact composition (pair (composition parts second)
    (composition (pair entry (composition parts first)) add)) leNat

def translationValidRealizer : Realizer translationValid :=
  (composition (composition (pair identity (composition (composition first first) cellPairsRealizer))
    (mapWith translatedCellRealizer)) all).congr
    (by intro z; simp only [Function.comp_apply,Function.comp_def,List.all_map,id_eq,translationValid])

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileTransitionProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A binary small-profile transition with a fresh dense completion -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

abbrev ProfileStepInput := ResidualParameters×(List Bool×List Bool)

def stepCheck : Realizer (fun z : ProfileStepInput => z.1.1.1) :=
  composition (composition first first) first

def stepViews : Realizer (fun z : ProfileStepInput => z.1.1.1.1.1.2) :=
  composition (f := fun z : ProfileStepInput => z.1.1.1)
    (g := fun z : ProfileCheckData => z.1.1.2) stepCheck profileViews

def stepProposal (z : ProfileStepInput) : Option (List ℕ×List ℕ) :=
  codeNeighborProposal (z.1.1.1,z.2.1)

def stepCandidateViews (z : ProfileStepInput) : List ℕ×List ℕ :=
  (stepProposal z).getD z.1.1.1.1.1.2

def stepCandidate (z : ProfileStepInput) : ProfileCheckData :=
  candidateData (z.1.1.1,stepCandidateViews z)

def stepCandidateParameters (z : ProfileStepInput) : ResidualParameters :=
  ((stepCandidate z,z.1.1.2),z.1.2)

def stepOldMargins (z : ProfileStepInput) : DensePrograms.MarginPair :=
  (residualParameters z.1).1

def stepOldMarginsRealizer : Realizer stepOldMargins :=
  composition (f := fun z : ProfileStepInput => residualParameters z.1)
    (g := fun z : DensePrograms.CanonicalParameters => z.1)
    (composition (f := fun z : ProfileStepInput => z.1) (g := residualParameters)
      first residualParametersRealizer) first

def stepNewMargins (z : ProfileStepInput) : DensePrograms.MarginPair :=
  (residualParameters (stepCandidateParameters z)).1

def stepCompletion (z : ProfileStepInput) : DensePrograms.MatrixCode :=
  reservedResidualDraw (z.1,z.2.2)

def stepCompletionRealizer : Realizer stepCompletion :=
  composition (f := fun z : ProfileStepInput => (z.1,z.2.2))
    (g := reservedResidualDraw) (pair first (composition second second)) reservedResidualDrawRealizer

def stepTranslation (z : ProfileStepInput) : DensePrograms.TranslationData :=
  ((stepOldMargins z,stepNewMargins z),stepCompletion z)

def profileStep (z : ProfileStepInput) : List ℕ×List ℕ :=
  if DensePrograms.translationValid (stepTranslation z) then stepCandidateViews z else z.1.1.1.1.1.2

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_BoundedProfileWalk
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial loop for the encoded small-profile walk -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped Polynomial

def capViews (z : ProfileCheckData×(List ℕ×List ℕ)) : List ℕ×List ℕ :=
  (capView ((z.1.1.1.1.length,z.1.2),z.2.1),capView ((z.1.1.1.1.length,z.1.2),z.2.2))

def capBounds (z : ProfileCheckData×(List ℕ×List ℕ)) : ℕ×ℕ :=
  (z.1.1.1.1.length,z.1.2)

def capBoundsRealizer : Realizer capBounds :=
  pair (composition (composition
    (f := fun z : ProfileCheckData×(List ℕ×List ℕ) => z.1)
    (g := fun z : ProfileCheckData => z.1.1.1) first profileCatalog) listLength)
    (composition first second)

abbrev ProfileConfiguration := ResidualParameters×(List ℕ×List ℕ)

def currentParameters (z : ProfileConfiguration) : ResidualParameters :=
  ((candidateData (z.1.1.1,z.2),z.1.1.2),z.1.2)

def currentParametersRealizer : Realizer currentParameters :=
  pair (pair (composition (pair (composition (composition first first) first) second)
      candidateDataRealizer) (composition (composition first first) second))
    (composition first second)

def boundedNext (z : ProfileConfiguration×ProfileWord) : List ℕ×List ℕ :=
  capViews (z.1.1.1.1,profileStep (currentParameters z.1,z.2))

def advanceProfile (z : ProfileWord×ProfileConfiguration) : ProfileConfiguration :=
  (z.2.1,boundedNext (z.2,z.1))

def profileWalk (z : ProfileConfiguration×List ProfileWord) : ProfileConfiguration :=
  z.2.foldl (fun state word => advanceProfile (word,state)) z.1

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingPositiveProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One executed positive-label counting run

The supplied word is partitioned into equally padded phase words. The phase
count only truncates a supplied list, so malformed scalar inputs do
not create an unbounded loop.
-/
namespace ContingencyTables.CountingPositiveProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms

abbrev Request := CountingDirectProgram.Request

end ContingencyTables.CountingPositiveProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseTableCoordinates
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reading the unique bin and offset of an accepted table -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped GridBoundary ProfilePrograms
open scoped BigOperators Classical

def tableFreeValueRealizer : Realizer tableFreeValue :=
  composition (pair (composition (composition first first) second)
    (composition shiftedCellRealizer second)) matrixEntryRealizer

def tableBinCoordinateRealizer : Realizer tableBinCoordinate :=
  composition (pair tableFreeValueRealizer gridCellWidthRealizer) quotient

def tableOffsetCoordinateRealizer : Realizer tableOffsetCoordinate :=
  composition (pair tableFreeValueRealizer gridCellWidthRealizer) remainder

def tableFreeCellsRealizer : Realizer tableFreeCells :=
  composition (pair identity (constant 0)) freeCellsRealizer

def tableBinCoordinatesRealizer : Realizer tableBinCoordinates :=
  composition (pair identity tableFreeCellsRealizer) (mapWith tableBinCoordinateRealizer)

def tableOffsetCoordinatesRealizer : Realizer tableOffsetCoordinates :=
  composition (pair identity tableFreeCellsRealizer) (mapWith tableOffsetCoordinateRealizer)

def tableWidthsRealizer : Realizer tableWidths :=
  composition (pair identity tableFreeCellsRealizer) (mapWith gridCellWidthRealizer)

def tableCoordinatesCode {m n : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (d : ℕ) (X : Table R P) : ExponentData :=
  (((marginCode R,marginCode P),tableOutput X),d)

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_NatListEquality
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary list equality for matching tabulated states and outputs -/

namespace ContingencyTables.NatListEquality
open MatchingFPRAS MatchingFPRAS.TreeTyped

def indicesRealizer : Realizer indices := composition (composition first listLength) range

def atEqualRealizer : Realizer atEqual :=
  composition (pair
    (composition (pair (composition first first) second) (getDFast 0))
    (composition (pair (composition first second) second) (getDFast 0))) natEqual

def listEqualRealizer : Realizer listEqual :=
  (composition (pair
    (composition (pair (composition first listLength) (composition second listLength)) natEqual)
    (composition (composition (pair identity indicesRealizer) (mapWith atEqualRealizer)) all))
    boolAnd).congr (by
      intro z
      simp only [Function.comp_apply,List.all_map,Function.comp_def,id_eq,listEqual])

end ContingencyTables.NatListEquality

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_AxisProposalTest
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Testing dense adjacency by the polynomial list of signed directions -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped GridBoundary

def axisNumberStepRealizer : Realizer axisNumberStep :=
  composition (pair (pair first (composition (pair second (constant 2)) quotient))
    (composition (pair (composition (pair second (constant 2)) remainder) (constant 1)) natEqual))
      axisListStepRealizer

def proposalMatchesRealizer : Realizer proposalMatches :=
  composition (pair identity
    (composition (pair (composition first first) second) axisNumberStepRealizer))
    (optionCases (constant false)
      (composition (pair second (composition (composition first first) second))
        NatListEquality.listEqualRealizer))

def proposalIndicesRealizer : Realizer proposalIndices := by
  let L : Realizer (fun z : ProposalTestData => z.1.2.length) :=
    composition (composition first second) listLength
  let M := composition (pair (constant 2) L) multiply
  exact composition M range

def hasProposalRealizer : Realizer hasProposal :=
  (composition (composition (pair identity proposalIndicesRealizer)
    (mapWith proposalMatchesRealizer)) any).congr (by
      intro z
      simp only [Function.comp_apply,List.any_map,id_eq,Function.comp_def,hasProposal])

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseCountProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executable dense off-diagonal counts without acceptance-word enumeration -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms GridBoundary
open scoped Classical

def countProposalInputRealizer : Realizer countProposalInput := by
  let D : Realizer (fun z : CountInput => z.1.2) := composition first second
  let K := composition (pair (constant 4) (composition D eighthPower)) multiply
  let X : Realizer (fun z : CountInput => z.1.1.2) :=
    composition (composition first first) second
  exact pair (pair K X) second

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_PreparedDenseCount
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial transition entries with a shared acceptance allowance -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms GridBoundary
open scoped BigOperators Classical

def preparedGapRealizer : Realizer preparedGap :=
  composition (pair
    (composition (composition second replaceFlatRealizer) flatExponentRealizer)
    (composition (composition second first) flatExponentRealizer)) subtract

def preparedOffCountRealizer : Realizer preparedOffCount := by
  let pin : Realizer (fun z : PreparedCountInput => (z.1,preparedGap z)) :=
    pair first preparedGapRealizer
  let powered := composition pin BoundedPowerPrograms.powerRealizer
  exact choose (composition (composition second countProposalInputRealizer) hasProposalRealizer)
    powered (constant 0)

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseMatrixTable
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructing the actual dense transition matrix from its finite states -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms GridBoundary
open scoped BigOperators Classical

def rowOffEntryRealizer : Realizer rowOffEntry :=
  composition (pair
    (composition (composition (composition first first) first) first)
    (pair (composition (composition first first) second) second)) preparedOffCountRealizer

def rowOffCountsRealizer : Realizer rowOffCounts :=
  composition (pair identity second) (mapWith rowOffEntryRealizer)

def rowEntryRealizer : Realizer rowEntry := by
  let current : Realizer (fun z : CountRowData×List ℕ => z.1.1.2.1.2) :=
    composition (composition (composition (composition first first) second) first) second
  let Q : Realizer (fun z : CountRowData×List ℕ => z.1.1.1.2) :=
    composition (composition (composition first first) first) second
  let total := composition (composition
    (first (A := CountRowData) (B := List ℕ)) rowOffCountsRealizer) listSum
  exact choose (composition (pair current second) NatListEquality.listEqualRealizer)
    (composition (pair Q total) subtract) rowOffEntryRealizer

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseMatrixProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial assembly of the dense count matrix in column order -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms GridBoundary
open scoped BigOperators Classical

def countMatrixEntryInputRealizer : Realizer countMatrixEntryInput := by
  let data : Realizer (fun z : (CountMatrixData×List ℕ)×List ℕ => z.1.1) :=
    composition first first
  let ctx := composition data first
  let margins := composition (composition ctx second) first
  let d := composition (composition ctx second) second
  let rowData := pair (pair (composition ctx first) (pair (pair margins second) d))
    (composition data second)
  exact pair rowData (composition first second)

def countMatrixEntryRealizer : Realizer countMatrixEntry :=
  composition countMatrixEntryInputRealizer rowEntryRealizer

def countColumnRealizer : Realizer countColumn :=
  composition (pair identity (composition first second)) (mapWith countMatrixEntryRealizer)

def countMatrixRealizer : Realizer countMatrix :=
  composition (pair identity second) (mapWith countColumnRealizer)

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseMatrixWalk
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary matrix propagation of the implemented dense walk -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms GridBoundary
open scoped BigOperators Classical

def initialEntryRealizer : Realizer initialEntry :=
  choose NatListEquality.listEqualRealizer (constant 1) (constant 0)

def initialVectorRealizer : Realizer initialVector :=
  composition (pair second first) (mapWith initialEntryRealizer)

def matrixWalkInputRealizer : Realizer matrixWalkInput :=
  pair (composition (composition first first) listLength)
    (pair (composition (composition first second) countMatrixRealizer)
      (composition (pair (composition (composition first second) second) second)
        initialVectorRealizer))

def matrixWalkRealizer : Realizer matrixWalk :=
  composition matrixWalkInputRealizer IntegerMatrixPrograms.iterateRealizer

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteGridWords
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit finite-box state enumeration, independent of sampling precision -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped GridBoundary
open scoped BigOperators

def clippedGridPowerInputRealizer : Realizer clippedGridPowerInput :=
  pair (composition first second)
    (composition (pair second (composition (composition first first) listLength)) minNat)

def clippedGridPowerRealizer : Realizer clippedGridPower :=
  composition clippedGridPowerInputRealizer BinaryPowerPrograms.powerRealizer

def gridCoordinateRealizer : Realizer gridCoordinate :=
  composition (pair
    (composition (pair (composition first second)
      (composition (pair (composition first first) second) clippedGridPowerRealizer)) quotient)
    (composition (composition first first) second)) remainder

def gridCoordinateIndicesRealizer : Realizer gridCoordinateIndices :=
  composition (composition (composition first first) listLength) range

def gridCoordinatesRealizer : Realizer gridCoordinates :=
  composition (pair identity gridCoordinateIndicesRealizer) (mapWith gridCoordinateRealizer)

def gridStateCountRealizer : Realizer gridStateCount :=
  composition (pair identity (composition first listLength)) clippedGridPowerRealizer

def gridWordsRealizer : Realizer gridWords :=
  composition (pair identity (composition gridStateCountRealizer range))
    (mapWith gridCoordinatesRealizer)

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseEnumeratedMatrix
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing every state of the dense transition table -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms GridBoundary
open scoped BigOperators

def enumerationDataRealizer : Realizer enumerationData := by
  let d : Realizer (fun z : EnumeratedMatrixInput => z.1.2.2) :=
    composition (composition first second) second
  let K := composition (pair (constant 4) (composition d eighthPower)) multiply
  exact pair second K

def enumeratedMatrixInputRealizer : Realizer enumeratedMatrixInput :=
  pair first (composition enumerationDataRealizer gridWordsRealizer)

def enumerationMeasure (z : EnumeratedMatrixInput) : ℕ :=
  gridStateCount (enumerationData z)+weight z

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_UnaryMarkers
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructing the bounded unary loop markers used in tabulation -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped

def unaryMarkersRealizer : Realizer unaryMarkers :=
  composition range (map (constant false))

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseWalkTabulation
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Canonical dense-walk tabulation from binary margins and precision -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms GridBoundary
open scoped BigOperators Classical

def tabulationStepsRealizer : Realizer tabulationSteps := by
  let d : Realizer (fun z : TabulationData => z.2.1) := composition second first
  let h : Realizer (fun z : TabulationData => z.2.2) := composition second second
  exact (composition (pair (composition d fiftiethPower)
    (composition (composition h successor) squareNat)) multiply).congr (by
      intro z; simp only [Function.comp_apply,tabulationSteps,Nat.succ_eq_add_one,pow_two])

def tabulationAllowanceRealizer : Realizer tabulationAllowance := by
  let d : Realizer (fun z : TabulationData => z.2.1) := composition second first
  let result := composition (pair (constant 8) (composition d fifthPower)) multiply
  exact result

def tabulationDenominatorInputRealizer : Realizer tabulationDenominatorInput :=
  pair (constant 2) (composition (composition second first) denseWidthRealizer)

def tabulationDenominatorRealizer : Realizer tabulationDenominator :=
  composition tabulationDenominatorInputRealizer BinaryPowerPrograms.powerRealizer

def tabulationDimensionsRealizer : Realizer tabulationDimensions := by
  let grid := composition (first (A := List ℕ×List ℕ) (B := ℕ×ℕ)) zeroGridRealizer
  let result := composition grid (map (constant false))
  exact result

def tabulationCountInputRealizer : Realizer tabulationCountInput := by
  let marks := composition tabulationAllowanceRealizer unaryMarkersRealizer
  let header := pair (pair marks tabulationDenominatorRealizer)
    (pair (first (A := List ℕ×List ℕ) (B := ℕ×ℕ)) (composition second first))
  exact pair header tabulationDimensionsRealizer

def tabulationMeasure (z : TabulationData) : ℕ :=
  (4*z.2.1^8)^tabulationDimension z+tabulationAllowance z+
    denseStepBits z.2.1+tabulationSteps z+weight z

def tabulationInputRealizer : Realizer tabulationInput := by
  let steps := composition tabulationStepsRealizer unaryMarkersRealizer
  let enum := composition tabulationCountInputRealizer enumeratedMatrixInputRealizer
  let grid := composition (first (A := List ℕ×List ℕ) (B := ℕ×ℕ)) zeroGridRealizer
  exact pair (pair steps enum) grid

def tabulateDenseWalkRealizer : Realizer tabulateDenseWalk :=
  composition tabulationInputRealizer matrixWalkRealizer

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_GridIndexProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary indexing into the explicitly enumerated grid -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped GridBoundary
open scoped BigOperators

def gridIndexPowerInputRealizer : Realizer gridIndexPowerInput :=
  pair (pair (composition (composition first first) (map (constant false)))
    (composition first second)) second

def gridIndexTermRealizer : Realizer gridIndexTerm := by
  let val : Realizer (fun z : GridIndexData×ℕ => z.1.1.getD z.2 0) :=
    composition (pair (composition first first) second) (getDFast 0)
  let power := composition gridIndexPowerInputRealizer clippedGridPowerRealizer
  let result := composition (pair val power) multiply
  exact result

def gridIndexIndicesRealizer : Realizer gridIndexIndices :=
  composition (composition first listLength) range

def gridIndexRealizer : Realizer gridIndex :=
  composition (composition (pair identity gridIndexIndicesRealizer)
    (mapWith gridIndexTermRealizer)) listSum

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_PreparedOffsetCount
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary evaluation of the offset numerator product -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped GridBoundary FairBits
open scoped BigOperators

def preparedOffsetInputRealizer : Realizer preparedOffsetInput := by
  let cap : Realizer (fun z : PreparedOffsetData×ℕ => z.1.1.1.1) :=
    composition (composition (composition first first) first) first
  let widths : Realizer (fun z : PreparedOffsetData×ℕ => z.1.1.1.2) :=
    composition (composition (composition first first) first) second
  let lengths : Realizer (fun z : PreparedOffsetData×ℕ => z.1.1.2) :=
    composition (composition first first) second
  let offsets : Realizer (fun z : PreparedOffsetData×ℕ => z.1.2) := composition first second
  let M := composition (pair widths second) (getDFast 0)
  let r := composition (pair lengths second) (getDFast 0)
  let beta := composition (pair offsets second) (getDFast 0)
  let gap := composition (pair (composition cap listLength) r) subtract
  let Q := composition (pair cap gap) BoundedPowerPrograms.powerRealizer
  exact pair (pair M Q) beta

def preparedOffsetIndicesRealizer : Realizer preparedOffsetIndices :=
  composition (composition (composition (composition first first) second) listLength) range

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseTrialCountProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing one accepted-table numerator from the cached bin vector -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped GridBoundary
open scoped BigOperators Classical

def trialCountIndexInputRealizer : Realizer trialCountIndexInput := by
  let data : Realizer (fun z : TrialCountData => z.2.1) := composition second first
  let d := composition data second
  let K := composition (pair (constant 4) (composition d eighthPower)) multiply
  exact pair (composition data tableBinCoordinatesRealizer) K

def trialCountOffsetInputRealizer : Realizer trialCountOffsetInput := by
  let data : Realizer (fun z : TrialCountData => z.2.1) := composition second first
  exact pair (pair (pair (composition first second) (composition data tableWidthsRealizer))
    (composition second offsetLengthsRealizer)) (composition data tableOffsetCoordinatesRealizer)

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_CompletionEnumerationProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit free-box enumeration with binary completion tests -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms
open scoped BigOperators Classical

def completionEnumerationDataRealizer : Realizer completionEnumerationData := by
  let dims := composition zeroGridRealizer (map (constant false))
  let base : Realizer (fun z : CompletionMargins => z.1.sum+1) :=
    composition (composition first listSum) successor
  exact pair dims base

def completionCandidateRealizer : Realizer completionCandidate :=
  composition (pair first unflattenGridRealizer) acceptCompletionRealizer

def completionCandidatesRealizer : Realizer completionCandidates :=
  composition (pair identity (composition completionEnumerationDataRealizer gridWordsRealizer))
    (mapWith completionCandidateRealizer)

def completionEnumerationMeasure (z : CompletionMargins) : ℕ :=
  gridStateCount (completionEnumerationData z)+weight z

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseCandidateCounts
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact accepted counts throughout the enumerated completion box -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped GridBoundary
open scoped BigOperators Classical

def candidateCountInputRealizer : Realizer candidateCountInput :=
  pair (composition first first)
    (pair (pair (pair (composition (composition first second) first) second)
      (composition (composition (composition first second) second) first))
      (composition (composition (composition first second) second) second))

def candidateCountMeasure (z : TrialCountContext) : ℕ :=
  gridStateCount (completionEnumerationData z.2.1)+weight z

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_RetryNumeratorProgram
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary first-success numerators via a two-coordinate recurrence -/

namespace ContingencyTables.RetryNumeratorPrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped

def twoEntries {A : Type} [Codec A] : Realizer (fun x : A×A => [x.1,x.2]) :=
  composition (pair first (composition second BinaryPowerPrograms.singleton)) listCons

def setupRealizer : Realizer setup := by
  let Q : Realizer (fun z : Input => z.2.1.1) := composition (composition second first) first
  let phi : Realizer (fun z : Input => z.2.1.2) := composition (composition second first) second
  let alpha : Realizer (fun z : Input => z.2.2.1) := composition (composition second second) first
  let hit : Realizer (fun z : Input => z.2.2.2) := composition (composition second second) second
  let column1 := composition (pair phi alpha) twoEntries
  let column2 := composition (pair (constant 0) Q) twoEntries
  let matrix := composition (pair column1 column2) twoEntries
  let initial := choose hit (constant 1) (constant 0)
  let vector := composition (pair initial (constant 1)) twoEntries
  exact pair (composition first listLength) (pair matrix vector)

def countRealizer : Realizer count :=
  composition (composition setupRealizer IntegerMatrixPrograms.iterateRealizer) (head 0)

end ContingencyTables.RetryNumeratorPrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_VectorRetryProgram
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # First-success propagation of an entire vector of integer counts -/

namespace ContingencyTables.VectorRetryPrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped
open scoped BigOperators

def failureRealizer : Realizer failure :=
  composition (pair (composition first second)
    (composition (composition second first) listSum)) subtract

def entryInputRealizer : Realizer entryInput := by
  let markers : Realizer (fun z : Input×ℕ => z.1.1.1) :=
    composition (composition first first) first
  let denominator : Realizer (fun z : Input×ℕ => z.1.1.2) :=
    composition (composition first first) second
  let success : Realizer (fun z : Input×ℕ => z.1.2.1.getD z.2 0) :=
    composition (pair (composition (composition first second) first) second) (getDFast 0)
  let hit : Realizer (fun z : Input×ℕ => decide (z.2=z.1.2.2)) :=
    composition (pair second (composition (composition first second) second)) natEqual
  exact pair markers (pair (pair denominator (composition first failureRealizer)) (pair success hit))

def indicesRealizer : Realizer indices :=
  composition (composition (composition second first) listLength) range

def countsRealizer : Realizer counts :=
  composition (pair identity indicesRealizer)
    (mapWith (composition entryInputRealizer RetryNumeratorPrograms.countRealizer))

end ContingencyTables.VectorRetryPrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_TableIndexProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing the position of a table in the completion enumeration -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped
open scoped BigOperators Classical

def tableFreeCoordinatesRealizer : Realizer tableFreeCoordinates :=
  composition (pair identity tableFreeCellsRealizer) (mapWith tableFreeValueRealizer)

def tableIndexInputRealizer : Realizer tableIndexInput :=
  pair (composition (pair identity (constant 0)) tableFreeCoordinatesRealizer)
    (composition (composition (composition first first) listSum) successor)

def tableIndexRealizer : Realizer tableIndex :=
  composition tableIndexInputRealizer gridIndexRealizer

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseDrawTabulation
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing the full integer law of an initialized dense draw -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms GridBoundary
open scoped BigOperators Classical

def rawDrawParameters (z : CanonicalParameters) : DenseDrawParameters :=
  (((z.1,zeroGrid z.1),z.2.1),z.2.2)

def rawDrawParametersRealizer : Realizer rawDrawParameters := by
  let margins : Realizer (fun z : CanonicalParameters => z.1) := first
  let grid := composition margins zeroGridRealizer
  let result := pair (pair (pair margins grid) (composition second first))
    (composition second second)
  exact result

def rawTrialBits (z : CanonicalParameters) : ℕ := trialWidth (rawDrawParameters z)

def rawTrialBitsRealizer : Realizer rawTrialBits :=
  composition rawDrawParametersRealizer trialWidthRealizer

def rawRepeat (z : CanonicalParameters) : ℕ := z.2.1^4*(z.2.2+1)

def rawRepeatRealizer : Realizer rawRepeat := by
  let d : Realizer (fun z : CanonicalParameters => z.2.1) := composition second first
  let h : Realizer (fun z : CanonicalParameters => z.2.2) := composition second second
  let result := composition (pair (composition d fourthPower)
    (composition h successor)) multiply
  exact result

def rawCountContext (z : CanonicalParameters) : TrialCountContext :=
  ((tabulateDenseWalk z,unaryMarkers (rawTrialBits z)),z)

def rawCountContextRealizer : Realizer rawCountContext := by
  let cap := composition rawTrialBitsRealizer unaryMarkersRealizer
  let result := pair (pair tabulateDenseWalkRealizer cap) identity
  exact result

def rawFallbackIndex (z : CanonicalParameters) : ℕ :=
  tableIndex (z.1,GreedyFeasibleTable.listMatrix z.1.1 z.1.2)

def rawFallbackIndexRealizer : Realizer rawFallbackIndex :=
  composition (pair first (composition first GreedyFeasibleTable.tableRealizer)) tableIndexRealizer

def rawVectorInput (z : CanonicalParameters) : VectorRetryPrograms.Input :=
  ((unaryMarkers (rawRepeat z),BinaryPowerPrograms.power (2,rawTrialBits z)),
    (candidateCounts (rawCountContext z),rawFallbackIndex z))

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_CachedProfileDecision
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reusing the outer transition test on an enumerated completion -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped

abbrev ShortStep := ResidualParameters×List Bool

def shortStepInput (z : ShortStep) : ProfileStepInput := (z.1,(z.2,[]))

def shortStepInputRealizer : Realizer shortStepInput :=
  pair first (pair second (constant []))

def cachedDecisionInput (z : ShortStep×DensePrograms.MatrixCode) : DensePrograms.TranslationData :=
  ((stepOldMargins (shortStepInput z.1),stepNewMargins (shortStepInput z.1)),z.2)

def cachedDecision (z : ShortStep×DensePrograms.MatrixCode) : List ℕ×List ℕ :=
  if DensePrograms.translationValid (cachedDecisionInput z)
    then stepCandidateViews (shortStepInput z.1) else z.1.1.1.1.1.1.2

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_MatrixCodeEquality
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial equality of explicitly stored rectangular arrays -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped

def matrixSignatureRealizer : Realizer matrixSignature := pair (map listLength) flatten

def matrixEqual : Realizer (fun z : MatrixCode×MatrixCode => decide (z.1=z.2)) :=
  (composition (pair (composition first matrixSignatureRealizer)
    (composition second matrixSignatureRealizer)) ProfilePrograms.profileCodeEqual).congr (by
      intro z
      simp only [Function.comp_apply,matrixSignature_injective.eq_iff])

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_CanonicalIntegerLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact finite integer law of the normalized Boolean sampler -/

namespace ContingencyTables.DensePrograms
open GridBoundary FairBits ResidualMixture FirstSuccess
open scoped BigOperators Classical
noncomputable section

variable {m n d : ℕ} (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
variable (hd : 14≤d) (hR : ∀ i,d^12≤R i) (hP : ∀ j,d^12≤P j)
variable (htotal : ∑ i,R i=∑ j,P j) (h : ℕ)

def canonicalCounts : IntegerLaw (Table R P) (2^normalizedDrawBits R P d h) :=
  let E : Table R P ≃ Table (normalizedMargin R) (normalizedMargin P) :=
    tableReindex (indexPermutation (marginPosition R)) (indexPermutation (marginPosition P)) R P
  (denseDrawCounts (normalizedMargin R) (normalizedMargin P) d hd
    (normalizedMargin_lower R _ hR) (normalizedMargin_lower P _ hP) finProdFinEquiv
    (by rw [normalizedMargin_total,normalizedMargin_total]; exact htotal) h
    (canonicalOrigin (m*n) d (by omega)) (E (canonicalFallback R P htotal))).equiv E.symm

theorem canonicalCounts_law :
    (canonicalCounts R P hd hR hP htotal h).toRational (by positivity)=
      mapLaw (uniformLaw (α := Fin (normalizedDrawBits R P d h) → Bool))
        (normalizedBooleanDraw R P hd hR hP htotal h
          (canonicalOrigin (m*n) d (by omega)) (canonicalFallback R P htotal)) := by
  let E : Table R P ≃ Table (normalizedMargin R) (normalizedMargin P) :=
    tableReindex (indexPermutation (marginPosition R)) (indexPermutation (marginPosition P)) R P
  let a := canonicalOrigin (m*n) d (show 0<d by omega)
  let ht : (∑ i,normalizedMargin R i)=∑ j,normalizedMargin P j := by
    rw [normalizedMargin_total,normalizedMargin_total]
    exact htotal
  let p : IntegerLaw (Table (normalizedMargin R) (normalizedMargin P))
      (2^normalizedDrawBits R P d h) :=
    denseDrawCounts (normalizedMargin R) (normalizedMargin P) d hd
      (normalizedMargin_lower R _ hR) (normalizedMargin_lower P _ hP)
      finProdFinEquiv ht h a (E (canonicalFallback R P htotal))
  let draw : (Fin (normalizedDrawBits R P d h) → Bool) →
      Table (normalizedMargin R) (normalizedMargin P) :=
    denseBooleanDraw (normalizedMargin R) (normalizedMargin P) d hd
      (normalizedMargin_lower R _ hR) (normalizedMargin_lower P _ hP)
      finProdFinEquiv ht h a (E (canonicalFallback R P htotal))
  have hp : p.toRational (by positivity)=
      mapLaw (uniformLaw (α := Fin (normalizedDrawBits R P d h) → Bool)) draw :=
    denseDrawCounts_law (normalizedMargin R) (normalizedMargin P) d hd
      (normalizedMargin_lower R _ hR) (normalizedMargin_lower P _ hP)
      finProdFinEquiv ht h a (E (canonicalFallback R P htotal))
  change (p.equiv E.symm).toRational (by positivity)=
    mapLaw (uniformLaw (α := Fin (normalizedDrawBits R P d h) → Bool))
      (fun bits => E.symm (draw bits))
  exact (IntegerLaw.toRational_equiv p E.symm (by positivity)).trans
    ((congrArg (equivLaw E.symm) hp).trans (mapLaw_equiv_output E.symm _ draw).symm)

/-- A reserved word contributes a power of two for its unused suffix. -/
def paddedCanonicalCounts (N : ℕ) (hN : normalizedDrawBits R P d h≤N) :
    IntegerLaw (Table R P) (2^N) :=
  ((canonicalCounts R P hd hR hP htotal h).scale
    (2^(N-normalizedDrawBits R P d h))).rebase (by rw [←pow_add,Nat.add_sub_of_le hN])

theorem paddedCanonicalCounts_law (N : ℕ) (hN : normalizedDrawBits R P d h≤N) :
    (paddedCanonicalCounts R P hd hR hP htotal h N hN).toRational (by positivity)=
      mapLaw (uniformLaw (α := Fin N → Bool))
        (fun bits => normalizedBooleanDraw R P hd hR hP htotal h
          (canonicalOrigin (m*n) d (by omega)) (canonicalFallback R P htotal)
          (prefixWord hN bits)) := by
  unfold paddedCanonicalCounts
  rw [IntegerLaw.toRational_rebase,IntegerLaw.toRational_scale,canonicalCounts_law]
  exact (padded_draw_law hN _).symm
  all_goals positivity

end
end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_BooleanEnumeration
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Enumerating only the short proposal word -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped
open scoped BigOperators Classical

def digitBoolRealizer : Realizer digitBool := composition (pair identity (constant 1)) natEqual

def booleanWordsRealizer : Realizer booleanWords :=
  composition (composition (pair identity (constant 2)) gridWordsRealizer)
    (map (map digitBoolRealizer))

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperIdealRejection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual stationary outer rejection law and its polynomial trial budget -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open ResidualMixture FirstSuccess CompletionCounts

noncomputable section
universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]
variable (r : I → ℕ) (c : J → ℕ)

/-- Read balance and padding, then return the unique unpadded table. -/
abbrev stateTrial : PaperStateJoint r c → Option (Table r c) :=
  partialEquivDraw (StateJointSuccess r c) (originalStateSuccessEquiv r c)

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ListedKernelAccuracy
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Mixing with the computed, canonically initialized completion draw -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal
open ResidualMixture FirstSuccess FairBits CompletionTranslation CompletionCounts
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (hr : 0 < (largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn r)).length)
variable (hc : 0 < (largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn c)).length)
variable (b h : ℕ) (hb : Nat.clog 2 (stateBound r c+2) ≤ b)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "i₀" => largeOptionEquiv r (d^20) hr none
local notation "j₀" => largeOptionEquiv c (d^20) hc none
local notation "R" => referenceRows r c (d^20) (d^12) (stateCapacity r c) i₀
local notation "P" => referenceColumns r c (d^20) (d^12) (stateCapacity r c) j₀

def listedFibreLaw (z : PaperStates r c) : RationalLaw (PaperFibre r c z) :=
  mapLaw (uniformLaw (α := Fin (25*(d+b+h+1)^62) → Bool)) (listedPaddedDraw r c hr hc b h hb z)

def listedReferenceLaw (z : PaperStates r c) : RationalLaw (Table (R z) (P z)) :=
  equivLaw (paperReferenceEquiv r c i₀ j₀ z) (listedFibreLaw r c hr hc b h hb z)

def listedSmallKernel (z : PaperStates r c) : RationalLaw (PaperStates r c) :=
  completionStepLaw R P (smallProposalLaw r c) (listedReferenceLaw r c hr hc b h hb) z


end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ListedBooleanStep
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The computed binary outer step has the proved mixing kernel -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal CompletionCounts
open ResidualMixture FirstSuccess FairBits CompletionTranslation SmallContextCoordinates
open scoped BigOperators Classical

noncomputable section
variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c))
variable (hr : 0 < (largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn r)).length)
variable (hc : 0 < (largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn c)).length)
variable (b h : ℕ) (hb : Nat.clog 2 (stateBound r c+2) ≤ b)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "i₀" => largeOptionEquiv r (d^20) hr none
local notation "j₀" => largeOptionEquiv c (d^20) hc none
local notation "R" => referenceRows r c (d^20) (d^12) (stateCapacity r c) i₀
local notation "P" => referenceColumns r c (d^20) (d^12) (stateCapacity r c) j₀
local notation "s" => smallProposalBits (I := Fin m) (J := Fin n)
local notation "f" => 25*(d+b+h+1)^62

def listedBlockDraw (x : PaperStates r c) (word : Fin f → Bool) : Table (R x) (P x) :=
  paperReferenceEquiv r c i₀ j₀ x (listedPaddedDraw r c hr hc b h hb x word)

def listedBitStep (x : PaperStates r c) (bits : Fin (s+f) → Bool) : PaperStates r c :=
  wordCompletionStep R P (decodedCodeProposal r c e) (listedBlockDraw r c hr hc b h hb) x bits

attribute [local irreducible] FirstSuccess.mapLaw completionStepLaw

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ListedBooleanDraw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Literal finite-word outer sampling with the computed dense draw -/

namespace ContingencyTables.SmallGraphProfiles
open ResidualMixture FirstSuccess CompletionTranslation CompletionCounts FairBits
open ProfilePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal SmallContextCoordinates
open scoped BigOperators Classical

noncomputable section
variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c))
variable (hr : 0 < (largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn r)).length)
variable (hc : 0 < (largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn c)).length)
variable (b h : ℕ) (hb : Nat.clog 2 (stateBound r c+2) ≤ b)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "s" => smallProposalBits (I := Fin m) (J := Fin n)
local notation "f" => 25*(d+b+h+1)^62

def listedFlatWalk (x : PaperStates r c) (n : ℕ)
    (bits : Fin (n*(s+f)) → Bool) : PaperStates r c :=
  wordWalk (listedBitStep r c e hr hc b h hb) x n
    (GridBoundary.gridWordEquiv n (s+f) bits)

def listedJointDraw (x : PaperStates r c) (n : ℕ)
    (bits : Fin (n*(s+f)+f) → Bool) : PaperStateJoint r c :=
  let draws := splitWordEquiv (n*(s+f)) f bits
  let z := listedFlatWalk r c e hr hc b h hb x n draws.1
  ⟨z,listedPaddedDraw r c hr hc b h hb z draws.2⟩

def listedOuterDraw (x : PaperStates r c) (n J₀ : ℕ) (z₀ : Table r c)
    (bits : Fin (J₀*(n*(s+f)+f)) → Bool) : Table r c :=
  wordRetry (fun bitword => stateTrial r c
    (listedJointDraw r c e hr hc b h hb x n bitword)) z₀ J₀
    (GridBoundary.gridWordEquiv J₀ (n*(s+f)+f) bits)


end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ListedIntegerLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integer transition counts for the actual outer-profile walk -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal
open CompletionCounts SmallContextCoordinates ResidualMixture FirstSuccess FairBits CompletionTranslation
open scoped BigOperators Classical
noncomputable section

variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c))
variable (hr : 0<(largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn r)).length)
variable (hc : 0<(largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn c)).length)
variable (b h : ℕ) (hb : Nat.clog 2 (stateBound r c+2)≤b)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "R" => listedRows r c (d^20) (d^12) (stateCapacity r c) hr
local notation "P" => listedColumns r c (d^20) (d^12) (stateCapacity r c) hc
local notation "s" => smallProposalBits (I := Fin m) (J := Fin n)
local notation "f" => 25*(d+b+h+1)^62

def listedCompletionCounts (x : PaperStates r c) : IntegerLaw (PaperFibre r c x) (2^f) :=
  (paddedCanonicalCounts (R x) (P x) (listed_dimension_fourteen r c hr hc)
    (listed_row_padding r c (d^20) (d^12) (stateCapacity r c) hr hc x)
    (listed_column_padding r c (d^20) (d^12) (stateCapacity r c) hr hc x)
    (listed_paper_totals r c hr hc x) h f (listedDrawBits_le r c hr hc b h hb x)).equiv
      (paperListedEquiv r c hr hc x).symm

/-- Completion counts are cached once per state; only the short proposal
word is enumerated to form this finite transition matrix. -/
def listedStepCounts (x : PaperStates r c) : IntegerLaw (PaperStates r c) (2^(s+f)) :=
  IntegerLaw.booleanFinish (listedCompletionCounts r c hr hc b h hb x)
    (fun word A => completionDecision R P x (decodedCodeProposal r c e x word)
      (paperListedEquiv r c hr hc x A))

attribute [local irreducible] listedStepCounts listedSmallKernel

/-- The complete adaptive walk is an integer matrix power. -/
def listedWalkCounts (x : PaperStates r c) (N : ℕ) :
    IntegerLaw (PaperStates r c) ((2^(s+f))^N) :=
  IntegerLaw.walk (listedStepCounts r c e hr hc b h hb) x N

attribute [local irreducible] listedWalkCounts

/-- Each final table count sums over the reached profile and its fresh
terminal completion; failed outer trials retain their exact numerator. -/
def listedTrialCounts (x : PaperStates r c) (N : ℕ) :
    IntegerLaw (Option (Table r c)) ((2^(s+f))^N*2^f) :=
  (listedWalkCounts r c e hr hc b h hb x N).bind
    (fun y => (listedCompletionCounts r c hr hc b h hb y).push
      (fun A => stateTrial r c ⟨y,A⟩))

def listedOuterCounts (x : PaperStates r c) (N J : ℕ) (fallback : Table r c) :
    IntegerLaw (Table r c) (((2^(s+f))^N*2^f)^J) :=
  (listedTrialCounts r c e hr hc b h hb x N).retry fallback J

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_OuterTableProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reconstructing and testing an original table from an outer trial -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped DensePrograms Polynomial

def outputCellPositionRealizer : Realizer outputCellPosition :=
  composition (pair second (composition (composition (composition first first) first) first))
    cellLookupRealizer

def outputSmallEntryRealizer : Realizer outputSmallEntry :=
  composition (pair (composition (composition (composition (composition first first) first) second) first)
    outputCellPositionRealizer) (getDFast 0)

def outputDensePositionRealizer : Realizer outputDensePosition :=
  pair (composition (pair (composition second first)
    (composition (composition (composition first first) second) first)) (indexOf natEqual))
    (composition (pair (composition second second)
      (composition (composition (composition first first) second) second)) (indexOf natEqual))

def outputLargeEntryRealizer : Realizer outputLargeEntry :=
  composition (pair (composition (pair (composition (composition first second) second)
      outputDensePositionRealizer) matrixEntryRealizer)
    (composition (composition (composition first second) first) second)) subtract

def outputEntryRealizer : Realizer outputEntry :=
  (choose (composition (pair outputCellPositionRealizer
      (composition (composition (composition (composition first first) first) first) listLength)) less)
    outputSmallEntryRealizer outputLargeEntryRealizer).congr
      (by intro z; simp only [Function.comp_apply,decide_eq_true_eq,outputEntry])

def paddingTestRealizer : Realizer paddingTest :=
  (composition (mapWith (composition (mapWith leNat) all)) all).congr
    (by intro z; simp only [Function.comp_apply,List.all_map,Function.comp_def,id_eq,paddingTest])

def outputShapeRealizer : Realizer outputShape := pair first (constant [])

def outputRowsRealizer : Realizer outputRows := composition outputShapeRealizer completionRowsRealizer
def outputColumnsRealizer : Realizer outputColumns := composition outputShapeRealizer completionColumnsRealizer

def outputRowEntryRealizer : Realizer outputRowEntry :=
  composition (pair (composition (composition first first) second)
    (pair (composition first second) second)) outputEntryRealizer

def outputRowRealizer : Realizer outputRow :=
  composition (pair identity (composition first outputColumnsRealizer)) (mapWith outputRowEntryRealizer)

def outputMatrixRealizer : Realizer outputMatrix :=
  composition (pair identity outputRowsRealizer) (mapWith outputRowRealizer)

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_OuterTrialProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Preparing the original-table return from a residual draw -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped DensePrograms

abbrev OuterTrialInput := (ProfileCheckData×ℕ)×MatrixCode

def outputLargeRows (z : OuterTrialInput) : List ℕ := largeIndices (z.1.1.2,z.1.1.1.2.1)
def outputLargeColumns (z : OuterTrialInput) : List ℕ := largeIndices (z.1.1.2,z.1.1.1.2.2)

def outputLargeRowsRealizer : Realizer outputLargeRows :=
  composition (pair (composition (composition first first) second)
    (composition (composition (composition (composition first first) first) second) first))
    largeIndicesRealizer
def outputLargeColumnsRealizer : Realizer outputLargeColumns :=
  composition (pair (composition (composition first first) second)
    (composition (composition (composition (composition first first) first) second) second))
    largeIndicesRealizer

def outputData (z : OuterTrialInput) : OuterTableData :=
  ((z.1.1.1.1,(outputLargeRows z,outputLargeColumns z)),((z.1.1.2,z.1.2),z.2))
def outputDataRealizer : Realizer outputData :=
  pair (pair (composition (composition (composition first first) first) first)
      (pair outputLargeRowsRealizer outputLargeColumnsRealizer))
    (pair (pair (composition (composition first first) second) (composition first second)) second)

def prepareOutput (z : OuterTrialInput) : OuterMatrixInput := (z.1.1.1.2,outputData z)
def prepareOutputRealizer : Realizer prepareOutput :=
  pair (composition (composition (composition first first) first) second) outputDataRealizer

def outerTrial (z : OuterTrialInput) : Option MatrixCode := acceptedTable (prepareOutput z)

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileTransitionCountSemantics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executed cached transitions have the actual walk's integer counts -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal
open SmallContextCoordinates CompletionCounts CompletionTranslation
open scoped BigOperators Classical
noncomputable section

variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c))
variable (hr : 0<(largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn r)).length)
variable (hc : 0<(largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn c)).length)
variable (b h : ℕ) (hb : Nat.clog 2 (stateBound r c+2)≤b)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "R" => listedRows r c (d^20) (d^12) (stateCapacity r c) hr
local notation "P" => listedColumns r c (d^20) (d^12) (stateCapacity r c) hc
local notation "s" => smallProposalBits (I := Fin m) (J := Fin n)
local notation "f" => 25*(d+b+h+1)^62

attribute [local irreducible] canonicalCounts listedStepCounts listedCompletionCounts
  normalizedDrawBits stateCode stateCodeData listedRows listedColumns
  completionDecision 

def listedUnpaddedCounts (x : PaperStates r c) :
    IntegerLaw (Table (R x) (P x)) (2^normalizedDrawBits (R x) (P x) d h) :=
  canonicalCounts (R x) (P x) (listed_dimension_fourteen r c hr hc)
    (listed_row_padding r c (d^20) (d^12) (stateCapacity r c) hr hc x)
    (listed_column_padding r c (d^20) (d^12) (stateCapacity r c) hr hc x)
    (listed_paper_totals r c hr hc x) h

def listedCompletionFactor (x : PaperStates r c) : ℕ :=
  2^(f-normalizedDrawBits (R x) (P x) d h)

def listedCachedDecision (x : PaperStates r c) (word : Fin s → Bool)
    (A : Table (R x) (P x)) : PaperStates r c :=
  completionDecision R P x (decodedCodeProposal r c e x word) A

attribute [local irreducible] listedUnpaddedCounts listedCompletionFactor listedCachedDecision

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_CachedTerminalSemantics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cached terminal success counts equal the actual completion law -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal
open SmallContextCoordinates CompletionCounts CompletionTranslation
open scoped BigOperators Classical
noncomputable section

variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c))
variable (hr : 0<(largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn r)).length)
variable (hc : 0<(largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn c)).length)
variable (b h : ℕ) (hb : Nat.clog 2 (stateBound r c+2)≤b)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "R" => listedRows r c (d^20) (d^12) (stateCapacity r c) hr
local notation "P" => listedColumns r c (d^20) (d^12) (stateCapacity r c) hc

attribute [local irreducible] canonicalCounts listedCompletionCounts listedUnpaddedCounts
  listedCompletionFactor stateCode stateCodeData listedRows listedColumns

def listedTerminalDecision (x : PaperStates r c) (A : Table (R x) (P x)) :
    Option (Table r c) := stateTrial r c ⟨x,(paperListedEquiv r c hr hc x).symm A⟩

attribute [local irreducible] listedTerminalDecision

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_OnlineTree
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineTree
open Turing MachineCost PhysicalStream OnlineStack TreeData TreeMachine TreeFunction TreeTyped

def initial (P : OnlineProc.Proc (K Reg)) (x s : Data) : StoreCfg P :=
  ⟨some default,none,encodeEnv (env x .nil s)⟩
def final (P : OnlineProc.Proc (K Reg)) (x s : Data) : StoreCfg P :=
  ⟨none,none,encodeEnv (env x .nil s)⟩
structure Realizer {A B : Type} [Codec A] [Codec B] (f : A → Experiment B) where
  program : OnlineProc.Proc (K Reg)
  cost : A → ℕ
  correct : ∀ a s,∃ q : Experiment B,
    Executes program.code program.coin (fun b=>final program (encode b) s)
      (initial program (encode a) s) q ∧
    (∀ g : B → ℚ,q.mean g=(f a).mean g) ∧ q.cost ≤ cost a
variable {A B C : Type} [Codec A] [Codec B] [Codec C]

def deterministic {f : A → B} (F : TreeTyped.Realizer f) : Realizer (fun a=>.done (f a)) where
  program := OnlineProc.deterministic F.program
  cost := F.cost
  correct := by
    intro a s
    obtain ⟨n,hn,he⟩:=F.correct a s
    obtain ⟨p,hp,hm,hc⟩:=Executes.of_run F.program.code n _ _ _ he
    refine ⟨p.map (fun _=>f a),?_,?_,?_⟩
    · exact hp.bind (fun _=>.done (f a)) _ (fun _=>.done (f a))
    · intro g
      rw [Experiment.mean_map,hm]; rfl
    · rw [Experiment.cost_map]
      exact hc.trans hn

noncomputable def composition {f : A → Experiment B} {g : B → Experiment C}
    (F : Realizer f) (G : Realizer g) : Realizer (fun a=>(f a).bind g) where
  program := OnlineProc.seq F.program G.program
  cost := fun a=>F.cost a+(f a).worst G.cost
  correct := by
    intro a s
    obtain ⟨p,hp,hm,hc⟩:=F.correct a s
    choose q hq hqm hqc using fun b=>G.correct b s
    have hp':=hp.relabel (OnlineProc.seq F.program G.program).code (OnlineProc.seq F.program G.program).coin
      Sum.inl (some (Sum.inr default)) (fun _=>rfl) (fun _=>rfl)
    have hq' b := (hq b).relabel (OnlineProc.seq F.program G.program).code (OnlineProc.seq F.program G.program).coin
      Sum.inr none (fun _=>rfl) (fun _=>rfl)
    refine ⟨p.bind q,hp'.bind q _ hq',?_,?_⟩
    · intro h
      simp_rw [Experiment.mean_bind,hqm]
      exact hm _
    · apply (Experiment.cost_bind_le_of_all p q ((f a).worst G.cost) ?_).trans (Nat.add_le_add_right hc _)
      exact (Experiment.all_of_mean_eq hm _ (Experiment.all_worst (f a) G.cost)).mono
        (fun b hb=>(hqc b).trans hb)

def Realizer.congr {f g : A → Experiment B} (F : Realizer f)
    (h : ∀ a w,(f a).mean w=(g a).mean w) : Realizer g where
  program := F.program
  cost := F.cost
  correct := by
    intro a s
    obtain ⟨q,hq,hm,hc⟩:=F.correct a s
    exact ⟨q,hq,fun w=>(hm w).trans (h a w),hc⟩

noncomputable def choose {f g : A → Experiment B} (F : Realizer f) (G : Realizer g) :
    Realizer (fun a=>.read (fun b=>if b then g a else f a)) where
  program := chooseProgram F.program G.program
  cost := fun a=>1+max (F.cost a) (G.cost a)
  correct := by
    intro a s
    obtain ⟨p,hp,hm,hc⟩:=F.correct a s
    obtain ⟨q,hq,hqm,hqc⟩:=G.correct a s
    have hp':=hp.relabel (chooseProgram F.program G.program).code (chooseProgram F.program G.program).coin
      (fun u=>Sum.inr (Sum.inl u)) none (fun _=>rfl) (fun _=>rfl)
    have hq':=hq.relabel (chooseProgram F.program G.program).code (chooseProgram F.program G.program).coin
      (fun u=>Sum.inr (Sum.inr u)) none (fun _=>rfl) (fun _=>rfl)
    refine ⟨.read (fun b=>if b then q else p),?_,?_,?_⟩
    · apply Executes.read _ _ _ _ _ rfl
      intro b
      cases b
      · exact hp'
      · exact hq'
    · intro h
      simp only [Experiment.mean,Bool.false_eq_true,↓reduceIte,hm,hqm]
    · simp only [Experiment.cost,Bool.false_eq_true,↓reduceIte]
      omega

end MatchingFPRAS.OnlineTree

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_OnlineFold
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineTree
open TreeData TreeMachine RegisterProc TreeFunction TreeTyped
open Turing MachineCost PhysicalStream OnlineStack

variable {A B : Type} [Codec A] [Codec B]

namespace Fold
open OnlineControl
open TreeTyped.Fold (Point)

noncomputable def cost (f : A×B → Experiment B) (t : A×B → ℕ) : List A → B → ℕ
  | [],_ => 10
  | a::as,b => t (a,b)+6*TreeFunction.size (encode a)+8*TreeFunction.size (encode as)+34+
      (f (a,b)).worst (cost f t as)

lemma runs {f : A×B → Experiment B} (F : Realizer f) (as : List A) (b : B) (s : Data) :
    ∃ q,At (code F.program) (fun b=>env (encode b) .nil s) (Option.some Point.loop)
      (env (encode (as,b)) .nil s) q ∧
      (∀ g : B → ℚ,q.mean g=(foldM f as b).mean g) ∧ q.cost ≤ cost f F.cost as b := by
  induction as generalizing b with
  | nil =>
    have hh := OnlineControl.halt (code F.program) (fun b=>env (encode b) .nil s) Point.halt rfl b
    have hc := OnlineControl.nilBranch (code F.program) (fun b=>env (encode b) .nil s)
      Point.check Point.halt Point.splitHead 1 rfl _ rfl _ hh
    obtain ⟨q,hq,hm,hcost⟩:=deterministicCall (code F.program) (fun b=>env (encode b) .nil s)
      Point.loop Point.check (TreeFunction.split 1 0 (by decide)) rfl _ _ _
      (split10 .nil (encode b) .nil s) _ hc
    refine ⟨q,hq,?_,?_⟩
    · intro g; simpa only [Experiment.mean,foldM] using hm g
    · simpa only [cost,size_nil,Experiment.cost] using hcost
  | cons a as ih =>
    choose q hq hm hcost using ih
    let out := fun b : B=>env (encode b) .nil s
    let M := code F.program
    let sr := TreeFunction.size (encode as)
    let sa := TreeFunction.size (encode a)
    have hreb v := deterministicCall M out Point.rebuild Point.loop
      (TreeFunction.cons 1 0 (by decide)) rfl _ _ _
      (cons10 (encode v) (encode as) s) (q v) (hq v)
    choose qr hr hmr hcr using hreb
    have hpop v := deterministicCall M out Point.popTail Point.rebuild
      (TreeFunction.split 1 2 (by decide)) rfl _ _ _
      (split12 (encode v) .nil (encode as) s) (qr v) (hr v)
    choose qp hp hmp hcp using hpop
    obtain ⟨r,hrf,hrm,hrc⟩:=F.correct (a,b) (.cons (encode as) s)
    have hbody := call M out Point.body Point.popTail F.program rfl
      (env (encode (a,b)) .nil (.cons (encode as) s))
      (fun v=>env (encode v) .nil (.cons (encode as) s)) r hrf qp hp
    have h4 := TreeTyped.Fold.pushArgs (encode a) (encode b) (encode as) s
    obtain ⟨p4,hp4,hm4,hc4⟩:=deterministicCall M out Point.pushArgs Point.body
      (TreeFunction.cons 3 0 (by decide)) rfl _ _ _ h4 _ hbody
    have h5 := TreeTyped.Fold.pushTail (encode a) (encode b) (encode as) s
    obtain ⟨p5,hp5,hm5,hc5⟩:=deterministicCall M out Point.pushTail Point.pushArgs
      (TreeFunction.cons 1 2 (by decide)) rfl _ _ _ h5 _ hp4
    have h6 := TreeTyped.Fold.splitHeads (encode a) (encode b) (encode as) s
    obtain ⟨p6,hp6,hm6,hc6⟩:=deterministicCall M out Point.splitHead Point.pushTail
      (TreeFunction.split 3 1 (by decide)) rfl _ _ _ h6 _ hp5
    have hc := OnlineControl.consBranch M out Point.check Point.halt Point.splitHead
      1 rfl (env (encode b) (encode (a::as)) s) (encode a) (encode as) rfl p6 hp6
    obtain ⟨p7,hp7,hm7,hc7⟩:=deterministicCall M out Point.loop Point.check
      (TreeFunction.split 1 0 (by decide)) rfl _ _ _
      (split10 (encode (a::as)) (encode b) .nil s) _ hc
    refine ⟨p7,hp7,?_,?_⟩
    · intro g
      rw [hm7,Experiment.mean,hm6,hm5,hm4,Experiment.mean,Experiment.mean_bind]
      simp_rw [hmp,hmr,hm]
      simpa only [foldM,Experiment.mean_bind] using hrm (fun v=>(foldM f as v).mean g)
    · have hcq : ∀ v,(qp v).cost ≤ 4*sr+10+cost f F.cost as v := by
        intro v
        have hr':=(hcr v)
        have hp':=(hcp v)
        have ht:=hcost v
        simp only [size_nil] at hp'
        dsimp [sr] at *
        omega
      have ha : r.All (fun v=>(qp v).cost ≤ 4*sr+10+(f (a,b)).worst (cost f F.cost as)) := by
        apply (Experiment.all_of_mean_eq hrm _ (Experiment.all_worst (f (a,b)) (cost f F.cost as))).mono
        intro v hv
        exact (hcq v).trans (Nat.add_le_add_left hv _)
      have hbind:=Experiment.cost_bind_le_of_all r qp _ ha
      simp only [Experiment.cost,size_nil,encode_list_cons,size_cons] at hc4 hc7
      simp only [cost]
      dsimp [sr,sa] at *
      omega
end Fold

noncomputable def fold {f : A×B → Experiment B} (F : Realizer f) :
    Realizer (fun ab : List A×B=>foldM f ab.1 ab.2) where
  program := OnlineControl.compile (Fold.code F.program)
  cost := fun ab=>Fold.cost f F.cost ab.1 ab.2
  correct := by
    intro ab s
    obtain ⟨q,hq,hm,hc⟩:=Fold.runs F ab.1 ab.2 s
    exact ⟨q,hq,hm,hc⟩
end MatchingFPRAS.OnlineTree

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_OnlineFrame
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineTree
open TreeData TreeMachine RegisterProc TreeFunction TreeTyped
open Turing MachineCost PhysicalStream OnlineStack

variable {A B C D : Type} [Codec A] [Codec B] [Codec C] [Codec D]
namespace Second
open OnlineControl

lemma runs {f : B → Experiment C} (F : Realizer f) (a : A) (b : B) (s : Data) :
    ∃ q,At (code F.program) (fun ac : A×C=>env (encode ac) .nil s) (Option.some Point.split)
      (env (encode (a,b)) .nil s) q ∧
      (∀ g : A×C → ℚ,q.mean g=(f b).mean (fun c=>g (a,c))) ∧
      q.cost ≤ F.cost b+8*TreeFunction.size (encode a)+22 := by
  let M:=code F.program
  let out:=fun ac : A×C=>env (encode ac) .nil s
  have hend c:=OnlineControl.halt M out Point.halt rfl (a,c)
  have hcons c:=deterministicCall M out Point.cons Point.halt
    (TreeFunction.cons 1 0 (by decide)) rfl _ _ _ (cons10 (encode c) (encode a) s) _ (hend c)
  choose pc hc hmc hcc using hcons
  have hpop c:=deterministicCall M out Point.pop Point.cons
    (TreeFunction.split 1 2 (by decide)) rfl _ _ _ (split12 (encode c) .nil (encode a) s) _ (hc c)
  choose pp hp hmp hcp using hpop
  obtain ⟨r,hr,hmr,hcr⟩:=F.correct b (.cons (encode a) s)
  have hbody:=call M out Point.body Point.pop F.program rfl
    (env (encode b) .nil (.cons (encode a) s)) (fun c=>env (encode c) .nil (.cons (encode a) s))
    r hr pp hp
  obtain ⟨p2,hp2,hm2,hc2⟩:=deterministicCall M out Point.save Point.body
    (TreeFunction.cons 1 2 (by decide)) rfl _ _ _ (cons12 (encode b) (encode a) s) _ hbody
  obtain ⟨p1,hp1,hm1,hc1⟩:=deterministicCall M out Point.split Point.save
    (TreeFunction.split 1 0 (by decide)) rfl _ _ _ (split10 (encode a) (encode b) .nil s) _ hp2
  refine ⟨p1,hp1,?_,?_⟩
  · intro g
    rw [hm1,hm2,Experiment.mean,Experiment.mean_bind]
    simp_rw [hmp,hmc,Experiment.mean]
    exact hmr _
  · have hb : ∀ c,(pp c).cost ≤ 4*TreeFunction.size (encode a)+11 := by
      intro c
      have h1:=hcc c
      have h2:=hcp c
      simp only [Experiment.cost,size_nil] at h1 h2
      omega
    have hbind:=Experiment.cost_bind_le r pp _ hb
    simp only [Experiment.cost,size_nil] at hc1 hc2
    omega
end Second

noncomputable def mapSecond {f : B → Experiment C} (F : Realizer f) :
    Realizer (fun ab : A×B=>(f ab.2).map (Prod.mk ab.1)) where
  program := OnlineControl.compile (Second.code F.program)
  cost := fun ab=>F.cost ab.2+8*TreeFunction.size (encode ab.1)+22
  correct := by
    intro ab s
    obtain ⟨q,hq,hm,hc⟩:=Second.runs F ab.1 ab.2 s
    exact ⟨q,hq,fun g=>by rw [Experiment.mean_map]; exact hm g,hc⟩

noncomputable def pair {f : A → Experiment B} {g : A → Experiment C}
    (F : Realizer f) (G : Realizer g) :
    Realizer (fun a=>(f a).bind (fun b=>(g a).map (Prod.mk b))) :=
  (composition (deterministic (TreeTyped.pair (TreeTyped.identity (A:=A)) TreeTyped.identity))
    (composition (mapSecond F)
      (composition (deterministic (TreeTyped.pair (TreeTyped.second (A:=A) (B:=B)) TreeTyped.first))
        (mapSecond G)))).congr (by
      intro a h
      simp only [Experiment.mean_bind,Experiment.mean,Experiment.mean_map,id_eq])
end MatchingFPRAS.OnlineTree

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_OnlineWord
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineWord
open PhysicalStream TreeData TreeFunction TreeTyped OnlineTree

noncomputable def stepRealizer : OnlineTree.Realizer step :=
  (OnlineTree.choose
    (OnlineTree.deterministic (TreeTyped.composition (TreeTyped.pair (TreeTyped.constant false) TreeTyped.second) TreeTyped.listCons))
    (OnlineTree.deterministic (TreeTyped.composition (TreeTyped.pair (TreeTyped.constant true) TreeTyped.second) TreeTyped.listCons))).congr
    (by intro x f; rfl)

noncomputable def listRealizer : OnlineTree.Realizer (fun as : List ℕ=>prepend as.length []) :=
  (OnlineTree.composition
    (OnlineTree.deterministic (TreeTyped.pair (TreeTyped.identity (A:=List ℕ)) (TreeTyped.constant ([] : List Bool))))
    (OnlineTree.fold stepRealizer)).congr (by
      intro as f
      change (OnlineTree.foldM step as []).mean f=(prepend as.length []).mean f
      rw [fold_step])

noncomputable def naturalRealizer : OnlineTree.Realizer (fun n : ℕ=>prepend n []) :=
  (OnlineTree.composition (OnlineTree.deterministic TreeTyped.range) listRealizer).congr
    (by intro n f; simp only [Experiment.mean_bind,Experiment.mean,List.length_range])

end MatchingFPRAS.OnlineWord

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FiniteWordExecution
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executing a computed finite Boolean sampler

The program reads a fresh word on the physical online machine, preserves
the input, and runs the deterministic binary sampler on that word.
-/

namespace ContingencyTables.FiniteWordExecution
open MatchingFPRAS MatchingFPRAS.PhysicalStream Polynomial

variable {A B : Type} [TreeTyped.Codec A] [TreeTyped.Codec B]

noncomputable def sourceRealizer {n : A → ℕ} (N : TreeTyped.Realizer n) :
    OnlineTree.Realizer (source n) :=
  (OnlineTree.composition (OnlineTree.deterministic N) OnlineWord.naturalRealizer).congr
    (by intro a g; rfl)

def wordMeasure (n : A → ℕ) (a : A) : ℕ := TreeTyped.weight a+n a

noncomputable def realizer {n : A → ℕ} {f : A×List Bool → B}
    (N : TreeTyped.Realizer n) (F : TreeTyped.Realizer f) : OnlineTree.Realizer (experiment n f) :=
  (OnlineTree.composition
    (OnlineTree.pair (OnlineTree.deterministic TreeTyped.identity) (sourceRealizer N))
    (OnlineTree.deterministic F)).congr (by
      intro a g
      simp only [Experiment.mean_bind,Experiment.mean,Experiment.mean_map,experiment,id_eq])

end ContingencyTables.FiniteWordExecution

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_OnlinePhysicalProgram
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineTree
open Turing TreeTyped TreeData TreeFunction TreeMachine TreePost PhysicalPost PhysicalStream

noncomputable def physicalProgram {A B : Type} [Codec A] [Codec B]
    {f : A→Experiment B} (F : Realizer f) : Program where
  State := OnlineStack.Q (K Reg) (fun _=>Bool) F.program.Label RegisterProc.Store
  table := liftBool (OnlineStack.table F.program.code F.program.coin)
  states := OnlineStack.states F.program.code
  supported := liftBool_supported _ _ (OnlineStack.table_supported F.program.code F.program.coin)
  entry := OnlineStack.initialState
  entry_mem := OnlineStack.initialState_mem F.program.code

noncomputable def physicalCost {A B : Type} [Codec A] [Codec B]
    {f : A→Experiment B} (F : Realizer f) (a : A) : ℕ :=
  F.cost a*OnlineStack.Executes.factor F.program.code (weight a) (F.cost a)

end MatchingFPRAS.OnlineTree

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_Packed
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.LiteralPacked
open TreeTyped TreeData TreeFunction TreeMachine TreePost

def symbolBits (a : Symbol) : List Bool := (TreeData.encode (TreeTyped.encode a)).reverse++[true]
noncomputable def chunk (a : Symbol) : List Symbol := (symbolBits a).flatMap (fun b=>block (letter b))
end MatchingFPRAS.LiteralPacked

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_PackedInverse
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.LiteralPacked
open TreeTyped TreeData TreePost

noncomputable def unchunk (b : LiteralBlockMap.Block (18*width)) : List Symbol :=
  [Function.invFun chunk (List.ofFn b)]
end MatchingFPRAS.LiteralPacked

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_PackedExecution
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.LiteralPacked
open Turing LiteralTape LiteralBlockMap

noncomputable def packCode := LiteralBlockMap.code 1 (fun b=>chunk (b 0)) header
noncomputable def unpackCode := LiteralBlockMap.code (18*width) unchunk []
end MatchingFPRAS.LiteralPacked

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_LiteralProgram
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Public binary input and output for typed finite programs

Literal packing is independent of the counting algorithm. Its cost includes every packing, execution, and printing step.
-/

namespace ContingencyTables.LiteralProgram
open MatchingFPRAS Turing PhysicalPost PhysicalStream LiteralPacked TreeTyped Polynomial

noncomputable def pack : Program := Program.ofTM1 packCode .start (fun _ => 0)
noncomputable def unpack : Program := Program.ofTM1 unpackCode .start (fun _ => 0)
noncomputable def post : Program := erase.seq unpack
noncomputable def packTime (n : ℕ) : ℕ :=
  (1+LiteralBlockMap.budget 1 (18*width) n 0)*MachineCost.programCost packCode
noncomputable def postTime (n : ℕ) : ℕ :=
  MachineCost.programCost (LiteralTape.eraseCode header.length)+
    (1+LiteralBlockMap.budget (18*width) 1 n 0)*MachineCost.programCost unpackCode

noncomputable def wrap {f : List Symbol → Experiment (List Symbol)}
    (F : OnlineTree.Realizer f) : Program := (pack.seq (OnlineTree.physicalProgram F)).seq post

noncomputable def wrapTime {f : List Symbol → Experiment (List Symbol)}
    (F : OnlineTree.Realizer f) (as : List Symbol) : ℕ :=
  packTime as.length+OnlineTree.physicalCost F as+postTime ((f as).worst List.length)

end ContingencyTables.LiteralProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FiniteWordMachine
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A single physical machine for a computed finite-word algorithm -/

namespace ContingencyTables.FiniteWordExecution
open MatchingFPRAS MatchingFPRAS.PhysicalStream Turing
open TreeTyped Polynomial

variable {n : List Symbol → ℕ} {f : List Symbol×List Bool → List Symbol}

noncomputable def machine (N : TreeTyped.Realizer n) (F : TreeTyped.Realizer f) : RandomMachine :=
  (LiteralProgram.wrap (realizer N F)).machine

noncomputable def machineTime (N : TreeTyped.Realizer n) (F : TreeTyped.Realizer f)
    (as : List Symbol) : ℕ := LiteralProgram.wrapTime (realizer N F) as

end ContingencyTables.FiniteWordExecution

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_OnlineIntegerRetry
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed online machine for repeat-until-success -/

namespace ContingencyTables.OnlineIntegerRetry
open MatchingFPRAS MatchingFPRAS.TreeData MatchingFPRAS.TreeMachine
open MatchingFPRAS.TreeFunction
open MatchingFPRAS.TreeTyped (Codec)
open MatchingFPRAS.RegisterProc MatchingFPRAS.OnlineStack
open MatchingFPRAS.PhysicalStream

variable {A B : Type} [Codec A] [Codec B] [Inhabited B]
variable {f : A → Experiment (Option B)} (F : OnlineTree.Realizer f)

def instructions : Label → OnlineControl.Instr Reg Label
  | .prepare => .call (OnlineProc.deterministic prepareProc) .trial
  | .trial => .call F.program .decode
  | .decode => .call (OnlineProc.deterministic (split 1 0 (by decide))) .test
  | .test => .branch 1 .retry .finish
  | .retry => .call (OnlineProc.deterministic retryProc) .prepare
  | .finish => .call (OnlineProc.deterministic finishProc) .halt
  | .halt => .halt

/-- A single finite control graph, independent of the number of retries. -/
def program : OnlineProc.Proc (K Reg) := OnlineControl.compile (instructions F)

def prefixExperiment (a : A) : ℕ → Experiment (Option B)
  | 0 => .done none
  | N+1 => (f a).bind (fun b => b.elim (prefixExperiment a N) (fun b => .done (some b)))

def stepCost (a : A) : ℕ := F.cost a+12*TreeFunction.size (TreeTyped.encode a)+TreeFunction.size (TreeTyped.encode (default : B))+40

end ContingencyTables.OnlineIntegerRetry

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_OnlinePartialCall
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Calling the actual retry loop without pretending it has halted -/

namespace ContingencyTables.OnlinePartialCall
open MatchingFPRAS MatchingFPRAS.TreeData
open MatchingFPRAS.TreeMachine (Env K encodeEnv)
open MatchingFPRAS.OnlineStack MatchingFPRAS.OnlineControl
open MatchingFPRAS.PhysicalStream Turing

variable {R Λ α : Type} [DecidableEq R]

def embed (M : Λ → Instr R Λ) (l : Λ) :
    (procedure (M l)).Label → Label M := fun u => .inr ⟨l,u⟩

def callCfg (M : Λ → Instr R Λ) (l : Λ)
    (c : TM2.Cfg (fun _ : K R => Bool) (procedure (M l)).Label RegisterProc.Store) :=
  StackComposition.mapCfg (embed M l) ((successor (M l)).map Sum.inl) c

abbrev Config (M : Λ → Instr R Λ) :=
  TM2.Cfg (fun _ : K R => Bool) (Label M) RegisterProc.Store

end ContingencyTables.OnlinePartialCall

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_ResidualWeightProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary computation of the rare branch's integer weights -/

namespace ContingencyTables.ResidualWeightPrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped
open scoped BigOperators Classical

def countRealizer : Realizer count := by
  let denominator : Realizer (fun z : Input => z.1.1) := composition first first
  let branch : Realizer (fun z : Input => z.1.2) := composition first second
  let cardinality : Realizer (fun z : Input => z.2.1) := composition second first
  let numerator : Realizer (fun z : Input => z.2.2) := composition second second
  let left := composition (pair denominator branch) multiply
  let right := composition (pair (composition (pair cardinality
    (composition branch predecessor)) multiply) numerator) multiply
  exact composition (pair left right) subtract

end ContingencyTables.ResidualWeightPrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperBinaryParameters
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary lengths for the small-chain capacity bound -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open CompletionCounts

universe u
variable {I J : Type u} [Fintype I] [Fintype J]
variable (r : I → ℕ) (c : J → ℕ)
local notation "d" => dimensionAllowance (I := I) (J := J)

noncomputable def smallBinaryLength : ℕ := d+Nat.clog 2 (stateBound r c+2)

lemma smallBinaryLength_parameters :
    Nat.clog 2 (stateBound r c+2) ≤ smallBinaryLength r c ∧
    d ≤ smallBinaryLength r c ∧ stateBound r c+1 ≤ 2^(smallBinaryLength r c) := by
  refine ⟨by unfold smallBinaryLength; omega,by unfold smallBinaryLength; omega,?_⟩
  have hb : Nat.clog 2 (stateBound r c+2) ≤ smallBinaryLength r c := by
    unfold smallBinaryLength
    omega
  exact (show stateBound r c+1 ≤ stateBound r c+2 by omega).trans
    ((Nat.le_pow_clog (by decide) (stateBound r c+2)).trans
      (Nat.pow_le_pow_right (by decide) hb))

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_OriginalProfileEntries
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The initial profile is read directly from the original table -/

namespace ContingencyTables.SmallGraphProfiles
open PhysicalCompletionFibres FirstPaperPhysicalMarginal FirstPaperProfiles
open PaddedCompletions CompletionCounts SmallContextCoordinates
open scoped BigOperators Classical

noncomputable section
variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)

def tableState (X : Table r c) : PaperStates r c := (originalStateSuccessEquiv r c X).val.1

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_OriginalProfileProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing the initial profile directly from the greedy table -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped DensePrograms

def originalFirstViewRealizer : Realizer originalFirstView :=
  composition (pair second (composition first first)) (mapWith matrixEntryRealizer)

def originalViewsRealizer : Realizer originalViews :=
  pair originalFirstViewRealizer
    (composition (pair (composition first second) originalFirstViewRealizer) complementValuesRealizer)

def initialViewInputRealizer : Realizer initialViewInput :=
  pair (pair marginCatalogRealizer marginThresholdRealizer) GreedyFeasibleTable.tableRealizer

def initialViewsRealizer : Realizer initialViews := composition initialViewInputRealizer originalViewsRealizer

def initialCheck (z : List ℕ×List ℕ) : ProfileCheckData := prepareProfileInput (z,initialViews z)
def initialCheckRealizer : Realizer initialCheck :=
  composition (pair identity initialViewsRealizer) prepareProfileInputRealizer

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileTrialProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A complete polynomial outer trial on supplied independent words -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

abbrev ProfileTrialData := (ProfileConfiguration×List ProfileWord)×List Bool

def trialState (z : ProfileTrialData) : ProfileConfiguration := profileWalk z.1

def trialParameters (z : ProfileTrialData) : ResidualParameters := currentParameters (trialState z)

def trialCompletion (z : ProfileTrialData) : DensePrograms.MatrixCode :=
  reservedResidualDraw (trialParameters z,z.2)

def trialOutputInput (z : ProfileTrialData) : OuterTrialInput :=
  ((trialParameters z).1,trialCompletion z)

def profileTrial (z : ProfileTrialData) : Option DensePrograms.MatrixCode :=
  outerTrial (trialOutputInput z)

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileWordProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Parsing the independent words of the physical outer trial -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped DensePrograms

def splitProfileWordRealizer : Realizer splitProfileWord :=
  pair (composition (pair second first) takeFast) (composition (pair second first) dropFast)

def profileWordWidthRealizer : Realizer profileWordWidth :=
  composition (pair (composition (composition first first) second) (composition first second)) add

def profileWalkWidthRealizer : Realizer profileWalkWidth :=
  composition (pair (composition (composition first first) first) profileWordWidthRealizer) multiply

def profileWalkChunksRealizer : Realizer profileWalkChunks :=
  composition (pair profileWordWidthRealizer
    (composition (pair second profileWalkWidthRealizer) takeFast)) wordChunksRealizer

def profileWalkWordsRealizer : Realizer profileWalkWords :=
  composition (pair (composition (composition first first) second) profileWalkChunksRealizer)
    (mapWith splitProfileWordRealizer)

def profileTerminalWordRealizer : Realizer profileTerminalWord :=
  composition (pair second profileWalkWidthRealizer) dropFast

abbrev PackedProfileTrial := (ProfileConfiguration×ProfileWordSchedule)×List Bool

def profileTrialWords (z : PackedProfileTrial) : ProfileWordInput := (z.1.2,z.2)
def profileTrialWordsRealizer : Realizer profileTrialWords := pair (composition first second) second

def prepareProfileTrial (z : PackedProfileTrial) : ProfileTrialData :=
  ((z.1.1,profileWalkWords (profileTrialWords z)),profileTerminalWord (profileTrialWords z))
def prepareProfileTrialRealizer : Realizer prepareProfileTrial :=
  pair (pair (composition first first)
    (composition profileTrialWordsRealizer profileWalkWordsRealizer))
    (composition profileTrialWordsRealizer profileTerminalWordRealizer)

def packedProfileTrial (z : PackedProfileTrial) : Option MatrixCode := profileTrial (prepareProfileTrial z)

open FairBits GridBoundary
open scoped Classical
end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileRetryProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial retry loop for the complete binary outer trial -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped DensePrograms

abbrev ProfileRetryParameters := (ProfileConfiguration×ProfileWordSchedule)×MatrixCode
abbrev ProfileRetryData := ProfileRetryParameters×List Bool

def profileTrialWidth (z : ProfileRetryData) : ℕ :=
  z.1.1.2.1.1*(z.1.1.2.1.2+z.1.1.2.2)+z.1.1.2.2

def profileRetryWordInput (z : ProfileRetryData) : ProfileWordInput := (z.1.1.2,z.2)
def profileRetryWordInputRealizer : Realizer profileRetryWordInput :=
  pair (composition (composition first first) second) second

def profileTrialWidthRealizer : Realizer profileTrialWidth :=
  composition (pair (composition profileRetryWordInputRealizer profileWalkWidthRealizer)
    (composition (composition (composition first first) second) second)) add

def profileRetryWords (z : ProfileRetryData) : List (List Bool) :=
  wordChunks (profileTrialWidth z,z.2)
def profileRetryWordsRealizer : Realizer profileRetryWords :=
  composition (pair profileTrialWidthRealizer second) wordChunksRealizer

def profileRetry (z : ProfileRetryData) : MatrixCode :=
  FirstSuccessProgram.retry packedProfileTrial (z.1,profileRetryWords z)

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileScheduleProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing the complete outer sampling schedule from binary margins -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped DensePrograms

def cubicPower : Realizer (fun n : ℕ => n^3) :=
  (composition (pair squareNat identity) multiply).congr (by
    intro n; simp only [Function.comp_apply,id_eq]; ring)

def twelfthPower : Realizer (fun n : ℕ => n^12) :=
  (composition fourthPower cubicPower).congr (by
    intro n; simp only [Function.comp_apply,←pow_mul])

def twoHundredthPower : Realizer (fun n : ℕ => n^200) :=
  (composition fiftiethPower fourthPower).congr (by
    intro n; simp only [Function.comp_apply,←pow_mul])

def sixtySecondPower : Realizer (fun n : ℕ => n^62) :=
  (composition (pair (composition twentiethPower cubicPower) squareNat) multiply).congr (by
    intro n; simp only [Function.comp_apply]; ring)

def marginPaddingRealizer : Realizer marginPadding :=
  composition (f := fun z : List ℕ×List ℕ => marginDimension z) (g := fun n : ℕ => n^12) (marginDimensionRealizer) twelfthPower

def marginStateBoundRealizer : Realizer marginStateBound :=
  composition (f := fun z : List ℕ×List ℕ => (((z.1.sum+(marginDimension z*marginPadding z))+marginThreshold z),2)) (g := fun t : ℕ×ℕ => t.1+t.2) (pair (composition (f := fun z : List ℕ×List ℕ => ((z.1.sum+(marginDimension z*marginPadding z)),marginThreshold z)) (g := fun t : ℕ×ℕ => t.1+t.2) (pair (composition (f := fun z : List ℕ×List ℕ => (z.1.sum,(marginDimension z*marginPadding z))) (g := fun t : ℕ×ℕ => t.1+t.2) (pair (composition (f := fun z : List ℕ×List ℕ => z.1) (g := List.sum) first listSum) (composition (f := fun z : List ℕ×List ℕ => (marginDimension z,marginPadding z)) (g := fun t : ℕ×ℕ => t.1*t.2) (pair (marginDimensionRealizer) (marginPaddingRealizer)) multiply)) add) (marginThresholdRealizer)) add) (constant 2)) add

def marginBinaryLengthRealizer : Realizer marginBinaryLength :=
  composition (f := fun z : List ℕ×List ℕ => (marginDimension z,(Nat.clog 2) ((marginStateBound z+2)))) (g := fun t : ℕ×ℕ => t.1+t.2) (pair (marginDimensionRealizer) (composition (f := fun z : List ℕ×List ℕ => (marginStateBound z+2)) (g := Nat.clog 2) (composition (f := fun z : List ℕ×List ℕ => (marginStateBound z,2)) (g := fun t : ℕ×ℕ => t.1+t.2) (pair (marginStateBoundRealizer) (constant 2)) add) ceilLogTwoRealizer)) add

def parameterDimensionRealizer : Realizer parameterDimension :=
  composition (f := fun z : SamplingParameters => z.1) (g := marginDimension) first marginDimensionRealizer

def parameterBinaryLengthRealizer : Realizer parameterBinaryLength :=
  composition (f := fun z : SamplingParameters => z.1) (g := marginBinaryLength) first marginBinaryLengthRealizer

def parameterTrialsRealizer : Realizer parameterTrials :=
  composition (f := fun z : SamplingParameters => ((parameterDimension z)^4,(z.2+1))) (g := fun t : ℕ×ℕ => t.1*t.2) (pair (composition (f := fun z : SamplingParameters => parameterDimension z) (g := fun n : ℕ => n^4) (parameterDimensionRealizer) fourthPower) (composition (f := fun z : SamplingParameters => (z.2,1)) (g := fun t : ℕ×ℕ => t.1+t.2) (pair (second) (constant 1)) add)) multiply

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileSamplingProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Preparing and executing the complete profile sampler -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped DensePrograms

/-- All constant configuration data is computed from the public margins. -/
def initialConfiguration (z : SamplingParameters) : ProfileConfiguration :=
  (((initialCheck z.1,marginPadding z.1),(parameterDimension z,parameterAccuracy z)),
    initialViews z.1)

def samplingRetryParameters (z : SamplingParameters) : ProfileRetryParameters :=
  ((initialConfiguration z,samplingSchedule z),GreedyFeasibleTable.listMatrix z.1.1 z.1.2)

def samplingMatrix (z : SamplingParameters×List Bool) : MatrixCode :=
  profileRetry (samplingRetryParameters z.1,z.2)

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfilePublicProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The sampler's public binary parser and matrix printer -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped MatchingFPRAS.LiteralParse MatchingFPRAS.LiteralCodec
open DensePrograms

def samplingPrecisionRealizer : Realizer samplingPrecision := by
  let M : Realizer (fun ns : List ℕ => ns.headD 0) := head 0
  let N : Realizer (fun ns : List ℕ => ns.tail.headD 0) := composition tail (head 0)
  let offset : Realizer (fun ns : List ℕ => 2+ns.headD 0+ns.tail.headD 0) :=
    composition (pair (composition (pair (constant 2) M) add) N) add
  exact composition (composition (pair identity offset) dropFast) (head 0)

def samplingInputRealizer : Realizer samplingInput :=
  pair GreedyFeasibleTable.marginListsRealizer samplingPrecisionRealizer

def parsedSamplingRealizer : Realizer parsedSampling := composition (f := parse) (g := samplingInput) parseRealizer samplingInputRealizer

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_UnitProfileProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The bounded profile program for the all-small branch -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped DensePrograms Polynomial

abbrev UnitStepInput := ProfileConfiguration×List Bool

def unitCandidateInput (z : UnitStepInput) : ProfileStepInput :=
  (currentParameters z.1,(z.2,[]))
def unitCandidateInputRealizer : Realizer unitCandidateInput :=
  pair (composition first currentParametersRealizer) (pair second (constant []))

def unitNext (z : UnitStepInput) : List ℕ×List ℕ :=
  capViews (z.1.1.1.1,stepCandidateViews (unitCandidateInput z))

def unitAdvance (z : List Bool×ProfileConfiguration) : ProfileConfiguration :=
  (z.2.1,unitNext (z.2,z.1))

def unitProfileWalk (z : ProfileConfiguration×List (List Bool)) : ProfileConfiguration :=
  z.2.foldl (fun state word => unitAdvance (word,state)) z.1

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_UnitTrialProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # All-small trials and retries use only the stored profile entries -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped DensePrograms

def unitPackedWords (z : PackedProfileTrial) : List (List Bool) :=
  wordChunks (z.1.2.1.2,z.2)
def unitPackedWordsRealizer : Realizer unitPackedWords :=
  composition (f := fun z : PackedProfileTrial => (z.1.2.1.2,z.2)) (g := wordChunks)
    (pair (composition (composition (composition first second) first) second) second) wordChunksRealizer

def unitPackedState (z : PackedProfileTrial) : ProfileConfiguration :=
  unitProfileWalk (z.1.1,unitPackedWords z)

def unitPackedTrial (z : PackedProfileTrial) : Option MatrixCode :=
  outerTrial ((currentParameters (unitPackedState z)).1,[])

def unitRetryWidth (z : ProfileRetryData) : ℕ := z.1.1.2.1.1*z.1.1.2.1.2
def unitRetryWidthRealizer : Realizer unitRetryWidth :=
  composition (f := fun z : ProfileRetryData => (z.1.1.2.1.1,z.1.1.2.1.2))
    (g := fun t : ℕ×ℕ => t.1*t.2)
    (pair (composition (composition (composition (composition first first) second) first) first)
      (composition (composition (composition (composition first first) second) first) second)) multiply

def unitRetryWords (z : ProfileRetryData) : List (List Bool) := wordChunks (unitRetryWidth z,z.2)
def unitRetryWordsRealizer : Realizer unitRetryWords :=
  composition (f := fun z : ProfileRetryData => (unitRetryWidth z,z.2)) (g := wordChunks)
    (pair unitRetryWidthRealizer second) wordChunksRealizer

def unitProfileRetry (z : ProfileRetryData) : MatrixCode :=
  FirstSuccessProgram.retry unitPackedTrial (z.1,unitRetryWords z)

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_AllSamplingProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A single computed sampler for large and all-small rectangles -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped DensePrograms

attribute [local irreducible] parameterUnitWords

def unitSamplingInput (z : SamplingWordInput) : ProfileRetryData :=
  (samplingRetryParameters z.1,unitSamplingBits z)

def unitSamplingMatrix (z : SamplingWordInput) : MatrixCode := unitProfileRetry (unitSamplingInput z)

def parameterLargeIndices (row : Bool) (z : SamplingParameters) : List ℕ :=
  largeIndices (marginThreshold z.1,if row then z.1.1 else z.1.2)
def parameterLargeIndicesRealizer (row : Bool) : Realizer (parameterLargeIndices row) := by
  cases row with
  | false =>
    exact composition
      (f := fun z : SamplingParameters => (marginThreshold z.1,z.1.2)) (g := largeIndices)
      (pair (composition (f := fun z : SamplingParameters => z.1) (g := marginThreshold)
        first marginThresholdRealizer) (composition first second)) largeIndicesRealizer
  | true =>
    exact composition
      (f := fun z : SamplingParameters => (marginThreshold z.1,z.1.1)) (g := largeIndices)
      (pair (composition (f := fun z : SamplingParameters => z.1) (g := marginThreshold)
        first marginThresholdRealizer) (composition first first)) largeIndicesRealizer

def hasLargeRectangle (z : SamplingParameters) : Bool :=
  decide (0<(parameterLargeIndices true z).length) && decide (0<(parameterLargeIndices false z).length)
def hasLargeRectangleRealizer : Realizer hasLargeRectangle :=
  composition (f := fun z : SamplingParameters =>
      (decide (0<(parameterLargeIndices true z).length),decide (0<(parameterLargeIndices false z).length)))
    (g := fun p : Bool×Bool => p.1 && p.2)
    (pair
      (composition (f := fun z : SamplingParameters => (0,(parameterLargeIndices true z).length))
        (g := fun p : ℕ×ℕ => decide (p.1<p.2))
        (pair (constant 0) (composition (f := parameterLargeIndices true) (g := List.length)
          (parameterLargeIndicesRealizer true) listLength)) less)
      (composition (f := fun z : SamplingParameters => (0,(parameterLargeIndices false z).length))
        (g := fun p : ℕ×ℕ => decide (p.1<p.2))
        (pair (constant 0) (composition (f := parameterLargeIndices false) (g := List.length)
          (parameterLargeIndicesRealizer false) listLength)) less)) boolAnd

def samplingMatrixAll (z : SamplingParameters×List Bool) : MatrixCode :=
  if hasLargeRectangle z.1 then samplingMatrix z else unitSamplingMatrix z

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperFiniteSampler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The initialized finite Boolean sampler on a nonempty large rectangle -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open CompletionCounts ResidualMixture FirstSuccess FairBits

noncomputable section
universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]
variable (r : I → ℕ) (c : J → ℕ)
variable (i₀ : LargeRows r ((dimensionAllowance (I := I) (J := J))^20))
variable (j₀ : LargeColumns c ((dimensionAllowance (I := I) (J := J))^20))
variable {q : ℕ}
variable (e : ({i : LargeRows r ((dimensionAllowance (I := I) (J := J))^20) // i≠i₀} ×
  {j : LargeColumns c ((dimensionAllowance (I := I) (J := J))^20) // j≠j₀}) ≃ Fin q)
local notation "d" => dimensionAllowance (I := I) (J := J)
local notation "b" => smallBinaryLength r c
local notation "s" => smallProposalBits (I := I) (J := J)

/-- The exact number of independent input bits used by the initialized
finite experiment. The physical simulation has additional operation cost. -/
abbrev finiteSamplerBits (k : ℕ) : ℕ :=
  let h := outerAccuracy d b k
  let n := outerSteps d b k
  let f := 25*(d+b+h+1)^62
  outerTrials d k*(n*(s+f)+f)

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_BoundedProfileSemantics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The bounded binary loop preserves the physical profile walk -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal CompletionCounts
open SmallContextCoordinates FirstSuccess FairBits
open scoped BigOperators Classical

noncomputable section
variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c))
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)

lemma stateCode_bounded (x : PaperStates r c) (a : Cells (paperSmall r c)) (side : Bool) :
    physicalProfile (paperSmall r c) (stateCapacity r c) r c (d^12) x (a,side)≤d^20 := by
  have he := (physicalProfile_feasible r c x).bounded (a,side)
  exact he.trans_eq (stateCapacity_small r c _ _ a.property)

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_AllSmallRational
attribute [-instance] _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual rational walk on an empty large rectangle -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open ResidualMixture FirstSuccess CompletionTranslation CompletionCounts CommonBasesFPRAS

noncomputable section
universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]
variable (r : I → ℕ) (c : J → ℕ)
local instance instDecidableEqPaperStates_1 : DecidableEq (PaperStates r c) := Classical.decEq _

def unitSmallStep (x : PaperStates r c) : RationalLaw (PaperStates r c) :=
  proposalStayLaw (proposalWeights r c x) (proposalWeights_nonnegative r c x)
    (proposalWeights_total r c x) x

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_AllSmallInitialization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reading the unique all-small completion directly from its profile -/

namespace ContingencyTables.SmallGraphProfiles
open scoped BigOperators Classical
open CompletionCounts PhysicalCompletionFibres PaddedCompletions

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]
variable (r : I → ℕ) (c : J → ℕ)

/-- The output data consists only of the two stored small views. Existence
of a completion supplies the erased proof that these are valid margins. -/
noncomputable def allSmallFibre
    (hsmall : ∀ i j,FirstPaperPhysicalMarginal.paperSmall r c i j=true)
    (z : PaperStates r c) : PaperFibre r c z := by
  let p := SmallContextFibres.naturalProfile z.val.val
  let views := (fun i j => p (⟨(i,j),hsmall i j⟩,false),
    fun i j => stateCapacity r c i j-p (⟨(i,j),hsmall i j⟩,true))
  have hv : ∃ h, (⟨views,h⟩ : RowColumnPair
      (fun i => r i+PaddedCompletions.rowLargeCount (FirstPaperPhysicalMarginal.paperSmall r c) i*
        ((dimensionAllowance (I := I) (J := J))^12))
      (fun j => c j+PaddedCompletions.columnLargeCount (FirstPaperPhysicalMarginal.paperSmall r c) j*
        ((dimensionAllowance (I := I) (J := J))^12))).val=views := by
    obtain ⟨Z⟩ := (inferInstance : Nonempty (PaperFibre r c z))
    have he : views=Z.val.val := by
      apply Prod.ext
      · funext i j
        exact (Z.property.2.2.1 i j (hsmall i j)).1.symm
      · funext i j
        exact (Z.property.2.2.1 i j (hsmall i j)).2.symm
    exact ⟨by rw [he]; exact Z.val.property,rfl⟩
  let pair := (⟨views,hv.choose⟩ : RowColumnPair
      (fun i => r i+PaddedCompletions.rowLargeCount (FirstPaperPhysicalMarginal.paperSmall r c) i*
        ((dimensionAllowance (I := I) (J := J))^12))
      (fun j => c j+PaddedCompletions.columnLargeCount (FirstPaperPhysicalMarginal.paperSmall r c) j*
        ((dimensionAllowance (I := I) (J := J))^12)))
  refine ⟨pair,?_⟩
  obtain ⟨Z⟩ := (inferInstance : Nonempty (PaperFibre r c z))
  have he : pair=Z.val := by
    apply Subtype.ext
    apply Prod.ext
    · funext i j
      exact (Z.property.2.2.1 i j (hsmall i j)).1.symm
    · funext i j
      exact (Z.property.2.2.1 i j (hsmall i j)).2.symm
  exact he.symm ▸ Z.property

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_UnitProfileSemantics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact finite-word semantics of the all-small profile walk -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal
open SmallContextCoordinates CompletionCounts FirstSuccess FairBits
open scoped BigOperators Classical

noncomputable section
attribute [local irreducible] stateCode unitNext capViews codeNeighborProposal
variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c))
local notation "s" => smallProposalBits (I := Fin m) (J := Fin n)

def unitCodeBitStep (x : PaperStates r c) (bits : Fin s → Bool) : PaperStates r c :=
  (decodedCodeProposal r c e x bits).getD x

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_UnitFiniteLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The computed all-small walk has the proved uniform sampling law -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms FirstPaperPhysicalMarginal CompletionCounts
open FirstSuccess FairBits CompletionTranslation SmallContextCoordinates ResidualMixture
open scoped BigOperators Classical

noncomputable section
variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c))
local notation "s" => smallProposalBits (I := Fin m) (J := Fin n)

attribute [local irreducible] FirstSuccess.mapLaw

def flatUnitCodeWalk (x : PaperStates r c) (n : ℕ) (bits : Fin (n*s) → Bool) : PaperStates r c :=
  wordWalk (unitCodeBitStep r c e) x n (GridBoundary.gridWordEquiv n s bits)

def unitCodeJointDraw (fallback : (z : PaperStates r c) → PaperFibre r c z)
    (x : PaperStates r c) (n : ℕ) (bits : Fin (n*s) → Bool) : PaperStateJoint r c :=
  let z := flatUnitCodeWalk r c e x n bits
  ⟨z,fallback z⟩

def unitCodeOuterDraw (fallback : (z : PaperStates r c) → PaperFibre r c z)
    (x : PaperStates r c) (n M : ℕ) (z₀ : Table r c)
    (bits : Fin (M*(n*s)) → Bool) : Table r c :=
  wordRetry (fun w => stateTrial r c (unitCodeJointDraw r c e fallback x n w)) z₀ M
    (GridBoundary.gridWordEquiv M (n*s) bits)

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_AllSamplingSemantics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One executable program chooses the correct rectangle branch -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms CompletionCounts FirstPaperPhysicalMarginal
open FirstSuccess FairBits SmallContextCoordinates
open scoped BigOperators Classical

noncomputable section
attribute [local irreducible] unitProfileRetry unitCodeOuterDraw
variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "b" => smallBinaryLength r c
local notation "s" => smallProposalBits (I := Fin m) (J := Fin n)

lemma hasLargeRectangle_spec (k : ℕ) :
    hasLargeRectangle ((List.ofFn r,List.ofFn c),k)=true ↔
      0<(largeIndices (d^20,List.ofFn r)).length ∧
      0<(largeIndices (d^20,List.ofFn c)).length := by
  simp only [hasLargeRectangle,parameterLargeIndices,marginThreshold_ofFn,
    ite_true, if_true,Bool.false_eq_true,ite_false,Bool.and_eq_true,decide_eq_true_eq]

lemma allSmall_of_no_large (k : ℕ)
    (h : hasLargeRectangle ((List.ofFn r,List.ofFn c),k)≠true) :
    ∀ i j,paperSmall r c i j=true := by
  intro i j
  apply Bool.eq_true_of_not_eq_false
  intro hij
  obtain ⟨hi,hj⟩ := (firstPaperSmall_false_iff r c (d^20) i j).mp hij
  have a := (largeIndexEquiv r (d^20)).symm ⟨i,hi⟩
  have b' := (largeIndexEquiv c (d^20)).symm ⟨j,hj⟩
  apply h
  apply (hasLargeRectangle_spec r c k).mpr
  exact ⟨Nat.zero_lt_of_lt a.isLt,Nat.zero_lt_of_lt b'.isLt⟩

lemma unitCodeBits_le (k : ℕ) : outerTrials d k*(outerSteps d b k*s)≤finiteSamplerBits r c k := by
  apply Nat.mul_le_mul_left
  exact (Nat.mul_le_mul_left (outerSteps d b k)
    (Nat.le_add_right s (25*(d+b+outerAccuracy d b k+1)^62))).trans (Nat.le_add_right _ _)

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_AllSamplingAccuracy
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Accuracy of the single computed sampler for arbitrary margins -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms CompletionCounts FirstPaperPhysicalMarginal
open ResidualMixture FirstSuccess FairBits SmallContextCoordinates
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "b" => smallBinaryLength r c

/-- The mathematical draw whose code is the output of the single public program. -/
def scheduledTableDraw (htotal : (∑ i,r i)=∑ j,c j) (k : ℕ)
    (bits : Fin (finiteSamplerBits r c k) → Bool) : Table r c :=
  if h : hasLargeRectangle ((List.ofFn r,List.ofFn c),k)=true then
    listedOuterDraw r c (computedCellEquiv r c)
      ((hasLargeRectangle_spec r c k).mp h).1 ((hasLargeRectangle_spec r c k).mp h).2
      b (outerAccuracy d b k) (smallBinaryLength_parameters r c).1
      (tableState r c (GreedyFeasibleTable.table r c htotal))
      (outerSteps d b k) (outerTrials d k) (GreedyFeasibleTable.table r c htotal) bits
  else
    unitCodeOuterDraw r c (computedCellEquiv r c) (allSmallFibre r c (allSmall_of_no_large r c k h))
      (tableState r c (GreedyFeasibleTable.table r c htotal)) (outerSteps d b k) (outerTrials d k)
      (GreedyFeasibleTable.table r c htotal) (prefixWord (unitCodeBits_le r c k) bits)

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ExactIntegerProgram
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary execution of an exact integer-weighted rejection trial -/

namespace ContingencyTables.ExactIntegerPrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms

def weightsCodeRealizer : Realizer weightsCode :=
  composition (f := fun xs : List ℕ => (xs.sum,xs))
    (g := fun z : ℕ×List ℕ => z.2.map (fun w => TreeFraction.normalize (w,z.1)))
    (pair listSum identity)
    (mapWith (composition (pair second first) TreeFraction.normalizeRealizer))

def choiceInputRealizer : Realizer choiceInput :=
  pair (composition first weightsCodeRealizer)
    (pair (composition second bitValue) (composition first listSum))

def weightedIndexRealizer : Realizer weightedIndex :=
  (choose (composition (pair (composition second bitValue) (composition first listSum)) less)
    (composition (composition choiceInputRealizer ExecutableChoice.chooseFast) TreeTyped.some)
    (constant none)).congr (by
      intro z
      simp only [Function.comp_apply,decide_eq_true_eq,weightedIndex])

end ContingencyTables.ExactIntegerPrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ExactIntegerRetry
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact law and geometric tail of integer rejection -/

namespace ContingencyTables.ExactIntegerChoice
open MatchingFPRAS ResidualMixture FirstSuccess
open scoped BigOperators Classical

noncomputable section
variable {r Q : ℕ} (w : Fin r → ℕ) (h : 0<totalWeight w) [NeZero Q]
variable (hQ : totalWeight w≤Q)

/-- `none` records that all supplied independent trials rejected; it is
not a fallback table. This is the finite prefix law of exact rejection. -/
def retryIntegerLaw (N : ℕ) : RationalLaw (Option (Fin r)) :=
  retryLaw (trialLaw w h hQ) (fun x => x.map some) none N

end
end ContingencyTables.ExactIntegerChoice

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ExactIntegerOnline
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The concrete fair-bit integer trial used by exact correction -/

namespace ContingencyTables.ExactIntegerOnline
open MatchingFPRAS MatchingFPRAS.TreeTyped MatchingFPRAS.PhysicalStream
open ExactIntegerChoice ExactIntegerPrograms FirstSuccess ResidualMixture
open scoped BigOperators Classical

def trialBitsRealizer : Realizer trialBits :=
  composition listSum DensePrograms.ceilLogTwoRealizer

noncomputable def trialRealizer : OnlineTree.Realizer trial :=
  FiniteWordExecution.realizer trialBitsRealizer weightedIndexRealizer

end ContingencyTables.ExactIntegerOnline

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_OriginalTableCheck
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary row and column checks for original-table candidates -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms Polynomial

def originalColumnTotalsRealizer : Realizer originalColumnTotals :=
  composition (pair second (composition
    (composition (composition first second) listLength) range)) (mapWith columnTotalRealizer)

def originalTableTestRealizer : Realizer originalTableTest :=
  composition (pair
    (composition (pair (composition second (map listSum)) (composition first first)) listNatEqual)
    (composition (pair originalColumnTotalsRealizer (composition first second)) listNatEqual)) boolAnd

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_OriginalTableEnumeration
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Enumerating original tables by all their bounded entries -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms Polynomial

def originalLayoutMarginsRealizer : Realizer originalLayoutMargins :=
  pair (composition (f := fun z : CompletionMargins => (0,z.1))
      (g := fun z : ℕ×List ℕ => z.1::z.2) (pair (constant 0) first) listCons)
    (composition (f := fun z : CompletionMargins => (0,z.2))
      (g := fun z : ℕ×List ℕ => z.1::z.2) (pair (constant 0) second) listCons)

def originalFreeMatrixRealizer : Realizer originalFreeMatrix :=
  composition (pair (composition first originalLayoutMarginsRealizer) second) unflattenGridRealizer

def originalCandidateRealizer : Realizer originalCandidate :=
  choose (composition (pair first originalFreeMatrixRealizer) originalTableTestRealizer)
    (composition originalFreeMatrixRealizer some) (constant none)

def originalEnumerationDataRealizer : Realizer originalEnumerationData :=
  composition originalLayoutMarginsRealizer completionEnumerationDataRealizer

def originalCandidatesRealizer : Realizer originalCandidates :=
  composition (pair identity (composition originalEnumerationDataRealizer gridWordsRealizer))
    (mapWith originalCandidateRealizer)

def originalEnumerationMeasure (z : CompletionMargins) : ℕ :=
  gridStateCount (originalEnumerationData z)+weight z

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ExactMatrixTrial
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Returning a matrix from the exact integer-weighted trial -/

namespace ContingencyTables.ExactMatrixTrial
open MatchingFPRAS MatchingFPRAS.TreeTyped MatchingFPRAS.PhysicalStream
open DensePrograms ProfilePrograms

def lookupRealizer : Realizer lookup :=
  composition (f := fun z : Lookup×ℕ => (z.1.2,z.1.1.getD z.2 none))
    (g := fun z : MatrixCode×Option MatrixCode => z.2.getD z.1)
    (pair (composition first second)
      (composition (pair (composition first first) second) (getDFast none)))
    FirstSuccessProgram.defaultRealizer

def decodeRealizer : Realizer decode :=
  (choose (composition second FirstSuccessProgram.isSomeRealizer)
    (composition (composition
      (pair first (composition (pair (constant (0:ℕ)) second) FirstSuccessProgram.defaultRealizer))
      lookupRealizer) some) (constant none)).congr (by
        intro z
        rcases z with ⟨cache,o⟩
        cases o <;> rfl)

noncomputable def trialRealizer : OnlineTree.Realizer trial :=
  (OnlineTree.composition
    (OnlineTree.pair (OnlineTree.deterministic first)
      (OnlineTree.composition (OnlineTree.deterministic second) ExactIntegerOnline.trialRealizer))
    (OnlineTree.deterministic decodeRealizer)).congr (by
      intro z g
      simp only [Experiment.mean_bind,Experiment.mean,Experiment.mean_map,trial])

end ContingencyTables.ExactMatrixTrial

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_OriginalTableIndex
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary lookup of an original table's finite-box index -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms

def originalIndexInputRealizer : Realizer originalIndexInput :=
  pair (composition second flatten)
    (composition (composition (composition first first) listSum) successor)

def originalIndexRealizer : Realizer originalIndex :=
  composition originalIndexInputRealizer gridIndexRealizer

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileBoxIndex
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A computed finite-box index for the two small-profile views -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms

def profileBoxIndex (z : ProfileCheckData) : ℕ :=
  gridIndex (flattenViews z.1.1.2,z.2+1)

def profileBoxIndexRealizer : Realizer profileBoxIndex :=
  composition (pair (composition profileViews flattenViewsRealizer)
    (composition second successor)) gridIndexRealizer

end ContingencyTables.ProfilePrograms

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal
open SmallContextCoordinates CompletionCounts
open scoped BigOperators Classical
noncomputable section

variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c))
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "U" => d^20

abbrev ProfileBox := Fin (q+q) → Fin (U+1)
abbrev ProfileIndex := Fin ((U+1)^(q+q))

def profileBoxCoordinates (x : PaperStates r c) : ProfileBox (m := m) (n := n) (q := q) :=
  fun i => ⟨physicalProfile (paperSmall r c) (stateCapacity r c) r c (d^12) x
      (flatViewEquiv (paperSmall r c) e i),
    Nat.lt_succ_of_le (stateCode_bounded r c x _ _)⟩

def profileIndex (x : PaperStates r c) : ProfileIndex (m := m) (n := n) (q := q) :=
  finFunctionFinEquiv (profileBoxCoordinates r c e x)

attribute [local irreducible] physicalProfile

attribute [local irreducible] profileBoxCoordinates profileIndex

def profileAt (k : ProfileIndex (m := m) (n := n) (q := q)) : Option (PaperStates r c) :=
  decodeStateCode r c e (splitViews (q,List.ofFn
    (fun i => ((finFunctionFinEquiv.symm k : ProfileBox (m := m) (n := n) (q := q)) i).val)))

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileBoxEnumeration
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executable enumeration of the bounded two-view profile box -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms

def profileEnumerationData (z : ProfileCheckData) : GridEnumerationData :=
  (((z.1.1.1++z.1.1.1).map (fun _ => false)),z.2+1)

def profileEnumerationDataRealizer : Realizer profileEnumerationData := by
  let catalog : Realizer (fun z : ProfileCheckData => z.1.1.1) :=
    composition (composition first first) first
  let markers := composition (composition (pair catalog catalog) append) (map (constant false))
  exact pair markers (composition second successor)

def profileBoxViews (z : ProfileCheckData) : List (List ℕ×List ℕ) :=
  (gridWords (profileEnumerationData z)).map (fun word => splitViews (z.1.1.1.length,word))

def profileBoxViewsRealizer : Realizer profileBoxViews := by
  let width : Realizer (fun z : ProfileCheckData => z.1.1.1.length) :=
    composition (composition (composition first first) first) listLength
  let words := composition profileEnumerationDataRealizer gridWordsRealizer
  exact composition (pair width words) (mapWith splitViewsRealizer)

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_MeasuredMap
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Costs for mapping cached computations over a finite list -/

namespace ContingencyTables.MeasuredMap
open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial

variable {A B C : Type} [Codec A] [Codec B] [Codec C]

def listMeasure (μ : A×B → ℕ) (z : A×List B) : ℕ :=
  weight z+(z.2.map (fun b => μ (z.1,b))).sum

end ContingencyTables.MeasuredMap

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_IntegerMatrixPoint
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Propagating an executable point mass through an integer matrix -/

namespace ContingencyTables.IntegerMatrixPrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial

def pointEntryRealizer : Realizer pointEntry :=
  (choose (composition (pair second first) natEqual) (constant 1) (constant 0)).congr (by
    intro z
    simp only [Function.comp_apply,decide_eq_true_eq]
    rfl)

def pointVectorRealizer : Realizer pointVector :=
  composition (pair second (composition (composition first listLength) range))
    (mapWith pointEntryRealizer)

def fromPointInputRealizer : Realizer (fun z : ℕ×(List (List ℕ)×ℕ) =>
    (z.1,(z.2.1,pointVector z.2))) :=
  pair first (pair (composition second first) (composition second pointVectorRealizer))

def fromPointRealizer : Realizer fromPoint :=
  composition fromPointInputRealizer iterateRealizer

end ContingencyTables.IntegerMatrixPrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_UnitIntegerLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integer counts for the all-small sampler's actual random words -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal
open FirstSuccess FairBits CompletionCounts ResidualMixture SmallContextCoordinates
open scoped BigOperators Classical
noncomputable section

variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c))
local notation "s" => smallProposalBits (I := Fin m) (J := Fin n)

def unitStepCounts (x : PaperStates r c) : IntegerLaw (PaperStates r c) (2^s) :=
  (IntegerLaw.boolean s).push (unitCodeBitStep r c e x)

attribute [local irreducible] unitStepCounts unitSmallStep

def unitWalkCounts (x : PaperStates r c) (N : ℕ) :
    IntegerLaw (PaperStates r c) ((2^s)^N) := IntegerLaw.walk (unitStepCounts r c e) x N

attribute [local irreducible] unitWalkCounts

def unitTrialCounts (hsmall : ∀ i j,paperSmall r c i j=true) (x : PaperStates r c) (N : ℕ) :
    IntegerLaw (Option (Table r c)) ((2^s)^N) :=
  (unitWalkCounts r c e x N).push (fun y => stateTrial r c ⟨y,allSmallFibre r c hsmall y⟩)

def unitOuterCounts (hsmall : ∀ i j,paperSmall r c i j=true)
    (x : PaperStates r c) (N J : ℕ) (fallback : Table r c) :
    IntegerLaw (Table r c) (((2^s)^N)^J) :=
  (unitTrialCounts r c e hsmall x N).retry fallback J

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_OriginalTableCardinality
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing the number of feasible original-table box entries -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms

def originalCardEntryRealizer : Realizer originalCardEntry :=
  choose FirstSuccessProgram.isSomeRealizer (constant 1) (constant 0)

def originalCardinalityRealizer : Realizer originalCardinality :=
  composition (f := originalCandidates) (g := fun xs => (xs.map originalCardEntry).sum)
    originalCandidatesRealizer (composition (map originalCardEntryRealizer) listSum)

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_OriginalResidualVector
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit integer correction weights on the original-table box -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms Polynomial

def residualVectorEntryRealizer : Realizer residualVectorEntry := by
  let candidate : Realizer (fun z : ResidualVectorCache×ℕ => z.1.1.1.getD z.2 none) :=
    composition (pair (composition (composition first first) first) second) (getDFast none)
  let numerator : Realizer (fun z : ResidualVectorCache×ℕ => z.1.1.2.getD z.2 0) :=
    composition (pair (composition (composition first first) second) second) (getDFast 0)
  let input : Realizer (fun z : ResidualVectorCache×ℕ =>
      (z.1.2.1,(z.1.2.2,z.1.1.2.getD z.2 0))) :=
    pair (composition (composition first second) first)
      (pair (composition (composition first second) second) numerator)
  exact choose (composition candidate FirstSuccessProgram.isSomeRealizer)
    (composition input ResidualWeightPrograms.countRealizer) (constant 0)

def residualVectorIndicesRealizer : Realizer residualVectorIndices :=
  composition (composition (composition first first) listLength) range

def residualVectorRealizer : Realizer residualVector :=
  composition (pair identity residualVectorIndicesRealizer) (mapWith residualVectorEntryRealizer)

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperCorrectionBudget
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cardinality and rare-branch precision for exact correction -/

namespace ContingencyTables.SmallGraphProfiles
open scoped BigOperators
open CompletionCounts

universe u
variable {I J : Type u} [Fintype I] [Fintype J]

noncomputable def correctionPrecision (r : I → ℕ) (c : J → ℕ) : ℕ :=
  (dimensionAllowance (I := I) (J := J))^6*(smallBinaryLength r c)^2

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ExactPublicLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact public output law and almost-sure termination -/

namespace ContingencyTables.ExactPublicLaw
open MatchingFPRAS MatchingFPRAS.PhysicalStream MatchingFPRAS.PhysicalPost Turing
open PhysicalEventBounds PhysicalPublicLaw SmallGraphProfiles
open scoped BigOperators Classical
noncomputable section
attribute [local irreducible] correctionPrecision
  PublishedInputs.FiniteBoxPrekopaLeindler PublishedInputs.FiniteCheeger
  CompletionCounts.dimensionAllowance

variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)

def prefixError (N : ℕ) : ℝ :=
  (1/(2:ℝ)^(correctionPrecision r c))*(1/2:ℝ)^N

end
end ContingencyTables.ExactPublicLaw

end OAI
end


