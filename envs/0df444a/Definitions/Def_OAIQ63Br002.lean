-- Prove2me | Definitions.Def_OAIQ63Br002
-- name    : OAIQ63Br002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T00:07:38.78397+00:00
-- url     : https://prove2.me/theorems/f5bfb2d3-caed-4f8f-bd02-dd293109bc19
-- title:
--   Definitions bundle OAIQ63Br002 of the split of OpenAI, Balanced counterexamples to Ryser's conjecture at prime orders (result family 162)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Balanced.main_result`, carved from OpenAI's openai/math development (OpenAI, *Balanced counterexamples to Ryser's conjecture at prime orders (result family 162)*, OpenAI Math Release, September 27, 2026, result family 162, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 481 declarations of OpenAI's Lean: 331 definitions, 5 inductive types or structures, 1 instance and 144 theorems. The definitions and types are `OAI.Balanced.DeletionCountingExposure.exposedLines`, `OAI.Balanced.DeletionCountingExposure.observation`, `OAI.Balanced.DeletionCountingExposure.pastUncovered`, `OAI.Balanced.DeterministicReduction`, `OAI.Balanced.ExposedExternalSum.externalEvent`, `OAI.Balanced.ExposedOppositeSum.freshTuples`, `OAI.Balanced.ExposedOppositeSum.oldOppositeFreshCount`, `OAI.Balanced.ExposedOppositeSum.oldOppositeFreshSum`, `OAI.Balanced.ExternalAssembly.freshGeneratorLabels`, `OAI.Balanced.ExternalAssembly.patternModel`, `OAI.Balanced.ExternalAssembly.support`, `OAI.Balanced.ExternalAssembly.swapKey`, `OAI.Balanced.FreshExternalWitness.fixedValues`, `OAI.Balanced.FreshExternalWitness.freshPairs`, `OAI.Balanced.FreshExternalWitness.orientedEvent`, `OAI.Balanced.FreshExternalWitness.probabilitySum`, `OAI.Balanced.FreshExternalWitness.sourceEvent`, `OAI.Balanced.FreshExternalWitness.sourceProbabilitySum`, `OAI.Balanced.FreshExternalWitness.sourceWitnessCount`, `OAI.Balanced.FreshExternalWitness.targetPoint`, `OAI.Balanced.FreshTupleWitness.fiberSuccessProbability`, `OAI.Balanced.FreshTupleWitness.pairPrescription`, `OAI.Balanced.FreshWitnessProbability.exposedLaw`, `OAI.Balanced.GeometricDeletionCounting.assemble`, `OAI.Balanced.GeometricDeletionCounting.deletionEquivFamilies`, `OAI.Balanced.GeometricDeletionCounting.offsetsAt`, `OAI.Balanced.IndependentSelector`, `OAI.Balanced.IsProfilePair`, `OAI.Balanced.LineOccupancy.hitAssignmentsEquiv`, `OAI.Balanced.LineOccupancy.transverseHitEquiv`, `OAI.Balanced.LineOccupancy.transverseOffsets`, `OAI.Balanced.LineOccupancy.unhitCount`, `OAI.Balanced.Local.Admissible`, `OAI.Balanced.Local.AdmissibleBadCover`, `OAI.Balanced.Local.Aligned`, `OAI.Balanced.Local.AlignedGlobal.AlignedOffsets`, `OAI.Balanced.Local.AlignedGlobal.PointSystem`, `OAI.Balanced.Local.AlignedGlobal.PrefixData`, `OAI.Balanced.Local.AlignedGlobal.ProjectionData`, `OAI.Balanced.Local.AlignedGlobal.coordinateEquiv` and 296 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `BalancedRyser_Candidates_CandidateBasics`, `BalancedRyser_Candidates_CandidateOccupancyBridge`, `BalancedRyser_Candidates_CandidateSelectionBridge`, `BalancedRyser_Candidates_Candidates`, `BalancedRyser_Candidates_ExposedExternalSum`, `BalancedRyser_Candidates_ExposedOppositeSum`, `BalancedRyser_Candidates_ExternalFreshGeneratorBound`, `BalancedRyser_Candidates_ExternalWitnessModel`, `BalancedRyser_Candidates_FreshExternalCountBound`, `BalancedRyser_Candidates_FreshExternalCounting`, `BalancedRyser_Candidates_FreshExternalWitness`, `BalancedRyser_Candidates_OppositeAssembly`, `BalancedRyser_Candidates_OppositeCases`, `BalancedRyser_Candidates_OppositeFreshMean`, `BalancedRyser_Candidates_SelectedCandidateFixedLaw`, `BalancedRyser_Candidates_SelectionCandidateLaw`, `BalancedRyser_Construction_ConstructionRepresentationLemmas`, `BalancedRyser_Construction_ExternalWitnessPartition`, `BalancedRyser_Deletion_Deletion`, `BalancedRyser_Deletion_DeletionCoordinates`, `BalancedRyser_Deletion_DeletionCountingExposure`, `BalancedRyser_Deletion_GeometricDeletionCounting`, `BalancedRyser_Deletion_SelectedDeletion`, `BalancedRyser_Deletion_SelectedDeletionCoordinates`, `BalancedRyser_Deletion_SelectedDeletionKernel`, `BalancedRyser_Deletion_SelectedDeletionPMF`, `BalancedRyser_Incidence_AffineIncidence`, `BalancedRyser_Incidence_AffinePlaneInstance`, `BalancedRyser_Incidence_AlignedGlobalProjectedIncidence`, `BalancedRyser_Incidence_LocalOrderedPencils`, `BalancedRyser_Incidence_PartialIncidence`, `BalancedRyser_Incidence_Projective`, `BalancedRyser_Incidence_Projective2`, `BalancedRyser_Incidence_ProjectiveModel`, `BalancedRyser_Incidence_ProjectiveNormalization`, `BalancedRyser_Incidence_RedeiPolynomial`, `BalancedRyser_Incidence_SelectionAffineAdapter`, `BalancedRyser_Incidence_Stability`, `BalancedRyser_Incidence_UnusedOffsetIncidence`, `BalancedRyser_Local_AlignedGlobalCardinality`, `BalancedRyser_Local_AlignedGlobalCurrentTuple`, `BalancedRyser_Local_AlignedGlobalProduct`, `BalancedRyser_Local_AlignedHistoryKernel`, `BalancedRyser_Local_AlignedProjectedExposure`, `BalancedRyser_Local_AlignedTokenPointLaw`, `BalancedRyser_Local_AlignedUnusedLaw`, `BalancedRyser_Local_AlignedUnusedTripleBound`, `BalancedRyser_Local_AlignedUsedObservable`, `BalancedRyser_Local_AlignedUsedTestTransport`, `BalancedRyser_Local_AlignmentNormalization`, `BalancedRyser_Local_ChildAlignment`, `BalancedRyser_Local_GlobalAlignedParentCoordinates`, `BalancedRyser_Local_HalfWeightLocalLemma`, `BalancedRyser_Local_Local`, `BalancedRyser_Local_LocalConditionFibers`, `BalancedRyser_Local_LocalConditionSpec`, `BalancedRyser_Local_LocalConfigurationPattern`, `BalancedRyser_Local_LocalCoverMarking`, `BalancedRyser_Local_LocalDirectionAssignments`, `BalancedRyser_Local_LocalExposureTiming`, `BalancedRyser_Local_LocalFailureSummation`, `BalancedRyser_Local_LocalFiberBounds`, `BalancedRyser_Local_LocalFourEvents`, `BalancedRyser_Local_LocalInjectionFreeLaw`, `BalancedRyser_Local_LocalKernel`, `BalancedRyser_Local_LocalParentMap`, `BalancedRyser_Local_LocalPatternEvents`, `BalancedRyser_Local_LocalPatternTransport`, `BalancedRyser_Local_LocalPrecoverageTransport`, `BalancedRyser_Local_LocalPrescribedGeometry`, `BalancedRyser_Local_LocalPrescriptionCounting`, `BalancedRyser_Local_LocalSelectedKernel`, `BalancedRyser_Local_LocalTupleReindex`, `BalancedRyser_Local_LocalTwoReuseAssembly`, `BalancedRyser_Local_LocalTwoReuseMean`, `BalancedRyser_Local_LocalTwoReuseUsedEvents`, `BalancedRyser_Local_LocalUnusedOffsetProbability`, `BalancedRyser_Local_LocalUnusedTripleProbability`, `BalancedRyser_Local_LocalUsedEventMean`, `BalancedRyser_Local_LocalUsedEventUnion`, `BalancedRyser_Local_LowReuseOrder`, `BalancedRyser_Local_MeasureLocalLemma`, `BalancedRyser_Local_ReusePrefix`, `BalancedRyser_Local_ReusePrescriptions`, `BalancedRyser_Local_ReuseScore`, `BalancedRyser_Local_ReuseTargetSum`, `BalancedRyser_Local_ReuseWeightedBound`, `BalancedRyser_Probability_EqualityPatternOrdering`, `BalancedRyser_Probability_FreshTupleWitness`, `BalancedRyser_Probability_FreshWitnessConditional`, `BalancedRyser_Probability_FreshWitnessProbability`, `BalancedRyser_Probability_MainAssembly`, `BalancedRyser_Probability_NearCoverVisibility`, `BalancedRyser_Probability_PatternIntegrability`, `BalancedRyser_Probability_PatternModelCancellation`, `BalancedRyser_Probability_PatternModelExpansion`, `BalancedRyser_Probability_PurposefulIndices`, `BalancedRyser_Probability_ScheduledCountingExposure`, `BalancedRyser_Probability_ScheduledCountingLaw`, `BalancedRyser_Probability_ScheduledMarksBridge`, `BalancedRyser_Probability_TupleExposure`, `BalancedRyser_Probability_UncoveredSubsetVariance`, `BalancedRyser_Profiles_LocalMarkedAnchors`, `BalancedRyser_Profiles_Profile`, `BalancedRyser_Profiles_ProfileClassMargin`, `BalancedRyser_Profiles_ProfileCountingAssembly`, `BalancedRyser_Profiles_ProfileFiniteMarks`, `BalancedRyser_Profiles_ProfileGridDetection`, `BalancedRyser_Profiles_ProfileMarkedError`, `BalancedRyser_Profiles_ProfileMarkedOrders`, `BalancedRyser_Profiles_ProfileMomentCompactness`, `BalancedRyser_Profiles_ProfileScheduledMargin`, `BalancedRyser_Profiles_ProfileScheduledMarks`, `BalancedRyser_Profiles_ProfileWitnessPayment`, `BalancedRyser_Selection_LineOccupancy`, `BalancedRyser_Selection_SelectionOccupancy`, `BalancedRyser_Selection_SelectionPushforward2`, `BalancedRyser_Selection_SelectionTailCompletion`.
--
--   **Imports.** It imports the published bundle `Def_BalancedRyser`; the bundles `OAIQ63Br000` and `OAIQ63Br001` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ63Br004`; the statements `OAI.Balanced.Local.injectiveUsedEventsEstimate_proof`, `OAI.Balanced.Local.pencilSmallReuse_proof`, `OAI.Balanced.ProfileCountingAssembly.profileCounting_of_sourceRareTailBound`, `OAI.Balanced.ProfileScheduledFiniteComparison.eventually_finiteDetection_of_profileClass`, `OAI.Balanced.deterministic_reduction`, `OAI.Balanced.pencilReuse_proof`, `OAI.Balanced.pencil_local`, `OAI.Balanced.robustDeletion_of_profileCounting` and `OAI.Balanced.robust_deletion`; the proofs of `OAI.Balanced.CandidateAbundanceAssembly.tendsto_square_fibers`, `OAI.Balanced.CandidateAbundanceAssembly.tendsto_successful_roots`, `OAI.Balanced.CandidateIncidenceTests.candidateGraphResult_of_incidence_estimates`, `OAI.Balanced.CandidateIncidenceTests.candidateGraphResult_of_size_estimate`, `OAI.Balanced.CandidateIncidenceTests.tendsto_smallGood`, `OAI.Balanced.ExternalWitnessTail.candidateSlots_of_uniform_moment`, `OAI.Balanced.Local.pencilSmallReuse_proof` and `OAI.Balanced.candidateGraph_proof`.
-- source:
--   OpenAI, Balanced counterexamples to Ryser's conjecture at prime orders (result family 162), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 162; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Balanced-Counterexamples-to-Rysers-Conjecture-at-Prime-Orders-September-27-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_BalancedRyser
import Definitions.Def_OAIQ63Br000
import Definitions.Def_OAIQ63Br001

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_Candidates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

noncomputable section
open scoped Classical
open Filter Topology

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def IndependentSelector (M : MergedPairs F) (f : Slot F → F) : Prop :=
  ∀ s t, s ≠ t → ¬ CandidateAdjacent M (s, f s) (t, f t)

def selectedConfiguration (M : MergedPairs F) (f : Slot F → F) : Configuration F :=
  ⟨M, fun s => retainedChoice M (s.1, f s)⟩

universe u

end
end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateBasics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

noncomputable section
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem retainedChoice_valid {M : MergedPairs F} {l : Line F}
    (h : SupportsValidTuple M l) : ValidChoice M l.1 (retainedChoice M l) := by
  simpa only [retainedChoice, dite_eq_left h] using Classical.choose_spec h

theorem choicesCompatible_symm {M : MergedPairs F} {g h : Direction F}
    {A B : SplitChoice F} (hc : ChoicesCompatible M g h A B) :
    ChoicesCompatible M h g B A := by
  rcases hc with ⟨hab, hba, hgen, hmerged⟩
  refine ⟨hba, hab, ?_, ?_⟩
  · simpa only [Finset.inter_comm] using hgen
  · intro heq d
    exact ⟨(hmerged heq.symm d).2, (hmerged heq.symm d).1⟩

theorem candidateAdjacent_symm {M : MergedPairs F} {v w : CandidateVertex F}
    (h : CandidateAdjacent M v w) : CandidateAdjacent M w v := by
  rcases h with ⟨hv, hw, hne, hbad⟩
  exact ⟨hw, hv, Ne.symm hne, fun hgood => hbad (choicesCompatible_symm hgood)⟩

theorem candidateAdjacent_irrefl (M : MergedPairs F) (v : CandidateVertex F) :
    ¬ CandidateAdjacent M v v := by
  intro h
  exact h.2.2.1 rfl

theorem selectedConfiguration_valid {M : MergedPairs F} {f : Slot F → F}
    (hd : DistinctConstituents M) (hf : CandidateSelector M f) :
    (selectedConfiguration M f).Valid := by
  refine ⟨hd, ?_⟩
  intro s
  exact retainedChoice_valid (hf s)

theorem selectedConfiguration_compatible_iff {M : MergedPairs F} {f : Slot F → F}
    (hf : CandidateSelector M f) :
    (selectedConfiguration M f).Compatible ↔ IndependentSelector M f := by
  rw [Configuration.compatible_iff_pairwise]
  constructor
  · intro h s t hst hadj
    exact hadj.2.2.2 (h s t hst)
  · intro h s t hst
    by_contra hbad
    apply h s t hst
    exact ⟨mem_candidateVertices.mpr (hf s), mem_candidateVertices.mpr (hf t), hst, hbad⟩

end
end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_AffineIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

variable {F : Type*} [Field F]

theorem line_eq_lineThrough (p : Point F) (l : Line F) (h : OnLine p l) :
    l = lineThrough l.1 p := by
  apply Prod.ext
  · rfl
  · exact h.symm

theorem eq_of_two_common_points (p r : Point F) (hne : p ≠ r)
    (l m : Line F) (hpl : OnLine p l) (hrl : OnLine r l)
    (hpm : OnLine p m) (hrm : OnLine r m) : l = m := by
  rcases p with ⟨x, y⟩
  rcases r with ⟨x', y'⟩
  rcases l with ⟨a, c⟩
  rcases m with ⟨b, d⟩
  cases a with
  | none =>
    cases b with
    | none =>
      simp only [OnLine, lineEval] at hpl hpm
      exact Prod.ext rfl (hpl.symm.trans hpm)
    | some b =>
      simp only [OnLine, lineEval] at hpl hrl hpm hrm
      have hx : x = x' := hpl.trans hrl.symm
      have hy : y = y' := by linear_combination hpm - hrm + b * hx
      exact False.elim (hne (Prod.ext hx hy))
  | some a =>
    cases b with
    | none =>
      simp only [OnLine, lineEval] at hpl hrl hpm hrm
      have hx : x = x' := hpm.trans hrm.symm
      have hy : y = y' := by linear_combination hpl - hrl + a * hx
      exact False.elim (hne (Prod.ext hx hy))
    | some b =>
      simp only [OnLine, lineEval] at hpl hrl hpm hrm
      by_cases hab : a = b
      · subst b
        exact Prod.ext rfl (hpl.symm.trans hpm)
      · have hmul : (a - b) * (x - x') = 0 := by
          linear_combination -hpl + hrl + hpm - hrm
        have hx : x = x' := sub_eq_zero.mp
          ((mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hab))
        have hy : y = y' := by linear_combination hpl - hrl + a * hx
        exact False.elim (hne (Prod.ext hx hy))

theorem common_point_eq_of_lines_ne (l m : Line F) (hne : l ≠ m)
    (p r : Point F) (hpl : OnLine p l) (hpm : OnLine p m)
    (hrl : OnLine r l) (hrm : OnLine r m) : p = r := by
  by_contra hpr
  exact hne (eq_of_two_common_points p r hpr l m hpl hrl hpm hrm)

def linePointsEquiv : (l : Line F) → {p : Point F // OnLine p l} ≃ F
  | (none, b) =>
    { toFun := fun p => p.val.2
      invFun := fun t => ⟨(b, t), rfl⟩
      left_inv := fun p => by
        apply Subtype.ext
        apply Prod.ext
        · exact p.property.symm
        · rfl
      right_inv := fun _ => rfl }
  | (some a, b) =>
    { toFun := fun p => p.val.1
      invFun := fun t => ⟨(t, a * t + b), by
        change a * t + b - a * t = b
        ring⟩
      left_inv := fun p => by
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · have h := p.property
          change p.val.2 - a * p.val.1 = b at h
          change a * p.val.1 + b = p.val.2
          linear_combination -h
      right_inv := fun _ => rfl }

theorem onLine_lineIntersection_left (l m : Line F) (hdir : l.1 ≠ m.1) :
    OnLine (lineIntersection l m) l := by
  rcases l with ⟨a, c⟩
  rcases m with ⟨b, d⟩
  cases a with
  | none =>
    cases b with
    | none => exact False.elim (hdir rfl)
    | some b => rfl
  | some a =>
    cases b with
    | none => simp [OnLine, lineIntersection, lineEval]
    | some b => simp [OnLine, lineIntersection, lineEval]

theorem onLine_lineIntersection_right (l m : Line F) (hdir : l.1 ≠ m.1) :
    OnLine (lineIntersection l m) m := by
  rcases l with ⟨a, c⟩
  rcases m with ⟨b, d⟩
  cases a with
  | none =>
    cases b with
    | none => exact False.elim (hdir rfl)
    | some b => simp [OnLine, lineIntersection, lineEval]
  | some a =>
    cases b with
    | none => rfl
    | some b =>
      have hab : a ≠ b := fun h => hdir (congrArg some h)
      change a * ((d - c) / (a - b)) + c - b * ((d - c) / (a - b)) = d
      field_simp [sub_ne_zero.mpr hab]
      ring

section Decidable

variable [DecidableEq F]

theorem existsUnique_line_of_ne (p r : Point F) (hne : p ≠ r) :
    ∃! l : Line F, OnLine p l ∧ OnLine r l := by
  refine ⟨joiningLine p r, ⟨onLine_joiningLine_left p r,
    onLine_joiningLine_right p r⟩, ?_⟩
  intro l hl
  exact eq_of_two_common_points p r hne l (joiningLine p r)
    hl.1 hl.2 (onLine_joiningLine_left p r) (onLine_joiningLine_right p r)

end Decidable

section Finite

variable [Fintype F] [DecidableEq F]

theorem linePoints_card (l : Line F) : (linePoints l).card = Fintype.card F := by
  unfold linePoints
  rw [← Fintype.card_subtype]
  exact Fintype.card_congr (linePointsEquiv l)

end Finite

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_AffinePlaneInstance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def linesInDirectionEquiv (d : Direction F) :
    {l : Line F // l.1 = d} ≃ F where
  toFun l := l.val.2
  invFun b := ⟨(d, b), rfl⟩
  left_inv l := by
    apply Subtype.ext
    apply Prod.ext
    · exact l.property.symm
    · rfl
  right_inv _ := rfl

omit [Field F] in
theorem card_lines_direction (d : Direction F) :
    (Finset.univ.filter (fun l : Line F => l.1 = d)).card = Fintype.card F := by
  rw [← Fintype.card_subtype]
  exact Fintype.card_congr (linesInDirectionEquiv d)

end

noncomputable def coordinatePlane (F : Type*) [Field F] [Fintype F] [DecidableEq F] :
    FiniteAffine.Plane (Fintype.card F) (Point F) (Direction F) (Line F) where
  direction := Prod.fst
  incident := OnLine
  card_points := by simp [Point, pow_two]
  card_directions := Fintype.card_option
  card_lines_direction := by
    intro d
    convert (card_lines_direction (F := F) d) using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ext l
    simp
  card_points_line := by
    intro l
    convert (linePoints_card l) using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ext p
    simp [linePoints]
  unique_line_direction := by
    intro p d
    refine ⟨lineThrough d p, ⟨rfl, onLine_lineThrough d p⟩, ?_⟩
    intro l hl
    rw [line_eq_lineThrough p l hl.2, hl.1]
  unique_join := existsUnique_line_of_ne

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

@[simp] theorem coordinatePlane_direction (l : Line F) :
    (coordinatePlane F).direction l = l.1 := rfl

@[simp] theorem coordinatePlane_incident (p : Point F) (l : Line F) :
    (coordinatePlane F).incident p l ↔ OnLine p l := Iff.rfl

@[simp] theorem coordinatePlane_linePoints (l : Line F) :
    (coordinatePlane F).linePoints l = linePoints l := by
  ext p
  simp only [FiniteAffine.Plane.linePoints, linePoints, Finset.mem_filter,
    Finset.mem_univ, true_and, coordinatePlane_incident]

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateSelectionBridge
attribute [-instance] _root_.OAI.Balanced.Selection.Process.snapshotPathLaw_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

noncomputable section
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def actualCandidateGraph (M : MergedPairs F) : SimpleGraph (AvailableCandidate M) where
  Adj v w := CandidateAdjacent M v.val w.val
  symm := ⟨fun _ _ h => candidateAdjacent_symm h⟩
  loopless := ⟨fun v => candidateAdjacent_irrefl M v.val⟩

def candidateSelectionInput (M : MergedPairs F)
    (J : AvailableCandidate M → Finset (CandidateVertex F)) :
    Selection.Input (Slot F) (AvailableCandidate M) where
  graph := actualCandidateGraph M
  slot v := v.val.1
  exceptional v := (J v).subtype (fun w => w ∈ candidateVertices M)

theorem candidateSelection_selector_of_transversal (M : MergedPairs F)
    (J : AvailableCandidate M → Finset (CandidateVertex F))
    (a : Slot F → AvailableCandidate M)
    (ha : Selection.IsIndependentTransversal (candidateSelectionInput M J) a) :
    CandidateSelector M (fun s => (a s).val.2) ∧
      IndependentSelector M (fun s => (a s).val.2) := by
  have heq (s : Slot F) : (a s).val = (s, (a s).val.2) :=
    Prod.ext (ha.1 s) rfl
  constructor
  · intro s
    have h := mem_candidateVertices.mp (a s).property
    rw [heq s] at h
    exact h
  · intro s t hst
    have h := ha.2 s t hst
    change ¬ CandidateAdjacent M (a s).val (a t).val at h
    rw [heq s, heq t] at h
    exact h

theorem candidateSelection_configuration_of_transversal (M : MergedPairs F)
    (J : AvailableCandidate M → Finset (CandidateVertex F))
    (a : Slot F → AvailableCandidate M) (hd : DistinctConstituents M)
    (ha : Selection.IsIndependentTransversal (candidateSelectionInput M J) a) :
    (selectedConfiguration M (fun s => (a s).val.2)).Valid ∧
      (selectedConfiguration M (fun s => (a s).val.2)).Compatible := by
  obtain ⟨hs, hi⟩ := candidateSelection_selector_of_transversal M J a ha
  exact ⟨selectedConfiguration_valid hd hs,
    (selectedConfiguration_compatible_iff hs).mpr hi⟩

end
end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionOccupancy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.SelectionOccupancy

noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable (C : Configuration F)

def secondConstituents : Finset (Line F) :=
  Finset.univ.image (fun d => constituent C.merged d true)

def initial (l : Line F) : Finset (Point F) :=
  if l ∈ secondConstituents C then linePoints l
  else (linePoints l).filter (fun p => ∀ d, ¬ OnLine p (constituent C.merged d true))

def final (l : Line F) : Finset (Point F) :=
  (initial C l).filter (fun p => ∀ S ∈ C.splitLines, S ≠ l → ¬ OnLine p S)

theorem initial_card_lower_bound (c₀ : ℝ) (hc₀ : c₀ ≤ 1)
    (hbase : ∀ l, l ∉ secondConstituents C →
      c₀ * Fintype.card F ≤
        (((linePoints l).filter (fun p => ∀ d,
          ¬ OnLine p (constituent C.merged d true))).card : ℝ)) :
    ∀ l, c₀ * Fintype.card F ≤ ((initial C l).card : ℝ) := by
  intro l
  by_cases hl : l ∈ secondConstituents C
  · rw [initial, ite_eq_left hl, linePoints_card]
    exact mul_le_of_le_one_left (Nat.cast_nonneg _) hc₀
  · simpa [initial, hl] using hbase l hl

omit [Field F] in
lemma secondConstituent_mem (d : Direction F) :
    constituent C.merged d true ∈ secondConstituents C := by
  exact Finset.mem_image.mpr ⟨d, Finset.mem_univ _, rfl⟩

lemma final_eq_initial_inter_retained (l : Line F) (hl : l ∉ C.splitLines) :
    final C l = initial C l ∩ C.retained := by
  ext p
  simp only [final, Finset.mem_filter, Finset.mem_inter, Configuration.retained,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hp, havoid⟩
    refine ⟨hp, ?_⟩
    intro S hS
    exact havoid S hS (fun heq => hl (heq ▸ hS))
  · rintro ⟨hp, havoid⟩
    exact ⟨hp, fun S hS _ => havoid S hS⟩

lemma mem_core_iff (p : Point F) :
    p ∈ C.core ↔ p ∈ C.retained ∧
      ∀ d, ¬ OnLine p (constituent C.merged d true) := by
  simp only [Configuration.core, Configuration.retained, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · intro h
    refine ⟨fun S hS => h S (Finset.mem_union_left _ hS), ?_⟩
    intro d
    exact h _ (Finset.mem_union_right _ (secondConstituent_mem C d))
  · rintro ⟨hs, hm⟩ l hl
    rcases Finset.mem_union.mp hl with hsplit | hsecond
    · exact hs l hsplit
    · rcases Finset.mem_image.mp hsecond with ⟨d, _, rfl⟩
      exact hm d

theorem final_eq_core_inter (l : Line F) (hl : l ∉ C.deletedLines) :
    final C l = linePoints l ∩ C.core := by
  have hs : l ∉ C.splitLines := fun h => hl (Finset.mem_union_left _ h)
  have hm : l ∉ secondConstituents C := fun h => hl (Finset.mem_union_right _ h)
  rw [final_eq_initial_inter_retained C l hs, initial, ite_eq_right hm]
  ext p
  simp only [Finset.mem_inter, Finset.mem_filter, mem_core_iff C]
  tauto

theorem final_secondConstituent (hV : C.Valid) (d : Direction F) :
    final C (constituent C.merged d true) =
      linePoints (constituent C.merged d true) ∩ C.retained := by
  have hs : constituent C.merged d true ∉ C.splitLines := by
    intro h
    exact Finset.disjoint_left.mp (C.split_disjoint_constituent hV) h
      (C.constituent_mem_lines d true)
  rw [final_eq_initial_inter_retained C _ hs, initial,
    ite_eq_left (secondConstituent_mem C d)]

theorem occupancy_of_final (hV : C.Valid) (ρ : ℝ) (B : ℕ)
    (hmultiplicity : ∀ p, ((constituentLines C.merged).filter (OnLine p)).card ≤ B)
    (hfinal : ∀ l, ρ * Fintype.card F ≤ ((final C l).card : ℝ)) :
    C.Occupancy ρ B := by
  refine ⟨hmultiplicity, ?_, ?_⟩
  · intro l hl
    simpa [final_eq_core_inter C l hl] using hfinal l
  · intro d
    simpa [final_secondConstituent C hV d] using hfinal (constituent C.merged d true)

lemma initiallyRetained_inter_line (l : Line F) :
    linePoints l ∩ initiallyRetained C.merged =
      (linePoints l).filter (fun p => ∀ d, ¬ OnLine p (constituent C.merged d true)) := by
  ext p
  simp [initiallyRetained, initialDeletedLines, Finset.mem_filter]

lemma constituent_multiplicity_le_sampled (p : Point F) :
    ((constituentLines C.merged).filter (OnLine p)).card ≤ sampledMultiplicity C.merged p := by
  have heq : (constituentLines C.merged).filter (OnLine p) =
      (Finset.univ.filter (fun ds : Direction F × Bool =>
        OnLine p (constituent C.merged ds.1 ds.2))).image
          (fun ds => constituent C.merged ds.1 ds.2) := by
    simp only [constituentLines, Finset.filter_image]
  rw [heq]
  exact Finset.card_image_le

theorem candidate_good_initial {c Cbound : ℝ}
    (hgood : CandidateGraphGood C.merged c Cbound) :
    (∀ p, ((constituentLines C.merged).filter (OnLine p)).card ≤
      ⌈Real.log (Fintype.card F : ℝ)⌉₊) ∧
    ∀ l, (1 / 5 : ℝ) * Fintype.card F ≤ ((initial C l).card : ℝ) := by
  refine ⟨?_, initial_card_lower_bound C (1 / 5) (by norm_num) ?_⟩
  · intro p
    exact (constituent_multiplicity_le_sampled C p).trans (hgood.2.2.2.1 p)
  · intro l hl
    have h := hgood.2.2.2.2 l hl
    simpa only [initiallyRetained_inter_line C l] using h

theorem occupancy_of_candidate_good_final {c Cbound ρ : ℝ}
    (hV : C.Valid) (hgood : CandidateGraphGood C.merged c Cbound)
    (hfinal : ∀ l, ρ * Fintype.card F ≤ ((final C l).card : ℝ)) :
    C.Occupancy ρ ⌈Real.log (Fintype.card F : ℝ)⌉₊ :=
  occupancy_of_final C hV ρ _ (candidate_good_initial C hgood).1 hfinal

end
end Balanced.SelectionOccupancy

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_SelectionAffineAdapter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

noncomputable section
open scoped Classical

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

namespace SelectionOccupancy

variable {F} (C : Configuration F)

theorem selection_finalTracked_eq {V : Type*} (line : V → Line F)
    (a : Slot F → V) (hline : ∀ s, line (a s) = (C.choice s).line) (l : Line F) :
    Selection.finalTracked (coordinatePlane F) line (initial C) a l = final C l := by
  ext p
  simp only [Selection.finalTracked, final, Finset.mem_filter]
  constructor
  · rintro ⟨hp, h⟩
    refine ⟨hp, ?_⟩
    intro S hS hne
    rcases Finset.mem_image.mp hS with ⟨s, _, rfl⟩
    simpa only [hline s, coordinatePlane] using (h s (by simpa only [hline s] using hne))
  · rintro ⟨hp, h⟩
    refine ⟨hp, ?_⟩
    intro s hne
    have hmem : (C.choice s).line ∈ C.splitLines :=
      Finset.mem_image.mpr ⟨s, Finset.mem_univ s, rfl⟩
    simpa only [hline s, coordinatePlane] using (h (C.choice s).line hmem
      (by simpa only [hline s] using hne))

end SelectionOccupancy
end
end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateOccupancyBridge
attribute [-instance] _root_.OAI.Balanced.Selection.Process.snapshotPathLaw_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

noncomputable section
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def candidateTrackedSets (M : MergedPairs F) : Line F → Finset (Point F) :=
  SelectionOccupancy.initial (selectedConfiguration M (fun _ => 0))

theorem candidateTrackedSets_eq (M : MergedPairs F) (f : Slot F → F) :
    candidateTrackedSets M = SelectionOccupancy.initial (selectedConfiguration M f) := rfl

theorem candidateSelection_output_line (M : MergedPairs F)
    (J : AvailableCandidate M → Finset (CandidateVertex F))
    (a : Slot F → AvailableCandidate M)
    (ha : Selection.IsIndependentTransversal (candidateSelectionInput M J) a)
    (s : Slot F) :
    candidateLine (a s).val =
      ((selectedConfiguration M (fun t => (a t).val.2)).choice s).line := by
  change ((a s).val.1.1, (a s).val.2) = (s.1, (a s).val.2)
  have hs : (a s).val.1 = s := ha.1 s
  rw [hs]

theorem candidateSelection_finalTracked (M : MergedPairs F)
    (J : AvailableCandidate M → Finset (CandidateVertex F))
    (a : Slot F → AvailableCandidate M)
    (ha : Selection.IsIndependentTransversal (candidateSelectionInput M J) a)
    (l : Line F) :
    Selection.finalTracked (coordinatePlane F) (fun v : AvailableCandidate M =>
      candidateLine v.val) (candidateTrackedSets M) a l =
      SelectionOccupancy.final (selectedConfiguration M (fun s => (a s).val.2)) l := by
  rw [candidateTrackedSets_eq M (fun s => (a s).val.2)]
  exact SelectionOccupancy.selection_finalTracked_eq _ _ a
    (candidateSelection_output_line M J a ha) l

theorem candidateSelection_occupancy_of_no_failure {M : MergedPairs F} {c C ρ : ℝ}
    (hgood : CandidateGraphGood M c C) (hd : DistinctConstituents M)
    (J : AvailableCandidate M → Finset (CandidateVertex F))
    (a : Slot F → AvailableCandidate M)
    (ha : Selection.IsIndependentTransversal (candidateSelectionInput M J) a)
    (hoccup : ∀ l : Line F, ρ * Fintype.card F ≤
      ((Selection.finalTracked (coordinatePlane F)
        (fun v : AvailableCandidate M => candidateLine v.val)
        (candidateTrackedSets M) a l).card : ℝ)) :
    (selectedConfiguration M (fun s => (a s).val.2)).Occupancy
      ρ ⌈Real.log (Fintype.card F : ℝ)⌉₊ := by
  have hv := (candidateSelection_configuration_of_transversal M J a hd ha).1
  apply SelectionOccupancy.occupancy_of_candidate_good_final _ hv hgood
  intro l
  simpa only [candidateSelection_finalTracked M J a ha l] using hoccup l

theorem candidateSelection_occupancy_failure_mass_le {M : MergedPairs F} {c C ρ : ℝ}
    (hgood : CandidateGraphGood M c C) (hd : DistinctConstituents M)
    (J : AvailableCandidate M → Finset (CandidateVertex F))
    (law : Selection.OutputLaw (candidateSelectionInput M J)) :
    (∑ a : Slot F → AvailableCandidate M,
      if ¬ (selectedConfiguration M (fun s => (a s).val.2)).Occupancy
      ρ ⌈Real.log (Fintype.card F : ℝ)⌉₊ then law.weight a else 0) ≤
    Selection.occupancyFailureMass law (coordinatePlane F)
      (fun v : AvailableCandidate M => candidateLine v.val) (candidateTrackedSets M) ρ := by
  rw [Selection.occupancyFailureMass, Finset.sum_filter]
  classical
  have huniv : @Finset.univ (Slot F → AvailableCandidate M)
      (@Pi.instFintype (Slot F) (fun _ => AvailableCandidate M)
        (fun a b => Classical.propDecidable (a = b)) inferInstance (fun _ => inferInstance)) =
      (Finset.univ : Finset (Slot F → AvailableCandidate M)) := by
    ext a
    simp
  rw [huniv]
  apply Finset.sum_le_sum
  intro a _
  by_cases hb : ¬ (selectedConfiguration M (fun s => (a s).val.2)).Occupancy
      ρ ⌈Real.log (Fintype.card F : ℝ)⌉₊
  · rw [ite_eq_left hb]
    by_cases hw : 0 < law.weight a
    · have ha := law.supported a hw
      have hf : ∃ l : Line F,
          ((Selection.finalTracked (coordinatePlane F)
            (fun v : AvailableCandidate M => candidateLine v.val)
            (candidateTrackedSets M) a l).card : ℝ) < ρ * Fintype.card F := by
        by_contra h
        apply hb
        apply candidateSelection_occupancy_of_no_failure hgood hd J a ha
        intro l
        exact le_of_not_gt (fun hl => h ⟨l, hl⟩)
      rw [ite_eq_left hf]
    · have hz : law.weight a = 0 :=
        le_antisymm (le_of_not_gt hw) (law.nonnegative a)
      simp only [hz, ite_self, le_refl]
  · rw [ite_eq_right hb]
    split_ifs
    · exact law.nonnegative a
    · exact le_refl 0

end
end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_ChildAlignment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.TupleAlignment

variable {F : Type*} [Field F]

instance instNonemptyChildOffsets (a : Bool → F) : Nonempty (ChildOffsets a) :=
  ⟨(childFreshEquiv a).symm (fun _ _ => 0)⟩

end Balanced.TupleAlignment

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_TupleExposure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

noncomputable section
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def oldGeneratorIndices (T : FourTuple F) (old : Finset (Direction F)) : Finset (Fin 4) :=
  Finset.univ.filter (fun i => T.generator i ∈ old)

end
end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_FreshWitnessProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.FreshWitnessProbability

open ConditionalRestriction TupleAlignment
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def exposedLaw (D : Finset (Direction F)) (a : MergedPairs F) : PMF (MergedPairs F) :=
  (offsetLaw F).filter {M | ∀ d, d ∈ D → M d = a d}
    ⟨a, by intro d hd; rfl, by simp [offsetLaw]⟩

end
end Balanced.FreshWitnessProbability

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_ExposedOppositeSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.ExposedOppositeSum

open CandidateValidityWitness FreshWitnessProbability
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def freshTuples (D : Finset (Direction F)) : Finset (FourTuple F) :=
  Finset.univ.filter (fun T => Function.Injective T.generator ∧
    ∀ i, T.generator i ∉ D)

def oldOppositeFreshSum (g : Direction F) (D : Finset (Direction F))
    (a : MergedPairs F) : ℝ :=
  ∑ T ∈ freshTuples D, ∑ c : F, ∑ d ∈ D.erase g, ∑ i : Fin 4,
    ((exposedLaw D a).toOuterMeasure {M | SuccessfulOn M T (g,c) ∧
      PairWitness M d (tuplePoint M T i) (tuplePoint M T (i + 2))}).toReal

def oldOppositeFreshCount (g : Direction F) (D : Finset (Direction F))
    (M : MergedPairs F) : ℕ :=
  ∑ T ∈ freshTuples D, ∑ c : F, ∑ d ∈ D.erase g, ∑ i : Fin 4,
    if SuccessfulOn M T (g,c) ∧
      PairWitness M d (tuplePoint M T i) (tuplePoint M T (i + 2)) then 1 else 0

end
end Balanced.ExposedOppositeSum

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_ExposedExternalSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.ExposedExternalSum

noncomputable section
open scoped Classical BigOperators
attribute [local instance] Classical.propDecidable
open CandidateValidityWitness FreshWitnessProbability ExposedOppositeSum
open ExposedExternalFresh

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def externalEvent (T : FourTuple F) (S : Line F) (d e : Direction F)
    (i j : Fin 4) : Set (MergedPairs F) := {M | SuccessfulOn M T S ∧
  ∃ x, OnLine x S ∧ PairWitness M d x (tuplePoint M T i) ∧
    PairWitness M e x (tuplePoint M T j)}

end
end Balanced.ExposedExternalSum

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_ExternalWitnessModel
attribute [-instance] _root_.OAI.Balanced.PatternModel.isProbabilityMeasure_measure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.ExternalAssembly

noncomputable section
open scoped Classical BigOperators
open MeasureTheory CandidateValidityWitness
attribute [local instance] Classical.propDecidable

universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]

def support (w : WitnessKey F) : Finset (Direction F) :=
  generatorSet w.1.1 ∪ {w.2.1, w.2.2}

omit [Fintype F] in

theorem witnessEvent_congr (g : Direction F) (w : WitnessKey F)
    (M N : MergedPairs F) (h : ∀ d ∈ support w, M d = N d) :
    M ∈ witnessEvent g w ↔ N ∈ witnessEvent g w := by
  have hp := TupleAlignment.tuplePoint_eq_of_eq_on_generators w.1.1
    (fun d hd => h d (Finset.mem_union_left _ hd))
  have hd := h w.2.1 (Finset.mem_union_right _ (by simp))
  have he := h w.2.2 (Finset.mem_union_right _ (by simp))
  simp only [witnessEvent, Set.mem_ofPred_eq, SuccessfulOn, targetLine,
    designated, PairWitness, constituent, hp, hd, he]

attribute [local instance] OAI.Balanced.ExternalAssembly.externalModelMeasurableSpace
abbrev patternModel (g : Direction F) : PatternModel.{u} where
  Color := Direction F
  Value := fun _ => Bool → F
  law := fun _ => (PMF.uniformOfFintype (Bool → F)).toMeasure
  Label := WitnessKey F
  support := support
  event := witnessEvent g
  eventMeasurable := fun _ => (Set.toFinite _).measurableSet
  dependsOn := witnessEvent_congr g

end
end Balanced.ExternalAssembly

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_ExternalFreshGeneratorBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.ExternalAssembly

noncomputable section
open scoped Classical BigOperators
open MeasureTheory CandidateValidityWitness CandidateExposure
open ExposedOppositeSum ExposedExternalSum
open ExposedExternalFresh FreshWitnessProbability
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def freshGeneratorLabels (D E : Finset (Direction F)) : Finset (WitnessKey F) :=
  (freshTuples D ×ˢ Finset.univ) ×ˢ (D ×ˢ E)

end
end Balanced.ExternalAssembly

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_FreshTupleWitness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.FreshTupleWitness

noncomputable section
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def pairPrescription (d : Direction F) (p r : Point F) (σ : Bool) : Bool → F :=
  fun b => if b = σ then lineEval d p else lineEval d r

end
end Balanced.FreshTupleWitness

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_FreshWitnessConditional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.FreshTupleWitness

noncomputable section
open scoped Classical BigOperators
open TupleAlignment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def fiberSuccessProbability (G : MergedPairs F → Prop)
    [Nonempty {M : MergedPairs F // G M}] (g : Direction F) (T : FourTuple F) : ℝ :=
  ((PMF.uniformOfFintype {M : MergedPairs F // G M}).toOuterMeasure
    {M | (∃ c, ∀ k, OnLine (tuplePoint M.1 T k) (g,c)) ∧
      Function.Injective (tuplePoint M.1 T)}).toReal

end
end Balanced.FreshTupleWitness

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_FreshExternalWitness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.FreshExternalWitness

noncomputable section
open scoped Classical BigOperators
open FreshTupleWitness TupleAlignment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def targetPoint (g : Direction F) (T : FourTuple F) (z : F)
    (M : MergedPairs F) : Point F :=
  ((linePointsEquiv (g, lineEval g (tuplePoint M T 0))).symm z).1

def orientedEvent (g : Direction F) (T : FourTuple F) (d e : Direction F)
    (i j : Fin 4) (σ τ : Bool) (z : F) (M : MergedPairs F) : Prop :=
  ((((∃ c, ∀ k, OnLine (tuplePoint M T k) (g,c)) ∧
      Function.Injective (tuplePoint M T)) ∧
    (OnLine (targetPoint g T z M) (constituent M d σ) ∧
      OnLine (tuplePoint M T i) (constituent M d (!σ)))) ∧
    (OnLine (targetPoint g T z M) (constituent M e τ) ∧
      OnLine (tuplePoint M T j) (constituent M e (!τ))))

abbrev fixedValues (D : Finset (Direction F)) (a : MergedPairs F)
    (M : MergedPairs F) : Prop := ∀ d, d ∈ D → M d = a d

end
end Balanced.FreshExternalWitness

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_FreshExternalCounting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.FreshExternalWitness

noncomputable section
open scoped Classical BigOperators
open FreshTupleWitness TupleAlignment CandidateExposure

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def freshPairs (D : Finset (Direction F)) (T : FourTuple F) :
    Finset (Direction F × Direction F) :=
  Finset.univ.filter (fun de => de.1 ≠ de.2 ∧ de.1 ∉ D ∧ de.2 ∉ D ∧
    (∀ k, T.generator k ≠ de.1) ∧ (∀ k, T.generator k ≠ de.2))

omit [Field F] in
@[simp] theorem mem_freshPairs (D : Finset (Direction F)) (T : FourTuple F)
    (de : Direction F × Direction F) :
    de ∈ freshPairs D T ↔ de.1 ≠ de.2 ∧ de.1 ∉ D ∧ de.2 ∉ D ∧
      (∀ k, T.generator k ≠ de.1) ∧ (∀ k, T.generator k ≠ de.2) := by
  simp only [freshPairs, Finset.mem_filter, Finset.mem_univ, true_and]

def probabilitySum (g : Direction F) (D : Finset (Direction F))
    (a : MergedPairs F) (i j : Fin 4) : ℝ :=
  ∑ r : RootPrescription g, ∑ de ∈ freshPairs D r.tuple,
    ∑ σ : Bool, ∑ τ : Bool, ∑ z : F,
      conditionalProbability D a {M | orientedEvent g r.tuple de.1 de.2 i j σ τ z M}

end
end Balanced.FreshExternalWitness

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_FreshExternalCountBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.FreshExternalWitness

noncomputable section
open scoped Classical BigOperators
open TupleAlignment CandidateExposure CandidateValidityWitness MeasureTheory

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def sourceEvent (g : Direction F) (T : FourTuple F) (i j : Fin 4)
    (de : Direction F × Direction F) (M : MergedPairs F) : Prop :=
  ∃ (c : F) (x : Point F), SuccessfulOn M T (g,c) ∧
    OnLine x (g,c) ∧ x ∉ designated M ⟨(g,c), T⟩ ∧ i ≠ j ∧
    de.1 ≠ g ∧ de.2 ≠ g ∧
    PairWitness M de.1 x (tuplePoint M T i) ∧
    PairWitness M de.2 x (tuplePoint M T j)

def sourceProbabilitySum (g : Direction F) (D : Finset (Direction F))
    (a : MergedPairs F) : ℝ :=
  ∑ i : Fin 4, ∑ j : Fin 4, ∑ r : RootPrescription g,
    ∑ de ∈ freshPairs D r.tuple,
      conditionalProbability D a {M | sourceEvent g r.tuple i j de M}

def sourceWitnessCount (g : Direction F) (D : Finset (Direction F))
    (M : MergedPairs F) : ℕ :=
  ∑ i : Fin 4, ∑ j : Fin 4, ∑ r : RootPrescription g,
    ((freshPairs D r.tuple).filter (fun de => sourceEvent g r.tuple i j de M)).card

end
end Balanced.FreshExternalWitness

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_OppositeCases
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.OppositeAssembly

noncomputable section
open scoped Classical BigOperators
open CandidateExposure CandidateValidityWitness PartialAlignment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

abbrev Label (F : Type*) := (FourTuple F × Fin 4) × Direction F

def witnesses (g : Direction F) (M : MergedPairs F) : Finset (Label F) :=
  (((eligibleTuples g).product Finset.univ).product Finset.univ).filter
    (fun w => M ∈ successfulInDirection w.1.1 g ∧ w.2 ≠ g ∧
      w.2 ∉ generatorSet w.1.1 ∧
      PairWitness M w.2 (tuplePoint M w.1.1 w.1.2)
        (tuplePoint M w.1.1 (w.1.2 + 2)))

theorem mem_witnesses (g : Direction F) (M : MergedPairs F)
    (T : FourTuple F) (i : Fin 4) (d : Direction F) :
    ((T,i),d) ∈ witnesses g M ↔
      T ∈ eligibleTuples g ∧ M ∈ successfulInDirection T g ∧ d ≠ g ∧
      d ∉ generatorSet T ∧ PairWitness M d (tuplePoint M T i)
        (tuplePoint M T (i+2)) := by
  simp [witnesses]

def freshWitnesses (g : Direction F) (D : Finset (Direction F))
    (M : MergedPairs F) : Finset (Label F) :=
  (witnesses g M).filter (fun w => w.2 ∉ D)

def oldFreshWitnesses (g : Direction F) (D : Finset (Direction F))
    (M : MergedPairs F) : Finset (Label F) :=
  (witnesses g M).filter (fun w => w.2 ∈ D ∧ ∀ i, w.1.1.generator i ∉ D)

end
end Balanced.OppositeAssembly

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_OppositeFreshMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.OppositeAssembly

noncomputable section
open scoped Classical BigOperators
open CandidateExposure CandidateValidityWitness MeasureTheory

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def freshTests (g : Direction F) (D : Finset (Direction F)) : Finset (Label F) :=
  (((eligibleTuples g).product Finset.univ).product Finset.univ).filter
    (fun w => w.2 ∉ D ∧ w.2 ∉ generatorSet w.1.1)

def freshEvent (g : Direction F) (w : Label F) : Set (MergedPairs F) :=
  {M | M ∈ successfulInDirection w.1.1 g ∧
    PairWitness M w.2 (tuplePoint M w.1.1 w.1.2)
      (tuplePoint M w.1.1 (w.1.2+2))}

end
end Balanced.OppositeAssembly

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_OppositeAssembly
attribute [-instance] _root_.OAI.Balanced.PatternModel.isProbabilityMeasure_measure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.OppositeAssembly

noncomputable section
open scoped Classical BigOperators
open CandidateExposure CandidateValidityWitness MeasureTheory ConditionalRestriction

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem witness_mem_iff_of_agree (g : Direction F) (w : Label F)
    (M N : MergedPairs F)
    (h : ∀ d ∈ insert w.2 (generatorSet w.1.1), M d = N d) :
    w ∈ witnesses g M ↔ w ∈ witnesses g N := by
  rcases w with ⟨⟨T,i⟩,d⟩
  have hd : M d = N d := h d (Finset.mem_insert_self _ _)
  have hp : tuplePoint M T = tuplePoint N T := by
    funext j
    have hj := h (T.generator j) (Finset.mem_insert_of_mem
      (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩))
    have hn := h (T.generator (j+1)) (Finset.mem_insert_of_mem
      (Finset.mem_image.mpr ⟨j+1,Finset.mem_univ _,rfl⟩))
    simp only [tuplePoint,constituent,hj,hn]
  simp only [mem_witnesses, successfulInDirection, alignedInDirection,
    Set.mem_ofPred_eq, PairWitness, hp, constituent, hd]

attribute [local instance] OAI.Balanced.OppositeAssembly.instMeasurableSpace_solutions_1
def witnessPatternModel (g : Direction F) : PatternModel where
  Color := Direction F
  Value := fun _ => Bool → F
  law := fun _ => (PMF.uniformOfFintype (Bool → F)).toMeasure
  Label := Label F
  support w := insert w.2 (generatorSet w.1.1)
  event w := {M | w ∈ witnesses g M}
  eventMeasurable _ := (Set.to_countable _).measurableSet
  dependsOn w M N h := witness_mem_iff_of_agree g w M N h

end
end Balanced.OppositeAssembly

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionPushforward2
attribute [-instance] _root_.OAI.Balanced.Selection.Process.snapshotPathLaw_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.FinitePushforward

open Finset

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]

theorem exists_supported_decoder {I V L : Type*} [Nonempty V]
    (allowed : I → V → Prop) (label : I → V → L)
    (hinj : ∀ i, Set.InjOn (label i) {v | allowed i v}) :
    ∃ decode : I → L → V, ∀ i v, allowed i v → decode i (label i v) = v := by
  classical
  let decode : I → L → V := fun i l =>
    if h : ∃ v, allowed i v ∧ label i v = l then Classical.choose h
    else Classical.choice (inferInstance : Nonempty V)
  refine ⟨decode, ?_⟩
  intro i v hv
  have hex : ∃ u, allowed i u ∧ label i u = label i v := ⟨v, hv, rfl⟩
  dsimp [decode]
  rw [dite_eq_left hex]
  exact hinj i (Classical.choose_spec hex).1 hv (Classical.choose_spec hex).2

theorem cylinderMass_pushWeight_le {I V L : Type*}
    [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V] [Nonempty V]
    [Fintype L] [DecidableEq L]
    (w : (I → V) → ℝ) (hw : ∀ t, 0 ≤ w t)
    (allowed : I → V → Prop) (label : I → V → L)
    (hsupport : ∀ t, 0 < w t → ∀ i, allowed i (t i))
    (hinj : ∀ i, Set.InjOn (label i) {v | allowed i v})
    (b : Finset I → ℝ)
    (hbound : ∀ J a, cylinderMass w J a ≤ b J)
    (J : Finset I) (prescribed : I → L) :
    cylinderMass (pushWeight (mapChoices label) w) J prescribed ≤ b J := by
  classical
  obtain ⟨decode, hdecode⟩ := exists_supported_decoder allowed label hinj
  let a : I → V := fun i => decode i (prescribed i)
  have himp : ∀ t, 0 < w t →
      (∀ i ∈ J, label i (t i) = prescribed i) → ∀ i ∈ J, t i = a i := by
    intro t ht hp i hi
    dsimp [a]
    rw [← hp i hi]
    exact (hdecode i (t i) (hsupport t ht i)).symm
  unfold cylinderMass
  rw [eventMass_pushWeight]
  have hpoint : ∀ t,
      (if ∀ i ∈ J, mapChoices label t i = prescribed i then w t else 0) ≤
        (if ∀ i ∈ J, t i = a i then w t else 0) := by
    intro t
    by_cases hz : w t = 0
    · simp [hz]
    have ht : 0 < w t := lt_of_le_of_ne (hw t) (Ne.symm hz)
    by_cases hp : ∀ i ∈ J, mapChoices label t i = prescribed i
    · have ha : ∀ i ∈ J, t i = a i := himp t ht hp
      rw [ite_eq_left hp, ite_eq_left ha]
    · simp only [ite_eq_right hp]
      split_ifs
      · exact hw t
      · exact le_rfl
  exact (sum_le_sum fun t _ => hpoint t).trans (hbound J a)

end Balanced.FinitePushforward

namespace Balanced.Selection

noncomputable section
attribute [local instance] Classical.propDecidable

variable {I V L : Type*} [Fintype I] [Fintype V] [Fintype L]
    {G : Input I V}

theorem labelWeight_cylinder_le [Nonempty V] (law : OutputLaw G) (label : I → V → L)
    (hinj : ∀ i, Set.InjOn (label i) {v | G.slot v = i})
    (b : Finset I → ℝ)
    (hbound : ∀ J a, cylinderMass law J a ≤ b J)
    (J : Finset I) (prescribed : I → L) :
    FinitePushforward.cylinderMass (law.labelWeight label) J prescribed ≤ b J := by
  apply FinitePushforward.cylinderMass_pushWeight_le law.weight law.nonnegative
    (fun i v => G.slot v = i) label
    (fun t ht => (law.supported t ht).1) hinj b
  intro J a
  simpa only [cylinderMass, FinitePushforward.cylinderMass, Finset.sum_filter] using hbound J a

end
end Balanced.Selection

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_SelectionCandidateLaw
attribute [-instance] _root_.OAI.Balanced.Selection.Process.snapshotPathLaw_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [eqF : DecidableEq F]

theorem candidateSelection_label_injective (M : MergedPairs F)
    (J : AvailableCandidate M → Finset (CandidateVertex F)) (s : Slot F) :
    Set.InjOn (fun v : AvailableCandidate M => v.val.2)
      {v | (candidateSelectionInput M J).slot v = s} := by
  intro v hv w hw heq
  apply Subtype.ext
  exact Prod.ext (hv.trans hw.symm) heq

theorem candidateSelection_nonempty (M : MergedPairs F) {c C : ℝ}
    (hc : 0 < c) (hgood : CandidateGraphGood M c C) :
    Nonempty (AvailableCandidate M) := by
  have hq : 0 < (Fintype.card F : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hslot : 0 < (candidateSlot M (none, false)).card := by
    exact_mod_cast (mul_pos hc hq).trans_le ((hgood.1 (none, false)).1)
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hslot
  exact ⟨⟨v, (Finset.mem_filter.mp hv).1⟩⟩

local instance instDecidableEqSlot : DecidableEq (Slot F) := Classical.decEq _

theorem candidateSelection_label_event (M : MergedPairs F)
    (J : AvailableCandidate M → Finset (CandidateVertex F))
    (law : Selection.OutputLaw (candidateSelectionInput M J))
    (P : (Slot F → F) → Prop) :
    (∑ f, if P f then law.labelWeight (fun _ v => v.val.2) f else 0) =
      ∑ a, if P (fun i => (a i).val.2) then law.weight a else 0 := by
  exact FinitePushforward.eventMass_pushWeight
    (FinitePushforward.mapChoices (fun (_ : Slot F) (v : AvailableCandidate M) => v.val.2))
    law.weight P

theorem candidateSelection_label_cylinder (M : MergedPairs F) {c C K : ℝ}
    (hc : 0 < c) (hgood : CandidateGraphGood M c C)
    (J : AvailableCandidate M → Finset (CandidateVertex F))
    (law : Selection.OutputLaw (candidateSelectionInput M J))
    (hbound : ∀ (S : Finset (Slot F)) (a : Slot F → AvailableCandidate M),
      Selection.cylinderMass law S a ≤ (K / (Fintype.card F : ℝ)) ^ S.card)
    (S : Finset (Slot F)) (f : Slot F → F) :
    FinitePushforward.cylinderMass (law.labelWeight (fun _ v => v.val.2)) S f ≤
      (K / (Fintype.card F : ℝ)) ^ S.card := by
  cases Subsingleton.elim eqF (Classical.decEq F)
  let := candidateSelection_nonempty M hc hgood
  exact Selection.labelWeight_cylinder_le law (fun _ v => v.val.2)
    (candidateSelection_label_injective M J) _ hbound S f

end
end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Deletion_Deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped NNReal

noncomputable section

namespace Balanced
open scoped _root_.Balanced

universe u

variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]

def deletionMultiplicity (D : Finset (Line F)) (x : Point F) : ℕ :=
  (D.filter fun l => OnLine x l).card

def empiricalMultiplicityMass (D : Finset (Line F)) (n : ℕ) : ℝ :=
  ((Finset.univ.filter fun x : Point F => deletionMultiplicity D x = n).card : ℝ) /
    (Fintype.card F : ℝ) ^ 2

noncomputable def deletionMultiplicityTV (k : ℕ) (D : Finset (Line F)) : ℝ :=
  (1 / 2 : ℝ) * ∑' n : ℕ, |empiricalMultiplicityMass D n - deletionPoissonMass k n|

noncomputable def exceptionalOccupancyLines (k : ℕ) (lam : ℝ)
    (D : Finset (Line F)) : Finset (Line F) := by
  classical
  exact Finset.univ.filter fun l => l ∉ D ∧
    lam ≤ |(((linePoints l ∩ uncoveredBy D).card : ℝ) / (Fintype.card F : ℝ)) -
      Real.exp (-(k : ℝ))|

def UniformDeletionVanishing (k : ℕ) (K : ℝ)
    (E : ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      DeletionSet F k → Prop) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
    ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      N ≤ Fintype.card F → k ≤ Fintype.card F →
      ∀ Q : PMF (DeletionSet F k), DeletionDominated k K Q →
        deletionEventProbability Q (E F) < ε

def RobustDeletionResult : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ K : ℝ, 0 ≤ K →
    (∀ τ : ℝ, 0 < τ → UniformDeletionVanishing.{u} k K
      (fun _ _ _ _ D => τ ≤ deletionMultiplicityTV k D.val)) ∧
    (∀ lam η : ℝ, 0 < lam → 0 < η → UniformDeletionVanishing.{u} k K
      (fun F _ _ _ D => η * (Fintype.card F : ℝ) ≤
        ((exceptionalOccupancyLines k lam D.val).card : ℝ))) ∧
    (∀ δ : ℝ, 0 < δ → UniformDeletionVanishing.{u} k K
      (fun _ _ _ _ D => BadCoreCover δ D.val))

end Balanced

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Deletion_SelectedDeletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter
open scoped Topology
attribute [local instance] Classical.propDecidable

namespace Balanced
open scoped _root_.Balanced
namespace SelectedDeletion

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

abbrev Output := Slot F → F

abbrev Kernel := MergedPairs F → Output F → ℝ

variable {F}

def configuration (M : MergedPairs F) (s : Output F) : Configuration F :=
  ⟨M, fun i => retainedChoice M (i.1, s i)⟩

def InitialGood (M : MergedPairs F) (c C : ℝ) : Prop :=
  CandidateGraphGood M c C ∧ DistinctConstituents M

def IsExperiment (κ : Kernel F) (c C : ℝ) : Prop :=
  (∀ M s, 0 ≤ κ M s) ∧
  (∀ M, ∑ s, κ M s ≤ 1) ∧
  (∀ M, ¬ InitialGood M c C → ∀ s, κ M s = 0) ∧
  (∀ M s, 0 < κ M s →
    (configuration M s).Valid ∧ (configuration M s).Compatible)

def fixedSuccessMass (κ : Kernel F) (M : MergedPairs F) : ℝ :=
  ∑ s, κ M s

def fixedCylinderMass (κ : Kernel F) (M : MergedPairs F)
    (J : Finset (Slot F)) (prescribed : Output F) : ℝ :=
  ∑ s, if ∀ i ∈ J, s i = prescribed i then κ M s else 0

def jointMass (κ : Kernel F) (E : MergedPairs F → Output F → Prop) : ℝ :=
  ∑ M, ((offsetLaw F) M).toReal * ∑ s, if E M s then κ M s else 0

def successMass (κ : Kernel F) : ℝ := jointMass κ (fun _ _ => True)

def deletionJointMass (κ : Kernel F) (D : DeletionSet F 3) : ℝ :=
  jointMass κ (fun M s => (configuration M s).deletedLines = D.val)

def RealizesConditionalLaw (κ : Kernel F) (Q : PMF (DeletionSet F 3)) : Prop :=
  ∀ D, (Q D).toReal = deletionJointMass κ D / successMass κ

def occupancyFailureMass (κ : Kernel F) (ρ : ℝ) : ℝ :=
  jointMass κ (fun M s =>
    ¬ (configuration M s).Occupancy ρ ⌈Real.log (Fintype.card F : ℝ)⌉₊)

end SelectedDeletion

universe u

end Balanced

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Deletion_SelectedDeletionKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable

namespace Balanced.SelectedDeletion

open Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

structure FixedLaw (M : MergedPairs F) (K ρ ε : ℝ) where
  weight : Output F → ℝ
  nonnegative : ∀ s, 0 ≤ weight s
  mass_le_one : (∑ s, weight s) ≤ 1
  supported : ∀ s, 0 < weight s →
    (configuration M s).Valid ∧ (configuration M s).Compatible
  success_lower : 1 - ε ≤ ∑ s, weight s
  cylinder_le : ∀ (J : Finset (Slot F)) (prescribed : Output F),
    (∑ s, if ∀ i ∈ J, s i = prescribed i then weight s else 0) ≤
      (K / (Fintype.card F : ℝ)) ^ J.card
  occupancy_le :
    (∑ s, if ¬ (configuration M s).Occupancy ρ ⌈Real.log (Fintype.card F : ℝ)⌉₊
      then weight s else 0) ≤ ε

theorem occupancy_mono {M : MergedPairs F} {s : Output F} {ρ ρ' : ℝ} {B : ℕ}
    (hρ : ρ' ≤ ρ) (h : (configuration M s).Occupancy ρ B) :
    (configuration M s).Occupancy ρ' B := by
  refine ⟨h.1, ?_, ?_⟩
  · intro l hl
    exact (mul_le_mul_of_nonneg_right hρ (Nat.cast_nonneg _)).trans (h.2.1 l hl)
  · intro d
    exact (mul_le_mul_of_nonneg_right hρ (Nat.cast_nonneg _)).trans (h.2.2 d)

def FixedLaw.relax {M : MergedPairs F} {K K' ρ ρ' ε : ℝ}
    (law : FixedLaw M K ρ ε) (hK : 0 ≤ K) (hKK : K ≤ K') (hρ : ρ' ≤ ρ) :
    FixedLaw M K' ρ' ε where
  weight := law.weight
  nonnegative := law.nonnegative
  mass_le_one := law.mass_le_one
  supported := law.supported
  success_lower := law.success_lower
  cylinder_le := by
    intro J prescribed
    exact (law.cylinder_le J prescribed).trans
      (pow_le_pow_left₀ (div_nonneg hK (Nat.cast_nonneg _))
        (div_le_div_of_nonneg_right hKK (Nat.cast_nonneg _)) J.card)
  occupancy_le := by
    apply le_trans _ law.occupancy_le
    apply sum_le_sum
    intro s _
    by_cases hs : ¬ (configuration M s).Occupancy ρ' ⌈Real.log (Fintype.card F : ℝ)⌉₊
    · have ht : ¬ (configuration M s).Occupancy ρ ⌈Real.log (Fintype.card F : ℝ)⌉₊ :=
        fun h => hs (occupancy_mono hρ h)
      simp [hs, ht]
    · simp only [hs, ite_false]
      split_ifs
      · exact le_rfl
      · exact law.nonnegative s

def glue {c C K ρ ε : ℝ}
    (laws : ∀ M : MergedPairs F, InitialGood M c C → FixedLaw M K ρ ε) : Kernel F :=
  fun M s => if h : InitialGood M c C then (laws M h).weight s else 0

end Balanced.SelectedDeletion

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_SelectedCandidateFixedLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.SelectedDeletion

noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [eqF : DecidableEq F]
local instance instDecidableEqSlot : DecidableEq (Slot F) := Classical.decEq _

end
end Balanced.SelectedDeletion

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Construction_ConstructionRepresentationLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace Balanced
open scoped _root_.Balanced

universe u

def DeterministicReduction : Prop :=
  ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
    (C : Configuration F) (ρ : ℝ) (B : ℕ),
    4 ≤ Fintype.card F → 0 < ρ → ρ < 1 →
    C.Valid → C.Compatible → C.Occupancy ρ B →
    C.CoreConcentration ρ → C.LocalCondition →
    2 * (1 + (B : ℝ)) < ρ * Fintype.card F →
    ∃ H : PartiteHypergraph (Fintype.card F + 1) (Fintype.card F + 1),
      H.Intersecting ∧ H.Nonisolated ∧ H.HasCoverNumber (Fintype.card F + 1) ∧
      Nonempty (ConfigurationRealization C H)

end Balanced

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Construction_ExternalWitnessPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.ExternalAssembly

noncomputable section
open scoped Classical BigOperators
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def swapKey (w : WitnessKey F) : WitnessKey F :=
  ((w.1.1, (w.1.2.2, w.1.2.1)), (w.2.2, w.2.1))

omit [Field F] [Fintype F] [DecidableEq F] in
@[simp] theorem swapKey_swapKey (w : WitnessKey F) : swapKey (swapKey w) = w := by
  rcases w with ⟨⟨T, i, j⟩, d, e⟩
  rfl

omit [Fintype F] in
@[simp] theorem witnessEvent_swapKey (g : Direction F) (w : WitnessKey F)
    (M : MergedPairs F) : M ∈ witnessEvent g (swapKey w) ↔ M ∈ witnessEvent g w := by
  simp only [witnessEvent, swapKey, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hs, hij, hde, he, hd, heT, hdT, x, hx, hex, hej, hdi⟩
    exact ⟨hs, hij.symm, hde.symm, hd, he, hdT, heT, x, hx, hex, hdi, hej⟩
  · rintro ⟨hs, hij, hde, hd, he, hdT, heT, x, hx, hex, hdi, hej⟩
    exact ⟨hs, hij.symm, hde.symm, he, hd, heT, hdT, x, hx, hex, hej, hdi⟩

@[simp] theorem swapKey_mem_witnesses (g : Direction F) (M : MergedPairs F)
    (w : WitnessKey F) : swapKey w ∈ witnesses g M ↔ w ∈ witnesses g M := by
  simp only [mem_witnesses, witnessEvent_swapKey]

open MeasureTheory

end
end Balanced.ExternalAssembly

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Deletion_DeletionCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.DeletionCoordinates

open Finset

variable {I A : Type*} [Fintype I] [Fintype A] [DecidableEq I] [DecidableEq A]

@[simp] theorem assemble_fiber (S : Finset (I × A)) : assemble (fiber S) = S := by
  ext l
  simp

end Balanced.DeletionCoordinates

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Deletion_DeletionCountingExposure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.DeletionCountingExposure

noncomputable section
open scoped BigOperators
open CountingExposurePosterior InjectionExposureLaw
attribute [local instance] Classical.propDecidable

variable {G ι α : Type*} [Fintype G] [Fintype ι] [Fintype α]
  [DecidableEq G] [DecidableEq ι] [DecidableEq α]

def observation (P : Finset (G × ι))
    (ω : Experiment (G := G) (ι := ι) (α := α)) : P → (G × ι) × α :=
  fun j => (ω.1 j, ω.2 (ω.1 j).1 (ω.1 j).2)

def exposedLines (P : Finset (G × ι))
    (ω : Experiment (G := G) (ι := ι) (α := α)) : Finset (G × α) :=
  P.image (nextLine ω)

section Affine
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {k : ℕ}

def pastUncovered (C : Finset (Line F)) (P : Finset (Direction F × Fin k))
    (ω : Experiment (G := Direction F) (ι := Fin k) (α := F)) : Finset (Point F) :=
  uncoveredBy (exposedLines P ω ∪ C)

end Affine
end
end Balanced.DeletionCountingExposure

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Deletion_GeometricDeletionCounting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace Balanced
open scoped _root_.Balanced
namespace GeometricDeletionCounting

variable {F : Type*} [Fintype F] [DecidableEq F]

def offsetsAt (D : Finset (Line F)) (d : Direction F) : Finset F :=
  Finset.univ.filter (fun a => (d, a) ∈ D)

@[simp] theorem mem_offsetsAt (D : Finset (Line F)) (d : Direction F) (a : F) :
    a ∈ offsetsAt D d ↔ (d, a) ∈ D := by
  simp [offsetsAt]

def assemble (S : Direction F → Finset F) : Finset (Line F) :=
  Finset.univ.biUnion (fun d => (S d).image (fun a => (d, a)))

@[simp] theorem mem_assemble (S : Direction F → Finset F) (d : Direction F) (a : F) :
    (d, a) ∈ assemble S ↔ a ∈ S d := by
  simp [assemble]

@[simp] theorem offsetsAt_assemble (S : Direction F → Finset F) (d : Direction F) :
    offsetsAt (assemble S) d = S d := by
  ext a
  simp

@[simp] theorem assemble_offsetsAt (D : Finset (Line F)) :
    assemble (offsetsAt D) = D := by
  ext l
  obtain ⟨d, a⟩ := l
  simp

theorem card_offsetsAt (D : Finset (Line F)) (d : Direction F) :
    (offsetsAt D d).card = (D.filter (fun l => l.1 = d)).card := by
  apply Finset.card_bij (fun a _ => (d, a))
  · intro a ha
    simpa using ha
  · intro a _ b _ hab
    exact (Prod.mk.inj hab).2
  · intro l hl
    obtain ⟨hlD, hld⟩ := Finset.mem_filter.mp hl
    refine ⟨l.2, ?_, ?_⟩
    · have heq : (d, l.2) = l := Prod.ext hld.symm rfl
      simpa only [mem_offsetsAt, heq] using hlD
    · exact Prod.ext hld.symm rfl

variable [Field F]

def deletionEquivFamilies (k : ℕ) :
    DeletionSet F k ≃ (Direction F → {S : Finset F // S.card = k}) where
  toFun D d := ⟨offsetsAt D.val d, by rw [card_offsetsAt]; exact D.property d⟩
  invFun S := ⟨assemble (fun d => (S d).val), by
    intro d
    rw [← card_offsetsAt, offsetsAt_assemble]
    exact (S d).property⟩
  left_inv D := by
    apply Subtype.ext
    exact assemble_offsetsAt D.val
  right_inv S := by
    funext d
    apply Subtype.ext
    exact offsetsAt_assemble (fun d => (S d).val) d

end GeometricDeletionCounting
end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Deletion_SelectedDeletionCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace Balanced.SelectedDeletionCoordinates

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

abbrev SingleOffsets (F : Type*) := Direction F → F
abbrev SplitOffsets (F : Type*) := Slot F → F

def offsetPairEquiv : (SingleOffsets F × SingleOffsets F) ≃ MergedPairs F where
  toFun M d b := if b then M.2 d else M.1 d
  invFun M := (fun d => M d false, fun d => M d true)
  left_inv M := by rfl
  right_inv M := by funext d b; cases b <;> rfl

def roles (ω : SingleOffsets F × SplitOffsets F) (d : Direction F) : Fin 3 → F :=
  ![ω.1 d, ω.2 (d, false), ω.2 (d, true)]

end Balanced.SelectedDeletionCoordinates

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_Stability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced

universe u

variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]

def PrimeStability : Prop :=
  ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
    Nat.Prime (Fintype.card F) →
    ∀ ζ : ℝ, 0 < ζ →
      max (100 : ℝ) (4 / ζ) ≤ (Fintype.card F : ℝ) →
      ∀ C : Finset (Line F), C.card ≤ Fintype.card F →
        (uncoveredPoints C).card < stabilityDensity ζ * (Fintype.card F : ℝ) ^ 2 →
        ∃ P : ProjectivePoint F,
          (1 - ζ) * (Fintype.card F : ℝ) ≤ (pencilSize C P : ℝ)

def NearCoverFailure (δ : ℝ) (D : Finset (Line F)) : Prop :=
  ∃ C : Finset (Line F), Disjoint C D ∧ C.card ≤ Fintype.card F ∧
    CoversPoints C (uncoveredPoints D) ∧
    δ * (Fintype.card F : ℝ) ^ 2 ≤ ((uncoveredPoints C).card : ℝ)

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Deletion_SelectedDeletionPMF
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Balanced.SelectedDeletion

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {κ : Kernel F} {c C : ℝ}

theorem jointMass_nonneg (hnonneg : ∀ M s, 0 ≤ κ M s)
    (E : MergedPairs F → Output F → Prop) : 0 ≤ jointMass κ E := by
  classical
  apply Finset.sum_nonneg
  intro M _
  apply mul_nonneg ENNReal.toReal_nonneg
  apply Finset.sum_nonneg
  intro s _
  split_ifs
  · exact hnonneg M s
  · exact le_rfl

theorem deletionJointMass_nonneg (hnonneg : ∀ M s, 0 ≤ κ M s)
    (D : DeletionSet F 3) : 0 ≤ deletionJointMass κ D :=
  jointMass_nonneg hnonneg _

theorem sum_deletionIndicator (hκ : IsExperiment κ c C)
    (M : MergedPairs F) (s : Output F) :
    (∑ D : DeletionSet F 3,
      if (configuration M s).deletedLines = D.val then κ M s else 0) = κ M s := by
  classical
  by_cases hz : κ M s = 0
  · simp [hz]
  have hpos : 0 < κ M s := lt_of_le_of_ne (hκ.1 M s) (Ne.symm hz)
  have hvalid := hκ.2.2.2 M s hpos
  let D₀ : DeletionSet F 3 :=
    ⟨(configuration M s).deletedLines,
      (configuration M s).deletedLines_isDeletionSet hvalid.1 hvalid.2⟩
  have heq : ∀ D : DeletionSet F 3,
      (configuration M s).deletedLines = D.val ↔ D = D₀ := by
    intro D
    constructor
    · intro h
      exact Subtype.ext h.symm
    · intro h
      subst D
      rfl
  simp_rw [heq]
  simp

theorem sum_deletionJointMass (hκ : IsExperiment κ c C) :
    ∑ D : DeletionSet F 3, deletionJointMass κ D = successMass κ := by
  classical
  simp only [deletionJointMass, jointMass, successMass, ite_true]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro M _
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  convert sum_deletionIndicator hκ M s using 1
  all_goals try with_reducible_and_instances rfl
  all_goals try (rw [if_pos trivial])
  apply Finset.sum_congr rfl
  intro D _
  by_cases h : (configuration M s).deletedLines = D.val <;> simp [h]

theorem sum_normalizedDeletionJointMass (hκ : IsExperiment κ c C)
    (hsuccess : 0 < successMass κ) :
    (∑ D : DeletionSet F 3, deletionJointMass κ D / successMass κ) = 1 := by
  rw [← Finset.sum_div, sum_deletionJointMass hκ]
  exact div_self (ne_of_gt hsuccess)

def conditionalDeletionLaw (hκ : IsExperiment κ c C)
    (hsuccess : 0 < successMass κ) : PMF (DeletionSet F 3) :=
  PMF.ofFintype (fun D => ENNReal.ofReal (deletionJointMass κ D / successMass κ)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg
      (fun D _ => div_nonneg (deletionJointMass_nonneg hκ.1 D) hsuccess.le)]
    rw [sum_normalizedDeletionJointMass hκ hsuccess]
    simp)

@[simp] theorem conditionalDeletionLaw_apply_toReal (hκ : IsExperiment κ c C)
    (hsuccess : 0 < successMass κ) (D : DeletionSet F 3) :
    (conditionalDeletionLaw hκ hsuccess D).toReal =
      deletionJointMass κ D / successMass κ := by
  exact ENNReal.toReal_ofReal
    (div_nonneg (deletionJointMass_nonneg hκ.1 D) hsuccess.le)

end Balanced.SelectedDeletion

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_Local
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local

open scoped BigOperators
open Filter

universe u

noncomputable section
attribute [local instance] Classical.propDecidable

abbrev TupleCode (F : Type u) := (Fin 4 → Direction F) × (Fin 4 → Bool)

abbrev ChoiceCode (F : Type u) := Line F × TupleCode F
abbrev Output (F : Type u) := Slot F → ChoiceCode F

def decodeTuple {F : Type u} (t : TupleCode F) : FourTuple F := ⟨t.1, t.2⟩
def decodeChoice {F : Type u} (c : ChoiceCode F) : SplitChoice F :=
  ⟨c.1, decodeTuple c.2⟩
def configuration {F : Type u} (M : MergedPairs F) (v : Output F) : Configuration F :=
  ⟨M, fun s => decodeChoice (v s)⟩

variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]

def constituentMultiplicity (M : MergedPairs F) (p : Point F) : ℕ :=
  (Finset.univ.filter (fun ds : Direction F × Bool =>
    OnLine p (constituent M ds.1 ds.2))).card

def offsetProbability (E : MergedPairs F → Prop) : ℝ :=
  (∑ M : MergedPairs F, if E M then (1 : ℝ) else 0) /
    Fintype.card (MergedPairs F)

def conditionedOffsetProbability (A E : MergedPairs F → Prop) : ℝ :=
  offsetProbability (fun M => A M ∧ E M) / offsetProbability A

structure RetentionRule (F : Type u) [Field F] [Fintype F] [DecidableEq F] where
  candidates : MergedPairs F → Direction F → Finset (ChoiceCode F)
  valid : ∀ M g c, c ∈ candidates M g → ValidChoice M g (decodeChoice c)
  uniqueLine : ∀ M g c d, c ∈ candidates M g → d ∈ candidates M g →
    c.1 = d.1 → c = d
  complete : ∀ M g c, ValidChoice M g (decodeChoice c) →
    ∃ d ∈ candidates M g, d.1 = c.1

abbrev Kernel (F : Type u) := MergedPairs F → Output F → ℝ

def KernelConditions (Q : RetentionRule F) (w : Kernel F) (K : ℝ) : Prop :=
  (∀ M v, 0 ≤ w M v) ∧
  (∀ M, ∑ v, w M v ≤ 1) ∧
  (∀ M v, 0 < w M v →
    (configuration M v).Valid ∧ (configuration M v).Compatible ∧
    (∀ s, v s ∈ Q.candidates M s.1) ∧
    (∀ p, constituentMultiplicity M p ≤ logBudget F)) ∧
  (∀ M (S : Finset (Slot F)) (t : Slot F → TupleCode F),
    (∑ v, if (∀ s ∈ S, (v s).2 = t s) then w M v else 0) ≤
      (K / Fintype.card F) ^ S.card)

def selectedProbability (w : Kernel F) (E : Configuration F → Prop) : ℝ :=
  (∑ M : MergedPairs F, ∑ v : Output F,
    if E (configuration M v) then w M v else 0) /
      Fintype.card (MergedPairs F)

def generatorUnionAt (C : Configuration F) (p : Point F) : Finset (Direction F) :=
  (Finset.univ.filter (fun s => OnLine p (C.choice s).line)).biUnion
    (fun s => generatorSet (C.choice s).tuple)

def reuseCount (C : Configuration F) (p : Point F) : ℕ :=
  4 * C.splitMultiplicity p - (generatorUnionAt C p).card

abbrev DirectionAssignment (F : Type u) (b κ : ℕ) :=
  (Fin b → Direction F) × (Fin (4 * b - κ) → Direction F)

def Eligible {b κ : ℕ} (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) : Prop :=
  Function.Injective a.1 ∧ Function.Injective a.2 ∧
    ∀ i j, a.2 (P.classOf i j) ≠ a.1 i

def prescribedTuple {b κ : ℕ} (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (i : Fin b) : FourTuple F :=
  ⟨fun j => a.2 (P.classOf i j), bits i⟩

def prescribedPoint {b κ : ℕ} (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b)
    (M : MergedPairs F) (ij : Fin b × Fin 4) : Point F :=
  tuplePoint M (prescribedTuple P a bits ij.1) ij.2

def Aligned {b κ : ℕ} (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (M : MergedPairs F) : Prop :=
  ∀ ij, OnLine (prescribedPoint P a bits M ij) (lineThrough (a.1 ij.1) p)

def Admissible {b κ : ℕ} (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (M : MergedPairs F) : Prop :=
  Aligned P a bits p M ∧ Function.Injective (prescribedPoint P a bits M) ∧
    (∀ ij, prescribedPoint P a bits M ij ≠ p) ∧
    (∀ i, lineThrough (a.1 i) p ∉ constituentLines M) ∧
    (∀ x, constituentMultiplicity M x ≤ logBudget F)

def prescribedDesignated {b κ : ℕ} (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (M : MergedPairs F) :
    Finset (Point F) := Finset.univ.image (prescribedPoint P a bits M)

def prescribedPartners {b κ : ℕ} (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (M : MergedPairs F) : Finset (Point F) :=
  (prescribedDesignated P a bits M).filter (fun x =>
    ∃ ds : Direction F × Bool, OnLine p (constituent M ds.1 ds.2) ∧
      OnLine x (constituent M ds.1 (!ds.2)))

def piecePoints (M : MergedPairs F) : LocalPiece F → Finset (Point F)
  | Sum.inl U => U
  | Sum.inr (Sum.inl l) => linePoints l
  | Sum.inr (Sum.inr d) => mergedPoints M d

def AllowedPiece {b κ : ℕ} (a : DirectionAssignment F b κ) (p : Point F)
    (M : MergedPairs F) : LocalPiece F → Prop
  | Sum.inl U => U.card ≤ 2
  | Sum.inr (Sum.inl l) =>
      l ∉ (Finset.univ.image (fun i => lineThrough (a.1 i) p)) ∪ constituentLines M
  | Sum.inr (Sum.inr _) => True

def BadCover {b κ : ℕ} (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (M : MergedPairs F) : Prop :=
  ∃ A : Finset (LocalPiece F), A.card ≤ b - 1 ∧
    (∀ x ∈ A, AllowedPiece a p M x) ∧
    prescribedDesignated P a bits M ⊆
      prescribedPartners P a bits p M ∪ A.biUnion (piecePoints M)

def AdmissibleBadCover {b κ : ℕ} (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (M : MergedPairs F) : Prop :=
  Admissible P a bits p M ∧ BadCover P a bits p M

def PencilLocalResult : Prop :=
  ∀ K : ℝ, 0 < K → ∃ ε : ℕ → ℝ,
    Tendsto ε atTop (nhds 0) ∧ (∀ q, 0 ≤ ε q) ∧
    ∃ q₀ : ℕ, ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      q₀ ≤ Fintype.card F → ∀ (Q : RetentionRule F) (w : Kernel F),
      KernelConditions Q w K →
      selectedProbability w (fun C => ¬ C.LocalCondition) ≤ ε (Fintype.card F)

def PencilReuseResult : Prop :=
  ∀ K : ℝ, 0 < K → ∃ C : ℝ, 0 < C ∧ ∃ q₀ : ℕ,
    ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      q₀ ≤ Fintype.card F → ∀ (Q : RetentionRule F) (w : Kernel F),
      KernelConditions Q w K → ∀ p : Point F,
      selectedProbability w (fun X => 2 ≤ X.splitMultiplicity p ∧ 3 ≤ reuseCount X p) ≤
        C / (Fintype.card F : ℝ) ^ 3

def AlignmentNormalizationResult : Prop :=
  ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
    ∀ b κ : ℕ, 3 ≤ b → b ≤ logBudget F → κ ≤ 2 →
    ∀ (P : EqualityPattern b κ) (a : DirectionAssignment F b κ), Eligible P a →
    ∀ (bits : Bits b) (p : Point F),
      offsetProbability (Aligned P a bits p) = 1 / (Fintype.card F : ℝ) ^ (4 * b)

def PencilSmallReuseResult : Prop :=
  AlignmentNormalizationResult.{u} ∧
  ∃ C : ℝ, 0 < C ∧ ∃ d q₀ : ℕ,
    ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      q₀ ≤ Fintype.card F → ∀ b κ : ℕ, 3 ≤ b → b ≤ logBudget F → κ ≤ 1 →
      ∀ (P : EqualityPattern b κ) (a : DirectionAssignment F b κ), Eligible P a →
      ∀ (bits : Bits b) (p : Point F),
      conditionedOffsetProbability (Aligned P a bits p) (AdmissibleBadCover P a bits p) ≤
        C * (b : ℝ) ^ d * (2 * (logBudget F : ℝ) / Fintype.card F) ^ (3 - κ)

def PencilTwoReusesResult : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ q₀ : ℕ,
    ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      q₀ ≤ Fintype.card F → ∀ b : ℕ, 3 ≤ b → b ≤ logBudget F →
      ∀ (P : EqualityPattern b 2) (bits : Bits b) (p : Point F),
      (∑ a : DirectionAssignment F b 2,
        if Eligible P a then offsetProbability (fun M =>
          Aligned P a bits p M ∧ AdmissibleBadCover P a bits p M) else 0) ≤
        ((Fintype.card F + 1 : ℕ) : ℝ) ^ (5 * b - 2) /
          (Fintype.card F : ℝ) ^ (4 * b) * (C * (b : ℝ) ^ 3 / Fintype.card F)

end
end Balanced.Local

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LowReuseOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

open Finset

theorem exists_smallReuseOrder {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (A : ι → Finset α) (s : Finset ι)
    (hcompat : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (A i ∩ A j).card ≤ 1)
    (hexcess : (∑ i ∈ s, (A i).card) - (s.biUnion A).card ≤ 2) :
    ∃ l : List ι, l.Nodup ∧ l.toFinset = s ∧ SmallReuseOrder A l := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    by_cases hs : s.Nonempty
    · obtain ⟨i, hi, hleaf⟩ := exists_low_reuse_leaf A s hs hcompat hexcess
      have hexcess' : (∑ j ∈ s.erase i, (A j).card) -
          ((s.erase i).biUnion A).card ≤ 2 := by
        have hdecomp := family_reuse_erase A s i hi
        omega
      obtain ⟨l, hnd, hset, horder⟩ := ih (s.erase i) (Finset.erase_ssubset hi)
        (fun j hj k hk hne => hcompat j (Finset.mem_of_mem_erase hj)
          k (Finset.mem_of_mem_erase hk) hne) hexcess'
      refine ⟨i :: l, List.nodup_cons.mpr ⟨?_, hnd⟩, ?_, ?_⟩
      · intro hil
        have hiset : i ∈ l.toFinset := List.mem_toFinset.mpr hil
        rw [hset] at hiset
        exact Finset.notMem_erase i s hiset
      · rw [List.toFinset_cons, hset, Finset.insert_erase hi]
      · exact ⟨horder, by simpa only [hset] using hleaf⟩
    · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      subst s
      exact ⟨[], by simp, by simp, trivial⟩

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_EqualityPatternOrdering
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.EqualityPattern

open Finset

theorem exists_smallReuseOrder {b κ : ℕ} (P : EqualityPattern b κ) (hκ : κ ≤ 2) :
    ∃ l : List (Fin b), l.Nodup ∧ l.toFinset = Finset.univ ∧
      Balanced.SmallReuseOrder P.classSet l := by
  apply Balanced.exists_smallReuseOrder P.classSet Finset.univ
  · intro i _ j _ hij
    exact P.pairOverlap i j hij
  · exact P.classSet_reuse_le.trans hκ

theorem generatorSet_prescribedTuple {F : Type*} [DecidableEq F]
    {b κ : ℕ} (P : EqualityPattern b κ) (a : DirectionAssignment F b κ)
    (bits : Bits b) (i : Fin b) :
    generatorSet (prescribedTuple P a bits i) = (P.classSet i).image a.2 := by
  simp [generatorSet, prescribedTuple, classSet, Finset.image_image, Function.comp_def]

theorem prescribed_generator_overlap_card {F : Type*} [DecidableEq F]
    {b κ : ℕ} (P : EqualityPattern b κ) (a : DirectionAssignment F b κ)
    (hinj : Function.Injective a.2) (bits : Bits b) (i : Fin b) (s : Finset (Fin b)) :
    ((generatorSet (prescribedTuple P a bits i)) ∩
      s.biUnion (fun j => generatorSet (prescribedTuple P a bits j))).card =
      (P.classSet i ∩ s.biUnion P.classSet).card := by
  simp_rw [P.generatorSet_prescribedTuple]
  rw [← Finset.biUnion_image, ← Finset.image_inter _ _ hinj,
    Finset.card_image_of_injective _ hinj]

end Balanced.Local.EqualityPattern

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_AlignmentNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local

open AlignedListProbability
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]

omit [Field F] [Fintype F] in

theorem smallReuseOrder_prescribed {b κ : ℕ} (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (ha : Function.Injective a.2)
    (bits : Bits b) (l : List (Fin b)) (h : SmallReuseOrder P.classSet l) :
    SmallReuseOrder (fun i => generatorSet (prescribedTuple P a bits i)) l := by
  induction l with
  | nil => trivial
  | cons i l ih =>
      refine ⟨ih h.1, ?_⟩
      rw [P.prescribed_generator_overlap_card a ha bits i l.toFinset]
      exact h.2

theorem alignment_probability {b κ : ℕ} (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (a : DirectionAssignment F b κ) (ha : Eligible P a)
    (bits : Bits b) (p : Point F) :
    offsetProbability (Aligned P a bits p) =
      1 / (Fintype.card F : ℝ) ^ (4 * b) := by
  obtain ⟨l, hnd, hfull, horder⟩ := P.exists_smallReuseOrder hκ
  have hlen : l.length = b := by
    rw [← List.toFinset_card_of_nodup hnd, hfull]
    simp
  have hall (i : Fin b) : i ∈ l := by
    apply List.mem_toFinset.mp
    rw [hfull]
    exact Finset.mem_univ _
  have hgenerators (i : Fin b) : Function.Injective (prescribedTuple P a bits i).generator :=
    ha.2.1.comp (P.withinTuple i)
  have htargets (i : Fin b) (j : Fin 4) :
      (prescribedTuple P a bits i).generator j ≠ (lineThrough (a.1 i) p).1 :=
    ha.2.2 i j
  have hprob := list_alignment_probability (prescribedTuple P a bits)
    (fun i => lineThrough (a.1 i) p) l (fun i _ => hgenerators i)
    (fun i _ => htargets i) (smallReuseOrder_prescribed P a ha.2.1 bits l horder)
  have hevent :
      {M | ListAligned (prescribedTuple P a bits) (fun i => lineThrough (a.1 i) p) l M} =
        {M | Aligned P a bits p M} := by
    ext M
    constructor
    · intro h ij
      exact h ij.1 (hall ij.1) ij.2
    · intro h i _ j
      exact h (i,j)
  rw [hevent, hlen] at hprob
  calc
    offsetProbability (Aligned P a bits p) =
        ((PMF.uniformOfFintype (MergedPairs F)).toOuterMeasure
          {M | Aligned P a bits p M}).toReal :=
      (FiniteUniformFibers.probability_eq_sum (Aligned P a bits p)).symm
    _ = ((Fintype.card F : ℝ)⁻¹ ^ 4) ^ b := hprob
    _ = 1 / (Fintype.card F : ℝ) ^ (4 * b) := by
      rw [← pow_mul, inv_pow, one_div]

theorem alignment_probability_pos {b κ : ℕ} (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (a : DirectionAssignment F b κ) (ha : Eligible P a)
    (bits : Bits b) (p : Point F) :
    0 < offsetProbability (Aligned P a bits p) := by
  rw [alignment_probability P hκ a ha bits p]
  positivity

end
end Balanced.Local

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_AlignedUnusedLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.AlignedUnused

open UniformConditionalProduct
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def usedDirections {b κ : ℕ} (_P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) : Finset (Direction F) := Finset.univ.image a.2

abbrev UsedArray {b κ : ℕ} (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) := {d : Direction F // d ∈ usedDirections P a} → Bool → F

abbrev UnusedArray {b κ : ℕ} (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) := {d : Direction F // d ∉ usedDirections P a} → Bool → F

def split {b κ : ℕ} (P : EqualityPattern b κ) (a : DirectionAssignment F b κ) :
    MergedPairs F ≃ UsedArray P a × UnusedArray P a :=
  arraySplitEquiv (fun d => d ∈ usedDirections P a)

omit [Fintype F] in

theorem aligned_agree {b κ : ℕ} (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (M N : MergedPairs F) (h : ∀ d ∈ usedDirections P a, M d = N d) :
    Aligned P a bits p M ↔ Aligned P a bits p N := by
  have hp (ij : Fin b × Fin 4) :
      prescribedPoint P a bits M ij = prescribedPoint P a bits N ij := by
    apply AlignedListProbability.tuplePoint_eq_of_agree
    intro d hd
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hd
    exact h _ (Finset.mem_image.mpr ⟨P.classOf ij.1 j, Finset.mem_univ _, rfl⟩)
  simp only [Aligned, hp]

def usedAligned {b κ : ℕ} (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (u : UsedArray P a) : Prop :=
  Aligned P a bits p ((split P a).symm (u, fun _ _ => 0))

omit [Fintype F] in
theorem aligned_iff_usedAligned {b κ : ℕ} (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F) (M : MergedPairs F) :
    Aligned P a bits p M ↔ usedAligned P a bits p ((split P a M).1) := by
  apply aligned_agree
  intro d hd
  have heq := congrArg Prod.fst ((split P a).apply_symm_apply
    ((split P a M).1, fun _ _ => 0))
  exact (congrFun heq ⟨d, hd⟩).symm

theorem alignment_supported {b κ : ℕ} (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (a : DirectionAssignment F b κ) (ha : Eligible P a) (bits : Bits b) (p : Point F) :
    ∃ M ∈ {M | Aligned P a bits p M},
      M ∈ (PMF.uniformOfFintype (MergedPairs F)).support := by
  have hpos := alignment_probability_pos P hκ a ha bits p
  have hex : ∃ M, Aligned P a bits p M := by
    by_contra h
    have hn : ∀ M, ¬ Aligned P a bits p M := not_exists.mp h
    have hz : offsetProbability (Aligned P a bits p) = 0 := by
      simp [offsetProbability, hn]
    rw [hz] at hpos
    exact (lt_irrefl 0) hpos
  obtain ⟨M, hM⟩ := hex
  exact ⟨M, hM, PMF.mem_support_uniformOfFintype M⟩

def alignedLaw {b κ : ℕ} (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (a : DirectionAssignment F b κ) (ha : Eligible P a) (bits : Bits b) (p : Point F) :
    PMF (MergedPairs F) :=
  (PMF.uniformOfFintype (MergedPairs F)).filter {M | Aligned P a bits p M}
    (alignment_supported P hκ a ha bits p)

theorem usedAligned_nonempty {b κ : ℕ} (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (a : DirectionAssignment F b κ) (ha : Eligible P a) (bits : Bits b) (p : Point F) :
    Nonempty {u : UsedArray P a // usedAligned P a bits p u} := by
  obtain ⟨M, hM, _⟩ := alignment_supported P hκ a ha bits p
  exact ⟨⟨(split P a M).1, (aligned_iff_usedAligned P a bits p M).mp hM⟩⟩

def usedLaw {b κ : ℕ} (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (a : DirectionAssignment F b κ) (ha : Eligible P a) (bits : Bits b) (p : Point F) :
    PMF (UsedArray P a) :=
  letI := usedAligned_nonempty P hκ a ha bits p
  (PMF.uniformOfFintype {u : UsedArray P a // usedAligned P a bits p u}).map Subtype.val

end
end Balanced.Local.AlignedUnused

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_AlignedGlobalCardinality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.AlignedGlobal

open AlignedUnused RootChildPartition

noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem card_aligned_mul {b κ : ℕ} (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (a : DirectionAssignment F b κ) (ha : Eligible P a)
    (bits : Bits b) (p : Point F) :
    Fintype.card {M : MergedPairs F // Aligned P a bits p M} *
      Fintype.card F ^ (4 * b) = Fintype.card (MergedPairs F) := by
  have hp := alignment_probability P hκ a ha bits p
  unfold offsetProbability at hp
  rw [← FiniteUniformFibers.probability_eq_sum,
    PMF.toOuterMeasure_uniformOfFintype_apply, ENNReal.toReal_div] at hp
  simp only [ENNReal.toReal_natCast] at hp
  change (Fintype.card {M : MergedPairs F // Aligned P a bits p M} : ℝ) /
    Fintype.card (MergedPairs F) = 1 / (Fintype.card F : ℝ) ^ (4 * b) at hp
  have ht : (Fintype.card (MergedPairs F) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hq : (Fintype.card F : ℝ) ^ (4 * b) ≠ 0 := by positivity
  have hm := (div_eq_div_iff ht hq).mp hp
  simp only [one_mul] at hm
  exact_mod_cast hm

omit [Field F] [Fintype F] in

theorem card_usedDirections {b κ : ℕ} (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (ha : Function.Injective a.2) :
    (usedDirections P a).card = 4 * b - κ := by
  rw [usedDirections, Finset.card_image_of_injective _ ha]
  simp

omit [Field F] in

theorem coordinate_exponent_identity {b κ : ℕ} (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (ha : Eligible P a)
    (D : Finset (Fin b × Fin 4)) (hD : D.card = 2 * κ) :
    Fintype.card {ij : Fin b × Fin 4 // ij ∉ D} +
      2 * Fintype.card {d : Direction F // d ∉ usedDirections P a} + 4 * b =
        2 * Fintype.card (Direction F) := by
  have hdle : D.card ≤ 4 * b := by
    simpa [Fintype.card_prod, Nat.mul_comm] using Finset.card_le_univ D
  have hule : (usedDirections P a).card ≤ Fintype.card (Direction F) :=
    Finset.card_le_univ _
  rw [card_usedDirections P a ha.2.1] at hule
  simp only [Fintype.card_subtype_compl, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_coe]
  rw [hD, card_usedDirections P a ha.2.1]
  omega

theorem card_aligned_eq_free_product {b κ : ℕ}
    (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (a : DirectionAssignment F b κ) (ha : Eligible P a)
    (bits : Bits b) (p : Point F)
    (D : Finset (Fin b × Fin 4)) (hD : D.card = 2 * κ) :
    Fintype.card {M : MergedPairs F // Aligned P a bits p M} =
      Fintype.card (FreeCoordinates (F := F) D × UnusedArray P a) := by
  apply Nat.eq_of_mul_eq_mul_right (pow_pos (Fintype.card_pos (α := F)) (4 * b))
  rw [card_aligned_mul P hκ a ha bits p]
  simp only [Fintype.card_prod, FreeCoordinates, UnusedArray,
    MergedPairs, Fintype.card_fun, Fintype.card_bool, ← pow_mul]
  rw [← pow_add, ← pow_add]
  congr 1
  have he := coordinate_exponent_identity P a ha D hD
  omega

end
end Balanced.Local.AlignedGlobal

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_AlignedGlobalProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.AlignedGlobal

open TupleAlignment RootChildPartition AlignedUnused
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

abbrev AlignedOffsets {b κ : ℕ} (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F) :=
  {M : MergedPairs F // Aligned P a bits p M}

def coordinates {b κ : ℕ} (P : EqualityPattern b κ) (R : Finset (Fin b))
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (M : AlignedOffsets P a bits p) :
    (FreeIndex P R → F) × UnusedArray P a :=
  ((fun ij => linePointEquiv (a.1 ij.1.1) (lineEval (a.1 ij.1.1) p)
      ⟨prescribedPoint P a bits M.1 ij.1, M.2 ij.1⟩),
    fun d => M.1 d.1)

omit [Fintype F] [DecidableEq F] in

theorem tuple_offsets_eq_of_points (T : FourTuple F)
    (hT : Function.Injective T.generator) (M N : MergedPairs F)
    (h : ∀ j, tuplePoint M T j = tuplePoint N T j) :
    ∀ j, M (T.generator j) = N (T.generator j) := by
  have heq : (fun j => M (T.generator j)) = (fun j => N (T.generator j)) := by
    apply (tuplePositionEquiv T.generator (adjacent_ne_of_injective T hT) T.side).injective
    funext j
    simpa only [tuplePositionEquiv_apply, tuplePoint, constituent] using h j
  exact congrFun heq

omit [Fintype F] in

theorem coordinates_injective {b κ : ℕ} (P : EqualityPattern b κ)
    (R : Finset (Fin b)) (a : DirectionAssignment F b κ) (ha : Eligible P a)
    (bits : Bits b) (p : Point F) :
    Function.Injective (coordinates P R a bits p) := by
  intro M N heq
  have hfree (ij : Fin b × Fin 4) (hij : ij ∉ dependentOccurrences P R) :
      prescribedPoint P a bits M.1 ij = prescribedPoint P a bits N.1 ij := by
    have h := congrFun (congrArg Prod.fst heq) (⟨ij, hij⟩ : FreeIndex P R)
    exact congrArg Subtype.val ((linePointEquiv (a.1 ij.1)
      (lineEval (a.1 ij.1) p)).injective h)
  have hroot (i : Fin b) (hi : i ∈ R) (j : Fin 4) :
      M.1 (a.2 (P.classOf i j)) = N.1 (a.2 (P.classOf i j)) := by
    apply tuple_offsets_eq_of_points (prescribedTuple P a bits i)
      (ha.2.1.comp (P.withinTuple i)) M.1 N.1
    intro k
    apply hfree (i,k)
    simp only [mem_dependentOccurrences, not_and]
    exact fun hnot => (hnot hi).elim
  have hold (c : Fin (4*b-κ)) (hc : c ∈ R.biUnion P.classSet) :
      M.1 (a.2 c) = N.1 (a.2 c) := by
    obtain ⟨i, hi, hj⟩ := Finset.mem_biUnion.mp hc
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hj
    exact hroot i hi j
  have hpoint (ij : Fin b × Fin 4) :
      prescribedPoint P a bits M.1 ij = prescribedPoint P a bits N.1 ij := by
    by_cases hdep : ij ∈ dependentOccurrences P R
    · have hd := (mem_dependentOccurrences P R ij).mp hdep
      let T := prescribedTuple P a bits ij.1
      have hT : Function.Injective T.generator := ha.2.1.comp (P.withinTuple ij.1)
      have hleft (O : MergedPairs F) :
          lineEval (a.2 (P.classOf ij.1 ij.2)) (prescribedPoint P a bits O ij) =
            O (a.2 (P.classOf ij.1 ij.2)) (bits ij.1 ij.2) := by
        exact tuplePosition_lineEval_left T.generator (adjacent_ne_of_injective T hT)
          T.side (fun j => O (T.generator j)) ij.2
      have hright (O : MergedPairs F) :
          lineEval (a.2 (P.classOf ij.1 (ij.2+1))) (prescribedPoint P a bits O ij) =
            O (a.2 (P.classOf ij.1 (ij.2+1))) (!(bits ij.1 (ij.2+1))) := by
        exact tuplePosition_lineEval_right T.generator (adjacent_ne_of_injective T hT)
          T.side (fun j => O (T.generator j)) ij.2
      rcases hd.2 with hl | hr
      · apply (lineEvalEquiv (a.2 (P.classOf ij.1 ij.2)) (a.1 ij.1)
          (ha.2.2 ij.1 ij.2)).injective
        apply Prod.ext
        · change lineEval _ _ = lineEval _ _
          rw [hleft, hleft, hold _ hl]
        · exact (M.2 ij).trans (N.2 ij).symm
      · apply (lineEvalEquiv (a.2 (P.classOf ij.1 (ij.2+1))) (a.1 ij.1)
          (ha.2.2 ij.1 (ij.2+1))).injective
        apply Prod.ext
        · change lineEval _ _ = lineEval _ _
          rw [hright, hright, hold _ hr]
        · exact (M.2 ij).trans (N.2 ij).symm
    · exact hfree ij hdep
  apply Subtype.ext
  funext d
  by_cases hd : d ∈ usedDirections P a
  · obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨⟨i,j⟩, rfl⟩ := P.everyClass c
    exact tuple_offsets_eq_of_points (prescribedTuple P a bits i)
      (ha.2.1.comp (P.withinTuple i)) M.1 N.1 (fun k => hpoint (i,k)) j
  · exact congrFun (congrArg Prod.snd heq) ⟨d, hd⟩

def coordinateEquiv {b κ : ℕ} (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (a : DirectionAssignment F b κ) (ha : Eligible P a) (bits : Bits b) (p : Point F) :
    AlignedOffsets P a bits p ≃ ((FreeIndex P R → F) × UnusedArray P a) :=
  Equiv.ofBijective (coordinates P R a bits p)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨coordinates_injective P R a ha bits p,
        card_aligned_eq_free_product P hκ a ha bits p (dependentOccurrences P R) hD⟩)

@[simp] theorem coordinateEquiv_apply {b κ : ℕ} (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (a : DirectionAssignment F b κ) (ha : Eligible P a) (bits : Bits b) (p : Point F)
    (M : AlignedOffsets P a bits p) :
    coordinateEquiv P hκ R hD a ha bits p M = coordinates P R a bits p M := rfl

end
end Balanced.Local.AlignedGlobal

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalDirectionAssignments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local

def assignmentFunction {F : Type*} {b κ : ℕ} (a : DirectionAssignment F b κ) :
    DirectionToken b κ → Direction F := Sum.elim a.1 a.2

def AllTokensDistinct {F : Type*} {b κ : ℕ} (a : DirectionAssignment F b κ) : Prop :=
  Function.Injective (assignmentFunction a)

def tokenInjectionEquiv (F : Type*) (b κ : ℕ) :
    (DirectionToken b κ ↪ Direction F) ≃
      {a : DirectionAssignment F b κ // AllTokensDistinct a} where
  toFun e := ⟨(fun i => e (Sum.inl i), fun j => e (Sum.inr j)), by
    intro x y h
    apply e.injective
    cases x <;> cases y <;> exact h⟩
  invFun a := ⟨assignmentFunction a.val, a.property⟩
  left_inv e := by ext x; cases x <;> rfl
  right_inv a := by apply Subtype.ext; rfl

theorem allTokensDistinct_eligible {F : Type*} {b κ : ℕ}
    (P : EqualityPattern b κ) (a : DirectionAssignment F b κ)
    (ha : AllTokensDistinct a) : Eligible P a := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j h
    have h' : Sum.inl i = (Sum.inl j : DirectionToken b κ) := ha h
    exact Sum.inl.inj h'
  · intro i j h
    have h' : Sum.inr i = (Sum.inr j : DirectionToken b κ) := ha h
    exact Sum.inr.inj h'
  · intro i j h
    have h' : Sum.inr (P.classOf i j) = (Sum.inl i : DirectionToken b κ) := ha h
    cases h'

end Balanced.Local

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_AlignedTokenPointLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.TokenExposure

open AlignedListProbability TupleAlignment PartialAlignment
noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ}

def tupleDirections (P : EqualityPattern b κ)
    (e : DirectionToken b κ ↪ Direction F) (i : Fin b) : Fin 4 → Direction F :=
  fun j => e (Sum.inr (P.classOf i j))

omit [Field F] [Fintype F] [DecidableEq F] in
theorem tupleDirections_injective (P : EqualityPattern b κ)
    (e : DirectionToken b κ ↪ Direction F) (i : Fin b) :
    Function.Injective (tupleDirections P e i) := by
  intro j k h
  exact P.withinTuple i (Sum.inr.inj (e.injective h))

omit [Field F] [Fintype F] [DecidableEq F] in
theorem tupleDirections_adjacent (P : EqualityPattern b κ)
    (e : DirectionToken b κ ↪ Direction F) (i : Fin b) :
    ∀ j, tupleDirections P e i j ≠ tupleDirections P e i (j+1) :=
  adjacent_ne_of_injective ⟨tupleDirections P e i, fun _ => false⟩
    (tupleDirections_injective P e i)

omit [Field F] [Fintype F] [DecidableEq F] in
theorem tupleDirections_ne_target (P : EqualityPattern b κ)
    (e : DirectionToken b κ ↪ Direction F) (i : Fin b) :
    ∀ j, tupleDirections P e i j ≠ e (Sum.inl i) := by
  intro j h
  have hbad := e.injective h
  cases hbad

end
end Balanced.Local.TokenExposure

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_AlignedProjectedExposure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.TokenExposure

open AlignedListProbability PartialAlignment InjectionExposure
noncomputable section
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ} {Z : Type*} [Fintype Z]

def pointOutput (P : EqualityPattern b κ) (bits : Bits b) (p : Point F)
    (i : Fin b) (J : Finset (Fin 4)) (hJ : J.card ≤ 1)
    (a : Z → Fin 4 → Bool → F)
    (x : Z → {j : Fin 4 // j ∈ freePositions J} → F)
    (e : DirectionToken b κ ↪ Direction F) (z : Z) (j : Fin 4) : Point F :=
  generatedPositions (tupleDirections P e i) (tupleDirections_adjacent P e i)
    (bits i) (e (Sum.inl i)) (tupleDirections_ne_target P e i)
    (lineEval (e (Sum.inl i)) p) J hJ (a z) (x z) j

end
end Balanced.Local.TokenExposure

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_AlignedGlobalCurrentTuple
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.AlignedGlobal
open RootChildPartition AlignedListProbability TupleAlignment PartialAlignment TokenExposure
noncomputable section
open scoped Classical
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ}

def currentOldIndices (P : EqualityPattern b κ) (R : Finset (Fin b))
    (i : Fin b) : Finset (Fin 4) :=
  if i ∈ R then ∅ else rootGeneratorIndices P R i

def currentFreeIndex (P : EqualityPattern b κ) (R : Finset (Fin b)) (i : Fin b)
    (j : {j : Fin 4 // j ∈ freePositions (currentOldIndices P R i)}) :
    FreeIndex P R := by
  refine ⟨(i,j.1), ?_⟩
  by_cases hi : i ∈ R
  · simp [mem_dependentOccurrences, hi]
  · have hj := j.2
    simp only [freePositions, Finset.mem_filter, Finset.mem_univ, true_and,
      currentOldIndices, ite_eq_right hi, rootGeneratorIndices] at hj
    simp only [mem_dependentOccurrences, hi, not_false_eq_true, true_and, not_or]
    exact hj

end
end Balanced.Local.AlignedGlobal

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalPrescribedGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.PrescribedGeometry

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ} {P : EqualityPattern b κ}
variable {a : DirectionAssignment F b κ} {bits : Bits b}
variable {p : Point F} {M : MergedPairs F}

omit [Fintype F] [DecidableEq F] in

theorem prescribedPoint_on_left (hE : Eligible P a) (i : Fin b) (j : Fin 4) :
    OnLine (prescribedPoint P a bits M (i, j))
      (constituent M (a.2 (P.classOf i j)) (bits i j)) := by
  apply onLine_lineIntersection_left
  change a.2 (P.classOf i j) ≠ a.2 (P.classOf i (j + 1))
  intro h
  have h' := P.withinTuple i (hE.2.1 h)
  fin_cases j <;> contradiction

omit [Fintype F] [DecidableEq F] in

theorem prescribedPoint_on_right (hE : Eligible P a) (i : Fin b) (j : Fin 4) :
    OnLine (prescribedPoint P a bits M (i, j))
      (constituent M (a.2 (P.classOf i (j + 1))) (!(bits i (j + 1)))) := by
  apply onLine_lineIntersection_right
  change a.2 (P.classOf i j) ≠ a.2 (P.classOf i (j + 1))
  intro h
  have h' := P.withinTuple i (hE.2.1 h)
  fin_cases j <;> contradiction

end
end Balanced.Local.PrescribedGeometry

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalFiberBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators Classical

namespace Balanced.LocalFiberBounds

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def indexedThrough (M : MergedPairs F) (U : Finset (Direction F)) (a : Point F) :
    Finset (Direction F × Bool) :=
  Finset.univ.filter (fun ds => ds.1 ∈ U ∧ OnLine a (constituent M ds.1 ds.2))

def partnerCandidates (M : MergedPairs F) (U : Finset (Direction F)) (a : Point F) :
    Finset (Line F) :=
  (indexedThrough M U a).image (fun ds => constituent M ds.1 (!ds.2))

def mergedCandidates (M : MergedPairs F) (U : Finset (Direction F)) (a : Point F) :
    Finset (Line F) :=
  (indexedThrough M U a).biUnion
    (fun ds => {constituent M ds.1 false, constituent M ds.1 true})

end Balanced.LocalFiberBounds

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalPrecoverageTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.PrescribedGeometry

noncomputable section
open scoped Classical
open LocalFiberBounds

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ} {P : EqualityPattern b κ}
variable {a : DirectionAssignment F b κ} {bits : Bits b}
variable {p : Point F} {M N : MergedPairs F}

def unusedDirections (a : DirectionAssignment F b κ) : Finset (Direction F) :=
  Finset.univ \ Finset.univ.image a.2

omit [Field F] in
@[simp] theorem mem_unusedDirections (d : Direction F) :
    d ∈ unusedDirections a ↔ d ∉ Finset.univ.image a.2 := by
  simp [unusedDirections]

end
end Balanced.Local.PrescribedGeometry

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalUnusedOffsetProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.UnusedOffsetProbability

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
open PrescribedGeometry

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

variable {b κ : ℕ} {P : EqualityPattern b κ}
variable {a : DirectionAssignment F b κ} {bits : Bits b} {p : Point F}

def unusedPrecoverage (P : EqualityPattern b κ) (a : DirectionAssignment F b κ)
    (bits : Bits b) (p : Point F) (M : MergedPairs F) : Prop :=
  ∃ ij : Fin b × Fin 4, ∃ d ∈ unusedDirections a, ∃ s : Bool,
    OnLine p (constituent M d s) ∧
    OnLine (prescribedPoint P a bits M ij) (constituent M d (!s))

end
end Balanced.Local.UnusedOffsetProbability

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_AlignedUsedObservable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.AlignedGlobal

open AlignedUnused TupleAlignment RootChildPartition
noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ}

def refreshUnused (P : EqualityPattern b κ) (a : DirectionAssignment F b κ)
    (M : MergedPairs F) (u : UnusedArray P a) : MergedPairs F :=
  (split P a).symm ((split P a M).1, u)

omit [Field F] [Fintype F] in
theorem refreshUnused_used (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (M : MergedPairs F) (u : UnusedArray P a)
    (d : Direction F) (hd : d ∈ usedDirections P a) :
    refreshUnused P a M u d = M d := by
  exact congrFun (congrArg Prod.fst
    ((split P a).apply_symm_apply ((split P a M).1, u))) ⟨d, hd⟩

def refreshAligned (P : EqualityPattern b κ) (a : DirectionAssignment F b κ)
    (bits : Bits b) (p : Point F) (M : AlignedOffsets P a bits p)
    (u : UnusedArray P a) : AlignedOffsets P a bits p :=
  ⟨refreshUnused P a M.1 u,
    (aligned_agree P a bits p M.1 (refreshUnused P a M.1 u)
      (fun d hd => (refreshUnused_used P a M.1 u d hd).symm)).mp M.2⟩

def generatedZero (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (a : DirectionAssignment F b κ) (ha : Eligible P a)
    (bits : Bits b) (p : Point F) (x : FreeIndex P R → F) : MergedPairs F :=
  ((coordinateEquiv P hκ R hD a ha bits p).symm (x, fun _ _ => 0)).1

end
end Balanced.Local.AlignedGlobal

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_AlignedHistoryKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.AlignedGlobal

open RootChildPartition InjectionExposure
noncomputable section
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ}

abbrev PrefixData (F : Type*) {b κ : ℕ} (P : EqualityPattern b κ)
    (S : Finset (Fin b)) :=
  ({i : Fin b // i ∈ S} → Fin 4 → Point F) ×
    ({c : Fin (4*b-κ) // c ∈ S.biUnion P.classSet} → Bool → Line F)

def prefixObservation (P : EqualityPattern b κ) (S : Finset (Fin b))
    (a : DirectionAssignment F b κ) (bits : Bits b) (M : MergedPairs F) :
    PrefixData F P S :=
  ((fun i j => prescribedPoint P a bits M (i.1,j)),
    fun c s => constituent M (a.2 c.1) s)

def prefixNoise (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R S : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (bits : Bits b) (p : Point F) (e : DirectionToken b κ ↪ Direction F) :
    PMF ((FreeIndex P R → F) × PrefixData F P S) :=
  let a := tokenInjectionEquiv F b κ e
  (PMF.uniformOfFintype (FreeIndex P R → F)).map fun x =>
    (x, prefixObservation P S a.1 bits
      (generatedZero P hκ R hD a.1 (allTokensDistinct_eligible P a.1 a.2) bits p x))

def currentNoise (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R S : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (bits : Bits b) (p : Point F) (i : Fin b)
    (e : DirectionToken b κ ↪ Direction F) :
    PMF ((FreeIndex P R → F) × (PrefixData F P S × (Fin 4 → Point F))) :=
  let a := tokenInjectionEquiv F b κ e
  (PMF.uniformOfFintype (FreeIndex P R → F)).map fun x =>
    let M := generatedZero P hκ R hD a.1 (allTokensDistinct_eligible P a.1 a.2) bits p x
    (x, prefixObservation P S a.1 bits M, fun j => prescribedPoint P a.1 bits M (i,j))

end
end Balanced.Local.AlignedGlobal

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_AlignedGlobalProjectedIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.AlignedGlobal
open RootChildPartition PartialAlignment TokenExposure InjectionExposure
noncomputable section
open scoped Classical
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ}

abbrev ProjectionData (P : EqualityPattern b κ) (R S : Finset (Fin b)) :=
  (FreeIndex P R → F) × PrefixData F P S

def projectionOffsets (P : EqualityPattern b κ) (R S : Finset (Fin b))
    (i : Fin b) (z : ProjectionData (F := F) P R S) (j : Fin 4) (s : Bool) : F :=
  if h : P.classOf i j ∈ S.biUnion P.classSet then (z.2.2 ⟨P.classOf i j,h⟩ s).2 else 0

def projectionFree (P : EqualityPattern b κ) (R S : Finset (Fin b))
    (i : Fin b) (z : ProjectionData (F := F) P R S)
    (j : {j : Fin 4 // j ∈ freePositions (currentOldIndices P R i)}) : F :=
  z.1 (currentFreeIndex P R i j)

def projectionObservation (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R S : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (bits : Bits b) (p : Point F) (e : DirectionToken b κ ↪ Direction F)
    (x : FreeIndex P R → F) : ProjectionData (F := F) P R S :=
  let a := tokenInjectionEquiv F b κ e
  (x,prefixObservation P S a.1 bits
    (generatedZero P hκ R hD a.1 (allTokensDistinct_eligible P a.1 a.2) bits p x))

end
end Balanced.Local.AlignedGlobal

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalConfigurationPattern
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.ConfigurationPattern
noncomputable section
attribute [local instance] Classical.propDecidable
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable (C : Configuration F) (hV : C.Valid) (hC : C.Compatible) (p : Point F)

def slots : Finset (Slot F) :=
  Finset.univ.filter (fun s => OnLine p (C.choice s).line)

def slotEquiv : Fin (C.splitMultiplicity p) ≃ {s // s ∈ slots C p} :=
  (Fintype.equivFinOfCardEq (by
    rw [Fintype.card_coe]
    exact (ConfigurationStructure.split_multiplicity_eq_slots C hV hC p).symm)).symm

def slot (i : Fin (C.splitMultiplicity p)) : Slot F :=
  (slotEquiv C hV hC p i).val

theorem slot_injective : Function.Injective (slot C hV hC p) :=
  Subtype.val_injective.comp (slotEquiv C hV hC p).injective

theorem slot_onLine (i : Fin (C.splitMultiplicity p)) :
    OnLine p (C.choice (slot C hV hC p i)).line :=
  (Finset.mem_filter.mp (slotEquiv C hV hC p i).property).2

theorem exists_slot {s : Slot F} (hs : OnLine p (C.choice s).line) :
    ∃ i, slot C hV hC p i = s := by
  let t : {s // s ∈ slots C p} := ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩⟩
  refine ⟨(slotEquiv C hV hC p).symm t, ?_⟩
  exact congrArg Subtype.val ((slotEquiv C hV hC p).apply_symm_apply t)

def point (ij : Fin (C.splitMultiplicity p) × Fin 4) : Point F :=
  tuplePoint C.merged (C.choice (slot C hV hC p ij.1)).tuple ij.2

def generator (ij : Fin (C.splitMultiplicity p) × Fin 4) : Direction F :=
  (C.choice (slot C hV hC p ij.1)).tuple.generator ij.2

theorem generator_image :
    Finset.univ.image (generator C hV hC p) = generatorUnionAt C p := by
  ext d
  constructor
  · intro hd
    obtain ⟨⟨i, j⟩, _, rfl⟩ := Finset.mem_image.mp hd
    exact Finset.mem_biUnion.mpr ⟨slot C hV hC p i,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, slot_onLine C hV hC p i⟩,
      Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩
  · intro hd
    obtain ⟨s, hs, hd⟩ := Finset.mem_biUnion.mp hd
    obtain ⟨i, rfl⟩ := exists_slot C hV hC p (Finset.mem_filter.mp hs).2
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hd
    exact Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩

include hV hC

theorem generator_card_le :
    (generatorUnionAt C p).card ≤ 4 * C.splitMultiplicity p := by
  rw [← generator_image C hV hC p]
  simpa [Nat.mul_comm] using
    (Finset.card_image_le (s := Finset.univ) (f := generator C hV hC p))

theorem generator_card_eq :
    (generatorUnionAt C p).card = 4 * C.splitMultiplicity p - reuseCount C p := by
  exact (Nat.sub_sub_self (generator_card_le C hV hC p)).symm

def generatorEquiv : {d // d ∈ generatorUnionAt C p} ≃
    Fin (4 * C.splitMultiplicity p - reuseCount C p) :=
  Fintype.equivFinOfCardEq (by
    rw [Fintype.card_coe]
    exact generator_card_eq C hV hC p)

theorem generator_mem (ij : Fin (C.splitMultiplicity p) × Fin 4) :
    generator C hV hC p ij ∈ generatorUnionAt C p := by
  rw [← generator_image C hV hC p]
  exact Finset.mem_image.mpr ⟨ij, Finset.mem_univ _, rfl⟩

def classOf (i : Fin (C.splitMultiplicity p)) (j : Fin 4) :
    Fin (4 * C.splitMultiplicity p - reuseCount C p) :=
  generatorEquiv C hV hC p ⟨generator C hV hC p (i, j), generator_mem C hV hC p (i, j)⟩

def assignedGenerator (k : Fin (4 * C.splitMultiplicity p - reuseCount C p)) :
    Direction F := ((generatorEquiv C hV hC p).symm k).val

theorem assignedGenerator_injective : Function.Injective (assignedGenerator C hV hC p) :=
  Subtype.val_injective.comp (generatorEquiv C hV hC p).symm.injective

theorem assigned_class (i : Fin (C.splitMultiplicity p)) (j : Fin 4) :
    assignedGenerator C hV hC p (classOf C hV hC p i j) =
      (C.choice (slot C hV hC p i)).tuple.generator j := by
  exact congrArg Subtype.val ((generatorEquiv C hV hC p).symm_apply_apply _)

theorem class_surjective :
    Function.Surjective (fun ij : Fin (C.splitMultiplicity p) × Fin 4 =>
      classOf C hV hC p ij.1 ij.2) := by
  intro k
  have hd := ((generatorEquiv C hV hC p).symm k).property
  have hd' : assignedGenerator C hV hC p k ∈ Finset.univ.image (generator C hV hC p) := by
    rw [generator_image]
    exact hd
  obtain ⟨⟨i, j⟩, _, he⟩ := Finset.mem_image.mp hd'
  refine ⟨(i, j), ?_⟩
  apply assignedGenerator_injective C hV hC p
  exact (assigned_class C hV hC p i j).trans he

theorem class_injective (i : Fin (C.splitMultiplicity p)) :
    Function.Injective (classOf C hV hC p i) := by
  intro j k h
  apply (hV.2 (slot C hV hC p i)).2.2.1
  simpa only [assigned_class] using congrArg (assignedGenerator C hV hC p) h

theorem assigned_mem_generators {i : Fin (C.splitMultiplicity p)}
    {k : Fin (4 * C.splitMultiplicity p - reuseCount C p)}
    (hk : k ∈ Finset.univ.image (classOf C hV hC p i)) :
    assignedGenerator C hV hC p k ∈ generatorSet (C.choice (slot C hV hC p i)).tuple := by
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hk
  rw [assigned_class]
  exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩

theorem class_pair_overlap (i j : Fin (C.splitMultiplicity p)) (hne : i ≠ j) :
    ((Finset.univ.image (classOf C hV hC p i)) ∩
      (Finset.univ.image (classOf C hV hC p j))).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro x hx y hy
  apply assignedGenerator_injective C hV hC p
  have hc := hC.2.1 (slot C hV hC p i) (slot C hV hC p j)
    (fun he => hne (slot_injective C hV hC p he))
  apply Finset.card_le_one.mp hc
  · exact Finset.mem_inter.mpr ⟨assigned_mem_generators C hV hC p (Finset.mem_inter.mp hx).1,
      assigned_mem_generators C hV hC p (Finset.mem_inter.mp hx).2⟩
  · exact Finset.mem_inter.mpr ⟨assigned_mem_generators C hV hC p (Finset.mem_inter.mp hy).1,
      assigned_mem_generators C hV hC p (Finset.mem_inter.mp hy).2⟩

def pattern : EqualityPattern (C.splitMultiplicity p) (reuseCount C p) where
  classOf := classOf C hV hC p
  everyClass := class_surjective C hV hC p
  withinTuple := class_injective C hV hC p
  pairOverlap := class_pair_overlap C hV hC p

def assignment : DirectionAssignment F (C.splitMultiplicity p) (reuseCount C p) :=
  (fun i => (slot C hV hC p i).1, assignedGenerator C hV hC p)

def bits : Bits (C.splitMultiplicity p) :=
  fun i => (C.choice (slot C hV hC p i)).tuple.side

end
end Balanced.Local.ConfigurationPattern

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalTupleReindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local
noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ} (P : EqualityPattern b κ) (σ : Equiv.Perm (Fin b))

def reindexAssignment (a : DirectionAssignment F b κ) : DirectionAssignment F b κ :=
  (a.1 ∘ σ, a.2)

end
end Balanced.Local

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_LocalOrderedPencils
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def BadLocalCoverAt (b : ℕ) (p : Point F) (C : Configuration F) : Prop :=
  ∃ A : Finset (LocalPiece F), A.card ≤ b - 1 ∧
    (∀ x ∈ A, C.AllowedLocalPiece p x) ∧
    C.designatedAt p ⊆ C.partnerSet p ∪ A.biUnion C.localPiecePoints

def OrderedBadPencil (b κ : ℕ) (p : Point F) (used : Fin b → Slot F)
    (C : Configuration F) : Prop :=
  Function.Injective used ∧
    ∃ (P : EqualityPattern b κ) (a : DirectionAssignment F b κ) (bits : Bits b),
      Eligible P a ∧ AdmissibleBadCover P a bits p C.merged ∧
        ∀ i, (used i).1 = a.1 i ∧
          (C.choice (used i)).tuple = prescribedTuple P a bits i ∧
          (C.choice (used i)).line = lineThrough (a.1 i) p

end
end Balanced.Local

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_PartialIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.PartialAlignment
open TupleAlignment
noncomputable section
attribute [local instance] Classical.propDecidable
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

abbrev MarkedPartialOffsets (d : Fin 4 → Direction F)
    (hd : ∀ j, d j ≠ d (j + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (c : F) (J : Finset (Fin 4)) (a : Fin 4 → Bool → F)
    (i : Fin 4) (y : Point F) :=
  {o : PartialOffsets J a //
    (∀ j, OnLine (tuplePositionEquiv d hd σ o.1 j) (g,c)) ∧
      tuplePositionEquiv d hd σ o.1 i = y}

def conditionalHitProbability (T : FourTuple F) (D : Finset (Direction F))
    (a : MergedPairs F) (g : Direction F) (i : Fin 4) (L : Line F) (c : F) : ℝ :=
  (((offsetLaw F).filter {M | ∀ d, d ∈ D → M d = a d}
    (canonical_exposure_supported D a)).toOuterMeasure
    {M | (∀ j, OnLine (tuplePoint M T j) (g,c)) ∧ OnLine (tuplePoint M T i) L}).toReal

def possibleHitOffsets (T : FourTuple F) (D : Finset (Direction F))
    (a : MergedPairs F) (g : Direction F) (i : Fin 4) (L : Line F) : Finset F :=
  Finset.univ.filter (fun c => ∃ M : MergedPairs F,
    (∀ d, d ∈ D → M d = a d) ∧
    (∀ j, OnLine (tuplePoint M T j) (g,c)) ∧ OnLine (tuplePoint M T i) L)

end
end Balanced.PartialAlignment

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_Projective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced

abbrev ProjectiveLine (F : Type*) := Option (Line F)

variable {F : Type*} [Field F]

def ProjectiveIncident (P : ProjectivePoint F) : ProjectiveLine F → Prop
  | some l => ThroughProjective l P
  | none => match P with
    | Sum.inl _ => False
    | Sum.inr _ => True

def dualLine : ProjectivePoint F → ProjectiveLine F
  | Sum.inl p => some (some p.1, -p.2)
  | Sum.inr none => none
  | Sum.inr (some m) => some (none, m)

def dualPoint : ProjectiveLine F → ProjectivePoint F
  | none => Sum.inr none
  | some (none, b) => Sum.inr (some b)
  | some (some m, b) => Sum.inl (m, -b)

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_Projective2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

variable {F : Type*} [Field F]

@[simp] theorem dualPoint_dualLine (P : ProjectivePoint F) :
    dualPoint (dualLine P) = P := by
  cases P with
  | inl p => rcases p with ⟨x,y⟩; simp [dualLine, dualPoint]
  | inr d => cases d <;> rfl

@[simp] theorem dualLine_dualPoint (l : ProjectiveLine F) :
    dualLine (dualPoint l) = l := by
  cases l with
  | none => rfl
  | some l => rcases l with ⟨d,b⟩; cases d <;> simp [dualLine, dualPoint]

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_ProjectiveModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

variable {F : Type*} [Field F]

def homogeneousPoint : ProjectivePoint F → Fin 3 → F
  | Sum.inl p => ![p.1, p.2, 1]
  | Sum.inr none => ![0, 1, 0]
  | Sum.inr (some m) => ![1, m, 0]

def homogeneousLine : ProjectiveLine F → Fin 3 → F
  | none => ![0, 0, 1]
  | some (none, b) => ![1, 0, -b]
  | some (some m, b) => ![-m, 1, -b]

theorem homogeneousPoint_ne_zero (P : ProjectivePoint F) : homogeneousPoint P ≠ 0 := by
  cases P with
  | inl p =>
    intro h
    have h2 := congrFun h 2
    simp [homogeneousPoint] at h2
  | inr d =>
    cases d with
    | none =>
      intro h
      have h1 := congrFun h 1
      simp [homogeneousPoint] at h1
    | some m =>
      intro h
      have h0 := congrFun h 0
      simp [homogeneousPoint] at h0

noncomputable def normalizeProjective (v : Fin 3 → F) : ProjectivePoint F := by
  classical
  exact if v 2 ≠ 0 then Sum.inl (v 0 / v 2, v 1 / v 2)
    else if v 0 ≠ 0 then Sum.inr (some (v 1 / v 0)) else Sum.inr none

@[simp] theorem normalize_homogeneousPoint (P : ProjectivePoint F) :
    normalizeProjective (homogeneousPoint P) = P := by
  cases P with
  | inl p => rcases p with ⟨x,y⟩; simp [normalizeProjective, homogeneousPoint]
  | inr d => cases d <;> simp [normalizeProjective, homogeneousPoint]

theorem normalizeProjective_smul (a : F) (ha : a ≠ 0) (v : Fin 3 → F) :
    normalizeProjective (a • v) = normalizeProjective v := by
  classical
  simp [normalizeProjective, Pi.smul_apply, smul_eq_mul, ha, mul_div_mul_left]

theorem exists_smul_homogeneous_normalize (v : Fin 3 → F) (hv : v ≠ 0) :
    ∃ a : F, a ≠ 0 ∧ a • homogeneousPoint (normalizeProjective v) = v := by
  classical
  by_cases h2 : v 2 ≠ 0
  · refine ⟨v 2, h2, ?_⟩
    ext i
    fin_cases i <;> simp [normalizeProjective, h2, homogeneousPoint, Pi.smul_apply,
      smul_eq_mul, mul_div_cancel₀]
  · have hz2 : v 2 = 0 := not_not.mp h2
    by_cases h0 : v 0 ≠ 0
    · refine ⟨v 0, h0, ?_⟩
      ext i
      fin_cases i <;> simp [normalizeProjective, hz2, h0, homogeneousPoint,
        Pi.smul_apply, smul_eq_mul, mul_div_cancel₀]
    · have hz0 : v 0 = 0 := not_not.mp h0
      have h1 : v 1 ≠ 0 := by
        intro h1
        apply hv
        ext i
        fin_cases i <;> simp_all
      refine ⟨v 1, h1, ?_⟩
      ext i
      fin_cases i <;> simp [normalizeProjective, hz2, hz0, homogeneousPoint,
        Pi.smul_apply, smul_eq_mul]

theorem projective_incident_iff_homogeneous (P : ProjectivePoint F) (l : ProjectiveLine F) :
    ProjectiveIncident P l ↔
      (∑ i : Fin 3, homogeneousLine l i * homogeneousPoint P i) = 0 := by
  cases P with
  | inl p =>
    rcases p with ⟨x,y⟩
    cases l with
    | none => simp [ProjectiveIncident, homogeneousLine, homogeneousPoint, Fin.sum_univ_succ]
    | some l =>
      rcases l with ⟨d,b⟩
      cases d with
      | none =>
        simp only [ProjectiveIncident, homogeneousLine, homogeneousPoint,
          ThroughProjective, OnLine, lineEval]
        simp [Fin.sum_univ_succ]
        constructor <;> intro h <;> linear_combination h
      | some m =>
        simp [ProjectiveIncident, homogeneousLine, homogeneousPoint,
          ThroughProjective, OnLine, lineEval, Fin.sum_univ_succ]
        constructor <;> intro h <;> linear_combination h
  | inr d =>
    cases d with
    | none =>
      cases l with
      | none => simp [ProjectiveIncident, homogeneousLine, homogeneousPoint, Fin.sum_univ_succ]
      | some l =>
        rcases l with ⟨d,b⟩
        cases d <;> simp [ProjectiveIncident, homogeneousLine, homogeneousPoint,
          ThroughProjective, Fin.sum_univ_succ]
    | some m =>
      cases l with
      | none => simp [ProjectiveIncident, homogeneousLine, homogeneousPoint, Fin.sum_univ_succ]
      | some l =>
        rcases l with ⟨d,b⟩
        cases d with
        | none => simp [ProjectiveIncident, homogeneousLine, homogeneousPoint,
            ThroughProjective, Fin.sum_univ_succ]
        | some a =>
          simp [ProjectiveIncident, homogeneousLine, homogeneousPoint,
            ThroughProjective, Fin.sum_univ_succ]
          constructor <;> intro h <;> linear_combination -h

theorem homogeneousLine_ne_zero (l : ProjectiveLine F) : homogeneousLine l ≠ 0 := by
  cases l with
  | none =>
    intro h
    have hh := congrFun h 2
    simp [homogeneousLine] at hh
  | some l =>
    rcases l with ⟨d,b⟩
    cases d with
    | none =>
      intro h
      have hh := congrFun h 0
      simp [homogeneousLine] at hh
    | some m =>
      intro h
      have hh := congrFun h 1
      simp [homogeneousLine] at hh

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_ProjectiveNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced
namespace ProjectiveNormalization

open scoped BigOperators

variable {F : Type*} [Field F]

structure Collineation (F : Type*) [Field F] where
  point : ProjectivePoint F ≃ ProjectivePoint F
  line : ProjectiveLine F ≃ ProjectiveLine F
  incident : ∀ P l, ProjectiveIncident (point P) (line l) ↔ ProjectiveIncident P l

noncomputable def pointEquiv (e : V F ≃ₗ[F] V F) :
    ProjectivePoint F ≃ ProjectivePoint F where
  toFun P := normalizeProjective (e (homogeneousPoint P))
  invFun P := normalizeProjective (e.symm (homogeneousPoint P))
  left_inv P := by
    obtain ⟨a, ha, hs⟩ := exists_smul_homogeneous_normalize
      (e (homogeneousPoint P)) (e.map_ne_zero_iff.mpr (homogeneousPoint_ne_zero P))
    have he : a • e.symm (homogeneousPoint (normalizeProjective (e (homogeneousPoint P)))) =
        homogeneousPoint P := by
      simpa only [map_smul, e.symm_apply_apply] using congrArg e.symm hs
    dsimp only
    rw [← normalizeProjective_smul a ha, he, normalize_homogeneousPoint]
  right_inv P := by
    obtain ⟨a, ha, hs⟩ := exists_smul_homogeneous_normalize
      (e.symm (homogeneousPoint P)) (e.symm.map_ne_zero_iff.mpr (homogeneousPoint_ne_zero P))
    have he : a • e (homogeneousPoint (normalizeProjective (e.symm (homogeneousPoint P)))) =
        homogeneousPoint P := by
      simpa only [map_smul, e.apply_symm_apply] using congrArg e hs
    dsimp only
    rw [← normalizeProjective_smul a ha, he, normalize_homogeneousPoint]

noncomputable def normalizeLine (v : V F) : ProjectiveLine F := by
  classical
  exact if v 1 ≠ 0 then some (some (-v 0 / v 1), -v 2 / v 1)
    else if v 0 ≠ 0 then some (none, -v 2 / v 0) else none

@[simp] theorem normalize_homogeneousLine (l : ProjectiveLine F) :
    normalizeLine (homogeneousLine l) = l := by
  cases l with
  | none => simp [normalizeLine, homogeneousLine]
  | some l =>
    rcases l with ⟨d,b⟩
    cases d <;> simp [normalizeLine, homogeneousLine]

theorem normalizeLine_smul (a : F) (ha : a ≠ 0) (v : V F) :
    normalizeLine (a • v) = normalizeLine v := by
  classical
  simp [normalizeLine, Pi.smul_apply, smul_eq_mul, ha, neg_div,
    mul_div_mul_left]

theorem exists_smul_homogeneousLine (v : V F) (hv : v ≠ 0) :
    ∃ a : F, a ≠ 0 ∧ a • homogeneousLine (normalizeLine v) = v := by
  classical
  by_cases h1 : v 1 ≠ 0
  · refine ⟨v 1, h1, ?_⟩
    ext i
    fin_cases i <;> simp [normalizeLine, h1, homogeneousLine, Pi.smul_apply,
      smul_eq_mul, mul_div_cancel₀]
  · have hz1 : v 1 = 0 := not_not.mp h1
    by_cases h0 : v 0 ≠ 0
    · refine ⟨v 0, h0, ?_⟩
      ext i
      fin_cases i <;> simp [normalizeLine, hz1, h0, homogeneousLine,
        Pi.smul_apply, smul_eq_mul, mul_div_cancel₀]
    · have hz0 : v 0 = 0 := not_not.mp h0
      have h2 : v 2 ≠ 0 := by
        intro h2
        apply hv
        ext i
        fin_cases i <;> simp_all
      refine ⟨v 2, h2, ?_⟩
      ext i
      fin_cases i <;> simp [normalizeLine, hz1, hz0, homogeneousLine,
        Pi.smul_apply, smul_eq_mul]

noncomputable def lineEquiv (e : V F ≃ₗ[F] V F) :
    ProjectiveLine F ≃ ProjectiveLine F where
  toFun l := normalizeLine (e (homogeneousLine l))
  invFun l := normalizeLine (e.symm (homogeneousLine l))
  left_inv l := by
    obtain ⟨a, ha, hs⟩ := exists_smul_homogeneousLine
      (e (homogeneousLine l)) (e.map_ne_zero_iff.mpr (homogeneousLine_ne_zero l))
    have he : a • e.symm (homogeneousLine (normalizeLine (e (homogeneousLine l)))) =
        homogeneousLine l := by
      simpa only [map_smul, e.symm_apply_apply] using congrArg e.symm hs
    dsimp only
    rw [← normalizeLine_smul a ha, he, normalize_homogeneousLine]
  right_inv l := by
    obtain ⟨a, ha, hs⟩ := exists_smul_homogeneousLine
      (e.symm (homogeneousLine l)) (e.symm.map_ne_zero_iff.mpr (homogeneousLine_ne_zero l))
    have he : a • e (homogeneousLine (normalizeLine (e.symm (homogeneousLine l)))) =
        homogeneousLine l := by
      simpa only [map_smul, e.apply_symm_apply] using congrArg e hs
    dsimp only
    rw [← normalizeLine_smul a ha, he, normalize_homogeneousLine]

noncomputable def ofLinear (e f : V F ≃ₗ[F] V F)
    (hpair : ∀ v w, (∑ i, f w i * e v i) = ∑ i, w i * v i) : Collineation F where
  point := pointEquiv e
  line := lineEquiv f
  incident P l := by
    rw [projective_incident_iff_homogeneous, projective_incident_iff_homogeneous]
    obtain ⟨a, ha, hs⟩ := exists_smul_homogeneous_normalize
      (e (homogeneousPoint P)) (e.map_ne_zero_iff.mpr (homogeneousPoint_ne_zero P))
    obtain ⟨b, hb, ht⟩ := exists_smul_homogeneousLine
      (f (homogeneousLine l)) (f.map_ne_zero_iff.mpr (homogeneousLine_ne_zero l))
    have hp := hpair (homogeneousPoint P) (homogeneousLine l)
    rw [← hs, ← ht] at hp
    have hp' : (b * a) *
        (∑ i, homogeneousLine (lineEquiv f l) i * homogeneousPoint (pointEquiv e P) i) =
        ∑ i, homogeneousLine l i * homogeneousPoint P i := by
      rw [Finset.mul_sum]
      convert hp using 1
      all_goals try with_reducible_and_instances rfl
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Pi.smul_apply, smul_eq_mul, pointEquiv, lineEquiv, Equiv.coe_fn_mk]
      ring
    rw [← hp', mul_eq_zero]
    simp [ha, hb]

namespace Collineation

noncomputable def refl : Collineation F where
  point := Equiv.refl _
  line := Equiv.refl _
  incident _ _ := Iff.rfl

noncomputable def trans (a b : Collineation F) : Collineation F where
  point := a.point.trans b.point
  line := a.line.trans b.line
  incident P l := (b.incident (a.point P) (a.line l)).trans (a.incident P l)

end Collineation

noncomputable def addCoordinate (i j : Fin 3) (hij : i ≠ j) (c : F) : Collineation F :=
  ofLinear (coordAdd i j hij c) (coordAdd j i hij.symm (-c)) (by
    intro v w
    fin_cases i <;> fin_cases j <;> (try exact (hij rfl).elim) <;>
      simp [coordAdd, Fin.sum_univ_three] <;> ring)

noncomputable def permuteCoordinates (e : Equiv.Perm (Fin 3)) : Collineation F :=
  ofLinear (coordPerm e) (coordPerm e) (by
    intro v w
    exact Equiv.sum_comp e (fun i => w i * v i))

noncomputable def pointToInfinity (P : ProjectivePoint F) : Collineation F :=
  match P with
  | Sum.inl p =>
      ((addCoordinate 0 2 (by decide) (-p.1)).trans
        (addCoordinate 1 2 (by decide) (-p.2))).trans
        (permuteCoordinates (Equiv.swap 1 2))
  | Sum.inr none => Collineation.refl
  | Sum.inr (some m) =>
      (addCoordinate 1 0 (by decide) (-m)).trans
        (permuteCoordinates (Equiv.swap 0 1))

noncomputable def verticalToInfinity (b : F) : Collineation F :=
  (addCoordinate 0 2 (by decide) (-b)).trans
    (permuteCoordinates (Equiv.swap 0 2))

end ProjectiveNormalization
end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_RedeiPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.StabilityPolynomial

open MvPolynomial
open scoped BigOperators

variable {F : Type*} [Field F]

noncomputable def redeiFactor (p : Point F) : MvPolynomial (Fin 2) F :=
  X 0 + C p.1 * X 1 - C p.2

end Balanced.StabilityPolynomial

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_UnusedOffsetIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open scoped Classical

namespace Balanced.UnusedOffsetIncidence

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

abbrev Offsets (D : Finset (Direction F)) := D → Bool → F

end Balanced.UnusedOffsetIncidence

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalFourEvents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.FourEvents

noncomputable section
open scoped Classical BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ}

def tuplePoints (P : EqualityPattern b κ) (a : DirectionAssignment F b κ)
    (bits : Bits b) (M : MergedPairs F) (i : Fin b) : Finset (Point F) :=
  Finset.univ.image (fun j => prescribedPoint P a bits M (i, j))

def usedDirections (a : DirectionAssignment F b κ) : Finset (Direction F) :=
  Finset.univ.image a.2

def usingTuples (P : EqualityPattern b κ) (a : DirectionAssignment F b κ)
    (d : Direction F) : Finset (Fin b) :=
  Finset.univ.filter (fun i => ∃ j, a.2 (P.classOf i j) = d)

omit [Field F] [Fintype F] in
@[simp] theorem usingTuples_class_card (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (ha : Function.Injective a.2)
    (c : Fin (4 * b - κ)) :
    (usingTuples P a (a.2 c)).card = classUseCount P c := by
  simp only [usingTuples, classUseCount, ha.eq_iff]

omit [Fintype F] in
@[simp] theorem mem_tuplePoints (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (M : MergedPairs F)
    (i : Fin b) (x : Point F) :
    x ∈ tuplePoints P a bits M i ↔ ∃ j, prescribedPoint P a bits M (i, j) = x := by
  simp [tuplePoints]

def Precoverage (P : EqualityPattern b κ) (a : DirectionAssignment F b κ)
    (bits : Bits b) (p : Point F) (M : MergedPairs F) : Prop :=
  (prescribedPartners P a bits p M).Nonempty

def UsedPairExtra (P : EqualityPattern b κ) (a : DirectionAssignment F b κ)
    (bits : Bits b) (M : MergedPairs F) : Prop :=
  ∃ d ∈ usedDirections a, ∃ i, i ∉ usingTuples P a d ∧
    ∃ x ∈ tuplePoints P a bits M i, x ∈ mergedPoints M d

def ForbiddenCollinearTriple (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (M : MergedPairs F) : Prop :=
  ∃ l : Line F, (∀ i, l ≠ lineThrough (a.1 i) p) ∧
    (∀ c s, l ≠ constituent M (a.2 c) s) ∧
    3 ≤ (prescribedDesignated P a bits M ∩ linePoints l).card

def UnusedNoncollinearTriple (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (M : MergedPairs F) : Prop :=
  ∃ d, d ∉ usedDirections a ∧ ∃ U : Finset (Point F), U.card = 3 ∧
    U ⊆ prescribedDesignated P a bits M ∩ mergedPoints M d ∧
    ¬ ∃ l : Line F, U ⊆ linePoints l

def UnusedPrecoverage (P : EqualityPattern b κ) (a : DirectionAssignment F b κ)
    (bits : Bits b) (p : Point F) (M : MergedPairs F) : Prop :=
  ∃ d, d ∉ usedDirections a ∧ ∃ s, OnLine p (constituent M d s) ∧
    ∃ x ∈ prescribedDesignated P a bits M, OnLine x (constituent M d (!s))

def extraCapacity (P : EqualityPattern b κ) (a : DirectionAssignment F b κ) :
    LocalPiece F → ℕ
  | Sum.inr (Sum.inr d) => 2 * ((usingTuples P a d).card - 1)
  | _ => 0

end
end Balanced.Local.FourEvents

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalUnusedTripleProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical

namespace Balanced.Local.UnusedTripleProbability

open PrescribedGeometry

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ}

def unusedOffsets (a : DirectionAssignment F b κ) (M : MergedPairs F) :
    UnusedOffsetIncidence.Offsets (unusedDirections a) := fun d => M d.1

end Balanced.Local.UnusedTripleProbability

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_AlignedUnusedTripleBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical

namespace Balanced.Local.UnusedTripleProbability

open PrescribedGeometry

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ}

def unusedArrayEquiv (P : EqualityPattern b κ) (a : DirectionAssignment F b κ) :
    AlignedUnused.UnusedArray P a ≃
      UnusedOffsetIncidence.Offsets (unusedDirections a) where
  toFun v d := v ⟨d.1, (mem_unusedDirections d.1).mp d.2⟩
  invFun o d := o ⟨d.1, (mem_unusedDirections d.1).mpr d.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Balanced.Local.UnusedTripleProbability

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalUsedEventUnion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.UsedEventUnion

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

open UnusedOffsetProbability

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ}

def usedConstituentTest (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (c : Fin (4 * b - κ)) (ij : Fin b × Fin 4) (s : Bool)
    (M : MergedPairs F) : Prop :=
  Admissible P a bits p M ∧ (∀ j, P.classOf ij.1 j ≠ c) ∧
    OnLine (prescribedPoint P a bits M ij) (constituent M (a.2 c) s)

def collinearTest (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (i j k : Fin b × Fin 4) (M : MergedPairs F) : Prop :=
  Admissible P a bits p M ∧
    i.1 ≠ j.1 ∧ i.1 ≠ k.1 ∧ j.1 ≠ k.1 ∧
    prescribedPoint P a bits M i ≠ prescribedPoint P a bits M j ∧
    prescribedPoint P a bits M i ≠ prescribedPoint P a bits M k ∧
    prescribedPoint P a bits M j ≠ prescribedPoint P a bits M k ∧
    OnLine (prescribedPoint P a bits M k)
      (joiningLine (prescribedPoint P a bits M i) (prescribedPoint P a bits M j)) ∧
    (∀ t, joiningLine (prescribedPoint P a bits M i) (prescribedPoint P a bits M j) ≠
      lineThrough (a.1 t) p) ∧
    (∀ c s, joiningLine (prescribedPoint P a bits M i) (prescribedPoint P a bits M j) ≠
      constituent M (a.2 c) s)

def alignedAverage (P : EqualityPattern b κ) (bits : Bits b) (p : Point F)
    (w : DirectionAssignment F b κ → ℝ)
    (E : DirectionAssignment F b κ → MergedPairs F → Prop) : ℝ :=
  ∑ a, w a * conditionedOffsetProbability (Aligned P a bits p) (E a)

end
end Balanced.Local.UsedEventUnion

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_AlignedUsedTestTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.UsedEventUnion

open AlignedUnused AlignedGlobal RootChildPartition
noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ}

def usedGeometricGuards (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (M : MergedPairs F) : Prop :=
  Aligned P a bits p M ∧ Function.Injective (prescribedPoint P a bits M) ∧
    (∀ ij, prescribedPoint P a bits M ij ≠ p) ∧
    (∀ i c s, lineThrough (a.1 i) p ≠ constituent M (a.2 c) s)

def geometricUsedTest (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (c : Fin (4*b-κ)) (ij : Fin b × Fin 4) (s : Bool)
    (M : MergedPairs F) : Prop :=
  usedGeometricGuards P a bits p M ∧ (∀ j, P.classOf ij.1 j ≠ c) ∧
    OnLine (prescribedPoint P a bits M ij) (constituent M (a.2 c) s)

def geometricCollinearTest (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (i j k : Fin b × Fin 4) (M : MergedPairs F) : Prop :=
  usedGeometricGuards P a bits p M ∧
    i.1 ≠ j.1 ∧ i.1 ≠ k.1 ∧ j.1 ≠ k.1 ∧
    prescribedPoint P a bits M i ≠ prescribedPoint P a bits M j ∧
    prescribedPoint P a bits M i ≠ prescribedPoint P a bits M k ∧
    prescribedPoint P a bits M j ≠ prescribedPoint P a bits M k ∧
    OnLine (prescribedPoint P a bits M k)
      (joiningLine (prescribedPoint P a bits M i) (prescribedPoint P a bits M j)) ∧
    (∀ t, joiningLine (prescribedPoint P a bits M i) (prescribedPoint P a bits M j) ≠
      lineThrough (a.1 t) p) ∧
    (∀ c s, joiningLine (prescribedPoint P a bits M i) (prescribedPoint P a bits M j) ≠
      constituent M (a.2 c) s)

end
end Balanced.Local.UsedEventUnion

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalParentMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.ParentMap

noncomputable section
open scoped Classical

variable {b : ℕ}

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {κ : ℕ} (P : EqualityPattern b κ)
variable (a : DirectionAssignment F b κ) (bits : Bits b) (M : MergedPairs F)

omit [Fintype F] [DecidableEq F] in

theorem endpoint_on_constituent (ha : Eligible P a) (i : Fin b) (r : Fin 4)
    (t : Bool) :
    OnLine (prescribedPoint P a bits M (i, endpointIndex r (bits i r) t))
      (constituent M (a.2 (P.classOf i r)) t) := by
  by_cases ht : t = bits i r
  · simpa [endpointIndex, ht] using
      PrescribedGeometry.prescribedPoint_on_left (M := M) ha i r
  · have ht' : t = !(bits i r) := by
      cases t <;> cases h : bits i r <;> simp_all
    rw [endpointIndex, ite_eq_right ht]
    simpa only [sub_add_cancel, ht'] using
      PrescribedGeometry.prescribedPoint_on_right (bits := bits) (M := M) ha i (r - 1)

omit [Fintype F] [DecidableEq F] in

theorem child_endpoint_eq_projection (ha : Eligible P a) (p : Point F)
    (hA : Aligned P a bits p M) (root child : Fin b) (r s : Fin 4)
    (hshared : P.classOf root r = P.classOf child s) (t : Bool) :
    prescribedPoint P a bits M (child, endpointIndex s (bits child s) t) =
      lineIntersection
        (lineThrough (a.2 (P.classOf root r))
          (prescribedPoint P a bits M (root, endpointIndex r (bits root r) t)))
        (lineThrough (a.1 child) p) := by
  have hroot := endpoint_on_constituent P a bits M ha root r t
  have hchild : OnLine
      (prescribedPoint P a bits M (child, endpointIndex s (bits child s) t))
      (constituent M (a.2 (P.classOf root r)) t) := by
    simpa only [hshared] using endpoint_on_constituent P a bits M ha child s t
  have hline : lineThrough (a.2 (P.classOf root r))
      (prescribedPoint P a bits M (root, endpointIndex r (bits root r) t)) =
        constituent M (a.2 (P.classOf root r)) t :=
    (line_eq_lineThrough _ _ hroot).symm
  rw [hline]
  have hd : a.2 (P.classOf root r) ≠ a.1 child := by
    simpa only [hshared] using ha.2.2 child s
  apply common_point_eq_of_lines_ne
    (constituent M (a.2 (P.classOf root r)) t) (lineThrough (a.1 child) p)
    (fun h => hd (congrArg Prod.fst h))
  · exact hchild
  · exact hA _
  · exact onLine_lineIntersection_left _ _ hd
  · exact onLine_lineIntersection_right _ _ hd

end
end Balanced.Local.ParentMap

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_GlobalAlignedParentCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.AlignedGlobal

open RootChildPartition TupleAlignment AlignedUnused

noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [DecidableEq F]

abbrev freeCoordinates {b κ : ℕ} (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (R : Finset (Fin b)) (M : AlignedOffsets P a bits p) : FreeIndex P R → F :=
  (coordinates P R a bits p M).1

def underlyingFree {b κ : ℕ} (P : EqualityPattern b κ) (R : Finset (Fin b))
    (root child : Fin b) (r s : Fin 4) (bits : Bits b) (hne : root ≠ child)
    (hdep : dependentOccurrences P R = ParentMap.dependent child s)
    (ij : Fin b × Fin 4) : FreeIndex P R :=
  ⟨ParentMap.underlying root child r s (bits root r) (bits child s) ij, by
    rw [hdep]
    exact ParentMap.underlying_not_dependent root child r s
      (bits root r) (bits child s) hne ij⟩

theorem free_point_eq_coordinate {b κ : ℕ} (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (R : Finset (Fin b)) (M : AlignedOffsets P a bits p) (ij : FreeIndex P R) :
    prescribedPoint P a bits M.1 ij.1 =
      ((linePointEquiv (a.1 ij.1.1) (lineEval (a.1 ij.1.1) p)).symm
        (freeCoordinates P a bits p R M ij)).1 := by
  exact (congrArg Subtype.val ((linePointEquiv (a.1 ij.1.1)
    (lineEval (a.1 ij.1.1) p)).symm_apply_apply
      ⟨prescribedPoint P a bits M.1 ij.1, M.2 ij.1⟩)).symm

def pointFromCoordinate {b κ : ℕ} (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (root child : Fin b) (r s : Fin 4) (ij : Fin b × Fin 4) (x : F) : Point F :=
  let u := ParentMap.underlying root child r s (bits root r) (bits child s) ij
  let z := ((linePointEquiv (a.1 u.1) (lineEval (a.1 u.1) p)).symm x).1
  if ij ∈ ParentMap.dependent child s then
    lineIntersection (lineThrough (a.2 (P.classOf root r)) z)
      (lineThrough (a.1 ij.1) p)
  else z

omit [DecidableEq F] in
theorem point_eq_parent_projection {b κ : ℕ} (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (ha : Eligible P a) (bits : Bits b)
    (p : Point F) (M : AlignedOffsets P a bits p)
    (root child : Fin b) (r s : Fin 4)
    (hshared : P.classOf root r = P.classOf child s) (ij : Fin b × Fin 4) :
    prescribedPoint P a bits M.1 ij =
      if ij ∈ ParentMap.dependent child s then
        lineIntersection (lineThrough (a.2 (P.classOf root r))
          (prescribedPoint P a bits M.1
            (ParentMap.underlying root child r s (bits root r) (bits child s) ij)))
          (lineThrough (a.1 ij.1) p)
      else prescribedPoint P a bits M.1
        (ParentMap.underlying root child r s (bits root r) (bits child s) ij) := by
  by_cases hd : ij ∈ ParentMap.dependent child s
  · rw [ite_eq_left hd]
    simp only [ParentMap.dependent, Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl
    · rw [ParentMap.underlying_first]
      simpa only [ParentMap.endpointIndex, ite_true] using
        ParentMap.child_endpoint_eq_projection P a bits M.1 ha p M.2
          root child r s hshared (bits child s)
    · rw [ParentMap.underlying_second]
      have hbit : (!(bits child s)) ≠ bits child s := by cases bits child s <;> decide
      simpa only [ParentMap.endpointIndex, ite_eq_right hbit] using
        ParentMap.child_endpoint_eq_projection P a bits M.1 ha p M.2
          root child r s hshared (!(bits child s))
  · rw [ite_eq_right hd, ParentMap.underlying_fixed root child r s
      (bits root r) (bits child s) hd]

theorem point_eq_pointFromCoordinate {b κ : ℕ} (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (ha : Eligible P a) (bits : Bits b)
    (p : Point F) (R : Finset (Fin b)) (root child : Fin b) (r s : Fin 4)
    (hne : root ≠ child) (hshared : P.classOf root r = P.classOf child s)
    (hdep : dependentOccurrences P R = ParentMap.dependent child s)
    (M : AlignedOffsets P a bits p) (ij : Fin b × Fin 4) :
    prescribedPoint P a bits M.1 ij = pointFromCoordinate P a bits p root child r s ij
      (freeCoordinates P a bits p R M (underlyingFree P R root child r s bits hne hdep ij)) := by
  have hbase := free_point_eq_coordinate P a bits p R M
    (underlyingFree P R root child r s bits hne hdep ij)
  change prescribedPoint P a bits M.1
      (ParentMap.underlying root child r s (bits root r) (bits child s) ij) = _ at hbase
  exact (point_eq_parent_projection P a ha bits p M root child r s hshared ij).trans
    (congrArg (fun z => if ij ∈ ParentMap.dependent child s then
      lineIntersection (lineThrough (a.2 (P.classOf root r)) z)
        (lineThrough (a.1 ij.1) p) else z) hbase)

omit [DecidableEq F] in
theorem pointFromCoordinate_free {b κ : ℕ} (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (root child : Fin b) (r s : Fin 4) (ij : Fin b × Fin 4)
    (hij : ij ∉ ParentMap.dependent child s) :
    Function.Injective (pointFromCoordinate P a bits p root child r s ij) ∧
      ∀ x, OnLine (pointFromCoordinate P a bits p root child r s ij x)
        (lineThrough (a.1 ij.1) p) := by
  have heq (x : F) : pointFromCoordinate P a bits p root child r s ij x =
      ((linePointEquiv (a.1 ij.1) (lineEval (a.1 ij.1) p)).symm x).1 := by
    dsimp only [pointFromCoordinate]
    rw [ite_eq_right hij, ParentMap.underlying_fixed root child r s
      (bits root r) (bits child s) hij]
  constructor
  · intro x y h
    rw [heq, heq] at h
    exact (linePointEquiv (a.1 ij.1) (lineEval (a.1 ij.1) p)).symm.injective
      (Subtype.ext h)
  · intro x
    rw [heq]
    exact ((linePointEquiv (a.1 ij.1) (lineEval (a.1 ij.1) p)).symm x).2

structure PointSystem {b κ : ℕ} (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (R : Finset (Fin b)) where
  underlying : (Fin b × Fin 4) → FreeIndex P R
  point : (Fin b × Fin 4) → F → Point F
  free_fixed : ∀ v : FreeIndex P R, underlying v.1 = v
  free_injective : ∀ v : FreeIndex P R, Function.Injective (point v.1)
  free_onLine : ∀ (v : FreeIndex P R) x, OnLine (point v.1 x) (lineThrough (a.1 v.1.1) p)
  realizes : ∀ (M : AlignedOffsets P a bits p) ij,
    prescribedPoint P a bits M.1 ij = point ij ((coordinates P R a bits p M).1 (underlying ij))

def pointSystemOfNoDependents {b κ : ℕ} (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (R : Finset (Fin b)) (hdep : dependentOccurrences P R = ∅) :
    PointSystem P a bits p R where
  underlying ij := ⟨ij, by rw [hdep]; simp⟩
  point ij x := ((linePointEquiv (a.1 ij.1) (lineEval (a.1 ij.1) p)).symm x).1
  free_fixed v := rfl
  free_injective v := by
    intro x y h
    exact (linePointEquiv (a.1 v.1.1) (lineEval (a.1 v.1.1) p)).symm.injective (Subtype.ext h)
  free_onLine v x := ((linePointEquiv (a.1 v.1.1) (lineEval (a.1 v.1.1) p)).symm x).2
  realizes M ij := free_point_eq_coordinate P a bits p R M ⟨ij, by rw [hdep]; simp⟩

def pointSystemOfLinkedPair {b κ : ℕ} (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (ha : Eligible P a) (bits : Bits b)
    (p : Point F) (R : Finset (Fin b)) (root child : Fin b) (r s : Fin 4)
    (hne : root ≠ child) (hshared : P.classOf root r = P.classOf child s)
    (hdep : dependentOccurrences P R = ParentMap.dependent child s) :
    PointSystem P a bits p R where
  underlying := underlyingFree P R root child r s bits hne hdep
  point := pointFromCoordinate P a bits p root child r s
  free_fixed v := by
    apply Subtype.ext
    exact ParentMap.underlying_fixed root child r s (bits root r) (bits child s)
      (by rw [← hdep]; exact v.2)
  free_injective v := (pointFromCoordinate_free P a bits p root child r s v.1
    (by rw [← hdep]; exact v.2)).1
  free_onLine v := (pointFromCoordinate_free P a bits p root child r s v.1
    (by rw [← hdep]; exact v.2)).2
  realizes M ij := point_eq_pointFromCoordinate P a ha bits p R root child r s
    hne hshared hdep M ij

end
end Balanced.Local.AlignedGlobal

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_MeasureLocalLemma
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
open MeasureTheory

namespace Balanced.CylinderConditioning

variable {ι Ω : Type*} [DecidableEq ι] [MeasurableSpace Ω]

theorem local_lemma (μ : Measure Ω) [IsProbabilityMeasure μ]
    (B : ι → Set Ω) (hB : ∀ i, MeasurableSet (B i))
    (N : ι → Finset ι) (x : ι → ℝ)
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
    (hp : ∀ i, μ.real (B i) ≤ x i * ∏ j ∈ N i, (1 - x j))
    (hind : ∀ i T, i ∉ T → Disjoint T (N i) →
      μ.real (B i ∩ avoid B T) = μ.real (B i) * μ.real (avoid B T)) :
    ∀ S, 0 < μ.real (avoid B S) ∧ ∀ i, i ∉ S →
      μ.real (avoid B S ∩ B i) ≤ x i * μ.real (avoid B S) := by
  have hcore := LocalLemma.avoidance_induction
    (fun S => μ.real (avoid B S)) (fun i => μ.real (B i)) x N
    (by simp) (fun S => measureReal_nonneg) hx0 hx1 hp
    (by
      intro S i hiS
      have hsplit := measureReal_inter_add_sdiff (μ := μ) (s := avoid B S) (hB i)
      rw [avoid_insert]
      have hiT : i ∉ S \ N i := fun hi => hiS (Finset.mem_sdiff.mp hi).1
      have hd : Disjoint (S \ N i) (N i) := by simp [Finset.disjoint_left]
      have hm : μ.real (avoid B S ∩ B i) ≤ μ.real (B i ∩ avoid B (S \ N i)) := by
        apply measureReal_mono _ (by finiteness)
        intro ω hω
        exact ⟨hω.2, avoid_antitone B Finset.sdiff_subset hω.1⟩
      rw [hind i (S \ N i) hiT hd] at hm
      linarith)
  intro S
  refine ⟨(hcore S).1, ?_⟩
  intro i hiS
  have hstep := (hcore S).2 i hiS
  have hsplit := measureReal_inter_add_sdiff (μ := μ) (s := avoid B S) (hB i)
  rw [avoid_insert] at hstep
  nlinarith

end Balanced.CylinderConditioning

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_HalfWeightLocalLemma
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
open MeasureTheory

namespace Balanced.CylinderConditioning

variable {ι Ω : Type*} [DecidableEq ι] [MeasurableSpace Ω]

theorem local_lemma_of_half_weight (μ : Measure Ω) [IsProbabilityMeasure μ]
    (B : ι → Set Ω) (hB : ∀ i, MeasurableSet (B i))
    (N : ι → Finset ι) (x : ι → ℝ)
    (hx0 : ∀ i, 0 ≤ x i) (hxhalf : ∀ i, x i ≤ 1 / 2)
    (hp : ∀ i, μ.real (B i) ≤ x i / 2)
    (hweight : ∀ i, ∑ j ∈ N i, x j ≤ 1 / 2)
    (hind : ∀ i T, i ∉ T → Disjoint T (N i) →
      μ.real (B i ∩ avoid B T) = μ.real (B i) * μ.real (avoid B T)) :
    ∀ S, 0 < μ.real (avoid B S) ∧ ∀ i, i ∉ S →
      μ.real (avoid B S ∩ B i) ≤ x i * μ.real (avoid B S) := by
  apply local_lemma μ B hB N x hx0 (fun i => by linarith [hxhalf i]) _ hind
  intro i
  have hprod := Balanced.one_sub_sum_le_avoidance_prod (N i) x
    (fun j _ => hx0 j) (fun j _ => by linarith [hxhalf j])
  have hlower : (1 / 2 : ℝ) ≤ ∏ j ∈ N i, (1 - x j) := by
    linarith [hweight i]
  have hm := mul_le_mul_of_nonneg_left hlower (hx0 i)
  linarith [hp i]

theorem local_lemma_cylinder_exp (μ : Measure Ω) [IsProbabilityMeasure μ]
    (B : ι → Set Ω) (hB : ∀ i, MeasurableSet (B i))
    (N : ι → Finset ι) (x : ι → ℝ)
    (hx0 : ∀ i, 0 ≤ x i) (hxhalf : ∀ i, x i ≤ 1 / 2)
    (hp : ∀ i, μ.real (B i) ≤ x i / 2)
    (hweight : ∀ i, ∑ j ∈ N i, x j ≤ 1 / 2)
    (hind : ∀ i T, i ∉ T → Disjoint T (N i) →
      μ.real (B i ∩ avoid B T) = μ.real (B i) * μ.real (avoid B T))
    (C : Set Ω) (T U : Finset ι) (hdisj : Disjoint T U)
    (hC : μ.real (C ∩ avoid B T) = μ.real C * μ.real (avoid B T))
    (s : ℝ) (hs : ∑ i ∈ U, x i ≤ s / 4) :
    0 < μ.real (avoid B (T ∪ U)) ∧
      μ.real (C ∩ avoid B (T ∪ U)) / μ.real (avoid B (T ∪ U)) ≤
        Real.exp (s / 2) * μ.real C := by
  have h := local_lemma_of_half_weight μ B hB N x hx0 hxhalf hp hweight hind
  refine ⟨(h _).1, ?_⟩
  have hc := conditional_event_bound μ B x hB (fun i => by linarith [hxhalf i])
    (fun S i hi => (h S).2 i hi) C T U hdisj (h _).1 hC
  have he := Balanced.prod_inv_one_sub_le_exp_half U x s
    (fun i _ => hx0 i) (fun i _ => hxhalf i) hs
  calc
    μ.real (C ∩ avoid B (T ∪ U)) / μ.real (avoid B (T ∪ U)) ≤
        μ.real C * ∏ i ∈ U, (1 - x i)⁻¹ := hc
    _ ≤ μ.real C * Real.exp (s / 2) :=
      mul_le_mul_of_nonneg_left he measureReal_nonneg
    _ = Real.exp (s / 2) * μ.real C := mul_comm _ _

end Balanced.CylinderConditioning

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_PurposefulIndices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.Surplus

noncomputable section
open scoped BigOperators Classical

def purposefulDirections {F : Type*} [DecidableEq F] {b κ : ℕ} (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (d : Direction F) : Finset (Fin b × Fin 4) :=
  Finset.univ.filter (fun ij =>
    a.2 (P.classOf ij.1 ij.2) = d ∨ a.2 (P.classOf ij.1 (ij.2 + 1)) = d)

end
end Balanced.Local.Surplus

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalCoverMarking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.Surplus

noncomputable section
open scoped BigOperators Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ} (P : EqualityPattern b κ)
  (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
  (M : MergedPairs F)

structure CoverAssignment (A : Finset (LocalPiece F)) where
  piece : Fin b × Fin 4 → Option (LocalPiece F)
  precovered : ∀ ij, piece ij = none ↔
    prescribedPoint P a bits M ij ∈ prescribedPartners P a bits p M
  covered : ∀ ij L, piece ij = some L → L ∈ A ∧
    prescribedPoint P a bits M ij ∈ piecePoints M L

def pieceExtra (t : Direction F → ℕ) : LocalPiece F → ℕ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 0
  | Sum.inr (Sum.inr d) => t d - 1

def pieceCapacity (t : Direction F → ℕ) (L : LocalPiece F) : ℕ :=
  2 + 2 * pieceExtra t L

def assignmentFibre {A : Finset (LocalPiece F)}
    (f : CoverAssignment P a bits p M A) (L : LocalPiece F) :
    Finset (Fin b × Fin 4) :=
  Finset.univ.filter (fun ij => f.piece ij = some L)

def protectedFibre {A : Finset (LocalPiece F)}
    (f : CoverAssignment P a bits p M A) : LocalPiece F → Finset (Fin b × Fin 4)
  | Sum.inl _ => ∅
  | Sum.inr (Sum.inl _) => ∅
  | Sum.inr (Sum.inr d) =>
      assignmentFibre P a bits p M f (Sum.inr (Sum.inr d)) ∩
        purposefulDirections P a d

end
end Balanced.Local.Surplus

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_LocalMarkedAnchors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.MarkedAnchors

noncomputable section
open scoped Classical
open Surplus

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ} (P : EqualityPattern b κ)
variable (a : DirectionAssignment F b κ) (bits : Bits b)
variable (p : Point F) (M : MergedPairs F)

omit [Field F] [Fintype F] in
@[simp] theorem mem_purposefulDirections (ha : Function.Injective a.2)
    (c : Fin (4 * b - κ)) (v : Fin b × Fin 4) :
    v ∈ purposefulDirections P a (a.2 c) ↔ AnchorExclusion.Purposeful P c v := by
  simp [purposefulDirections, AnchorExclusion.Purposeful, ha.eq_iff]

end
end Balanced.Local.MarkedAnchors

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalConditionSpec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.ConditionSpec

noncomputable section
open scoped Classical
open Surplus MarkedAnchors

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ} (P : EqualityPattern b κ)
variable (a : DirectionAssignment F b κ) (bits : Bits b)
variable (p : Point F) (M : MergedPairs F)

def Holds (v : Position b) : Code b κ → Prop
  | Sum.inl _ => ∃ d : Direction F, d ∉ FourEvents.usedDirections a ∧
      ∃ t : Bool, OnLine p (constituent M d t) ∧
        OnLine (prescribedPoint P a bits M v) (constituent M d (!t)) ∧
        constituent M d (!t) ≠ lineThrough (a.1 v.1) p
  | Sum.inr (Sum.inl xy) =>
      prescribedPoint P a bits M xy.1 ≠ prescribedPoint P a bits M xy.2 ∧
      OnLine (prescribedPoint P a bits M v)
        (joiningLine (prescribedPoint P a bits M xy.1) (prescribedPoint P a bits M xy.2)) ∧
      joiningLine (prescribedPoint P a bits M xy.1) (prescribedPoint P a bits M xy.2) ≠
        lineThrough (a.1 v.1) p
  | Sum.inr (Sum.inr (Sum.inl x)) =>
      ∃ d : Direction F, d ∉ FourEvents.usedDirections a ∧
        prescribedPoint P a bits M x ∈ mergedPoints M d ∧
        ∃ t : Bool, OnLine (prescribedPoint P a bits M v) (constituent M d t) ∧
          constituent M d t ≠ lineThrough (a.1 v.1) p
  | Sum.inr (Sum.inr (Sum.inr cx)) =>
      OnLine (prescribedPoint P a bits M v)
        (lineThrough (a.2 cx.1) (prescribedPoint P a bits M cx.2)) ∧
      lineThrough (a.2 cx.1) (prescribedPoint P a bits M cx.2) ≠
        lineThrough (a.1 v.1) p

end
end Balanced.Local.ConditionSpec

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalConditionFibers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.ConditionSpec

noncomputable section
open scoped Classical
open LocalFiberBounds

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ}

def PointHolds (a : DirectionAssignment F b κ) (p : Point F)
    (M : MergedPairs F) (x : Position b → Point F) (v : Position b) :
    Code b κ → Prop
  | Sum.inl _ => ∃ d : Direction F, d ∉ FourEvents.usedDirections a ∧
      ∃ t : Bool, OnLine p (constituent M d t) ∧
        OnLine (x v) (constituent M d (!t)) ∧
        constituent M d (!t) ≠ lineThrough (a.1 v.1) p
  | Sum.inr (Sum.inl xy) => x xy.1 ≠ x xy.2 ∧
      OnLine (x v) (joiningLine (x xy.1) (x xy.2)) ∧
      joiningLine (x xy.1) (x xy.2) ≠ lineThrough (a.1 v.1) p
  | Sum.inr (Sum.inr (Sum.inl w)) =>
      ∃ d : Direction F, d ∉ FourEvents.usedDirections a ∧
        x w ∈ mergedPoints M d ∧
        ∃ t : Bool, OnLine (x v) (constituent M d t) ∧
          constituent M d t ≠ lineThrough (a.1 v.1) p
  | Sum.inr (Sum.inr (Sum.inr cw)) =>
      OnLine (x v) (lineThrough (a.2 cw.1) (x cw.2)) ∧
      lineThrough (a.2 cw.1) (x cw.2) ≠ lineThrough (a.1 v.1) p

def unusedDirections (a : DirectionAssignment F b κ) : Finset (Direction F) :=
  Finset.univ \ FourEvents.usedDirections a

def testLines (a : DirectionAssignment F b κ) (p : Point F)
    (M : MergedPairs F) (x : Position b → Point F) : Code b κ → Finset (Line F)
  | Sum.inl _ => partnerCandidates M (unusedDirections a) p
  | Sum.inr (Sum.inl xy) => {joiningLine (x xy.1) (x xy.2)}
  | Sum.inr (Sum.inr (Sum.inl w)) => mergedCandidates M (unusedDirections a) (x w)
  | Sum.inr (Sum.inr (Sum.inr cw)) => {lineThrough (a.2 cw.1) (x cw.2)}

end
end Balanced.Local.ConditionSpec

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.KernelBridge

open scoped BigOperators ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*}

def encodeTuple (T : FourTuple F) : TupleCode F := (T.generator, T.side)
def encodeChoice (C : SplitChoice F) : ChoiceCode F := (C.line, encodeTuple C.tuple)

@[simp] theorem decode_encode_tuple (T : FourTuple F) :
    decodeTuple (encodeTuple T) = T := by cases T; rfl

@[simp] theorem decode_encode_choice (C : SplitChoice F) :
    decodeChoice (encodeChoice C) = C := by cases C; rfl

@[simp] theorem encode_decode_tuple (t : TupleCode F) :
    encodeTuple (decodeTuple t) = t := by cases t; rfl

@[simp] theorem encode_decode_choice (c : ChoiceCode F) :
    encodeChoice (decodeChoice c) = c := by cases c; rfl

variable [Field F] [Fintype F] [DecidableEq F]

def canonicalRetention : RetentionRule F where
  candidates M g :=
    (Finset.univ.filter (fun l : Line F => l.1 = g ∧ SupportsValidTuple M l)).image
      (fun l => encodeChoice (retainedChoice M l))
  valid := by
    classical
    intro M g c hc
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hc
    have hl' := (Finset.mem_filter.mp hl).2
    simp only [decode_encode_choice]
    rcases hl' with ⟨rfl, hs⟩
    simpa only [retainedChoice, dite_eq_left hs] using Classical.choose_spec hs
  uniqueLine := by
    classical
    intro M g c d hc hd hline
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hd
    change l = m at hline
    subst m
    rfl
  complete := by
    classical
    intro M g c hc
    have hdir : c.1.1 = g := hc.1
    have hs : SupportsValidTuple M c.1 := by
      refine ⟨decodeTuple c.2, ?_⟩
      simpa only [hdir, decodeChoice] using hc
    refine ⟨encodeChoice (retainedChoice M c.1), ?_, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨c.1, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdir, hs⟩

end
end Balanced.Local.KernelBridge

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalTwoReuseAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.TwoReuseAssembly

noncomputable section
open scoped Classical BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

universe u

def InjectiveTwoReuseEstimate : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ q₀ : ℕ,
    ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      q₀ ≤ Fintype.card F → ∀ b : ℕ, 3 ≤ b → b ≤ logBudget F →
      ∀ (P : EqualityPattern b 2) (bits : Bits b) (p : Point F),
        (∑ a : DirectionAssignment F b 2,
          if AllTokensDistinct a then conditionedOffsetProbability
            (Aligned P a bits p) (AdmissibleBadCover P a bits p) else 0) ≤
          ((Fintype.card F + 1 : ℕ) : ℝ) ^ (5 * b - 2) *
            (C * (b : ℝ) ^ 3 / Fintype.card F)

end
end Balanced.Local.TwoReuseAssembly

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalTwoReuseMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.TwoReuseAssembly
noncomputable section
open scoped BigOperators Classical
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

universe u

def InjectiveTwoReuseMeanEstimate : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ q₀ : ℕ,
    ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      q₀ ≤ Fintype.card F → ∀ b : ℕ, 3 ≤ b → b ≤ logBudget F →
      ∀ (P : EqualityPattern b 2) (bits : Bits b) (p : Point F),
        (∑ e : DirectionToken b 2 ↪ Direction F,
          conditionedOffsetProbability
            (Aligned P (tokenInjectionEquiv F b 2 e).1 bits p)
            (AdmissibleBadCover P (tokenInjectionEquiv F b 2 e).1 bits p)) /
          Fintype.card (DirectionToken b 2 ↪ Direction F) ≤
            C * (b : ℝ) ^ 3 / Fintype.card F

end
end Balanced.Local.TwoReuseAssembly

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalTwoReuseUsedEvents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.TwoReuseAssembly
noncomputable section
open scoped Classical BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def usedEventConditionalMass {b : ℕ} (P : EqualityPattern b 2)
    (a : DirectionAssignment F b 2) (bits : Bits b) (p : Point F) : ℝ :=
  conditionedOffsetProbability (Aligned P a bits p)
    (fun M => Admissible P a bits p M ∧ FourEvents.UsedPairExtra P a bits M) +
  conditionedOffsetProbability (Aligned P a bits p)
    (fun M => Admissible P a bits p M ∧ FourEvents.ForbiddenCollinearTriple P a bits p M)

def usedEventMean {b : ℕ} (P : EqualityPattern b 2) (bits : Bits b) (p : Point F) : ℝ :=
  (∑ e : DirectionToken b 2 ↪ Direction F,
    usedEventConditionalMass P (tokenInjectionEquiv F b 2 e).1 bits p) /
      Fintype.card (DirectionToken b 2 ↪ Direction F)

universe u

def InjectiveUsedEventsEstimate : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ q₀ : ℕ,
    ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      q₀ ≤ Fintype.card F → ∀ b : ℕ, 3 ≤ b → b ≤ logBudget F →
      ∀ (P : EqualityPattern b 2) (bits : Bits b) (p : Point F),
        usedEventMean P bits p ≤ C * (b : ℝ) ^ 3 / Fintype.card F

end
end Balanced.Local.TwoReuseAssembly

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalUsedEventMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.UsedEventUnion

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ}

def injectionAverage (P : EqualityPattern b κ) (bits : Bits b) (p : Point F)
    (E : DirectionAssignment F b κ → MergedPairs F → Prop) : ℝ :=
  (∑ e : DirectionToken b κ ↪ Direction F,
    conditionedOffsetProbability (Aligned P (tokenInjectionEquiv F b κ e).1 bits p)
      (E (tokenInjectionEquiv F b κ e).1)) /
    Fintype.card (DirectionToken b κ ↪ Direction F)

def injectionWeight (F : Type*) [Fintype F] (b κ : ℕ)
    (a : DirectionAssignment F b κ) : ℝ :=
  if AllTokensDistinct a then (Fintype.card (DirectionToken b κ ↪ Direction F) : ℝ)⁻¹
    else 0

universe u

end
end Balanced.Local.UsedEventUnion

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalInjectionFreeLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.UsedEventUnion

noncomputable section
open scoped BigOperators
open AlignedGlobal RootChildPartition
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ}

def injectionFreeProbability (P : EqualityPattern b κ) (R : Finset (Fin b))
    [Nonempty (DirectionToken b κ ↪ Direction F)]
    (G : (DirectionToken b κ ↪ Direction F) → (FreeIndex P R → F) → Prop) : ℝ :=
  ((PMF.uniformOfFintype ((DirectionToken b κ ↪ Direction F) ×
    (FreeIndex P R → F))).toOuterMeasure {z | G z.1 z.2}).toReal

def injectedGenerated (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2 * κ)
    (bits : Bits b) (p : Point F) (e : DirectionToken b κ ↪ Direction F)
    (x : FreeIndex P R → F) : MergedPairs F :=
  generatedZero P hκ R hD (tokenInjectionEquiv F b κ e).1
    (allTokensDistinct_eligible P _ (tokenInjectionEquiv F b κ e).2) bits p x

end
end Balanced.Local.UsedEventUnion

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalExposureTiming
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.Timing
open RootChildPartition AlignedGlobal UsedEventUnion
noncomputable section
open scoped Classical
variable {b κ : ℕ}

def prefixTokens (P : EqualityPattern b κ) (S : Finset (Fin b)) :
    Finset (DirectionToken b κ) :=
  S.image Sum.inl ∪ (S.biUnion P.classSet).image Sum.inr

@[simp] theorem inl_mem_prefixTokens (P : EqualityPattern b κ)
    (S : Finset (Fin b)) (i : Fin b) :
    Sum.inl i ∈ prefixTokens P S ↔ i ∈ S := by
  simp [prefixTokens]

@[simp] theorem inr_mem_prefixTokens (P : EqualityPattern b κ)
    (S : Finset (Fin b)) (c : Fin (4*b-κ)) :
    Sum.inr c ∈ prefixTokens P S ↔ c ∈ S.biUnion P.classSet := by
  simp [prefixTokens]

end
end Balanced.Local.Timing

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalPatternTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Balanced.Local

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ} {P Q : EqualityPattern b κ}

def relabelAssignment (e : Fin (4 * b - κ) ≃ Fin (4 * b - κ)) :
    DirectionAssignment F b κ ≃ DirectionAssignment F b κ :=
  Equiv.prodCongr (Equiv.refl _) (Equiv.arrowCongr e (Equiv.refl _))

variable (e : Fin (4 * b - κ) ≃ Fin (4 * b - κ))
variable (he : ∀ i j, e (P.classOf i j) = Q.classOf i j)

omit [Field F] [Fintype F] [DecidableEq F] in
@[simp] theorem relabelAssignment_target (a : DirectionAssignment F b κ) :
    (relabelAssignment e a).1 = a.1 := rfl

include he

omit he in

def directionBadCoverMass (P : EqualityPattern b κ) (bits : Bits b) (p : Point F) : ℝ :=
  ∑ a : DirectionAssignment F b κ,
    if Eligible P a then offsetProbability (fun M =>
      Aligned P a bits p M ∧ AdmissibleBadCover P a bits p M) else 0

end Balanced.Local

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalPrescriptionCounting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ}

def prescriptionSlots (a : DirectionAssignment F b κ) (side : Fin b → Bool) :
    Fin b → Slot F := fun i => (a.1 i, side i)

def PencilPrescriptionOccurs (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (side : Fin b → Bool)
    (p : Point F) (C : Configuration F) : Prop :=
  Eligible P a ∧ AdmissibleBadCover P a bits p C.merged ∧
    ∀ i, (C.choice (prescriptionSlots a side i)).tuple = prescribedTuple P a bits i

abbrev PencilPrescriptions (R : Finset (EqualityPattern b κ)) :=
  R × DirectionAssignment F b κ × Bits b × (Fin b → Bool)

def prescriptionOccurs (R : Finset (EqualityPattern b κ))
    (p : Point F) (j : PencilPrescriptions (F := F) R) (C : Configuration F) : Prop :=
  PencilPrescriptionOccurs j.1.1 j.2.1 j.2.2.1 j.2.2.2 p C

def prescriptionRead (R : Finset (EqualityPattern b κ))
    (j : PencilPrescriptions (F := F) R) : Fin b → Slot F :=
  prescriptionSlots j.2.1 j.2.2.2

end
end Balanced.Local

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalPatternEvents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def LargePencilEvent (C : Configuration F) : Prop :=
  ∃ p, logBudget F < C.splitMultiplicity p

def HighReuseEvent (C : Configuration F) : Prop :=
  ∃ p, 2 ≤ C.splitMultiplicity p ∧ 3 ≤ reuseCount C p

end
end Balanced.Local

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalFailureSummation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def SmallBadLocalEvent (C : Configuration F) : Prop :=
  ∃ p : Point F, ∃ b ∈ Finset.Icc 3 (logBudget F), ∃ κ ∈ Finset.range 3,
    C.splitMultiplicity p = b ∧ reuseCount C p = κ ∧ BadLocalCoverAt b p C

end
end Balanced.Local

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalSelectedKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.KernelBridge

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def encodeOutput (M : MergedPairs F) (y : SelectedDeletion.Output F) : Output F :=
  fun s => encodeChoice (retainedChoice M (s.1, y s))

@[simp] theorem configuration_encodeOutput (M : MergedPairs F)
    (y : SelectedDeletion.Output F) :
    configuration M (encodeOutput M y) = SelectedDeletion.configuration M y := by
  simp only [configuration, encodeOutput, decode_encode_choice, SelectedDeletion.configuration]

def transportedKernel (κ : SelectedDeletion.Kernel F) : Kernel F :=
  fun M v => ∑ y, if encodeOutput M y = v then κ M y else 0

end
end Balanced.Local.KernelBridge

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_ReuseTargetSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.PartialAlignment
open TupleAlignment

noncomputable section
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def externalAlignmentEvent (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (p : Point F) (g : Direction F) (J : Finset (Fin 4))
    (a : Fin 4 → Bool → F) : Set (PartialOffsets J a) :=
  {o | (∀ i, OnLine (tuplePositionEquiv d hd σ o.1 i) (lineThrough g p)) ∧
    ∀ i, tuplePositionEquiv d hd σ o.1 i ≠ p}

def externalAlignmentProbability (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (p : Point F) (g : Direction F) (J : Finset (Fin 4))
    (a : Fin 4 → Bool → F) : ℝ :=
  ((PMF.uniformOfFintype (PartialOffsets J a)).toOuterMeasure
    (externalAlignmentEvent d hd σ p g J a)).toReal

def possibleExternalTargets (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (p : Point F) (J : Finset (Fin 4)) (a : Fin 4 → Bool → F) :
    Finset (Direction F) :=
  Finset.univ.filter (fun g => ∃ o, o ∈ externalAlignmentEvent d hd σ p g J a)

end
end Balanced.PartialAlignment

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_ReusePrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.ReuseTower

open scoped BigOperators
noncomputable section
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

abbrev Prescription (F : Type*) := Slot F × Local.TupleCode F

def prescriptionTuple (r : Prescription F) : FourTuple F := Local.decodeTuple r.2

def prescriptionGenerators (r : Prescription F) : Finset (Direction F) :=
  generatorSet (prescriptionTuple r)

def exposedDirections (pre : List (Prescription F)) : Finset (Direction F) :=
  pre.toFinset.biUnion prescriptionGenerators

def oldCount (pre : List (Prescription F)) (r : Prescription F) : ℕ :=
  (oldGeneratorIndices (prescriptionTuple r) (exposedDirections pre)).card

def prescriptionEvent (p : Point F) (r : Prescription F) (M : MergedPairs F) : Prop :=
  Function.Injective r.2.1 ∧ (∀ i, r.2.1 i ≠ r.1.1) ∧
    (∀ i, OnLine (tuplePoint M (prescriptionTuple r) i) (lineThrough r.1.1 p)) ∧
    ∀ i, tuplePoint M (prescriptionTuple r) i ≠ p

def prefixEvent (p : Point F) (pre : List (Prescription F)) (M : MergedPairs F) : Prop :=
  ∀ r ∈ pre, prescriptionEvent p r M

def prefixWeight (K : ℝ) (p : Point F) (pre : List (Prescription F)) : ℝ :=
  (K / Fintype.card F) ^ pre.length * Local.offsetProbability (prefixEvent p pre)

def expose (old : Finset (Direction F)) (M : MergedPairs F) : old → Bool → F :=
  fun d => M d

omit [Field F] [Fintype F] [DecidableEq F] in
@[simp] theorem expose_eq_iff (old : Finset (Direction F)) (M N : MergedPairs F) :
    expose old M = expose old N ↔ ∀ d ∈ old, M d = N d := by
  constructor
  · intro h d hd
    exact congrFun h ⟨d, hd⟩
  · intro h
    funext d
    exact h d d.2

@[simp] theorem prefixWeight_nil (K : ℝ) (p : Point F) :
    prefixWeight K p [] = 1 := by
  simp [prefixWeight, Local.offsetProbability, prefixEvent]

end
end Balanced.ReuseTower

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_ReuseScore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.ReuseTower

open scoped BigOperators
noncomputable section
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def prefixScore : List (Prescription F) → ℕ
  | [] => 0
  | r :: pre => prefixScore pre + reuseSaving (oldCount pre r)

end
end Balanced.ReuseTower

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_ReusePrescriptions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.ReusePrescription

open Local Local.KernelBridge
open scoped BigOperators

noncomputable section
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

abbrev Code (F : Type*) := Slot F × Local.TupleCode F

def generators (c : Code F) : Finset (Direction F) :=
  generatorSet (decodeTuple c.2)

def TupleEligible (c : Code F) : Prop :=
  Function.Injective c.2.1 ∧ ∀ i, c.2.1 i ≠ c.1.1

def Eligible (l : List (Code F)) : Prop :=
  (l.map Prod.fst).Nodup ∧ (∀ c ∈ l, TupleEligible c) ∧
    3 ≤ reuseExposureScore generators l

def AlignedExternal (p : Point F) (l : List (Code F)) (M : MergedPairs F) : Prop :=
  ∀ c ∈ l,
    (∀ i, OnLine (tuplePoint M (decodeTuple c.2) i) (lineThrough c.1.1 p)) ∧
    ∀ i, tuplePoint M (decodeTuple c.2) i ≠ p

def Matches (l : List (Code F)) (C : Configuration F) : Prop :=
  ∀ c ∈ l, encodeTuple (C.choice c.1).tuple = c.2

def encode (C : Configuration F) (s : Slot F) : Code F :=
  (s, encodeTuple (C.choice s).tuple)

def slots (l : List (Code F)) : Finset (Slot F) := (l.map Prod.fst).toFinset

def codeAt (l : List (Code F)) (s : Slot F) : TupleCode F :=
  if h : ∃ c ∈ l, c.1 = s then (Classical.choose h).2
  else (fun _ => none, fun _ => false)

def witnesses (F : Type*) [Field F] [Fintype F] [DecidableEq F] :
    Finset (List (Code F)) :=
  (Finset.range 7).biUnion (fun n => (allLists (Code F) n).filter Eligible)

@[simp] theorem mem_witnesses (l : List (Code F)) :
    l ∈ witnesses F ↔ l.length ≤ 6 ∧ Eligible l := by
  simp only [witnesses, Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter,
    mem_allLists]
  constructor
  · rintro ⟨n, hn, hlen, hel⟩
    exact ⟨by omega, hel⟩
  · rintro ⟨hlen, hel⟩
    exact ⟨l.length, by omega, rfl, hel⟩

end
end Balanced.ReusePrescription

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_ReuseWeightedBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.ReuseTower

open scoped BigOperators
noncomputable section
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def weightedWitnessMass (K : ℝ) (p : Point F) (n : ℕ) : ℝ :=
  ∑ a : Fin n → Prescription F,
    if 3 ≤ reuseExposureScore prescriptionGenerators (List.ofFn a).reverse then
      prefixWeight K p (List.ofFn a).reverse else 0

end
end Balanced.ReuseTower

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_MainAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

open Filter
open scoped Topology

noncomputable section
open scoped Classical

def SelectedLocalTransport : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F],
    ∀ (κ : SelectedDeletion.Kernel F) (c C K : ℝ),
      0 ≤ K → SelectedDeletion.IsExperiment κ c C →
      (∀ M (J : Finset (Slot F)) (prescribed : SelectedDeletion.Output F),
        SelectedDeletion.fixedCylinderMass κ M J prescribed ≤
          (K / (Fintype.card F : ℝ)) ^ J.card) →
      ∃ Q : Local.RetentionRule F, ∃ w : Local.Kernel F,
        Local.KernelConditions Q w K ∧ ∀ E : Configuration F → Prop,
          Local.selectedProbability w E =
            SelectedDeletion.jointMass κ (fun M s => E (SelectedDeletion.configuration M s))

def SelectedCoreTransport : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F],
    ∀ (κ : SelectedDeletion.Kernel F) (c C : ℝ)
      (Q : PMF (DeletionSet F 3)),
      SelectedDeletion.IsExperiment κ c C →
      SelectedDeletion.RealizesConditionalLaw κ Q →
      0 < SelectedDeletion.successMass κ →
      ∀ E : Finset (Line F) → Prop,
        SelectedDeletion.jointMass κ
          (fun M s => E (SelectedDeletion.configuration M s).deletedLines) =
          SelectedDeletion.successMass κ * deletionEventProbability Q (fun D => E D.val)

end

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_Profile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter Finset MeasureTheory
open scoped Topology NNReal

namespace Balanced
open scoped _root_.Balanced

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def planeProfile (D C : Finset (Line F)) : Profile := fun ij =>
  ((Finset.univ.filter (fun x : Point F =>
    lineMultiplicity D x = ij.1 ∧ lineMultiplicity C x = ij.2)).card : ℝ) /
      (Fintype.card F : ℝ) ^ 2

def lineProfile (D C : Finset (Line F)) (l : Line F) : Profile := fun ij =>
  (((linePoints l).filter (fun x =>
    lineMultiplicity D x = ij.1 ∧ lineMultiplicity C x = ij.2)).card : ℝ) /
      (Fintype.card F : ℝ)

def empiricalProfileMeasure (D C E : Finset (Line F)) : FiniteMeasure Profile := by
  let a : ℝ≥0 := ⟨(Fintype.card F : ℝ)⁻¹, by positivity⟩
  let ν : FiniteMeasure Profile := ∑ l ∈ E, profileDirac (lineProfile D C l)
  exact a • ν

def IsProfilePair (k : ℕ) (D C : Finset (Line F)) : Prop :=
  IsDeletionSet k D ∧ Disjoint D C ∧ C.card ≤ Fintype.card F

universe u

abbrev ProfileClass :=
  ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
    Finset (Line F) → Finset (Line F) → Prop

def ProfileClassValid (k : ℕ) (A : ProfileClass.{u}) : Prop :=
  ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
    (D C : Finset (Line F)), A F D C → IsProfilePair k D C

def ProfileClassSizeGap (a : ℝ) (A : ProfileClass.{u}) : Prop :=
  ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
    (D C : Finset (Line F)), A F D C →
      C.card = 0 ∨ a * (Fintype.card F : ℝ) ≤ (C.card : ℝ)

def ProfileSequenceLimit
    {F : ℕ → Type u} [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)]
    (D C : ∀ n, Finset (Line (F n)))
    (c : ℝ) (P : Profile) (νD νC : FiniteMeasure Profile) : Prop :=
  Tendsto (fun n => ((C n).card : ℝ) / (Fintype.card (F n) : ℝ)) atTop (𝓝 c) ∧
  Tendsto (fun n => planeProfile (D n) (C n)) atTop (𝓝 P) ∧
  Tendsto (fun n => empiricalProfileMeasure (D n) (C n) (D n)) atTop (𝓝 νD) ∧
  Tendsto (fun n => empiricalProfileMeasure (D n) (C n) (C n)) atTop (𝓝 νC)

def ProfileVisibleExcess (A : ProfileClass.{u}) : Prop :=
  ∀ (F : ℕ → Type u) [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)]
    (D C : ∀ n, Finset (Line (F n))),
    (∀ n, A (F n) (D n) (C n)) →
    Tendsto (fun n => Fintype.card (F n)) atTop atTop →
    ∀ (c : ℝ) (P : Profile) (νD νC : FiniteMeasure Profile),
      ProfileSequenceLimit D C c P νD νC →
      c < (νD : Measure Profile).real (deletionVisible P) +
        (νC : Measure Profile).real (coverVisible P)

def uniformProfileWitnessProbability (k : ℕ) (A : ProfileClass.{u})
    (F : Type u) [Field F] [Fintype F] [DecidableEq F] : ℝ := by
  classical
  exact ((Finset.univ.filter (fun D : DeletionSet F k =>
    ∃ C : Finset (Line F), A F D.val C)).card : ℝ) /
      (Fintype.card (DeletionSet F k) : ℝ)

def ProfileCountingResult : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ A : ProfileClass.{u},
    ProfileClassValid k A →
    (∃ a : ℝ, 0 < a ∧ ProfileClassSizeGap a A) →
    ProfileVisibleExcess A →
    ∃ b : ℝ, 0 < b ∧ ∃ N : ℕ,
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
        N ≤ Fintype.card F → k ≤ Fintype.card F →
        uniformProfileWitnessProbability k A F ≤
          Real.exp (-b * (Fintype.card F : ℝ) * Real.log (Fintype.card F : ℝ))

end Balanced

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_NearCoverVisibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory

namespace Balanced.NearCoverVisibility

def NearCoverClass (k : ℕ) (δ : ℝ) (ε : ℕ → ℝ) : ProfileClass :=
  fun F _ _ _ D C =>
    IsProfilePair k D C ∧
    CoversPoints C (uncoveredBy D) ∧
    δ * (Fintype.card F : ℝ) ^ 2 ≤ ((uncoveredBy C).card : ℝ) ∧
    deletionMultiplicityTV k D ≤ ε (Fintype.card F) ∧
    ((exceptionalOccupancyLines k (ε (Fintype.card F)) D).card : ℝ) ≤
      ε (Fintype.card F) * (Fintype.card F : ℝ)

end Balanced.NearCoverVisibility

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_PatternIntegrability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped BigOperators

namespace Balanced.PatternModel

variable (P : PatternModel)

noncomputable def additionalSupport (K₀ : Finset P.Color) (as : List P.Label) : Finset P.Color :=
  by
    classical
    exact as.toFinset.biUnion (fun a => P.support a \ K₀)

end Balanced.PatternModel

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_PatternModelCancellation
attribute [-instance] _root_.OAI.Balanced.PatternModel.isProbabilityMeasure_measure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Balanced.PatternProof

variable (P : PatternModel)

noncomputable def fillFresh (K : Finset P.Color) (x : P.Sample) (a : P.Label)
    (z : (c : ↥(P.support a \ K)) → P.Value c) : P.Sample := by
  classical
  exact fun c => if hc : c ∈ P.support a \ K then z ⟨c, hc⟩ else x c

end Balanced.PatternProof

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_PatternModelExpansion
attribute [-instance] _root_.OAI.Balanced.PatternModel.isProbabilityMeasure_measure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped BigOperators

namespace Balanced.PatternModelMoments

variable (P : PatternModel)

attribute [local instance] Classical.propDecidable

def noIsolated (K : Finset P.Color) {n : ℕ} (a : Fin n → P.Label) : Prop :=
  ∀ i, ∃ j, j ≠ i ∧
    ((P.support (a j) \ K) ∩ (P.support (a i) \ K)).Nonempty

end Balanced.PatternModelMoments

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_ScheduledCountingExposure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.ScheduledCountingExposure

universe u

noncomputable section
open scoped Classical BigOperators ENNReal
open ExposureInterleaving CountingExposurePosterior
open UniformDeletionEnumeration

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {k m : ℕ}

abbrev DExperiment (F : Type*) [Fintype F] (k : ℕ) :=
  CountingExposurePosterior.Experiment (G := Direction F) (ι := Fin k) (α := F)

abbrev Sample (F : Type*) [Fintype F] (k : ℕ) :=
  DExperiment F k × Equiv.Perm (Line F)

def pastD (γ : ℝ) (s : Steps F k m) : Finset (Direction F × Fin k) :=
  (previousD γ s).map timeToToken.toEmbedding

def pastC (c : Fin m ↪ Line F) (γ : ℝ) (s : Steps F k m) : Finset (Line F) :=
  (previousC γ s).map c

def uncovered (c : Fin m ↪ Line F) (γ : ℝ) (s : Steps F k m)
    (ω : Sample F k) : Finset (Point F) :=
  uncoveredBy (DeletionCountingExposure.exposedLines (pastD γ s) ω.1 ∪
    (pastC c γ s).map ω.2.toEmbedding)

def target (c : Fin m ↪ Line F) : Steps F k m → Sample F k → Line F
  | Sum.inl i, ω => nextLine ω.1 (timeToToken i)
  | Sum.inr i, ω => ω.2 (c i)

def Mark (c : Fin m ↪ Line F) (γ η ε : ℝ) (s : Steps F k m)
    (ω : Sample F k) : Prop :=
  η < parameter γ s ∧ CoverCountingExposure.Marked (uncovered c γ s ω) ε (target c s ω)

def markCount (c : Fin m ↪ Line F) (γ η ε : ℝ) (ω : Sample F k) : ℕ :=
  (Finset.univ.filter (fun s => Mark c γ η ε s ω)).card

def arrayUncovered (d : Fin (k * (Fintype.card F + 1)) → Line F)
    (c : Fin m → Line F) (γ : ℝ) (s : Steps F k m) : Finset (Point F) :=
  uncoveredBy ((previousD γ s).image d ∪ (previousC γ s).image c)

def arrayMark (d : Fin (k * (Fintype.card F + 1)) → Line F)
    (c : Fin m → Line F) (γ η ε : ℝ) (s : Steps F k m) : Prop :=
  η < parameter γ s ∧ CoverCountingExposure.Marked (arrayUncovered d c γ s) ε
    (Sum.elim d c s)

def arrayMarkCount (d : Fin (k * (Fintype.card F + 1)) → Line F)
    (c : Fin m → Line F) (γ η ε : ℝ) : ℕ :=
  (Finset.univ.filter (arrayMark d c γ η ε)).card

def Cylinder (c : Fin m ↪ Line F) (γ η ε : ℝ)
    (t : Finset (Steps F k m)) (ω : Sample F k) : Prop :=
  ∀ s ∈ t, Mark c γ η ε s ω

end
end Balanced.ScheduledCountingExposure

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileWitnessPayment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.ProfileWitnessPayment

universe u

noncomputable section
open scoped BigOperators Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def pairMarkAverage (k m : ℕ)
    (w : DeletionSet F k → Finset (Line F) → ℝ) : ℝ :=
  ((∑ D, ∑ C ∈ witnesses F m, w D C) /
    (Fintype.card (DeletionSet F k) : ℝ)) / (witnesses F m).card

end
end Balanced.ProfileWitnessPayment

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_ScheduledCountingLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.ScheduledCountingExposure

noncomputable section
open scoped BigOperators Classical
open CountingJointLaw ProfileWitnessPayment

universe u

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {k m : ℕ}

def fixedPairTail (γ η ε a : ℝ) (D : DeletionSet F k) (C : Finset (Line F)) : ℝ :=
  fixedPairMean (m := m) (fun d c =>
    if a ≤ (arrayMarkCount (k := k) d c γ η ε : ℝ) then (1 : ℝ) else 0) D C

def coverPositions (hm : m ≤ Fintype.card F) : Fin m ↪ Line F :=
  ((Fin.castLEEmb hm).trans (Fintype.equivFin F).symm.toEmbedding).trans
    ⟨fun a => ((none : Direction F), a), fun _ _ h => congrArg Prod.snd h⟩

end
end Balanced.ScheduledCountingExposure

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_UncoveredSubsetVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace Balanced.UncoveredSampling

open WithoutReplacement UncoveredExchange

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable def planeFraction (S T : Finset (Line F)) : ℝ :=
  ((uncoveredBy (S ∪ T)).card : ℝ) / (Fintype.card F : ℝ)^2

noncomputable def targetFraction (L : Line F) (S T : Finset (Line F)) : ℝ :=
  ((linePoints L ∩ uncoveredBy (S ∪ T)).card : ℝ) / (Fintype.card F : ℝ)

end Balanced.UncoveredSampling

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileMarkedOrders
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory

namespace Balanced.ProfileMarkedOrders

open ConditionalOrderVariance UncoveredSampling PermutationSubsetLaw

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def firstMark (U V : Finset (Line F)) (I : U → Finset U) (J : U → Finset V)
    (z : U → ℝ) (η ε : ℝ) (i : U) (p : OrderPair U V) : Prop :=
  η < z i ∧ ε < |targetFraction (p.1 i).val
      (populationLines U ((I i).map p.1.toEmbedding))
      (populationLines V ((J i).map p.2.toEmbedding)) -
    planeFraction (populationLines U ((I i).map p.1.toEmbedding))
      (populationLines V ((J i).map p.2.toEmbedding))|

def firstMarkCount (U V : Finset (Line F)) (I : U → Finset U) (J : U → Finset V)
    (z : U → ℝ) (η ε : ℝ) (p : OrderPair U V) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => firstMark U V I J z η ε i p)).card

variable (U V : Finset (Line F))
  [MeasurableSpace (OrderPair U V)] [MeasurableSingletonClass (OrderPair U V)]

def targetMarkEvent (I : Finset U) (J : Finset V) (x : U) (ε : ℝ) :
    Set (OrderPair U V) := {p | ε < |targetFraction x.val
      (populationLines U (I.map p.1.toEmbedding))
      (populationLines V (J.map p.2.toEmbedding)) -
    planeFraction (populationLines U (I.map p.1.toEmbedding))
      (populationLines V (J.map p.2.toEmbedding))|}

def targetStatistic (I : Finset U) (J : Finset V) (x : U)
    (p : OrderPair U V) : ℝ :=
  targetFraction x.val (populationLines U (I.map p.1.toEmbedding))
    (populationLines V (J.map p.2.toEmbedding))

def planeStatistic (I : Finset U) (J : Finset V) (p : OrderPair U V) : ℝ :=
  planeFraction (populationLines U (I.map p.1.toEmbedding))
    (populationLines V (J.map p.2.toEmbedding))

def conditionalMean (i x : U) (f : OrderPair U V → ℝ) : ℝ :=
  𝔼 p ∈ (Finset.univ.filter (fun σ : Equiv.Perm U => σ i = x)) ×ˢ
    (Finset.univ : Finset (Equiv.Perm V)), f p

def markCount (ID : U → Finset U) (JD : U → Finset V) (zD : U → ℝ)
    (IC : V → Finset V) (JC : V → Finset U) (zC : V → ℝ)
    (η ε : ℝ) (p : OrderPair U V) : ℕ :=
  firstMarkCount U V ID JD zD η ε p +
    firstMarkCount V U IC JC zC η ε p.swap

def orderLaw : PMF (OrderPair U V) := PMF.uniformOfFintype _

end Balanced.ProfileMarkedOrders

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileScheduledMarks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace Balanced.ProfileScheduledMarks

open ExposureInterleaving ConditionalOrderVariance ProfileMarkedOrders

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def label (U : Finset (Line F)) : U ≃ Fin U.card :=
  Fintype.equivFinOfCardEq (Fintype.card_coe U)

def prefixD (D C : Finset (Line F)) (s : Step D.card C.card) : Finset D :=
  (previousD (Real.sqrt 2) s).map (label D).symm.toEmbedding

def prefixC (D C : Finset (Line F)) (s : Step D.card C.card) : Finset C :=
  (previousC (Real.sqrt 2) s).map (label C).symm.toEmbedding

def unexposedD (D C : Finset (Line F)) (s : Step D.card C.card) : Finset D :=
  (remainingD (Real.sqrt 2) s).map (label D).symm.toEmbedding

def unexposedC (D C : Finset (Line F)) (s : Step D.card C.card) : Finset C :=
  (remainingC (Real.sqrt 2) s).map (label C).symm.toEmbedding

def stepD (D C : Finset (Line F)) (i : D) : Step D.card C.card :=
  Sum.inl (label D i)

def stepC (D C : Finset (Line F)) (j : C) : Step D.card C.card :=
  Sum.inr (label C j)

def zD (D : Finset (Line F)) (i : D) : ℝ := grid (label D i)

def zC (C : Finset (Line F)) (j : C) : ℝ := coverGrid (Real.sqrt 2) (label C j)

def ID (D C : Finset (Line F)) (i : D) : Finset D := prefixD D C (stepD D C i)
def JD (D C : Finset (Line F)) (i : D) : Finset C := prefixC D C (stepD D C i)
def IC (D C : Finset (Line F)) (j : C) : Finset C := prefixC D C (stepC D C j)
def JC (D C : Finset (Line F)) (j : C) : Finset D := prefixD D C (stepC D C j)

omit [Field F] [Fintype F] [DecidableEq F] in
@[simp] theorem current_not_ID (D C : Finset (Line F)) (i : D) : i ∉ ID D C i := by
  simp [ID, prefixD, stepD, Finset.mem_map_equiv]

omit [Field F] [Fintype F] [DecidableEq F] in
@[simp] theorem current_not_IC (D C : Finset (Line F)) (j : C) : j ∉ IC D C j := by
  simp [IC, prefixC, stepC, Finset.mem_map_equiv]

omit [Field F] [Fintype F] [DecidableEq F] in
@[simp] theorem unexposedC_empty (D : Finset (Line F))
    (s : Step D.card (∅ : Finset (Line F)).card) : unexposedC D ∅ s = ∅ := by
  exact Finset.eq_empty_of_forall_notMem
    (fun index => (Finset.notMem_empty index.val index.property).elim)

omit [Field F] [Fintype F] [DecidableEq F] in
@[simp] theorem prefixC_empty (D : Finset (Line F))
    (s : Step D.card (∅ : Finset (Line F)).card) : prefixC D ∅ s = ∅ := by
  exact Finset.eq_empty_of_forall_notMem (fun j => (Finset.notMem_empty j.1 j.2).elim)

def sourceMarkCount (D C : Finset (Line F)) (η ε : ℝ) (p : OrderPair D C) : ℕ :=
  markCount D C (ID D C) (JD D C) (zD D) (IC D C) (JC D C) (zC C) η ε p

def normalizedMean (D C : Finset (Line F)) (η ε : ℝ) : ℝ :=
  (𝔼 p : OrderPair D C, (sourceMarkCount D C η ε p : ℝ)) / Fintype.card F

end Balanced.ProfileScheduledMarks

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_ScheduledMarksBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.ScheduledMarksBridge

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
open ExposureInterleaving ConditionalOrderVariance ProfileScheduledMarks
open UncoveredSampling

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def rankMark {n m : ℕ} (d : Fin n → Line F) (c : Fin m → Line F)
    (η ε : ℝ) (s : Step n m) : Prop :=
  η < parameter (Real.sqrt 2) s ∧
    CoverCountingExposure.Marked
      (uncoveredBy ((previousD (Real.sqrt 2) s).image d ∪
        (previousC (Real.sqrt 2) s).image c)) ε (Sum.elim d c s)

def rankCount {n m : ℕ} (d : Fin n → Line F) (c : Fin m → Line F)
    (η ε : ℝ) : ℕ :=
  (Finset.univ.filter (rankMark d c η ε)).card

def orderedArray (D : Finset (Line F)) (p : Equiv.Perm D) : Fin D.card → Line F :=
  fun i => (p ((label D).symm i)).val

def populationOrder (D : Finset (Line F)) {n : ℕ} (h : n = D.card) : Fin n ≃ D :=
  (finCongr h).trans (label D).symm

end
end Balanced.ScheduledMarksBridge

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileMomentCompactness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.ProfileMomentCompactness
open scoped BigOperators
open Filter Topology

def box (n : ℕ) : Finset Index :=
  Finset.range (n + 1) ×ˢ Finset.range (n + 1)

lemma weight_nonneg (i : Index) : 0 ≤ weight i := by
  unfold weight
  positivity

theorem mem_profiles_iff (M : ℝ) (p : Index → ℝ) :
    p ∈ profiles M ↔ (∀ i, 0 ≤ p i) ∧ HasSum p 1 ∧
      Summable (fun i => weight i * p i) ∧
      (∑' i, weight i * p i) ≤ M := by
  constructor
  · rintro ⟨hp, hs, hm⟩
    have hw : ∀ i, 0 ≤ weight i * p i := fun i =>
      mul_nonneg (weight_nonneg i) (hp i)
    exact ⟨hp, hs, summable_of_sum_le hw hm, Real.tsum_le_of_sum_le hw hm⟩
  · rintro ⟨hp, hs, hw, hm⟩
    refine ⟨hp, hs, fun s => ?_⟩
    exact (hw.sum_le_tsum s (fun i hi =>
      mul_nonneg (weight_nonneg i) (hp i))).trans hm

end Balanced.ProfileMomentCompactness

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileClassMargin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace Balanced.ProfileClassMargin

open ProfileDetection ProfileDetectionLimit ProfileParameterLaw

universe u

abbrev Test := ℕ → ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
  Finset (Line F) → Finset (Line F) → ℝ

def LimitLowerBound (A : ProfileClass.{u}) (test : Test.{u}) : Prop :=
  ∀ (F : ℕ → Type u) [∀ t, Field (F t)] [∀ t, Fintype (F t)]
    [∀ t, DecidableEq (F t)] (D C : ∀ t, Finset (Line (F t))),
    (∀ t, A (F t) (D t) (C t)) →
    Tendsto (fun t => Fintype.card (F t)) atTop atTop →
    ∀ (c : ℝ) (P : Profile) (νD νC : FiniteMeasure Profile),
      ProfileSequenceLimit D C c P νD νC →
      ∀ (n : ℕ) (r : ℝ), r < cutoffMass P νD νC n →
        ∀ᶠ t in atTop, r < test n (F t) (D t) (C t)

end Balanced.ProfileClassMargin

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileMarkedError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter
open scoped Topology BigOperators

namespace Balanced.ProfileMarkedError

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def loss (U V : Finset (Line F)) (I : U → Finset U) (J : U → Finset V)
    (z : U → ℝ) (η ε : ℝ) : ℝ :=
  ∑ i : U, if η < z i then
    32 * (((I i).card : ℝ) + (J i).card) /
      ((Fintype.card F : ℝ)^2 * ε^2) else 0

end Balanced.ProfileMarkedError

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileFiniteMarks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace Balanced.ProfileFiniteMarks

open ConditionalOrderVariance ProfileMarkedOrders ProfileScheduledMarks
open ProfileDetectionBridge ProfileMarkedError

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def detectionSum (U : Finset (Line F)) (z : U → ℝ)
    (a b : U → U → ℝ) (η ε : ℝ) : ℝ :=
  ∑ i : U, 𝔼 x : U,
    if η < z i ∧ z i < 1 ∧ 3 * ε < |a i x - b i x| then (1 : ℝ) else 0

def dFinite (D C : Finset (Line F)) (η ε : ℝ) : ℝ :=
  detectionSum D (zD D)
    (fun i x => dTest (lineProfile D C x) (zD D i))
    (fun i _ => planeTest (planeProfile D C) (zD D i)) η ε / Fintype.card F

def cFinite (D C : Finset (Line F)) (η ε : ℝ) : ℝ :=
  detectionSum C (zC C)
    (fun i x => cTest (lineProfile D C x) (zC C i))
    (fun i _ => planeTest (planeProfile D C) (zC C i)) η ε / Fintype.card F

end Balanced.ProfileFiniteMarks

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileGridDetection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace Balanced.ProfileGridDetection

section ActualGrids

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def dGridCutoffMass (D C : Finset (Line F)) (t : ℕ) : ℝ :=
  (∑ i ∈ Finset.range D.card,
    (empiricalProfileMeasure D C D : Measure Profile).real {x |
      (x, (((i + 1 : ℕ) : ℝ) / D.card)) ∈
        ProfileDetection.cutoffDetection Prod.snd
          (ProfileDetectionLimit.dDiscrepancy (planeProfile D C)) t}) / D.card

def cGridCutoffMass (D C : Finset (Line F)) (t : ℕ) : ℝ :=
  (∑ i ∈ Finset.range C.card,
    (empiricalProfileMeasure D C C : Measure Profile).real {x |
      (x, ((((i + 1 : ℕ) : ℝ) / C.card) ^ (Real.sqrt 2)⁻¹)) ∈
        ProfileDetection.cutoffDetection Prod.snd
          (ProfileDetectionLimit.cDiscrepancy (planeProfile D C)) t}) / C.card

@[simp] theorem cGridCutoffMass_empty (D : Finset (Line F)) (t : ℕ) :
    cGridCutoffMass D ∅ t = 0 := by simp [cGridCutoffMass]

end ActualGrids

end Balanced.ProfileGridDetection

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileScheduledMargin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable
open Filter MeasureTheory
open scoped Topology BigOperators

namespace Balanced.ProfileScheduledMargin

open ConditionalOrderVariance ProfileScheduledMarks

universe u

def sourceTest : ProfileClassMargin.Test.{u} := fun n F _ _ _ D C =>
  normalizedMean (F := F) D C (threshold n) (threshold n)

variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]

def tailProbability (D C : Finset (Line F)) (η ε ξ : ℝ) : ℝ :=
  𝔼 p : OrderPair D C,
    if (C.card : ℝ) + ξ * (Fintype.card F : ℝ) / 2 ≤
      (sourceMarkCount D C η ε p : ℝ) then 1 else 0

end Balanced.ProfileScheduledMargin

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileCountingAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Balanced.ProfileCountingAssembly

universe u

open ProfileScheduledMargin ProfileWitnessPayment

def SourceRareTailBound (k : ℕ) : Prop :=
  ∀ η ε ξ : ℝ, 0 < η → η ≤ 1 → 0 < ε → 0 < ξ →
    ∃ L : ℝ, ∃ N : ℕ,
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
        (m : ℕ), N ≤ Fintype.card F → k ≤ Fintype.card F →
        m ≤ Fintype.card F →
        pairMarkAverage (F := F) k m (fun D C => tailProbability D.val C η ε ξ) ≤
          Real.exp (L * (Fintype.card F : ℝ) -
            (ξ / 2) * (Fintype.card F : ℝ) * Real.log (Fintype.card F : ℝ)) /
              (Fintype.card F : ℝ) ^ m

end Balanced.ProfileCountingAssembly

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_LineOccupancy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.LineOccupancy

open scoped BigOperators

variable {F : Type*} [Field F]

def transverseHitEquiv (l : Line F) (d : Direction F) (hne : l.1 ≠ d) :
    F ≃ {p : Point F // OnLine p l} where
  toFun a := ⟨lineIntersection l (d, a), onLine_lineIntersection_left l (d, a) hne⟩
  invFun p := lineEval d p.val
  left_inv a := onLine_lineIntersection_right l (d, a) hne
  right_inv p := by
    apply Subtype.ext
    apply common_point_eq_of_lines_ne l (d, lineEval d p.val)
      (fun h => hne (congrArg Prod.fst h))
    · exact onLine_lineIntersection_left _ _ hne
    · exact onLine_lineIntersection_right _ _ hne
    · exact p.property
    · rfl

variable [Fintype F] [DecidableEq F]

def hitAssignmentsEquiv (l : Line F) :
    (TransverseDirections l → F) ≃
      (TransverseDirections l → {p : Point F // OnLine p l}) :=
  Equiv.piCongrRight fun d => transverseHitEquiv l d.val (Ne.symm d.property)

noncomputable def unhitCount (l : Line F) (a : TransverseDirections l → F) : ℕ := by
  classical
  exact (Finset.univ.filter (fun p : {p : Point F // OnLine p l} =>
    ∀ d : TransverseDirections l, ¬ OnLine p.val (d.val, a d))).card

def transverseOffsets (l : Line F) (M : MergedPairs F) : TransverseDirections l → F :=
  fun d => M d.val true

end Balanced.LineOccupancy

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionTailCompletion
attribute [-instance] _root_.OAI.Balanced.Selection.Process.snapshotPathLaw_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory

namespace Balanced.Selection.Process.Tail

variable {I V : Type*} [Fintype I] [Fintype V]

omit [Fintype I] [Fintype V] in

theorem complete_isIndependentTransversal (G : Input I V) (S : State I V)
    (fixed : I → V)
    (hslot : ∀ i ∉ S.remaining, G.slot (fixed i) = i)
    (hind : ∀ i ∉ S.remaining, ∀ j ∉ S.remaining, i ≠ j →
      ¬ G.graph.Adj (fixed i) (fixed j))
    (hcross : ∀ i ∉ S.remaining, ∀ v ∈ currentVertices G S,
      ¬ G.graph.Adj (fixed i) v)
    (a : Slots.Assignment (Domain G S))
    (ha : a ∈ TailConditioning.independentTransversals (Domain G S) (graph G S)) :
    IsIndependentTransversal G (complete G S fixed a) := by
  constructor
  · intro i
    by_cases hi : i ∈ S.remaining
    · simp only [complete, dite_eq_left hi]
      exact (Finset.mem_filter.mp (a ⟨i, hi⟩).2).2
    · rw [complete_recorded G S fixed a i hi]
      exact hslot i hi
  · intro i j hij
    by_cases hi : i ∈ S.remaining <;> by_cases hj : j ∈ S.remaining
    · simpa only [complete, dite_eq_left hi, dite_eq_left hj, graph, SimpleGraph.comap_adj, value] using
        ha ⟨i, hi⟩ ⟨j, hj⟩
    · simp only [complete, dite_eq_left hi, dite_eq_right hj]
      exact fun h => hcross j hj _ (value_mem_current G S ⟨⟨i, hi⟩, a ⟨i, hi⟩⟩) h.symm
    · simp only [complete, dite_eq_right hi, dite_eq_left hj]
      exact hcross i hi _ (value_mem_current G S ⟨⟨j, hj⟩, a ⟨j, hj⟩⟩)
    · simp only [complete, dite_eq_right hi, dite_eq_right hj]
      exact hind i hi j hj hij

end Balanced.Selection.Process.Tail

end

end OAI
end


