-- Prove2me | Definitions.Def_OAIQ63Br000
-- name    : OAIQ63Br000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T00:05:45.805872+00:00
-- url     : https://prove2.me/theorems/71f7cc7a-808e-457a-9452-bdbac9f22430
-- title:
--   Definitions bundle OAIQ63Br000 of the split of OpenAI, Balanced counterexamples to Ryser's conjecture at prime orders (result family 162)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Balanced.main_result`, carved from OpenAI's openai/math development (OpenAI, *Balanced counterexamples to Ryser's conjecture at prime orders (result family 162)*, OpenAI Math Release, September 27, 2026, result family 162, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 527 declarations of OpenAI's Lean: 358 definitions, 5 inductive types or structures, 10 instances and 154 theorems. The definitions and types are `OAI.Balanced.Adjacent`, `OAI.Balanced.AffinePermutationExposure.targetOrderMean`, `OAI.Balanced.AffinePlaneOrderExposure.erasedPlanePowerMean`, `OAI.Balanced.AffinePlaneOrderExposure.planeOrderMean`, `OAI.Balanced.AffinePlaneOrderExposure.planePowerMean`, `OAI.Balanced.AffineProfileExposure.targetExposureMean`, `OAI.Balanced.AffineProfileExposure.targetPowerMean`, `OAI.Balanced.AffineSecondMoment`, `OAI.Balanced.AlignedListProbability.ListAligned`, `OAI.Balanced.AlignedListProbability.alignedFreeCoordinatesEquiv`, `OAI.Balanced.AlignedListProbability.generatedOffsets`, `OAI.Balanced.AlignedListProbability.generatedPositions`, `OAI.Balanced.AllConstituentPairsDistinct`, `OAI.Balanced.AvailableCandidate`, `OAI.Balanced.BadCoreCover`, `OAI.Balanced.BernoulliTail.thinningCutoff`, `OAI.Balanced.BoundedDriftConcentration`, `OAI.Balanced.BoundedProfile`, `OAI.Balanced.CandidateAbundanceAssembly.abundanceAssemblyMeasurableSpace`, `OAI.Balanced.CandidateAbundanceAssembly.slotLinearConstant`, `OAI.Balanced.CandidateAdjacent`, `OAI.Balanced.CandidateConstituentTail.instMeasurableSpace_solutions`, `OAI.Balanced.CandidateConstituentTail.tailConstant`, `OAI.Balanced.CandidateExposedWitness.forcedPoint`, `OAI.Balanced.CandidateExposure.EligiblePair`, `OAI.Balanced.CandidateExposure.alignedInDirection`, `OAI.Balanced.CandidateExposure.alignmentExponent`, `OAI.Balanced.CandidateExposure.candidateAbundanceMeasurableSpace`, `OAI.Balanced.CandidateExposure.candidateHighMomentsMeasurableSpace`, `OAI.Balanced.CandidateExposure.candidateLabelMeasurableSpace`, `OAI.Balanced.CandidateExposure.centeredMomentConstant`, `OAI.Balanced.CandidateExposure.conditionalProbability`, `OAI.Balanced.CandidateExposure.eligibleTupleEquivRootPrescription`, `OAI.Balanced.CandidateExposure.eligibleTuples`, `OAI.Balanced.CandidateExposure.exposedLaw`, `OAI.Balanced.CandidateExposure.overlapProbabilitySum`, `OAI.Balanced.CandidateExposure.overlappingTupleCount`, `OAI.Balanced.CandidateExposure.pairModelMeasurableSpace`, `OAI.Balanced.CandidateExposure.pairPatternModel`, `OAI.Balanced.CandidateExposure.pairSuccessEvent` and 323 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `BalancedRyser_Candidates_CandidateAbundance`, `BalancedRyser_Candidates_CandidateAbundanceAssembly`, `BalancedRyser_Candidates_CandidateBasics`, `BalancedRyser_Candidates_CandidateConditionalMean`, `BalancedRyser_Candidates_CandidateConstituentMoments`, `BalancedRyser_Candidates_CandidateConstituentTail`, `BalancedRyser_Candidates_CandidateConstituentTarget`, `BalancedRyser_Candidates_CandidateExposedWitness`, `BalancedRyser_Candidates_CandidateExposure`, `BalancedRyser_Candidates_CandidateFirstMoment`, `BalancedRyser_Candidates_CandidateGeneratorPairFamily`, `BalancedRyser_Candidates_CandidateGeneratorPairModel`, `BalancedRyser_Candidates_CandidateGeneratorPairMoments`, `BalancedRyser_Candidates_CandidateGlobalLineMean`, `BalancedRyser_Candidates_CandidateGlobalLineModel`, `BalancedRyser_Candidates_CandidateGlobalLineTail`, `BalancedRyser_Candidates_CandidateGraphEndpoint`, `BalancedRyser_Candidates_CandidateHighMoments`, `BalancedRyser_Candidates_CandidateLabelBridge`, `BalancedRyser_Candidates_CandidateLineGate`, `BalancedRyser_Candidates_CandidateLineHitFamily`, `BalancedRyser_Candidates_CandidateMixedExternal`, `BalancedRyser_Candidates_CandidateOldExternalOverlap`, `BalancedRyser_Candidates_CandidateOldOppositeOverlap`, `BalancedRyser_Candidates_CandidatePairCounts`, `BalancedRyser_Candidates_CandidatePairFibers`, `BalancedRyser_Candidates_CandidatePairMoments`, `BalancedRyser_Candidates_CandidatePairPatternModel`, `BalancedRyser_Candidates_CandidatePointFamily`, `BalancedRyser_Candidates_CandidatePrescribedLine`, `BalancedRyser_Candidates_CandidatePrescriptionTransport`, `BalancedRyser_Candidates_CandidateProbabilityAssembly`, `BalancedRyser_Candidates_CandidateRetentionTransport`, `BalancedRyser_Candidates_CandidateRootCount`, `BalancedRyser_Candidates_CandidateRootFibers`, `BalancedRyser_Candidates_CandidateSecondary`, `BalancedRyser_Candidates_CandidateSelectionBridge`, `BalancedRyser_Candidates_CandidateTwoLineFamily`, `BalancedRyser_Candidates_CandidateTwoLineMoments`, `BalancedRyser_Candidates_CandidateValidityAssembly`, `BalancedRyser_Candidates_CandidateValidityWitness`, `BalancedRyser_Candidates_Candidates`, `BalancedRyser_Candidates_ConstituentOffsets`, `BalancedRyser_Candidates_DeletedConstituentForcing`, `BalancedRyser_Candidates_ExternalWitnessModel`, `BalancedRyser_Candidates_ExternalWitnessMoments`, `BalancedRyser_Candidates_MixedExternalAssembly`, `BalancedRyser_Construction_BlockPartitions`, `BalancedRyser_Construction_ConfigurationHypergraph`, `BalancedRyser_Construction_ConfigurationRealizationBridge`, `BalancedRyser_Construction_Construction`, `BalancedRyser_Construction_ConstructionRepresentationLemmas`, `BalancedRyser_Construction_LocalCoverObstruction`, `BalancedRyser_Construction_PartitionEncoding`, `BalancedRyser_Construction_PartitionHypergraph`, `BalancedRyser_Deletion_ConfigurationDeletion`, `BalancedRyser_Deletion_Deletion`, `BalancedRyser_Deletion_DeletionCoordinates`, `BalancedRyser_Deletion_UniformDeletionEnumeration`, `BalancedRyser_Incidence_Affine`, `BalancedRyser_Incidence_AffineIncidence`, `BalancedRyser_Incidence_AffinePairEvaluation`, `BalancedRyser_Incidence_AffinePencilForcing`, `BalancedRyser_Incidence_AffinePermutationExposure`, `BalancedRyser_Incidence_AffinePlaneOrderExposure`, `BalancedRyser_Incidence_AffineProfileExposure`, `BalancedRyser_Incidence_CandidateFreshIncidence`, `BalancedRyser_Incidence_CandidateIncidence`, `BalancedRyser_Incidence_CandidateIncidenceCountTransport`, `BalancedRyser_Incidence_CandidateIncidenceInitialSums`, `BalancedRyser_Incidence_CandidateIncidenceMean`, `BalancedRyser_Incidence_CandidateIncidenceModel`, `BalancedRyser_Incidence_CandidateIncidenceProbability`, `BalancedRyser_Incidence_CandidateIncidenceRootSums`, `BalancedRyser_Incidence_CandidateIncidenceTests`, `BalancedRyser_Incidence_CandidateIncidenceTransport`, `BalancedRyser_Incidence_CandidatePointIncidence`, `BalancedRyser_Incidence_CandidatePointIncidenceMean`, `BalancedRyser_Incidence_CandidateSmallIncidence`, `BalancedRyser_Incidence_CorePencil`, `BalancedRyser_Incidence_ElementaryIncidence`, `BalancedRyser_Incidence_PartialIncidenceCounts`, `BalancedRyser_Incidence_SinglePencilObstruction`, `BalancedRyser_Incidence_Stability`, `BalancedRyser_Local_AlignedFreeCoordinates`, `BalancedRyser_Local_AlignedListProbability`, `BalancedRyser_Local_AlignedPointExposure`, `BalancedRyser_Local_ChildAlignment`, `BalancedRyser_Local_GlobalPartialAlignment`, `BalancedRyser_Local_InjectionExposureLaw`, `BalancedRyser_Local_LowReuseOrder`, `BalancedRyser_Local_PartialAlignment`, `BalancedRyser_Local_TupleAlignment`, `BalancedRyser_Probability_Concentration`, `BalancedRyser_Probability_ConditionalOrderVariance`, `BalancedRyser_Probability_ConditionalRestriction`, `BalancedRyser_Probability_ConfigurationBlockCardinality`, `BalancedRyser_Probability_ConfigurationStructure`, `BalancedRyser_Probability_CoreRepresentatives`, `BalancedRyser_Probability_CountingExposureKernel`, `BalancedRyser_Probability_CountingExposurePosterior`, `BalancedRyser_Probability_CountingJointLaw`, `BalancedRyser_Probability_CoverCountingExposure`, `BalancedRyser_Probability_CylinderConditioning`, `BalancedRyser_Probability_FiniteFixedLaw`, `BalancedRyser_Probability_FiniteUniformConditioning`, `BalancedRyser_Probability_FiniteUniformFibers`, `BalancedRyser_Probability_ForcedNonsplitLabels`, `BalancedRyser_Probability_FullyExposedTargets`, `BalancedRyser_Probability_GeneratorEnumeration`, `BalancedRyser_Probability_GlobalTupleLaw`, `BalancedRyser_Probability_ParallelBlockCapacity`, `BalancedRyser_Probability_PatternAllowedGate`, `BalancedRyser_Probability_PatternGate`, `BalancedRyser_Probability_PatternIntegrability`, `BalancedRyser_Probability_PatternMomentsLemmas`, `BalancedRyser_Probability_PatternPrefixSupport`, `BalancedRyser_Probability_PointLabelInjective`, `BalancedRyser_Probability_RootPatternModel`, `BalancedRyser_Probability_RootSuccess`, `BalancedRyser_Probability_ThinningTail`, `BalancedRyser_Probability_UniformRestriction`, `BalancedRyser_Profiles_Profile`, `BalancedRyser_Profiles_ProfileEmpiricalMeasure`, `BalancedRyser_Profiles_ProfileMomentCompactness`, `BalancedRyser_Profiles_ProfileWitnessPayment`, `BalancedRyser_Selection_LineOccupancy`.
--
--   **Imports.** It imports the published bundle `Def_BalancedRyser`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ63Br002` and `OAIQ63Br003`; the statements `OAI.Balanced.CandidateAbundanceAssembly.tendsto_successful_roots`, `OAI.Balanced.CandidateIncidenceTests.candidateGraphResult_of_incidence_estimates`, `OAI.Balanced.CandidateIncidenceTests.candidateGraphResult_of_size_estimate`, `OAI.Balanced.CandidateIncidenceTests.tendsto_smallGood`, `OAI.Balanced.ExternalWitnessTail.candidateSlots_of_uniform_moment` and `OAI.Balanced.candidateGraph_proof`.
-- source:
--   OpenAI, Balanced counterexamples to Ryser's conjecture at prime orders (result family 162), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 162; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Balanced-Counterexamples-to-Rysers-Conjecture-at-Prime-Orders-September-27-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_BalancedRyser

section
-- module Solutions.OAIQ063_BR.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_Affine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced

abbrev Point (F : Type*) := F × F
abbrev Direction (F : Type*) := Option F
abbrev Line (F : Type*) := Direction F × F
abbrev ProjectivePoint (F : Type*) := Point F ⊕ Direction F

variable {F : Type*} [Field F]

def lineEval : Direction F → Point F → F
  | none, p => p.1
  | some m, p => p.2 - m * p.1

def OnLine (p : Point F) (l : Line F) : Prop := lineEval l.1 p = l.2

def lineThrough (d : Direction F) (p : Point F) : Line F := (d, lineEval d p)

def ThroughProjective (l : Line F) : ProjectivePoint F → Prop
  | Sum.inl p => OnLine p l
  | Sum.inr d => l.1 = d

def joiningLine [DecidableEq F] (p r : Point F) : Line F :=
  if p.1 = r.1 then (none, p.1)
  else let m := (r.2 - p.2) / (r.1 - p.1)
       (some m, p.2 - m * p.1)

def lineIntersection (l m : Line F) : Point F :=
  match l.1, m.1 with
  | none, none => (l.2, 0)
  | none, some b => (l.2, b * l.2 + m.2)
  | some a, none => (m.2, a * m.2 + l.2)
  | some a, some b =>
      let x := (m.2 - l.2) / (a - b)
      (x, a * x + l.2)

variable [Fintype F] [DecidableEq F]

instance instDecidableOnLine (p : Point F) (l : Line F) : Decidable (OnLine p l) :=
  inferInstanceAs (Decidable (lineEval l.1 p = l.2))

instance instDecidableThroughProjective (l : Line F) (P : ProjectivePoint F) : Decidable (ThroughProjective l P) :=
  match P with
  | Sum.inl p => inferInstanceAs (Decidable (OnLine p l))
  | Sum.inr d => inferInstanceAs (Decidable (l.1 = d))

def linePoints (l : Line F) : Finset (Point F) := Finset.univ.filter (fun p => OnLine p l)

def linesInDirection (d : Direction F) : Finset (Line F) :=
  Finset.univ.filter (fun l => l.1 = d)

def CoversPoints (C : Finset (Line F)) (U : Finset (Point F)) : Prop :=
  ∀ p ∈ U, ∃ l ∈ C, OnLine p l

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_TupleAlignment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.TupleAlignment

variable {F : Type*} [Field F]

def lineEvalEquiv (d e : Direction F) (hne : d ≠ e) : Point F ≃ F × F where
  toFun p := (lineEval d p, lineEval e p)
  invFun a := lineIntersection (d, a.1) (e, a.2)
  left_inv p := by
    rcases p with ⟨x,y⟩
    cases d with
    | none =>
      cases e with
      | none => exact (hne rfl).elim
      | some b => simp [lineEval, lineIntersection]
    | some a =>
      cases e with
      | none => simp [lineEval, lineIntersection]
      | some b =>
        have hab : a - b ≠ 0 := sub_ne_zero.mpr (by simpa using hne)
        apply Prod.ext <;> simp only [lineEval, lineIntersection]
        · field_simp
          ring
        · field_simp
          ring
  right_inv p := by
    rcases p with ⟨x,y⟩
    cases d with
    | none =>
      cases e with
      | none => exact (hne rfl).elim
      | some b => simp [lineEval, lineIntersection]
    | some a =>
      cases e with
      | none => simp [lineEval, lineIntersection]
      | some b =>
        have hab : a - b ≠ 0 := sub_ne_zero.mpr (by simpa using hne)
        apply Prod.ext <;> simp only [lineEval, lineIntersection]
        · ring
        · field_simp
          ring

@[simp] theorem lineEvalEquiv_apply (d e : Direction F) (hne : d ≠ e) (p : Point F) :
    lineEvalEquiv d e hne p = (lineEval d p, lineEval e p) := rfl

@[simp] theorem lineEvalEquiv_symm_apply (d e : Direction F) (hne : d ≠ e) (a : F × F) :
    (lineEvalEquiv d e hne).symm a = lineIntersection (d,a.1) (e,a.2) := rfl

def offsetPairsEquiv (σ : Fin 4 → Bool) :
    (Fin 4 → Bool → F) ≃ (Fin 4 → F × F) where
  toFun o i := (o i (σ i), o (i + 1) (!(σ (i + 1))))
  invFun p i b := if b = σ i then (p i).1 else (p (i - 1)).2
  left_inv o := by
    funext i b
    cases h : σ i <;> cases b <;> simp [h]
  right_inv p := by
    funext i
    apply Prod.ext <;> simp

def tuplePositionEquiv (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool) :
    (Fin 4 → Bool → F) ≃ (Fin 4 → Point F) :=
  (offsetPairsEquiv σ).trans
    (Equiv.piCongrRight fun i => (lineEvalEquiv (d i) (d (i + 1)) (hd i)).symm)

@[simp] theorem tuplePositionEquiv_apply (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (o : Fin 4 → Bool → F) (i : Fin 4) :
    tuplePositionEquiv d hd σ o i =
      lineIntersection (d i, o i (σ i))
        (d (i + 1), o (i + 1) (!(σ (i + 1)))) := rfl

def linePointEquiv (g : Direction F) (c : F) :
    {p : Point F // OnLine p (g, c)} ≃ F where
  toFun p := match g with | none => p.1.2 | some _ => p.1.1
  invFun t := ⟨match g with | none => (c,t) | some m => (t,m*t+c), by
    cases g <;> simp [OnLine, lineEval]⟩
  left_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨x,y⟩,h⟩
    cases g with
    | none =>
      have hx : x = c := h
      simp [hx]
    | some m =>
      have hy : y - m*x = c := h
      apply Prod.ext
      · rfl
      · dsimp
        linear_combination -hy
  right_inv t := by cases g <;> rfl

def alignedOffsetsEquiv (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (c : F) :
    {o : Fin 4 → Bool → F // ∀ i, OnLine (tuplePositionEquiv d hd σ o i) (g,c)} ≃
      (Fin 4 → F) :=
  (Equiv.subtypeEquivOfSubtype (tuplePositionEquiv d hd σ)).trans
    (Equiv.subtypePiEquivPi.trans
      (Equiv.piCongrRight fun _ => linePointEquiv g c))

theorem uniform_map_equiv {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] (e : α ≃ β) :
    (PMF.uniformOfFintype α).map e = PMF.uniformOfFintype β := by
  classical
  ext b
  rw [PMF.map_apply, ← e.symm.tsum_eq]
  simp [Fintype.card_congr e]

section Finite
variable [Fintype F] [DecidableEq F]

theorem card_alignedOffsets (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (c : F) :
    Fintype.card {o : Fin 4 → Bool → F //
      ∀ i, OnLine (tuplePositionEquiv d hd σ o i) (g,c)} = (Fintype.card F)^4 := by
  rw [Fintype.card_congr (alignedOffsetsEquiv d hd σ g c)]
  simp

theorem alignedOffsets_probability (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (c : F) :
    (Fintype.card {o : Fin 4 → Bool → F //
      ∀ i, OnLine (tuplePositionEquiv d hd σ o i) (g,c)} : ℝ) /
      Fintype.card (Fin 4 → Bool → F) = (Fintype.card F : ℝ)⁻¹^4 := by
  rw [card_alignedOffsets]
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow]
  have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

theorem alignedOffsets_outer_probability (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (c : F) :
    ((PMF.uniformOfFintype (Fin 4 → Bool → F)).toOuterMeasure
      {o | ∀ i, OnLine (tuplePositionEquiv d hd σ o i) (g,c)}).toReal =
      (Fintype.card F : ℝ)⁻¹^4 := by
  rw [PMF.toOuterMeasure_uniformOfFintype_apply, ENNReal.toReal_div]
  simp only [ENNReal.toReal_natCast]
  convert alignedOffsets_probability d hd σ g c using 2
  all_goals try with_reducible_and_instances rfl
  congr 1

end Finite

end Balanced.TupleAlignment

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_FiniteUniformConditioning
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

theorem uniform_filter_eq_subtype_map {α : Type*} [Fintype α] [Nonempty α]
    (s : Set α) [Fintype s] [Nonempty s]
    (h : ∃ a ∈ s, a ∈ (PMF.uniformOfFintype α).support) :
    (PMF.uniformOfFintype α).filter s h =
      (PMF.uniformOfFintype s).map Subtype.val := by
  classical
  ext a
  by_cases ha : a ∈ s
  · have hmap : ((PMF.uniformOfFintype s).map Subtype.val) a =
        (Fintype.card s : ENNReal)⁻¹ := by
      rw [PMF.map_apply]
      rw [tsum_eq_single (⟨a, ha⟩ : s)]
      · simp
      · intro b hb
        rw [ite_eq_right]
        intro hab
        exact hb (Subtype.ext hab.symm)
    rw [hmap, PMF.filter_apply, ← PMF.toOuterMeasure_apply,
      PMF.toOuterMeasure_uniformOfFintype_apply, Set.indicator_of_mem ha,
      PMF.uniformOfFintype_apply]
    have hq0 : (Fintype.card α : ENNReal) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    have hqtop : (Fintype.card α : ENNReal) ≠ ⊤ := by simp
    have hs0 : (Fintype.card s : ENNReal) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    have hstop : (Fintype.card s : ENNReal) ≠ ⊤ := by simp
    rw [div_eq_mul_inv, ENNReal.mul_inv (Or.inl hs0) (Or.inl hstop), inv_inv]
    calc
      (Fintype.card α : ENNReal)⁻¹ *
          ((Fintype.card s : ENNReal)⁻¹ * Fintype.card α) =
        (Fintype.card s : ENNReal)⁻¹ *
          ((Fintype.card α : ENNReal)⁻¹ * Fintype.card α) := by ac_rfl
      _ = _ := by rw [ENNReal.inv_mul_cancel hq0 hqtop, mul_one]
  · rw [PMF.filter_apply_eq_zero_of_notMem h ha, PMF.map_apply]
    symm
    apply ENNReal.tsum_eq_zero.mpr
    intro b
    rw [ite_eq_right]
    intro hab
    exact ha (hab ▸ b.2)

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

abbrev ChildOffsets (a : Bool → F) :=
  {o : Fin 4 → Bool → F // o 0 = a}

def childFreshEquiv (a : Bool → F) : ChildOffsets a ≃ (Fin 3 → Bool → F) where
  toFun o i := o.1 i.succ
  invFun f := ⟨Fin.cases a f, rfl⟩
  left_inv o := by
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact o.2.symm
    · rfl
  right_inv f := rfl

@[simp] theorem tuplePositionEquiv_symm_apply
    (d : Fin 4 → Direction F) (hd : ∀ i, d i ≠ d (i + 1))
    (σ : Fin 4 → Bool) (p : Fin 4 → Point F) (i : Fin 4) (b : Bool) :
    (tuplePositionEquiv d hd σ).symm p i b =
      if b = σ i then lineEval (d i) (p i) else lineEval (d i) (p (i - 1)) := by
  simp [tuplePositionEquiv, offsetPairsEquiv, lineEvalEquiv]

@[simp] theorem lineEvalEquiv_symm_fst (d e : Direction F) (hne : d ≠ e) (a : F × F) :
    lineEval d ((lineEvalEquiv d e hne).symm a) = a.1 :=
  congrArg Prod.fst ((lineEvalEquiv d e hne).apply_symm_apply a)

@[simp] theorem lineEvalEquiv_symm_snd (d e : Direction F) (hne : d ≠ e) (a : F × F) :
    lineEval e ((lineEvalEquiv d e hne).symm a) = a.2 :=
  congrArg Prod.snd ((lineEvalEquiv d e hne).apply_symm_apply a)

def childAlignedPositions (d₀ g : Direction F) (hg : d₀ ≠ g)
    (σ₀ : Bool) (c : F) (a : Bool → F) (x : F × F) : Fin 4 → Point F :=
  ![(lineEvalEquiv d₀ g hg).symm (a σ₀, c),
    ((linePointEquiv g c).symm x.1).1,
    ((linePointEquiv g c).symm x.2).1,
    (lineEvalEquiv d₀ g hg).symm (a (!σ₀), c)]

theorem childAlignedPositions_onLine (d₀ g : Direction F) (hg : d₀ ≠ g)
    (σ₀ : Bool) (c : F) (a : Bool → F) (x : F × F) (i : Fin 4) :
    OnLine (childAlignedPositions d₀ g hg σ₀ c a x i) (g,c) := by
  fin_cases i
  · exact lineEvalEquiv_symm_snd d₀ g hg (a σ₀,c)
  · exact ((linePointEquiv g c).symm x.1).2
  · exact ((linePointEquiv g c).symm x.2).2
  · exact lineEvalEquiv_symm_snd d₀ g hg (a (!σ₀),c)

abbrev AlignedChildOffsets (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (c : F) (a : Bool → F) :=
  {o : ChildOffsets a // ∀ i,
    OnLine (tuplePositionEquiv d hd σ o.1 i) (g,c)}

def alignedChildFromPair (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (hg : d 0 ≠ g) (c : F) (a : Bool → F) (x : F × F) :
    AlignedChildOffsets d hd σ g c a := by
  let p := childAlignedPositions (d 0) g hg (σ 0) c a x
  refine ⟨⟨(tuplePositionEquiv d hd σ).symm p, ?_⟩, ?_⟩
  · funext b
    rw [tuplePositionEquiv_symm_apply]
    by_cases hb : b = σ 0
    · rw [ite_eq_left hb]
      change lineEval (d 0) ((lineEvalEquiv (d 0) g hg).symm (a (σ 0), c)) = a b
      rw [lineEvalEquiv_symm_fst, hb]
    · rw [ite_eq_right hb]
      change lineEval (d 0) ((lineEvalEquiv (d 0) g hg).symm (a (!(σ 0)), c)) = a b
      rw [lineEvalEquiv_symm_fst]
      cases b <;> cases hσ : σ 0 <;> simp_all
  · intro i
    change OnLine ((tuplePositionEquiv d hd σ)
      ((tuplePositionEquiv d hd σ).symm p) i) (g,c)
    rw [Equiv.apply_symm_apply]
    exact childAlignedPositions_onLine (d 0) g hg (σ 0) c a x i

@[simp] theorem alignedChildFromPair_positions (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (hg : d 0 ≠ g) (c : F) (a : Bool → F) (x : F × F) :
    tuplePositionEquiv d hd σ (alignedChildFromPair d hd σ g hg c a x).1.1 =
      childAlignedPositions (d 0) g hg (σ 0) c a x := by
  exact (tuplePositionEquiv d hd σ).apply_symm_apply _

@[simp] theorem tuplePosition_lineEval_left (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (o : Fin 4 → Bool → F) (i : Fin 4) :
    lineEval (d i) (tuplePositionEquiv d hd σ o i) = o i (σ i) :=
  lineEvalEquiv_symm_fst (d i) (d (i + 1)) (hd i) _

@[simp] theorem tuplePosition_lineEval_right (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (o : Fin 4 → Bool → F) (i : Fin 4) :
    lineEval (d (i + 1)) (tuplePositionEquiv d hd σ o i) =
      o (i + 1) (!(σ (i + 1))) :=
  lineEvalEquiv_symm_snd (d i) (d (i + 1)) (hd i) _

def alignedChildToPair (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (c : F) (a : Bool → F)
    (o : AlignedChildOffsets d hd σ g c a) : F × F :=
  ((linePointEquiv g c) ⟨tuplePositionEquiv d hd σ o.1.1 1, o.2 1⟩,
   (linePointEquiv g c) ⟨tuplePositionEquiv d hd σ o.1.1 2, o.2 2⟩)

def alignedChildOffsetsEquiv (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (hg : d 0 ≠ g) (c : F) (a : Bool → F) :
    AlignedChildOffsets d hd σ g c a ≃ F × F where
  toFun := alignedChildToPair d hd σ g c a
  invFun := alignedChildFromPair d hd σ g hg c a
  left_inv o := by
    apply Subtype.ext
    apply Subtype.ext
    apply (tuplePositionEquiv d hd σ).injective
    rw [alignedChildFromPair_positions]
    funext i
    fin_cases i
    · change (lineEvalEquiv (d 0) g hg).symm (a (σ 0), c) = _
      apply (lineEvalEquiv (d 0) g hg).injective
      rw [Equiv.apply_symm_apply]
      apply Prod.ext
      · change a (σ 0) = lineEval (d 0) (tuplePositionEquiv d hd σ o.1.1 0)
        rw [tuplePosition_lineEval_left, o.1.2]
      · exact (o.2 0).symm
    · exact congrArg Subtype.val ((linePointEquiv g c).symm_apply_apply
        ⟨tuplePositionEquiv d hd σ o.1.1 1, o.2 1⟩)
    · exact congrArg Subtype.val ((linePointEquiv g c).symm_apply_apply
        ⟨tuplePositionEquiv d hd σ o.1.1 2, o.2 2⟩)
    · change (lineEvalEquiv (d 0) g hg).symm (a (!(σ 0)), c) = _
      apply (lineEvalEquiv (d 0) g hg).injective
      rw [Equiv.apply_symm_apply]
      apply Prod.ext
      · change a (!(σ 0)) = lineEval (d 0) (tuplePositionEquiv d hd σ o.1.1 3)
        have h := tuplePosition_lineEval_right d hd σ o.1.1 3
        simpa only [show (3 : Fin 4) + 1 = 0 from rfl, o.1.2] using h.symm
      · exact (o.2 3).symm
  right_inv x := by
    simp only [alignedChildToPair, alignedChildFromPair_positions]
    change ((linePointEquiv g c) ((linePointEquiv g c).symm x.1),
      (linePointEquiv g c) ((linePointEquiv g c).symm x.2)) = x
    simp only [Equiv.apply_symm_apply, Prod.mk.eta]

abbrev ChildOffsetsAt (j : Fin 4) (a : Bool → F) :=
  {o : Fin 4 → Bool → F // o j = a}

def childRotationEquiv (j : Fin 4) (a : Bool → F) :
    ChildOffsetsAt j a ≃ ChildOffsets a where
  toFun o := ⟨fun i => o.1 (i + j), by simpa using o.2⟩
  invFun o := ⟨fun i => o.1 (i - j), by simpa using o.2⟩
  left_inv o := by
    apply Subtype.ext
    funext i
    simp
  right_inv o := by
    apply Subtype.ext
    funext i
    simp

omit [Field F] in
theorem rotated_adjacent (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (j : Fin 4) :
    ∀ i, d (i + j) ≠ d (i + 1 + j) := by
  intro i
  simpa only [add_assoc, add_comm, add_left_comm] using hd (i + j)

theorem tuplePosition_rotation (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (o : Fin 4 → Bool → F) (j i : Fin 4) :
    tuplePositionEquiv (fun k => d (k + j)) (rotated_adjacent d hd j)
      (fun k => σ (k + j)) (fun k => o (k + j)) i =
      tuplePositionEquiv d hd σ o (i + j) := by
  simp only [tuplePositionEquiv_apply, add_assoc, add_comm]

abbrev AlignedChildOffsetsAt (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (c : F) (j : Fin 4) (a : Bool → F) :=
  {o : ChildOffsetsAt j a // ∀ i,
    OnLine (tuplePositionEquiv d hd σ o.1 i) (g,c)}

def alignedChildRotationEquiv (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (c : F) (j : Fin 4) (a : Bool → F) :
    AlignedChildOffsetsAt d hd σ g c j a ≃
      AlignedChildOffsets (fun i => d (i + j)) (rotated_adjacent d hd j)
        (fun i => σ (i + j)) g c a :=
  Equiv.subtypeEquiv (childRotationEquiv j a) (fun o => by
    constructor
    · intro ho i
      change OnLine (tuplePositionEquiv (fun k => d (k + j))
        (rotated_adjacent d hd j) (fun k => σ (k + j))
        (fun k => o.1 (k + j)) i) (g,c)
      rw [tuplePosition_rotation]
      exact ho (i + j)
    · intro ho i
      have h := ho (i - j)
      change OnLine (tuplePositionEquiv (fun k => d (k + j))
        (rotated_adjacent d hd j) (fun k => σ (k + j))
        (fun k => o.1 (k + j)) (i - j)) (g,c) at h
      rw [tuplePosition_rotation] at h
      simpa only [sub_add_cancel] using h)

def alignedChildOffsetsAtEquiv (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (j : Fin 4) (hg : d j ≠ g) (c : F) (a : Bool → F) :
    AlignedChildOffsetsAt d hd σ g c j a ≃ F × F :=
  (alignedChildRotationEquiv d hd σ g c j a).trans
    (alignedChildOffsetsEquiv (fun i => d (i + j)) (rotated_adjacent d hd j)
      (fun i => σ (i + j)) g (by simpa using hg) c a)

instance instNonemptyChildOffsetsAt (j : Fin 4) (a : Bool → F) : Nonempty (ChildOffsetsAt j a) :=
  ⟨(childRotationEquiv j a).symm ((childFreshEquiv a).symm (fun _ _ => 0))⟩

section Finite
variable [Fintype F] [DecidableEq F]

omit [Field F] in
theorem card_childOffsets (a : Bool → F) :
    Fintype.card (ChildOffsets a) = Fintype.card F ^ 6 := by
  rw [Fintype.card_congr (childFreshEquiv a)]
  simp [← pow_mul]

omit [Field F] in
theorem card_childOffsetsAt (j : Fin 4) (a : Bool → F) :
    Fintype.card (ChildOffsetsAt j a) = Fintype.card F ^ 6 := by
  rw [Fintype.card_congr (childRotationEquiv j a), card_childOffsets]

theorem card_alignedChildOffsetsAt (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (j : Fin 4) (hg : d j ≠ g) (c : F) (a : Bool → F) :
    Fintype.card (AlignedChildOffsetsAt d hd σ g c j a) = Fintype.card F ^ 2 := by
  rw [Fintype.card_congr (alignedChildOffsetsAtEquiv d hd σ g j hg c a)]
  simp [pow_two]

theorem alignedChildOffsetsAt_pmf_probability (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (j : Fin 4) (hg : d j ≠ g) (c : F) (a : Bool → F) :
    ((PMF.uniformOfFintype (ChildOffsetsAt j a)).toOuterMeasure
      {o | ∀ i, OnLine (tuplePositionEquiv d hd σ o.1 i) (g,c)}).toReal =
      (Fintype.card F : ℝ)⁻¹ ^ 4 := by
  rw [PMF.toOuterMeasure_uniformOfFintype_apply]
  change ((Fintype.card (AlignedChildOffsetsAt d hd σ g c j a) : ENNReal) /
    (Fintype.card (ChildOffsetsAt j a) : ENNReal)).toReal = _
  rw [card_alignedChildOffsetsAt d hd σ g j hg, card_childOffsetsAt]
  simp only [Nat.cast_pow, ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_natCast]
  have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

end Finite
end Balanced.TupleAlignment

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_PartialAlignment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.PartialAlignment
open TupleAlignment

variable {F : Type*}

abbrev PartialOffsets (J : Finset (Fin 4)) (a : Fin 4 → Bool → F) :=
  {o : Fin 4 → Bool → F // ∀ i ∈ J, o i = a i}

def freshGenerators (J : Finset (Fin 4)) : Finset (Fin 4) :=
  Finset.univ.filter (fun i => i ∉ J)

def freePositions (J : Finset (Fin 4)) : Finset (Fin 4) :=
  Finset.univ.filter (fun i => i ∉ J ∧ i + 1 ∉ J)

def partialFreshEquiv (J : Finset (Fin 4)) (a : Fin 4 → Bool → F) :
    PartialOffsets J a ≃ ({i : Fin 4 // i ∉ J} → Bool → F) where
  toFun o i := o.1 i.1
  invFun f := ⟨fun i => if hi : i ∈ J then a i else f ⟨i,hi⟩, by
    intro i hi
    simp [hi]⟩
  left_inv o := by
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ J
    · simp only [dite_eq_left hi]
      exact (o.2 i hi).symm
    · simp only [dite_eq_right hi]
  right_inv f := by
    funext i
    simp only [dite_eq_right i.2]

variable [Field F]

abbrev AlignedPartialOffsets (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (c : F) (J : Finset (Fin 4)) (a : Fin 4 → Bool → F) :=
  {o : PartialOffsets J a // ∀ i,
    OnLine (tuplePositionEquiv d hd σ o.1 i) (g,c)}

def alignedFreeCoordinates (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (c : F) (J : Finset (Fin 4)) (a : Fin 4 → Bool → F)
    (o : AlignedPartialOffsets d hd σ g c J a) :
    {i : Fin 4 // i ∈ freePositions J} → F :=
  fun i => (linePointEquiv g c) ⟨tuplePositionEquiv d hd σ o.1.1 i.1, o.2 i.1⟩

theorem alignedFreeCoordinates_injective (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (hg : ∀ i, d i ≠ g) (c : F)
    (J : Finset (Fin 4)) (a : Fin 4 → Bool → F) :
    Function.Injective (alignedFreeCoordinates d hd σ g c J a) := by
  intro o p h
  apply Subtype.ext
  apply Subtype.ext
  apply (tuplePositionEquiv d hd σ).injective
  funext i
  by_cases hfree : i ∉ J ∧ i + 1 ∉ J
  · have hi : i ∈ freePositions J := by simp [freePositions, hfree]
    have hcoord := congrFun h (⟨i,hi⟩ : {i // i ∈ freePositions J})
    exact congrArg Subtype.val ((linePointEquiv g c).injective hcoord)
  · by_cases hi : i ∈ J
    · apply (lineEvalEquiv (d i) g (hg i)).injective
      apply Prod.ext
      · change lineEval (d i) (tuplePositionEquiv d hd σ o.1.1 i) =
          lineEval (d i) (tuplePositionEquiv d hd σ p.1.1 i)
        rw [tuplePosition_lineEval_left, tuplePosition_lineEval_left,
          o.1.2 i hi, p.1.2 i hi]
      · exact (o.2 i).trans (p.2 i).symm
    · have hnext : i + 1 ∈ J := by tauto
      apply (lineEvalEquiv (d (i + 1)) g (hg (i + 1))).injective
      apply Prod.ext
      · change lineEval (d (i + 1)) (tuplePositionEquiv d hd σ o.1.1 i) =
          lineEval (d (i + 1)) (tuplePositionEquiv d hd σ p.1.1 i)
        rw [tuplePosition_lineEval_right, tuplePosition_lineEval_right,
          o.1.2 (i + 1) hnext, p.1.2 (i + 1) hnext]
      · exact (o.2 i).trans (p.2 i).symm

instance instNonemptyPartialOffsets (J : Finset (Fin 4)) (a : Fin 4 → Bool → F) :
    Nonempty (PartialOffsets J a) := ⟨⟨a, by intro i hi; rfl⟩⟩

section Finite
variable [Fintype F] [DecidableEq F]

omit [Field F] in
theorem card_partialOffsets (J : Finset (Fin 4)) (a : Fin 4 → Bool → F) :
    Fintype.card (PartialOffsets J a) =
      Fintype.card F ^ (2 * (freshGenerators J).card) := by
  rw [Fintype.card_congr (partialFreshEquiv J a)]
  simp only [Fintype.card_fun, Fintype.card_bool, ← pow_mul, Fintype.card_subtype]
  rfl

omit [DecidableEq F] in

theorem partialOffsets_supported (J : Finset (Fin 4)) (a : Fin 4 → Bool → F) :
    ∃ o ∈ {o : Fin 4 → Bool → F | ∀ i ∈ J, o i = a i},
      o ∈ (PMF.uniformOfFintype (Fin 4 → Bool → F)).support :=
  ⟨a, by intro i hi; rfl, PMF.mem_support_uniformOfFintype _⟩

theorem partialOffsets_conditional_law (J : Finset (Fin 4)) (a : Fin 4 → Bool → F) :
    (PMF.uniformOfFintype (Fin 4 → Bool → F)).filter
      {o | ∀ i ∈ J, o i = a i} (partialOffsets_supported J a) =
      (PMF.uniformOfFintype (PartialOffsets J a)).map Subtype.val := by
  let : Nonempty ({o : Fin 4 → Bool → F | ∀ i ∈ J, o i = a i} :
      Set (Fin 4 → Bool → F)) := ⟨⟨a, by intro i hi; rfl⟩⟩
  exact Balanced.uniform_filter_eq_subtype_map _ _

end Finite
end Balanced.PartialAlignment

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_UniformRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.TupleAlignment

open scoped BigOperators ENNReal

theorem uniform_map_fst {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] :
    (PMF.uniformOfFintype (α × β)).map Prod.fst = PMF.uniformOfFintype α := by
  classical
  ext a
  simp only [PMF.map_apply, PMF.uniformOfFintype_apply, tsum_fintype,
    Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul]
  simp [ENNReal.mul_inv, ENNReal.mul_inv_cancel, Fintype.card_ne_zero, mul_left_comm]

noncomputable def restrictionEquiv {ι D A : Type*} (e : ι ↪ D) :
    (D → A) ≃ (ι → A) × ({d : D // d ∉ Set.range e} → A) := by
  classical
  exact (Equiv.piEquivPiSubtypeProd (fun d => d ∈ Set.range e) (fun _ => A)).trans
    (Equiv.prodCongr
      (Equiv.piCongrLeft (fun _ : Set.range e => A)
        (Equiv.ofInjective e e.injective)).symm
      (Equiv.refl _))

@[simp] theorem restrictionEquiv_fst {ι D A : Type*} (e : ι ↪ D)
    (o : D → A) (i : ι) : (restrictionEquiv e o).1 i = o (e i) := rfl

theorem uniform_map_restrict {ι D A : Type*}
    [Fintype ι] [Fintype D] [Fintype A] [DecidableEq ι] [DecidableEq D] [Nonempty A] (e : ι ↪ D) :
    (PMF.uniformOfFintype (D → A)).map (fun o i => o (e i)) =
      PMF.uniformOfFintype (ι → A) := by
  classical
  have h := congrArg (fun p => p.map Prod.fst) (uniform_map_equiv (restrictionEquiv (A:=A) e))
  rw [PMF.map_comp, uniform_map_fst] at h
  exact h

end Balanced.TupleAlignment

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_ConditionalRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.ConditionalRestriction
open TupleAlignment

noncomputable section
attribute [local instance] Classical.propDecidable

variable {D ι A : Type*}

abbrev FixedArray (P : D → Prop) (a : D → A) :=
  {o : D → A // ∀ d, P d → o d = a d}

instance instNonemptyFixedArray (P : D → Prop) (a : D → A) : Nonempty (FixedArray P a) :=
  ⟨⟨a, by intro d hd; rfl⟩⟩

def fixedFreshEquiv (P : D → Prop) (a : D → A) :
    FixedArray P a ≃ ({d : D // ¬ P d} → A) where
  toFun o d := o.1 d.1
  invFun f := ⟨fun d => if hd : P d then a d else f ⟨d,hd⟩, by
    intro d hd
    simp only [dite_eq_left hd]⟩
  left_inv o := by
    apply Subtype.ext
    funext d
    by_cases hd : P d
    · simp only [dite_eq_left hd]
      exact (o.2 d hd).symm
    · simp only [dite_eq_right hd]
  right_inv f := by
    funext d
    simp only [dite_eq_right d.2]

def fixedRestrict (e : ι ↪ D) (P : D → Prop) (a : D → A)
    (o : FixedArray P a) : FixedArray (fun i => P (e i)) (fun i => a (e i)) :=
  ⟨fun i => o.1 (e i), fun i hi => o.2 (e i) hi⟩

def freshEmbedding (e : ι ↪ D) (P : D → Prop) :
    {i : ι // ¬ P (e i)} ↪ {d : D // ¬ P d} where
  toFun i := ⟨e i.1, i.2⟩
  inj' := by
    intro i j h
    apply Subtype.ext
    exact e.injective (congrArg Subtype.val h)

theorem fixedRestriction_commutes (e : ι ↪ D) (P : D → Prop) (a : D → A) :
    fixedRestrict e P a ∘ (fixedFreshEquiv P a).symm =
      (fixedFreshEquiv (fun i => P (e i)) (fun i => a (e i))).symm ∘
        (fun f i => f (freshEmbedding e P i)) := by
  funext f
  apply Subtype.ext
  funext i
  rfl

variable [Fintype D] [Fintype ι] [Fintype A]
  [DecidableEq D] [DecidableEq ι] [Nonempty A]

theorem uniform_fixed_restrict (e : ι ↪ D) (P : D → Prop) (a : D → A) :
    (PMF.uniformOfFintype (FixedArray P a)).map (fixedRestrict e P a) =
      PMF.uniformOfFintype (FixedArray (fun i => P (e i)) (fun i => a (e i))) := by
  have hsource := uniform_map_equiv (fixedFreshEquiv P a).symm
  have htarget := uniform_map_equiv (fixedFreshEquiv (fun i => P (e i)) (fun i => a (e i))).symm
  have hrestrict := uniform_map_restrict (A := A) (freshEmbedding e P)
  rw [← hsource, PMF.map_comp, fixedRestriction_commutes,
    ← PMF.map_comp, hrestrict, htarget]

theorem fixed_supported (P : D → Prop) (a : D → A) :
    ∃ o ∈ {o : D → A | ∀ d, P d → o d = a d},
      o ∈ (PMF.uniformOfFintype (D → A)).support :=
  ⟨a, by intro d hd; rfl, PMF.mem_support_uniformOfFintype _⟩

theorem uniform_fixed_filter (P : D → Prop) (a : D → A) :
    (PMF.uniformOfFintype (D → A)).filter
      {o | ∀ d, P d → o d = a d} (fixed_supported P a) =
      (PMF.uniformOfFintype (FixedArray P a)).map Subtype.val := by
  let : Nonempty ({o : D → A | ∀ d, P d → o d = a d} : Set (D → A)) :=
    ⟨⟨a, by intro d hd; rfl⟩⟩
  exact Balanced.uniform_filter_eq_subtype_map _ _

theorem uniform_conditional_restrict (e : ι ↪ D) (P : D → Prop) (a : D → A) :
    ((PMF.uniformOfFintype (D → A)).filter
      {o | ∀ d, P d → o d = a d} (fixed_supported P a)).map
      (fun o i => o (e i)) =
    (PMF.uniformOfFintype (ι → A)).filter
      {o | ∀ i, P (e i) → o i = a (e i)}
      (fixed_supported (fun i => P (e i)) (fun i => a (e i))) := by
  rw [uniform_fixed_filter, uniform_fixed_filter, PMF.map_comp]
  change (PMF.uniformOfFintype (FixedArray P a)).map
    (Subtype.val ∘ fixedRestrict e P a) = _
  rw [← PMF.map_comp, uniform_fixed_restrict]

end
end Balanced.ConditionalRestriction

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Construction_Construction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced

noncomputable section
attribute [local instance] Classical.propDecidable

abbrev Slot (F : Type*) := Direction F × Bool
abbrev MergedPairs (F : Type*) := Direction F → Bool → F

structure FourTuple (F : Type*) where
  generator : Fin 4 → Direction F
  side : Fin 4 → Bool
  deriving DecidableEq

structure SplitChoice (F : Type*) where
  line : Line F
  tuple : FourTuple F
  deriving DecidableEq

structure Configuration (F : Type*) where
  merged : MergedPairs F
  choice : Slot F → SplitChoice F
  deriving DecidableEq

instance instFintypeFourTuple {F : Type*} [Fintype F] : Fintype (FourTuple F) :=
  Fintype.ofEquiv ((Fin 4 → Direction F) × (Fin 4 → Bool))
    { toFun := fun p => ⟨p.1, p.2⟩
      invFun := fun t => (t.generator, t.side)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

instance instFintypeSplitChoice {F : Type*} [Fintype F] : Fintype (SplitChoice F) :=
  Fintype.ofEquiv (Line F × FourTuple F)
    { toFun := fun p => ⟨p.1, p.2⟩
      invFun := fun t => (t.line, t.tuple)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def constituent (M : MergedPairs F) (d : Direction F) (s : Bool) : Line F := (d, M d s)

def DistinctConstituents (M : MergedPairs F) : Prop :=
  ∀ d, M d false ≠ M d true

def constituentLines (M : MergedPairs F) : Finset (Line F) :=
  Finset.univ.image (fun ds : Direction F × Bool => constituent M ds.1 ds.2)

def mergedPoints (M : MergedPairs F) (d : Direction F) : Finset (Point F) :=
  linePoints (constituent M d false) ∪ linePoints (constituent M d true)

def tuplePoint (M : MergedPairs F) (T : FourTuple F) (i : Fin 4) : Point F :=
  lineIntersection (constituent M (T.generator i) (T.side i))
    (constituent M (T.generator (i + 1)) (!(T.side (i + 1))))

def designated (M : MergedPairs F) (C : SplitChoice F) : Finset (Point F) :=
  Finset.univ.image (tuplePoint M C.tuple)

def generatorSet (T : FourTuple F) : Finset (Direction F) :=
  Finset.univ.image T.generator

def Adjacent (M : MergedPairs F) (S : Line F) (p r : Point F) : Prop :=
  OnLine p S ∧ OnLine r S ∧ p ≠ r ∧ ∃ d : Direction F, d ≠ S.1 ∧
    ((OnLine p (constituent M d false) ∧ OnLine r (constituent M d true)) ∨
     (OnLine p (constituent M d true) ∧ OnLine r (constituent M d false)))

noncomputable def ValidChoice (M : MergedPairs F) (g : Direction F)
    (C : SplitChoice F) : Prop :=
  C.line.1 = g ∧ C.line ∉ constituentLines M ∧
  Function.Injective C.tuple.generator ∧ (∀ i, C.tuple.generator i ≠ g) ∧
  Function.Injective (tuplePoint M C.tuple) ∧
  (∀ i, OnLine (tuplePoint M C.tuple i) C.line) ∧
  ¬ Adjacent M C.line (tuplePoint M C.tuple 0) (tuplePoint M C.tuple 2) ∧
  ¬ Adjacent M C.line (tuplePoint M C.tuple 1) (tuplePoint M C.tuple 3) ∧
  ∀ p, OnLine p C.line → p ∉ designated M C →
    (Finset.univ.filter (fun i : Fin 4 => Adjacent M C.line p (tuplePoint M C.tuple i))).card ≤ 1

namespace Configuration

variable (C : Configuration F)

noncomputable def Valid : Prop :=
  DistinctConstituents C.merged ∧ ∀ s, ValidChoice C.merged s.1 (C.choice s)

noncomputable def Compatible : Prop :=
  (∀ i j, i ≠ j → ∀ p ∈ designated C.merged (C.choice j), ¬ OnLine p (C.choice i).line) ∧
  (∀ i j, i ≠ j →
    ((generatorSet (C.choice i).tuple) ∩ (generatorSet (C.choice j).tuple)).card ≤ 1) ∧
  (∀ i j, i ≠ j → i.1 = j.1 → ∀ d,
    ¬ (2 ≤ ((designated C.merged (C.choice i)) ∩ mergedPoints C.merged d).card ∧
       1 ≤ ((designated C.merged (C.choice j)) ∩ mergedPoints C.merged d).card))

def splitLines : Finset (Line F) := Finset.univ.image (fun s => (C.choice s).line)

def deletedLines : Finset (Line F) :=
  C.splitLines ∪ Finset.univ.image (fun d => constituent C.merged d true)

def core : Finset (Point F) :=
  Finset.univ.filter (fun p => ∀ l ∈ C.deletedLines, ¬ OnLine p l)

def retained : Finset (Point F) :=
  Finset.univ.filter (fun p => ∀ l ∈ C.splitLines, ¬ OnLine p l)

def points : Finset (Point F) :=
  C.retained ∪ Finset.univ.biUnion (fun s => designated C.merged (C.choice s))

def splitLinesAt (p : Point F) : Finset (Line F) :=
  C.splitLines.filter (OnLine p)

def splitMultiplicity (p : Point F) : ℕ := (C.splitLinesAt p).card

def designatedAt (p : Point F) : Finset (Point F) :=
  (Finset.univ.filter (fun s => OnLine p (C.choice s).line)).biUnion
    (fun s => designated C.merged (C.choice s))

def partnerSet (p : Point F) : Finset (Point F) :=
  (C.designatedAt p).filter (fun x => ∃ ds : Direction F × Bool,
    OnLine p (constituent C.merged ds.1 ds.2) ∧
    OnLine x (constituent C.merged ds.1 (!ds.2)))

def Occupancy (ρ : ℝ) (B : ℕ) : Prop :=
  (∀ p, ((constituentLines C.merged).filter (OnLine p)).card ≤ B) ∧
  (∀ l, l ∉ C.deletedLines → ρ * Fintype.card F ≤ ((linePoints l ∩ C.core).card : ℝ)) ∧
  (∀ d, ρ * Fintype.card F ≤
    ((linePoints (constituent C.merged d true) ∩ C.retained).card : ℝ))

def CoreConcentration (ρ : ℝ) : Prop :=
  ∀ L : Finset (Line F), (∀ l ∈ L, l ∉ C.deletedLines) →
    L.card ≤ Fintype.card F → CoversPoints L C.core →
    ∃ P : ProjectivePoint F,
      (1 - ρ / 4) * Fintype.card F ≤ ((L.filter (fun l => ThroughProjective l P)).card : ℝ)

end Configuration

abbrev LocalPiece (F : Type*) := Finset (Point F) ⊕ (Line F ⊕ Direction F)

namespace Configuration

variable (C : Configuration F)

def localPiecePoints : LocalPiece F → Finset (Point F)
  | Sum.inl U => U
  | Sum.inr (Sum.inl l) => linePoints l
  | Sum.inr (Sum.inr d) => mergedPoints C.merged d

def AllowedLocalPiece (p : Point F) : LocalPiece F → Prop
  | Sum.inl U => U.card ≤ 2
  | Sum.inr (Sum.inl l) => l ∉ C.splitLinesAt p ∪ constituentLines C.merged
  | Sum.inr (Sum.inr _) => True

def LocalCondition : Prop :=
  ∀ p, 3 ≤ C.splitMultiplicity p →
    ¬ ∃ A : Finset (LocalPiece F), A.card ≤ C.splitMultiplicity p - 1 ∧
      (∀ a ∈ A, C.AllowedLocalPiece p a) ∧
      C.designatedAt p ⊆ C.partnerSet p ∪ A.biUnion C.localPiecePoints

abbrev BlockLabel (F : Type*) := Line F ⊕ (Direction F ⊕ (Slot F × Bool))

def blockDirection : BlockLabel F → Direction F
  | Sum.inl l => l.1
  | Sum.inr (Sum.inl d) => d
  | Sum.inr (Sum.inr (s, _)) => s.1

def blockPoints : BlockLabel F → Finset (Point F)
  | Sum.inl l => linePoints l ∩ C.points
  | Sum.inr (Sum.inl d) => mergedPoints C.merged d ∩ C.points
  | Sum.inr (Sum.inr (s, false)) =>
      {tuplePoint C.merged (C.choice s).tuple 0, tuplePoint C.merged (C.choice s).tuple 2}
  | Sum.inr (Sum.inr (s, true)) =>
      {tuplePoint C.merged (C.choice s).tuple 1, tuplePoint C.merged (C.choice s).tuple 3}

def IsBlockLabel : BlockLabel F → Prop
  | Sum.inl l => l ∉ C.splitLines ∪ constituentLines C.merged
  | Sum.inr _ => True

noncomputable def blockLabels : Finset (BlockLabel F) :=
  Finset.univ.filter C.IsBlockLabel

noncomputable def labelsInDirection (d : Direction F) : Finset (BlockLabel F) :=
  C.blockLabels.filter (fun b => blockDirection b = d)

end Configuration
end
end Balanced

end OAI
end

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

def SupportsValidTuple (M : MergedPairs F) (l : Line F) : Prop :=
  ∃ T : FourTuple F, ValidChoice M l.1 ⟨l, T⟩

def retainedChoice (M : MergedPairs F) (l : Line F) : SplitChoice F :=
  ⟨l, if h : SupportsValidTuple M l then Classical.choose h
    else ⟨fun _ => none, fun _ => false⟩⟩

abbrev CandidateVertex (F : Type*) := Slot F × F

def candidateLine (v : CandidateVertex F) : Line F := (v.1.1, v.2)

def candidateChoice (M : MergedPairs F) (v : CandidateVertex F) : SplitChoice F :=
  retainedChoice M (candidateLine v)

def candidateVertices (M : MergedPairs F) : Finset (CandidateVertex F) :=
  Finset.univ.filter (fun v => SupportsValidTuple M (candidateLine v))

def candidateSlot (M : MergedPairs F) (s : Slot F) : Finset (CandidateVertex F) :=
  (candidateVertices M).filter (fun v => v.1 = s)

def ChoicesCompatible (M : MergedPairs F) (g h : Direction F)
    (A B : SplitChoice F) : Prop :=
  (∀ p ∈ designated M A, ¬ OnLine p B.line) ∧
  (∀ p ∈ designated M B, ¬ OnLine p A.line) ∧
  ((generatorSet A.tuple) ∩ (generatorSet B.tuple)).card ≤ 1 ∧
  (g = h → ∀ d,
    ¬ (2 ≤ ((designated M A) ∩ mergedPoints M d).card ∧
       1 ≤ ((designated M B) ∩ mergedPoints M d).card) ∧
    ¬ (2 ≤ ((designated M B) ∩ mergedPoints M d).card ∧
       1 ≤ ((designated M A) ∩ mergedPoints M d).card))

def CandidateAdjacent (M : MergedPairs F) (v w : CandidateVertex F) : Prop :=
  v ∈ candidateVertices M ∧ w ∈ candidateVertices M ∧ v.1 ≠ w.1 ∧
  ¬ ChoicesCompatible M v.1.1 w.1.1 (candidateChoice M v) (candidateChoice M w)

def candidateNeighbors (M : MergedPairs F) (v : CandidateVertex F) : Finset (CandidateVertex F) :=
  (candidateVertices M).filter (CandidateAdjacent M v)

def sampledMultiplicity (M : MergedPairs F) (p : Point F) : ℕ :=
  (Finset.univ.filter (fun ds : Direction F × Bool => OnLine p (constituent M ds.1 ds.2))).card

def initialDeletedLines (M : MergedPairs F) : Finset (Line F) :=
  Finset.univ.image (fun d => constituent M d true)

def initiallyRetained (M : MergedPairs F) : Finset (Point F) :=
  Finset.univ.filter (fun p => ∀ l ∈ initialDeletedLines M, ¬ OnLine p l)

def CandidateGraphGood (M : MergedPairs F) (c C : ℝ) : Prop :=
  let q : ℝ := Fintype.card F
  (∀ s, c * q ≤ ((candidateSlot M s).card : ℝ) ∧
    (candidateSlot M s).card ≤ Fintype.card F) ∧
  (∀ v ∈ candidateVertices M,
    ((candidateNeighbors M v).card : ℝ) ≤ C * q ∧
    ∀ s, (((candidateNeighbors M v) ∩ candidateSlot M s).card : ℝ) ≤ q ^ (1 / 8 : ℝ)) ∧
  (∀ v ∈ candidateVertices M, ∃ J : Finset (CandidateVertex F),
    J ⊆ candidateVertices M ∧ (J.card : ℝ) ≤ q ^ (1 / 8 : ℝ) ∧
    (∀ w ∈ J, CandidateAdjacent M v w ∨ w.1 = v.1) ∧
    ∀ w ∈ candidateVertices M, w ∉ J →
      (((candidateNeighbors M v) ∩ candidateNeighbors M w).card : ℝ) ≤ q ^ (1 / 8 : ℝ)) ∧
  (∀ p, sampledMultiplicity M p ≤ ⌈Real.log q⌉₊) ∧
  (∀ l, l ∉ initialDeletedLines M →
    (1 / 5 : ℝ) * q ≤ ((linePoints l ∩ initiallyRetained M).card : ℝ))

def offsetLaw (F : Type*) [Field F] [Fintype F] : PMF (MergedPairs F) :=
  PMF.uniformOfFintype (MergedPairs F)

def offsetEventProbability (E : Set (MergedPairs F)) : ℝ :=
  ((offsetLaw F).toOuterMeasure E).toReal

def CandidateSelector (M : MergedPairs F) (f : Slot F → F) : Prop :=
  ∀ s, SupportsValidTuple M (s.1, f s)

universe u

def CandidateGraphResult : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
  ∀ (F : ℕ → Type u) [∀ n, Field (F n)] [∀ n, Fintype (F n)] [∀ n, DecidableEq (F n)],
    Tendsto (fun n => Fintype.card (F n)) atTop atTop →
    Tendsto (fun n => offsetEventProbability (F := F n)
      {M | CandidateGraphGood M c C}) atTop (𝓝 1) ∧
    Tendsto (fun n => offsetEventProbability (F := F n)
      {M | CandidateGraphGood M c C ∧ DistinctConstituents M}) atTop (𝓝 (Real.exp (-1)))

end
end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_GlobalTupleLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.TupleAlignment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem fin_four_ne_next (i : Fin 4) : i ≠ i + 1 := by
  fin_cases i <;> decide

omit [Field F] [Fintype F] [DecidableEq F] in

theorem adjacent_ne_of_injective (T : FourTuple F) (hT : Function.Injective T.generator)
    (i : Fin 4) : T.generator i ≠ T.generator (i + 1) :=
  fun h => fin_four_ne_next i (hT h)

end Balanced.TupleAlignment

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_GlobalPartialAlignment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.PartialAlignment
open TupleAlignment ConditionalRestriction

noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def exposedTupleIndices (T : FourTuple F) (D : Finset (Direction F)) : Finset (Fin 4) :=
  Finset.univ.filter (fun i => T.generator i ∈ D)

theorem offsetLaw_eq_uniform : offsetLaw F = PMF.uniformOfFintype (MergedPairs F) := by
  ext M
  simp only [offsetLaw, PMF.uniformOfFintype_apply, Fintype.card_fun,
    Fintype.card_option, Fintype.card_bool]

theorem global_exposed_tuple_law (T : FourTuple F)
    (hT : Function.Injective T.generator) (D : Finset (Direction F)) (a : MergedPairs F) :
    ((PMF.uniformOfFintype (MergedPairs F)).filter
      {M | ∀ d, d ∈ D → M d = a d} (fixed_supported (fun d => d ∈ D) a)).map
      (fun M i => M (T.generator i)) =
    (PMF.uniformOfFintype (Fin 4 → Bool → F)).filter
      {o | ∀ i ∈ exposedTupleIndices T D, o i = a (T.generator i)}
      (partialOffsets_supported (exposedTupleIndices T D) (fun i => a (T.generator i))) := by
  simpa only [exposedTupleIndices, Finset.mem_filter, Finset.mem_univ, true_and,
    Function.Embedding.coeFn_mk] using
    uniform_conditional_restrict (A := Bool → F) ⟨T.generator, hT⟩
      (fun d => d ∈ D) a

theorem canonical_exposure_supported (D : Finset (Direction F)) (a : MergedPairs F) :
    ∃ M ∈ {M : MergedPairs F | ∀ d, d ∈ D → M d = a d},
      M ∈ (offsetLaw F).support := by
  rw [offsetLaw_eq_uniform]
  exact fixed_supported (fun d => d ∈ D) a

end
end Balanced.PartialAlignment

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_GeneratorEnumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

open Finset

section FiniteLabels
variable {α : Type*} [Fintype α] [DecidableEq α]

def generatorLabelsWithOldCount (old : Finset α) (j : ℕ) : Finset (Fin 4 → α) :=
  Finset.univ.filter (fun g => (Finset.univ.filter (fun i => g i ∈ old)).card = j)

def tupleCodesWithOldCount (old : Finset α) (j : ℕ) :
    Finset ((Fin 4 → α) × (Fin 4 → Bool)) :=
  (generatorLabelsWithOldCount old j).product Finset.univ

end FiniteLabels

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateExposure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateExposure

noncomputable section
open scoped Classical BigOperators
open PartialAlignment TupleAlignment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def exposedLaw (D : Finset (Direction F)) (a : MergedPairs F) : PMF (MergedPairs F) :=
  (offsetLaw F).filter {M | ∀ d, d ∈ D → M d = a d}
    (canonical_exposure_supported D a)

def alignedInDirection (T : FourTuple F) (g : Direction F) : Set (MergedPairs F) :=
  {M | ∃ c, ∀ i, OnLine (tuplePoint M T i) (g,c)}

def successfulInDirection (T : FourTuple F) (g : Direction F) : Set (MergedPairs F) :=
  {M | M ∈ alignedInDirection T g ∧ Function.Injective (tuplePoint M T)}

def conditionalProbability (D : Finset (Direction F)) (a : MergedPairs F)
    (E : Set (MergedPairs F)) : ℝ := ((exposedLaw D a).toOuterMeasure E).toReal

def alignmentExponent (j : ℕ) : ℕ := if j ≤ 2 then 3 else if j = 3 then 2 else 0

end
end Balanced.CandidateExposure

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateFirstMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateExposure

noncomputable section
open scoped Classical BigOperators
open PartialAlignment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def eligibleTuples (g : Direction F) : Finset (FourTuple F) :=
  Finset.univ.filter (fun T => Function.Injective T.generator ∧ ∀ i, T.generator i ≠ g)

def tuplesWithExposure (g : Direction F) (D : Finset (Direction F)) (j : ℕ) :
    Finset (FourTuple F) :=
  (eligibleTuples g).filter (fun T => (exposedTupleIndices T D).card = j)

def successProbabilitySum (g : Direction F) (D : Finset (Direction F))
    (a : MergedPairs F) : ℝ :=
  ∑ T ∈ eligibleTuples g, conditionalProbability D a (successfulInDirection T g)

def overlapProbabilitySum (g : Direction F) (D : Finset (Direction F))
    (a : MergedPairs F) : ℝ :=
  ∑ T ∈ (eligibleTuples g).filter (fun T => 0 < (exposedTupleIndices T D).card),
    conditionalProbability D a (successfulInDirection T g)

end
end Balanced.CandidateExposure

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateConditionalMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateExposure

noncomputable section
open scoped Classical BigOperators
open MeasureTheory PartialAlignment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def successfulTupleCount (g : Direction F) (M : MergedPairs F) : ℕ :=
  ((eligibleTuples g).filter (fun T => M ∈ successfulInDirection T g)).card

def overlappingTupleCount (g : Direction F) (D : Finset (Direction F))
    (M : MergedPairs F) : ℕ :=
  (((eligibleTuples g).filter (fun T => 0 < (exposedTupleIndices T D).card)).filter
    (fun T => M ∈ successfulInDirection T g)).card

end
end Balanced.CandidateExposure

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_RootSuccess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.TupleAlignment

open scoped BigOperators
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

abbrev RootPrescription (g : Direction F) :=
  (Fin 4 ↪ {d : Direction F // d ≠ g}) × (Fin 4 → Bool)

noncomputable def RootPrescription.tuple {g : Direction F}
    (a : RootPrescription g) : FourTuple F :=
  ⟨fun i => (a.1 i).1, a.2⟩

omit [Field F] [Fintype F] [DecidableEq F] in
theorem RootPrescription.injective {g : Direction F} (a : RootPrescription g) :
    Function.Injective a.tuple.generator := by
  intro i j h
  exact a.1.injective (Subtype.ext h)

noncomputable def rootSuccessCount (g : Direction F) (M : MergedPairs F) : ℕ := by
  classical
  exact (Finset.univ.filter (fun a : RootPrescription g =>
    (∃ c, ∀ i, OnLine (tuplePoint M a.tuple i) (g,c)) ∧
      Function.Injective (tuplePoint M a.tuple))).card

end Balanced.TupleAlignment

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateRootCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateExposure

noncomputable section
open scoped Classical BigOperators
open TupleAlignment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def eligibleTupleEquivRootPrescription (g : Direction F) :
    {T : FourTuple F // T ∈ eligibleTuples g} ≃ RootPrescription g where
  toFun T := (⟨fun i => ⟨T.1.generator i, (Finset.mem_filter.mp T.2).2.2 i⟩,
    fun i j h => (Finset.mem_filter.mp T.2).2.1 (congrArg Subtype.val h)⟩, T.1.side)
  invFun a := ⟨a.tuple, Finset.mem_filter.mpr ⟨Finset.mem_univ _, a.injective,
    fun i => (a.1 i).2⟩⟩
  left_inv T := by
    apply Subtype.ext
    cases T with
    | mk T h => cases T; rfl
  right_inv a := by
    apply Prod.ext
    · ext i
      rfl
    · rfl

omit [Field F] in
@[simp] theorem equivRootPrescription_tuple (g : Direction F)
    (T : {T : FourTuple F // T ∈ eligibleTuples g}) :
    (eligibleTupleEquivRootPrescription g T).tuple = T.1 := by
  cases T with
  | mk T h => cases T; rfl

end
end Balanced.CandidateExposure

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_FiniteFixedLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.ConditionalRestriction

noncomputable section
open scoped Classical BigOperators
open MeasureTheory TupleAlignment

variable {D A : Type*} [Fintype D] [Fintype A] [DecidableEq D] [Nonempty A]

def fixArray (P : D → Prop) (a ω : D → A) : D → A :=
  fun d => if P d then a d else ω d

end
end Balanced.ConditionalRestriction

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_PatternMomentsLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open scoped BigOperators
open MeasureTheory

namespace Balanced
open scoped _root_.Balanced

universe u

structure PatternModel where
  Color : Type u
  [colorFintype : Fintype Color]
  [colorDecidableEq : DecidableEq Color]
  Value : Color → Type u
  [valueMeasurable : ∀ c, MeasurableSpace (Value c)]
  law : ∀ c, Measure (Value c)
  [lawProbability : ∀ c, IsProbabilityMeasure (law c)]
  Label : Type u
  [labelFintype : Fintype Label]
  support : Label → Finset Color
  event : Label → Set (∀ c, Value c)
  eventMeasurable : ∀ a, MeasurableSet (event a)
  dependsOn : ∀ a x y, (∀ c ∈ support a, x c = y c) → (x ∈ event a ↔ y ∈ event a)

attribute [instance] PatternModel.colorFintype PatternModel.colorDecidableEq PatternModel.valueMeasurable
  PatternModel.lawProbability PatternModel.labelFintype

namespace PatternModel

abbrev Sample (P : PatternModel) := ∀ c, P.Value c

noncomputable def measure (P : PatternModel) : Measure P.Sample := Measure.pi P.law

noncomputable def fixCoordinates (P : PatternModel) (K : Finset P.Color)
    (x ω : P.Sample) : P.Sample := by
  classical
  exact fun c => if c ∈ K then x c else ω c

noncomputable def indicator (P : PatternModel) (a : P.Label) (ω : P.Sample) : ℝ :=
  (P.event a).indicator (fun _ => 1) ω

noncomputable def count (P : PatternModel) (ω : P.Sample) : ℝ :=
  ∑ a, P.indicator a ω

noncomputable def fixedExpectation (P : PatternModel) (K : Finset P.Color)
    (x : P.Sample) (f : P.Sample → ℝ) : ℝ :=
  ∫ ω, f (P.fixCoordinates K x ω) ∂P.measure

noncomputable def overlapCount (P : PatternModel) (K₀ K : Finset P.Color)
    (ω : P.Sample) : ℝ := by
  classical
  exact ∑ a, if Disjoint (P.support a \ K₀) K then 0 else P.indicator a ω

end PatternModel

end Balanced

end

section

namespace Balanced
open scoped _root_.Balanced

open scoped BigOperators

theorem inv_one_sub_le_exp_two_mul {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1 / 2) :
    (1 - x)⁻¹ ≤ Real.exp (2 * x) := by
  have hpos : 0 < 1 - x := by linarith
  have hinv : (1 - x)⁻¹ ≤ 1 + 2 * x := by
    apply (inv_le_iff_one_le_mul₀ hpos).2
    nlinarith
  exact hinv.trans (by simpa [add_comm] using Real.add_one_le_exp (2 * x))

theorem one_sub_sum_le_avoidance_prod {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i) (hx' : ∀ i ∈ s, x i ≤ 1) :
    1 - ∑ i ∈ s, x i ≤ ∏ i ∈ s, (1 - x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hxa := hx a (Finset.mem_insert_self a s)
    have hxa' := hx' a (Finset.mem_insert_self a s)
    have hxs : ∀ i ∈ s, 0 ≤ x i := fun i hi => hx i (Finset.mem_insert_of_mem hi)
    have hxs' : ∀ i ∈ s, x i ≤ 1 := fun i hi => hx' i (Finset.mem_insert_of_mem hi)
    have hsum : 0 ≤ ∑ i ∈ s, x i := Finset.sum_nonneg hxs
    have hmul := mul_le_mul_of_nonneg_left (ih hxs hxs') (show 0 ≤ 1 - x a by linarith)
    simp only [Finset.sum_insert ha, Finset.prod_insert ha]
    nlinarith [mul_nonneg hxa hsum]

theorem prod_inv_one_sub_le_exp_two_sum {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i) (hx' : ∀ i ∈ s, x i ≤ 1 / 2) :
    (∏ i ∈ s, (1 - x i)⁻¹) ≤ Real.exp (2 * ∑ i ∈ s, x i) := by
  calc
    (∏ i ∈ s, (1 - x i)⁻¹) ≤ ∏ i ∈ s, Real.exp (2 * x i) := by
      apply Finset.prod_le_prod
      · intro i hi
        exact inv_nonneg.mpr (by linarith [hx' i hi])
      · intro i hi
        exact inv_one_sub_le_exp_two_mul (hx i hi) (hx' i hi)
    _ = Real.exp (2 * ∑ i ∈ s, x i) := by
      rw [← Real.exp_sum, Finset.mul_sum]

theorem prod_inv_one_sub_le_exp_half {ι : Type*} (t : Finset ι) (x : ι → ℝ)
    (s : ℝ) (hx : ∀ i ∈ t, 0 ≤ x i) (hx' : ∀ i ∈ t, x i ≤ 1 / 2)
    (hs : ∑ i ∈ t, x i ≤ s / 4) :
    (∏ i ∈ t, (1 - x i)⁻¹) ≤ Real.exp (s / 2) := by
  apply (prod_inv_one_sub_le_exp_two_sum t x hx hx').trans
  apply Real.exp_le_exp.mpr
  linarith

end Balanced

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_RootPatternModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical
open MeasureTheory

namespace Balanced.TupleAlignment

universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]

def rootSuccessEvent (g : Direction F) (a : RootPrescription g) :
    Set (MergedPairs F) :=
  {M | (∃ c, ∀ i, OnLine (tuplePoint M a.tuple i) (g, c)) ∧
    Function.Injective (tuplePoint M a.tuple)}

omit [Fintype F] in
theorem tuplePoint_eq_of_eq_on_generators (T : FourTuple F)
    {M N : MergedPairs F}
    (h : ∀ d ∈ generatorSet T, M d = N d) :
    tuplePoint M T = tuplePoint N T := by
  funext i
  have h₁ := h (T.generator i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  have h₂ := h (T.generator (i + 1))
    (Finset.mem_image.mpr ⟨i + 1, Finset.mem_univ _, rfl⟩)
  simp only [tuplePoint, constituent, h₁, h₂]

end Balanced.TupleAlignment

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateLabelBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateExposure

noncomputable section
open scoped Classical BigOperators
open TupleAlignment PartialAlignment MeasureTheory

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

local instance candidateLabelMeasurableSpace : MeasurableSpace F := ⊤

end
end Balanced.CandidateExposure

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

instance isProbabilityMeasure_measure : IsProbabilityMeasure P.measure := by
  unfold measure
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

@[simp] lemma fixedExpectation_const (K : Finset P.Color) (x : P.Sample) (c : ℝ) :
    P.fixedExpectation K x (fun _ => c) = c := by
  simp [fixedExpectation]

noncomputable def positiveProduct (K₀ : Finset P.Color) (x : P.Sample)
    (as : List P.Label) (ω : P.Sample) : ℝ :=
  (as.map fun a => P.indicator a ω + P.fixedExpectation K₀ x (P.indicator a)).prod

noncomputable def productWeight (K₀ : Finset P.Color) (x : P.Sample)
    (as : List P.Label) : ℝ :=
  P.fixedExpectation K₀ x (P.positiveProduct K₀ x as)

@[simp] lemma productWeight_nil (K₀ : Finset P.Color) (x : P.Sample) :
    P.productWeight K₀ x [] = 1 := by
  change P.fixedExpectation K₀ x (fun _ => (1 : ℝ)) = 1
  exact P.fixedExpectation_const K₀ x 1

end Balanced.PatternModel

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_PatternPrefixSupport
attribute [-instance] _root_.OAI.Balanced.PatternModel.isProbabilityMeasure_measure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.PatternModel

attribute [local instance] Classical.propDecidable

variable (P : PatternModel)

def freshPrefixSupport (K₀ : Finset P.Color) (pre : List P.Label) : Finset P.Color :=
  pre.foldr (fun a U => U ∪ (P.support a \ K₀)) ∅

@[simp] lemma freshPrefixSupport_nil (K₀ : Finset P.Color) :
    P.freshPrefixSupport K₀ [] = ∅ := rfl

@[simp] lemma freshPrefixSupport_cons (K₀ : Finset P.Color) (a : P.Label)
    (pre : List P.Label) :
    P.freshPrefixSupport K₀ (a :: pre) =
      P.freshPrefixSupport K₀ pre ∪ (P.support a \ K₀) := rfl

end Balanced.PatternModel

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateHighMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateExposure

noncomputable section
open scoped Classical BigOperators
open MeasureTheory TupleAlignment PartialAlignment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
local instance candidateHighMomentsMeasurableSpace : MeasurableSpace F := ⊤

def centeredMomentConstant (m s : ℕ) : ℝ :=
  ((2 * s).factorial : ℝ) * 2 ^ (2 * s) *
    (2 * (20480 * ((m : ℝ) + 8 * s + 1) ^ 4)) ^ (2 * s)

end
end Balanced.CandidateExposure

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateAbundance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateExposure

noncomputable section
open scoped Classical BigOperators
open MeasureTheory TupleAlignment Filter Topology

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
local instance candidateAbundanceMeasurableSpace : MeasurableSpace F := ⊤

end
end Balanced.CandidateExposure

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidatePrescribedLine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidatePrescribed

noncomputable section
open scoped Classical
open Finset PartialAlignment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

abbrev Code (F : Type*) := (Fin 4 → Direction F) × (Fin 4 → Bool)

def exposedLaw (old : Finset (Direction F)) (a : MergedPairs F) :
    PMF (MergedPairs F) :=
  (offsetLaw F).filter {M | ∀ d, d ∈ old → M d = a d}
    (canonical_exposure_supported old a)

def Eligible (l : Line F) (c : Code F) : Prop :=
  Function.Injective c.1 ∧ ∀ i, c.1 i ≠ l.1

def alignmentMass (old : Finset (Direction F)) (a : MergedPairs F)
    (l : Line F) (c : Code F) : ℝ :=
  if Eligible l c then
    ((exposedLaw old a).toOuterMeasure
      {M | ∀ i, OnLine (tuplePoint M ⟨c.1, c.2⟩ i) l}).toReal
  else 0

def alignedCodes (M : MergedPairs F) (l : Line F) : Finset (Code F) :=
  Finset.univ.filter (fun c => Eligible l c ∧
    ∀ i, OnLine (tuplePoint M ⟨c.1, c.2⟩ i) l)

def successfulCodes (M : MergedPairs F) (l : Line F) : Finset (Code F) :=
  (alignedCodes M l).filter
    (fun c => Function.Injective (tuplePoint M ⟨c.1, c.2⟩))

end
end Balanced.CandidatePrescribed

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateConstituentTarget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidatePrescribed

noncomputable section
open scoped Classical
open Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def constituentTargetCodes (M : MergedPairs F) (g : Direction F) : Finset (Code F) :=
  successfulCodes M (constituent M g false) ∪
    successfulCodes M (constituent M g true)

end
end Balanced.CandidatePrescribed

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateConstituentMoments
attribute [-instance] _root_.OAI.Balanced.PatternModel.isProbabilityMeasure_measure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidatePrescribed

noncomputable section
open scoped Classical BigOperators
open MeasureTheory ConditionalRestriction

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

local instance instMeasurableSpace_solutions : MeasurableSpace F := ⊤
local instance instMeasurableSingletonClass_solutions : MeasurableSingletonClass F := ⟨fun _ => trivial⟩

theorem constituentTarget_mem_iff_of_agree (g : Direction F) (c : Code F)
    (M N : MergedPairs F)
    (h : ∀ d ∈ insert g (generatorSet (⟨c.1,c.2⟩ : FourTuple F)), M d = N d) :
    c ∈ constituentTargetCodes M g ↔ c ∈ constituentTargetCodes N g := by
  have hg : M g = N g := h g (Finset.mem_insert_self _ _)
  have hp : tuplePoint M (⟨c.1,c.2⟩ : FourTuple F) =
      tuplePoint N (⟨c.1,c.2⟩ : FourTuple F) := by
    funext i
    have hi := h (c.1 i) (Finset.mem_insert_of_mem
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))
    have hn := h (c.1 (i+1)) (Finset.mem_insert_of_mem
      (Finset.mem_image.mpr ⟨i+1, Finset.mem_univ _, rfl⟩))
    simp only [tuplePoint, constituent, hi, hn]
  simp only [constituentTargetCodes, Finset.mem_union, successfulCodes,
    alignedCodes, Finset.mem_filter, Finset.mem_univ, true_and]
  simp only [constituent, hg, hp]

def constituentTargetPatternModel (g : Direction F) : PatternModel where
  Color := Direction F
  Value := fun _ => Bool → F
  law := fun _ => (PMF.uniformOfFintype (Bool → F)).toMeasure
  Label := Code F
  support c := insert g (generatorSet (⟨c.1,c.2⟩ : FourTuple F))
  event c := {M | c ∈ constituentTargetCodes M g}
  eventMeasurable _ := (Set.to_countable _).measurableSet
  dependsOn c M N h := constituentTarget_mem_iff_of_agree g c M N h

end
end Balanced.CandidatePrescribed

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

@[simp] theorem onLine_lineThrough (d : Direction F) (p : Point F) :
    OnLine p (lineThrough d p) := rfl

@[simp] theorem lineThrough_direction (d : Direction F) (p : Point F) :
    (lineThrough d p).1 = d := rfl

section Decidable

variable [DecidableEq F]

@[simp] theorem onLine_joiningLine_left (p r : Point F) :
    OnLine p (joiningLine p r) := by
  unfold joiningLine
  split <;> rfl

@[simp] theorem onLine_joiningLine_right (p r : Point F) :
    OnLine r (joiningLine p r) := by
  unfold joiningLine
  split
  · rename_i h
    exact h.symm
  · rename_i h
    change r.2 - (r.2 - p.2) / (r.1 - p.1) * r.1 =
      p.2 - (r.2 - p.2) / (r.1 - p.1) * p.1
    field_simp [sub_ne_zero.mpr (Ne.symm h)]
    ring

end Decidable

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateValidityWitness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateValidityWitness

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def SuccessfulOn (M : MergedPairs F) (T : FourTuple F) (S : Line F) : Prop :=
  Function.Injective T.generator ∧ (∀ i, T.generator i ≠ S.1) ∧
  Function.Injective (tuplePoint M T) ∧ (∀ i, OnLine (tuplePoint M T i) S)

def PairWitness (M : MergedPairs F) (d : Direction F) (x y : Point F) : Prop :=
  ∃ s : Bool, OnLine x (constituent M d s) ∧
    OnLine y (constituent M d (!s))

def OppositeWitness (M : MergedPairs F) (T : FourTuple F) (S : Line F) : Prop :=
  ∃ (i : Fin 4) (d : Direction F), d ≠ S.1 ∧ d ∉ generatorSet T ∧
    PairWitness M d (tuplePoint M T i) (tuplePoint M T (i + 2))

def ExternalDoubleWitness (M : MergedPairs F) (T : FourTuple F) (S : Line F) : Prop :=
  ∃ (x : Point F) (i j : Fin 4) (d e : Direction F),
    OnLine x S ∧ x ∉ designated M ⟨S, T⟩ ∧ i ≠ j ∧ d ≠ e ∧
    d ≠ S.1 ∧ e ≠ S.1 ∧ d ∉ generatorSet T ∧ e ∉ generatorSet T ∧
    PairWitness M d x (tuplePoint M T i) ∧
    PairWitness M e x (tuplePoint M T j)

end Balanced.CandidateValidityWitness

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateConstituentTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateConstituentTail

noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Filter CandidatePrescribed

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
local instance instMeasurableSpace_solutions : MeasurableSpace F := ⊤

def tailConstant : ℝ := (40960 * ((((300 - 1) * 5 : ℕ) : ℝ) + 2)^4)^300

end
end Balanced.CandidateConstituentTail

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

@[simp] theorem retainedChoice_line (M : MergedPairs F) (l : Line F) :
    (retainedChoice M l).line = l := rfl

@[simp] theorem mem_candidateVertices {M : MergedPairs F} {v : CandidateVertex F} :
    v ∈ candidateVertices M ↔ SupportsValidTuple M (candidateLine v) := by
  simp [candidateVertices]

@[simp] theorem mem_candidateSlot {M : MergedPairs F} {s : Slot F} {v : CandidateVertex F} :
    v ∈ candidateSlot M s ↔ SupportsValidTuple M (candidateLine v) ∧ v.1 = s := by
  simp [candidateSlot]

theorem Configuration.compatible_iff_pairwise (C : Configuration F) :
    C.Compatible ↔ ∀ s t, s ≠ t →
      ChoicesCompatible C.merged s.1 t.1 (C.choice s) (C.choice t) := by
  constructor
  · rintro ⟨hpoints, hgen, hmerged⟩ s t hst
    refine ⟨hpoints t s (Ne.symm hst), hpoints s t hst, hgen s t hst, ?_⟩
    intro heq d
    exact ⟨hmerged s t hst heq d, hmerged t s (Ne.symm hst) heq.symm d⟩
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro s t hst
      exact (h s t hst).2.1
    · intro s t hst
      exact (h s t hst).2.2.1
    · intro s t hst heq d
      exact ((h s t hst).2.2.2 heq d).1

end
end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateRootFibers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.TupleAlignment

noncomputable section
open scoped Classical BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def RootPrescription.choice {g : Direction F} (M : MergedPairs F)
    (a : RootPrescription g) : SplitChoice F :=
  ⟨lineThrough g (tuplePoint M a.tuple 0), a.tuple⟩

omit [Fintype F] [DecidableEq F] in
@[simp] theorem RootPrescription.choice_tuple {g : Direction F}
    (M : MergedPairs F) (a : RootPrescription g) :
    (a.choice M).tuple = a.tuple := rfl

omit [Fintype F] [DecidableEq F] in
@[simp] theorem RootPrescription.choice_direction {g : Direction F}
    (M : MergedPairs F) (a : RootPrescription g) :
    (a.choice M).line.1 = g := rfl

def RootPrescription.ofTuple (g : Direction F) (T : FourTuple F)
    (hinj : Function.Injective T.generator) (havoid : ∀ i, T.generator i ≠ g) :
    RootPrescription g :=
  (⟨fun i => ⟨T.generator i, havoid i⟩,
    fun _ _ h => hinj (congrArg Subtype.val h)⟩, T.side)

omit [Field F] [Fintype F] [DecidableEq F] in
@[simp] theorem RootPrescription.ofTuple_tuple (g : Direction F) (T : FourTuple F)
    (hinj : Function.Injective T.generator) (havoid : ∀ i, T.generator i ≠ g) :
    (RootPrescription.ofTuple g T hinj havoid).tuple = T := rfl

def successfulPrescriptions (M : MergedPairs F) (g : Direction F) :
    Finset (RootPrescription g) :=
  Finset.univ.filter (fun a =>
    (∃ c, ∀ i, OnLine (tuplePoint M a.tuple i) (g, c)) ∧
    Function.Injective (tuplePoint M a.tuple))

@[simp] theorem successfulPrescriptions_card (M : MergedPairs F) (g : Direction F) :
    (successfulPrescriptions M g).card = rootSuccessCount g M := rfl

end
end Balanced.TupleAlignment

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateValidityAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateValidityAssembly

noncomputable section
open scoped Classical
open TupleAlignment CandidateValidityWitness

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def constituentFailures (M : MergedPairs F) (g : Direction F) :
    Finset (RootPrescription g) :=
  (successfulPrescriptions M g).filter
    (fun a => (a.choice M).line ∈ constituentLines M)

def oppositeFailures (M : MergedPairs F) (g : Direction F) :
    Finset (RootPrescription g) :=
  (successfulPrescriptions M g).filter
    (fun a => OppositeWitness M a.tuple (a.choice M).line)

def externalFailures (M : MergedPairs F) (g : Direction F) :
    Finset (RootPrescription g) :=
  (successfulPrescriptions M g).filter
    (fun a => ExternalDoubleWitness M a.tuple (a.choice M).line)

def prescriptionCode {g : Direction F} (a : RootPrescription g) :
    CandidatePrescribed.Code F := (a.tuple.generator, a.tuple.side)

end
end Balanced.CandidateValidityAssembly

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateOldOppositeOverlap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateOldOpposite

noncomputable section
open scoped Classical BigOperators
open CandidateExposure CandidateValidityWitness PartialAlignment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def overlappingWitnesses (g : Direction F) (D : Finset (Direction F))
    (M : MergedPairs F) : Finset ((FourTuple F × Fin 4) × Direction F) :=
  (((((eligibleTuples g).filter (fun T => 0 < (exposedTupleIndices T D).card)).filter
    (fun T => M ∈ successfulInDirection T g)).product Finset.univ).product D).filter
    (fun w => w.2 ≠ g ∧ w.2 ∉ generatorSet w.1.1 ∧
      PairWitness M w.2 (tuplePoint M w.1.1 w.1.2)
        (tuplePoint M w.1.1 (w.1.2 + 2)))

end
end Balanced.CandidateOldOpposite

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateExposedWitness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateExposedWitness

open CandidateValidityWitness

variable {F : Type*} [Field F]

def forcedPoint (a : MergedPairs F) (S : Line F) (d : Direction F) (s : Bool) : Point F :=
  lineIntersection S (constituent a d s)

end Balanced.CandidateExposedWitness

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidatePairCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidatePairs

noncomputable section
open scoped Classical BigOperators
open MeasureTheory PartialAlignment ConditionalRestriction
open CandidateExposure

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def lineTuples (M : MergedPairs F) (l : Line F) : Finset (FourTuple F) :=
  (eligibleTuples l.1).filter (fun T =>
    (∀ i, OnLine (tuplePoint M T i) l) ∧ Function.Injective (tuplePoint M T))

def lineCount (M : MergedPairs F) (l : Line F) : ℕ := (lineTuples M l).card

def targetLine (g : Direction F) (T : FourTuple F) (M : MergedPairs F) : Line F :=
  (g, lineEval g (tuplePoint M T 0))

def pairCount (g : Direction F) (M : MergedPairs F) : ℕ :=
  ∑ T ∈ eligibleTuples g, if M ∈ successfulInDirection T g then
    lineCount M (targetLine g T M) else 0

section Measurable
variable [MeasurableSpace F] [MeasurableSingletonClass F]

def firstOverlapPairCount (old : Finset (Direction F)) (g : Direction F)
    (M : MergedPairs F) : ℕ :=
  ∑ T ∈ (eligibleTuples g).filter (fun T => 0 < (exposedTupleIndices T old).card),
    if M ∈ successfulInDirection T g then lineCount M (targetLine g T M) else 0

end Measurable
end
end Balanced.CandidatePairs

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidatePairPatternModel
attribute [-instance] _root_.OAI.Balanced.PatternModel.isProbabilityMeasure_measure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical
open MeasureTheory

namespace Balanced.CandidateExposure

universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
local instance pairModelMeasurableSpace : MeasurableSpace F := ⊤

abbrev EligiblePair (g : Direction F) :=
  ↥(eligibleTuples g) × ↥(eligibleTuples g)

def pairSuccessEvent (g : Direction F) (a : EligiblePair g) : Set (MergedPairs F) :=
  {M | (∃ c, (∀ i, OnLine (tuplePoint M a.1.val i) (g, c)) ∧
      (∀ i, OnLine (tuplePoint M a.2.val i) (g, c))) ∧
    Function.Injective (tuplePoint M a.1.val) ∧
    Function.Injective (tuplePoint M a.2.val)}

abbrev pairPatternModel (g : Direction F) : PatternModel.{u} where
  Color := Direction F
  Value := fun _ => Bool → F
  law := fun _ => (PMF.uniformOfFintype (Bool → F)).toMeasure
  Label := EligiblePair g
  support := fun a => generatorSet a.1.val ∪ generatorSet a.2.val
  event := pairSuccessEvent g
  eventMeasurable := fun _ => (Set.toFinite _).measurableSet
  dependsOn := by
    intro a M N h
    have h₁ := TupleAlignment.tuplePoint_eq_of_eq_on_generators a.1.val
      (fun d hd => h d (Finset.mem_union_left _ hd))
    have h₂ := TupleAlignment.tuplePoint_eq_of_eq_on_generators a.2.val
      (fun d hd => h d (Finset.mem_union_right _ hd))
    simp only [pairSuccessEvent, Set.mem_ofPred_eq, h₁, h₂]

end Balanced.CandidateExposure

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidatePairFibers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidatePairs
noncomputable section
open scoped Classical BigOperators
open CandidateExposure TupleAlignment
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def successfulPairs (g : Direction F) (M : MergedPairs F) : Finset (EligiblePair g) :=
  Finset.univ.filter (fun a => M ∈ pairSuccessEvent g a)

end
end Balanced.CandidatePairs

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidatePairMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidatePairs

noncomputable section
open scoped Classical BigOperators
open MeasureTheory CandidateExposure

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
local instance pairMomentMeasurableSpace : MeasurableSpace F := ⊤

def pairTotalConstant (m : ℕ) : ℝ :=
  (20480 * ((m : ℝ) + 4 + 1)^4) * (20480 * ((m : ℝ) + 1)^4)

def pairFirstOverlapConstant (m : ℕ) : ℝ :=
  (20480 * ((m : ℝ) + 4 + 1)^4) * (16384 * ((m : ℝ) + 1)^4)

def pairExposureConstant (m : ℕ) : ℝ :=
  pairTotalConstant m + 2 * pairFirstOverlapConstant m

def pairCenteredMomentConstant (m s : ℕ) : ℝ :=
  ((2*s).factorial : ℝ) * 2^(2*s) *
    (2 * pairExposureConstant (m + 16*s))^(2*s)

def pairLinearThreshold : ℝ := pairExposureConstant 0 + 1

end
end Balanced.CandidatePairs

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateAbundanceAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateAbundanceAssembly

noncomputable section
open scoped Classical Topology
open Filter MeasureTheory TupleAlignment CandidateValidityAssembly CandidatePairs

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
local instance abundanceAssemblyMeasurableSpace : MeasurableSpace F := ⊤

def slotLinearConstant : ℝ := 25 / pairLinearThreshold

end
end Balanced.CandidateAbundanceAssembly

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_CandidateIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateIncidence

noncomputable section
open scoped Classical BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {M : MergedPairs F}

def points (M : MergedPairs F) (v : CandidateVertex F) : Finset (Point F) :=
  designated M (candidateChoice M v)

def exceptionalSet (M : MergedPairs F) (v : CandidateVertex F) : Finset (CandidateVertex F) :=
  (candidateVertices M).filter (fun w =>
    candidateLine w = candidateLine v ∨ (points M w ∩ points M v).Nonempty)

def B (M : MergedPairs F) (v : CandidateVertex F) : Finset (CandidateVertex F) :=
  (candidateVertices M).filter (fun w => ∃ p ∈ points M v, OnLine p (candidateLine w))

def E (M : MergedPairs F) (v : CandidateVertex F) : Finset (CandidateVertex F) :=
  (candidateVertices M).filter (fun w => ∃ p ∈ points M w, OnLine p (candidateLine v))

def pointCandidates (M : MergedPairs F) (p : Point F) : Finset (CandidateVertex F) :=
  (candidateVertices M).filter (fun z => p ∈ points M z)

def pointLineCandidates (M : MergedPairs F) (p : Point F) (l : Line F) :
    Finset (CandidateVertex F) :=
  (candidateVertices M).filter (fun z => OnLine p (candidateLine z) ∧
    ∃ r ∈ points M z, OnLine r l)

def twoLineCandidates (M : MergedPairs F) (l k : Line F) : Finset (CandidateVertex F) :=
  (candidateVertices M).filter (fun z => ∃ p ∈ points M z, ∃ r ∈ points M z,
    p ≠ r ∧ OnLine p l ∧ OnLine r k)

def secondary (M : MergedPairs F) (v : CandidateVertex F) : Finset (CandidateVertex F) :=
  candidateNeighbors M v \ (B M v ∪ E M v)

end
end Balanced.CandidateIncidence

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateSecondary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateIncidence

noncomputable section
open scoped Classical BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {M : MergedPairs F}

def generators (M : MergedPairs F) (v : CandidateVertex F) : Finset (Direction F) :=
  generatorSet (candidateChoice M v).tuple

def generatorPairCandidates (M : MergedPairs F) (e : Finset (Direction F)) :
    Finset (CandidateVertex F) :=
  (candidateVertices M).filter (fun w => e ⊆ generators M w)

def generatorConflicts (M : MergedPairs F) (v : CandidateVertex F) :
    Finset (CandidateVertex F) :=
  (candidateVertices M).filter (fun w => 2 ≤ (generators M v ∩ generators M w).card)

def directionsAt (M : MergedPairs F) (p : Point F) : Finset (Direction F) :=
  (Finset.univ.filter (fun ds : Direction F × Bool =>
    OnLine p (constituent M ds.1 ds.2))).image Prod.fst

def touchedDirections (M : MergedPairs F) (v : CandidateVertex F) : Finset (Direction F) :=
  (points M v).biUnion (directionsAt M)

def mergedConflicts (M : MergedPairs F) (v : CandidateVertex F) :
    Finset (CandidateVertex F) :=
  (candidateVertices M).filter (fun w => v.1.1 = w.1.1 ∧
    ∃ d, (points M v ∩ mergedPoints M d).Nonempty ∧
      (points M w ∩ mergedPoints M d).Nonempty)

def lineHitSlot (M : MergedPairs F) (s : Slot F) (l : Line F) : Finset (CandidateVertex F) :=
  (candidateSlot M s).filter (fun w => ∃ p ∈ points M w, OnLine p l)

def mergedHitCandidates (M : MergedPairs F) (g d : Direction F) : Finset (CandidateVertex F) :=
  (candidateVertices M).filter (fun w => w.1.1 = g ∧
    (points M w ∩ mergedPoints M d).Nonempty)

end
end Balanced.CandidateIncidence

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateRetentionTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateRetentionTransport

noncomputable section
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def successfulChoices (M : MergedPairs F) : Finset (SplitChoice F) :=
  Finset.univ.filter fun C =>
    Function.Injective C.tuple.generator ∧
    (∀ i, C.tuple.generator i ≠ C.line.1) ∧
    Function.Injective (tuplePoint M C.tuple) ∧
    ∀ i, OnLine (tuplePoint M C.tuple i) C.line

def successfulTest (M : MergedPairs F) (P : SplitChoice F → Prop) :
    Finset (SplitChoice F) := (successfulChoices M).filter P

@[simp] theorem mem_successfulTest (M : MergedPairs F) (P : SplitChoice F → Prop)
    (C : SplitChoice F) :
    C ∈ successfulTest M P ↔ C ∈ successfulChoices M ∧ P C := by
  simp only [successfulTest, Finset.mem_filter]

end
end Balanced.CandidateRetentionTransport

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidatePrescriptionTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateRetentionTransport

noncomputable section
open scoped Classical BigOperators
open TupleAlignment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

@[simp] theorem mem_successfulChoices (M : MergedPairs F) (C : SplitChoice F) :
    C ∈ successfulChoices M ↔
    Function.Injective C.tuple.generator ∧
    (∀ i, C.tuple.generator i ≠ C.line.1) ∧
    Function.Injective (tuplePoint M C.tuple) ∧
    ∀ i, OnLine (tuplePoint M C.tuple i) C.line := by
  simp only [successfulChoices, Finset.mem_filter, Finset.mem_univ, true_and]

end
end Balanced.CandidateRetentionTransport

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateGeneratorPairModel
attribute [-instance] _root_.OAI.Balanced.PatternModel.isProbabilityMeasure_measure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateGeneratorPair

noncomputable section
open scoped Classical BigOperators
open MeasureTheory TupleAlignment CandidateExposure

universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
local instance instMeasurableSpace_solutions : MeasurableSpace F := ⊤

abbrev patternModel (e : Finset (Direction F)) : PatternModel.{u} where
  Color := Direction F
  Value := fun _ => Bool → F
  law := fun _ => (PMF.uniformOfFintype (Bool → F)).toMeasure
  Label := Σ g : Direction F, RootPrescription g
  support := fun a => generatorSet a.2.tuple
  event := fun a => {M | e ⊆ generatorSet a.2.tuple ∧ M ∈ rootSuccessEvent a.1 a.2}
  eventMeasurable := fun _ => (Set.toFinite _).measurableSet
  dependsOn := by
    intro a M N h
    have heq := tuplePoint_eq_of_eq_on_generators a.2.tuple h
    simp only [Set.mem_ofPred_eq, rootSuccessEvent, heq]

def count (e : Finset (Direction F)) (M : MergedPairs F) : ℕ :=
  (CandidateRetentionTransport.successfulTest M
    (fun C => e ⊆ generatorSet C.tuple)).card

def probabilitySum (e D : Finset (Direction F)) (a : MergedPairs F) : ℝ :=
  ∑ g : Direction F, ∑ T ∈ (eligibleTuples g).filter
    (fun T => e ⊆ generatorSet T), conditionalProbability D a (successfulInDirection T g)

end
end Balanced.CandidateGeneratorPair

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_CandidateFreshIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateFreshIncidence

noncomputable section
open scoped Classical BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def positionProbability (P : (Fin 4 → Point F) → Prop) : ℝ :=
  ((PMF.uniformOfFintype (Fin 4 → Point F)).toOuterMeasure {p | P p}).toReal

end
end Balanced.CandidateFreshIncidence

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_FullyExposedTargets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.TupleAlignment

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def SuccessfulPositions (p : Fin 4 → Point F) (g : Direction F) : Prop :=
  (∃ c, ∀ i, OnLine (p i) (g, c)) ∧ Function.Injective p

end
end Balanced.TupleAlignment

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_CandidateIncidenceMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateExposure

noncomputable section
open scoped Classical BigOperators
open PartialAlignment TupleAlignment MeasureTheory

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def successfulLineHit (T : FourTuple F) (g : Direction F) (L : Line F) :
    Set (MergedPairs F) :=
  {M | M ∈ successfulInDirection T g ∧ ∃ i, OnLine (tuplePoint M T i) L}

end
end Balanced.CandidateExposure

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateGeneratorPairMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateGeneratorPair

noncomputable section
open scoped Classical BigOperators
open MeasureTheory CandidateExposure

universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
local instance instMeasurableSpace_solutions_1 : MeasurableSpace F := ⊤

end
end Balanced.CandidateGeneratorPair

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_CandidateIncidenceTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateIncidenceTests

noncomputable section
open scoped Classical
open CandidateRetentionTransport

abbrev Test (F : Type*) :=
  Point F ⊕ ((Point F × Line F) ⊕ ((Line F × Line F) ⊕
    ((Direction F × Direction F) ⊕ (Direction F × Line F))))

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def count (M : MergedPairs F) : Test F → ℕ
  | Sum.inl p => (successfulTest M (fun A => p ∈ designated M A)).card
  | Sum.inr (Sum.inl (p, l)) =>
      if ¬ OnLine p l then
        (successfulTest M (fun A => OnLine p A.line ∧
          ∃ r ∈ designated M A, OnLine r l)).card else 0
  | Sum.inr (Sum.inr (Sum.inl (l, k))) =>
      if l ≠ k ∧ l ∉ constituentLines M ∧ k ∉ constituentLines M then
        (successfulTest M (fun A => ∃ p ∈ designated M A, ∃ r ∈ designated M A,
          p ≠ r ∧ OnLine p l ∧ OnLine r k)).card else 0
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl (d, e)))) =>
      if d ≠ e then
        (successfulTest M (fun A => ({d, e} : Finset (Direction F)) ⊆
          generatorSet A.tuple)).card else 0
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (g, l)))) =>
      (successfulTest M (fun A => A.line.1 = g ∧
        ∃ p ∈ designated M A, OnLine p l)).card

def SmallGood (M : MergedPairs F) (P : ℕ) : Prop := ∀ t : Test F, count M t ≤ P

def GlobalGood (M : MergedPairs F) (C : ℝ) : Prop :=
  ∀ l : Line F, l ∉ constituentLines M →
    ((successfulTest M (fun A => ∃ p ∈ designated M A, OnLine p l)).card : ℝ) ≤
      C * Fintype.card F

def SizeGood (M : MergedPairs F) (c : ℝ) : Prop :=
  ∀ s : Slot F, c * Fintype.card F ≤ ((candidateSlot M s).card : ℝ)

universe u

end
end Balanced.CandidateIncidenceTests

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateGeneratorPairFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory

namespace Balanced.CandidateIncidenceTests

universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
local instance generatorFamilyMeasurableSpace : MeasurableSpace F := ⊤

end Balanced.CandidateIncidenceTests

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateLineGate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateLineGate

noncomputable section
open scoped Classical BigOperators
open CandidateExposure

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Field F] in
theorem not_mem_constituentLines_iff (M : MergedPairs F) (L : Line F) :
    L ∉ constituentLines M ↔ ∀ b : Bool, M L.1 b ≠ L.2 := by
  constructor
  · intro h b hb
    apply h
    apply Finset.mem_image.mpr
    refine ⟨(L.1, b), Finset.mem_univ _, ?_⟩
    exact Prod.ext rfl hb
  · intro h hL
    obtain ⟨⟨d, b⟩, _, heq⟩ := Finset.mem_image.mp hL
    have hd : d = L.1 := congrArg Prod.fst heq
    have hv : M d b = L.2 := congrArg Prod.snd heq
    exact h b (hd ▸ hv)

omit [Field F] in
theorem not_mem_iff_of_direction_agreement (L : Line F) (M a : MergedPairs F)
    (h : M L.1 = a L.1) :
    L ∉ constituentLines M ↔ L ∉ constituentLines a := by
  rw [not_mem_constituentLines_iff, not_mem_constituentLines_iff, h]

end
end Balanced.CandidateLineGate

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateGlobalLineMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateGlobalLine

noncomputable section
open scoped Classical BigOperators
open CandidateExposure PartialAlignment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def lineSuccessEvent (T : FourTuple F) (g : Direction F) (L : Line F) :
    Set (MergedPairs F) :=
  {M | M ∈ successfulInDirection T g ∧ ∃ i, OnLine (tuplePoint M T i) L}

end
end Balanced.CandidateGlobalLine

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_CandidateIncidenceModel
attribute [-instance] _root_.OAI.Balanced.PatternModel.isProbabilityMeasure_measure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateIncidence

noncomputable section
open scoped Classical BigOperators
open MeasureTheory TupleAlignment CandidateExposure

universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
local instance incidenceModelMeasurableSpace : MeasurableSpace F := ⊤

abbrev Test (F : Type*) := FourTuple F → Direction F → (Fin 4 → Point F) → Prop

def event (R : Test F) (g : Direction F) (a : RootPrescription g) :
    Set (MergedPairs F) :=
  {M | M ∈ rootSuccessEvent g a ∧ R a.tuple g (tuplePoint M a.tuple)}

abbrev model (R : Test F) (g : Direction F) : PatternModel.{u} where
  Color := Direction F
  Value := fun _ => Bool → F
  law := fun _ => (PMF.uniformOfFintype (Bool → F)).toMeasure
  Label := RootPrescription g
  support := fun a => generatorSet a.tuple
  event := event R g
  eventMeasurable := fun _ => (Set.toFinite _).measurableSet
  dependsOn := by
    intro a M N h
    have heq := tuplePoint_eq_of_eq_on_generators a.tuple h
    simp only [event, rootSuccessEvent, Set.mem_ofPred_eq, heq]

abbrev allModel (R : Test F) : PatternModel.{u} where
  Color := Direction F
  Value := fun _ => Bool → F
  law := fun _ => (PMF.uniformOfFintype (Bool → F)).toMeasure
  Label := Σ g : Direction F, RootPrescription g
  support := fun a => generatorSet a.2.tuple
  event := fun a => event R a.1 a.2
  eventMeasurable := fun _ => (Set.toFinite _).measurableSet
  dependsOn := by
    intro a M N h
    have heq := tuplePoint_eq_of_eq_on_generators a.2.tuple h
    simp only [event, rootSuccessEvent, Set.mem_ofPred_eq, heq]

def tupleCount (R : Test F) (g : Direction F) (M : MergedPairs F) : ℕ :=
  ((eligibleTuples g).filter fun T =>
    M ∈ successfulInDirection T g ∧ R T g (tuplePoint M T)).card

def lineHitTest (L : Line F) : Test F := fun _ _ p => ∃ i, OnLine (p i) L

end
end Balanced.CandidateIncidence

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_PatternGate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.PatternModel

noncomputable section
open scoped Classical BigOperators
open MeasureTheory

abbrev gated (P : PatternModel) (A : Finset P.Color) (E : Set P.Sample)
    (hE : MeasurableSet E)
    (hdep : ∀ x y, (∀ c ∈ A, x c = y c) → (x ∈ E ↔ y ∈ E)) : PatternModel where
  Color := P.Color
  Value := P.Value
  law := P.law
  Label := P.Label
  support a := P.support a ∪ A
  event a := E ∩ P.event a
  eventMeasurable a := hE.inter (P.eventMeasurable a)
  dependsOn a x y h := by
    have h₁ := hdep x y (fun c hc => h c (Finset.mem_union_right _ hc))
    have h₂ := P.dependsOn a x y (fun c hc => h c (Finset.mem_union_left _ hc))
    exact and_congr h₁ h₂

variable (P : PatternModel) (A : Finset P.Color) (E : Set P.Sample)
    (hE : MeasurableSet E)
    (hdep : ∀ x y, (∀ c ∈ A, x c = y c) → (x ∈ E ↔ y ∈ E))

@[simp] theorem gated_measure : (P.gated A E hE hdep).measure = P.measure := rfl

@[simp] theorem gated_fixCoordinates (D : Finset P.Color) (x ω : P.Sample) :
    (P.gated A E hE hdep).fixCoordinates D x ω = P.fixCoordinates D x ω := rfl

@[simp] theorem gated_fixedExpectation (D : Finset P.Color) (x : P.Sample)
    (f : P.Sample → ℝ) :
    (P.gated A E hE hdep).fixedExpectation D x f = P.fixedExpectation D x f := rfl

end
end Balanced.PatternModel

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateGlobalLineModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateGlobalLine

noncomputable section
open scoped Classical BigOperators
open MeasureTheory CandidateExposure CandidateIncidence PartialAlignment

universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
local instance globalLineModelMeasurableSpace : MeasurableSpace F := ⊤

abbrev lineModel (L : Line F) := allModel (lineHitTest L)

def oldLineTest (L : Line F) (D : Finset (Direction F)) : Test F :=
  fun T _ p => 0 < (exposedTupleIndices T D).card ∧ ∃ i, OnLine (p i) L

omit [Field F] in
theorem lineGate_depends (L : Line F) (M N : MergedPairs F)
    (h : ∀ d ∈ ({L.1} : Finset (Direction F)), M d = N d) :
    L ∉ constituentLines M ↔ L ∉ constituentLines N :=
  CandidateLineGate.not_mem_iff_of_direction_agreement L M N (h L.1 (by simp))

abbrev gatedLineModel (L : Line F) : PatternModel.{u} :=
  (lineModel L).gated {L.1} {M | L ∉ constituentLines M}
    (Set.toFinite _).measurableSet (lineGate_depends L)

def globalLineMomentConstant (s : ℕ) : ℝ :=
  ((2*s).factorial : ℝ) * 2^(2*s) *
    (2 * (163840 * ((1 + 10*s : ℕ) + 1)^4 : ℝ))^(2*s)

end
end Balanced.CandidateGlobalLine

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_CandidateIncidenceTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateRetentionTransport

noncomputable section
open scoped Classical BigOperators
open TupleAlignment CandidateIncidence CandidateGlobalLine

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def choiceTest (P : SplitChoice F → Prop) : Test F :=
  fun T g p => P ⟨lineThrough g (p 0), T⟩

end
end Balanced.CandidateRetentionTransport

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateGlobalLineTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateGlobalLine
noncomputable section
open scoped Classical BigOperators
open MeasureTheory CandidateExposure CandidateIncidence Filter Topology

universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
local instance globalLineTailMeasurableSpace : MeasurableSpace F := ⊤

def globalLineCount (L : Line F) (M : MergedPairs F) : ℕ :=
  ∑ g : Direction F, tupleCount (lineHitTest L) g M

end
end Balanced.CandidateGlobalLine

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_ExternalWitnessModel
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

abbrev WitnessKey (F : Type u) :=
  (FourTuple F × (Fin 4 × Fin 4)) × (Direction F × Direction F)

def targetLine (g : Direction F) (M : MergedPairs F) (T : FourTuple F) : Line F :=
  (g, lineEval g (tuplePoint M T 0))

def witnessEvent (g : Direction F) (w : WitnessKey F) : Set (MergedPairs F) :=
  {M | SuccessfulOn M w.1.1 (targetLine g M w.1.1) ∧
    w.1.2.1 ≠ w.1.2.2 ∧ w.2.1 ≠ w.2.2 ∧
    w.2.1 ≠ g ∧ w.2.2 ≠ g ∧
    w.2.1 ∉ generatorSet w.1.1 ∧ w.2.2 ∉ generatorSet w.1.1 ∧
    ∃ x, OnLine x (targetLine g M w.1.1) ∧
      x ∉ designated M ⟨targetLine g M w.1.1, w.1.1⟩ ∧
      PairWitness M w.2.1 x (tuplePoint M w.1.1 w.1.2.1) ∧
      PairWitness M w.2.2 x (tuplePoint M w.1.1 w.1.2.2)}

def witnesses (g : Direction F) (M : MergedPairs F) : Finset (WitnessKey F) :=
  Finset.univ.filter (fun w => M ∈ witnessEvent g w)

@[simp] theorem mem_witnesses (g : Direction F) (M : MergedPairs F)
    (w : WitnessKey F) : w ∈ witnesses g M ↔ M ∈ witnessEvent g w := by
  simp [witnesses]

end
end Balanced.ExternalAssembly

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateOldExternalOverlap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateOldExternal

noncomputable section
open scoped Classical BigOperators
open CandidateExposure CandidateValidityWitness CandidateExposedWitness PartialAlignment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def targetLine (M : MergedPairs F) (g : Direction F) (T : FourTuple F) : Line F :=
  lineThrough g (tuplePoint M T 0)

def IsExternalWitness (M : MergedPairs F) (g : Direction F) (T : FourTuple F)
    (i j : Fin 4) (d e : Direction F) (x : Point F) : Prop :=
  OnLine x (targetLine M g T) ∧ x ∉ designated M ⟨targetLine M g T, T⟩ ∧
  i ≠ j ∧ d ≠ e ∧ d ≠ g ∧ e ≠ g ∧ d ∉ generatorSet T ∧ e ∉ generatorSet T ∧
  PairWitness M d x (tuplePoint M T i) ∧ PairWitness M e x (tuplePoint M T j)

abbrev WitnessKey (F : Type*) :=
  (FourTuple F × (Fin 4 × Fin 4)) × (Direction F × Direction F)

abbrev WitnessLabel (F : Type*) := WitnessKey F × Point F

def oldOverlapKeys (g : Direction F) (D : Finset (Direction F)) (M : MergedPairs F) :
    Finset (WitnessKey F) :=
  (((((eligibleTuples g).filter (fun T => 0 < (exposedTupleIndices T D).card)).filter
    (fun T => M ∈ successfulInDirection T g)).product Finset.univ).product (D.product D))

def oldOverlapWitnesses (g : Direction F) (D : Finset (Direction F)) (M : MergedPairs F) :
    Finset (WitnessLabel F) :=
  ((oldOverlapKeys g D M).product Finset.univ).filter (fun w =>
    IsExternalWitness M g w.1.1.1 w.1.1.2.1 w.1.1.2.2 w.1.2.1 w.1.2.2 w.2)

def oldOverlapPrescriptions (g : Direction F) (D : Finset (Direction F)) :
    Finset (WitnessKey F) :=
  ((((eligibleTuples g).filter (fun T => 0 < (exposedTupleIndices T D).card)).product
    Finset.univ).product (D.product D))

def keyEvent (g : Direction F) (k : WitnessKey F) : Set (MergedPairs F) :=
  {M | M ∈ successfulInDirection k.1.1 g ∧
    ∃ x, IsExternalWitness M g k.1.1 k.1.2.1 k.1.2.2 k.2.1 k.2.2 x}

end
end Balanced.CandidateOldExternal

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_FiniteUniformFibers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.FiniteUniformFibers

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem probability_fintype_congr {Ω : Type*} (f g : Fintype Ω) [Nonempty Ω]
    {s t : Set Ω} (h : s = t) :
    ((@PMF.uniformOfFintype Ω f inferInstance).toOuterMeasure s).toReal =
      ((@PMF.uniformOfFintype Ω g inferInstance).toOuterMeasure t).toReal := by
  cases Subsingleton.elim f g
  cases h
  rfl

theorem probability_eq_sum {Ω : Type*} [Fintype Ω] [Nonempty Ω] (E : Ω → Prop) :
    ((PMF.uniformOfFintype Ω).toOuterMeasure {ω | E ω}).toReal =
      (∑ ω, if E ω then (1 : ℝ) else 0) / Fintype.card Ω := by
  rw [PMF.toOuterMeasure_uniformOfFintype_apply, ENNReal.toReal_div]
  simp only [ENNReal.toReal_natCast, Fintype.card_subtype, Finset.sum_boole, Set.mem_ofPred_eq]

theorem sum_inter_eq_mul {Ω Y : Type*} [Fintype Ω] [Fintype Y]
    (expose : Ω → Y) (E B : Ω → Prop) (c : ℝ)
    (hE : ∀ x y, expose x = expose y → (E x ↔ E y))
    (hB : ∀ x, (∑ y : {y // expose y = expose x},
      if B y then (1 : ℝ) else 0) =
        c * Fintype.card {y // expose y = expose x}) :
    (∑ x, if E x ∧ B x then (1 : ℝ) else 0) =
      c * ∑ x, if E x then (1 : ℝ) else 0 := by
  classical
  rw [← Fintype.sum_fiberwise expose (fun x => if E x ∧ B x then (1 : ℝ) else 0),
    ← Fintype.sum_fiberwise expose (fun x => if E x then (1 : ℝ) else 0),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  cases isEmpty_or_nonempty {x // expose x = z} with
  | inl h =>
      let := h
      simp
  | inr h =>
      obtain ⟨x⟩ := h
      have hx (y : {x // expose x = z}) : E y ↔ E x :=
        hE y x (y.property.trans x.property.symm)
      by_cases he : E x
      · have hb := hB x
        rw [x.property] at hb
        simpa only [hx, he, true_and, ite_true, Finset.sum_const,
          Finset.card_univ, nsmul_eq_mul, mul_one] using hb
      · simp only [hx, he, false_and, ite_false, Finset.sum_const_zero, mul_zero]

theorem fixed_probability_inter {D A : Type*} [Fintype D] [Fintype A]
    [DecidableEq D] [Nonempty A] (S : Finset D) (E B : (D → A) → Prop) (c : ℝ)
    (hE : ∀ x y, (∀ d ∈ S, x d = y d) → (E x ↔ E y))
    (hB : ∀ a : D → A,
      ((PMF.uniformOfFintype (ConditionalRestriction.FixedArray (fun d => d ∈ S) a)).toOuterMeasure
        {x | B x.1}).toReal = c) :
    ((PMF.uniformOfFintype (D → A)).toOuterMeasure {x | E x ∧ B x}).toReal =
      c * ((PMF.uniformOfFintype (D → A)).toOuterMeasure {x | E x}).toReal := by
  classical
  let expose : (D → A) → (S → A) := fun x d => x d
  have heq (x y : D → A) : expose x = expose y ↔ ∀ d ∈ S, x d = y d := by
    constructor
    · intro h d hd
      exact congrFun h ⟨d,hd⟩
    · intro h
      funext d
      exact h d d.2
  have hf (a : D → A) :
      (∑ x : {x // expose x = expose a}, if B x then (1 : ℝ) else 0) =
        c * Fintype.card {x // expose x = expose a} := by
    let e : {x // expose x = expose a} ≃
        ConditionalRestriction.FixedArray (fun d => d ∈ S) a :=
      Equiv.subtypeEquivRight (fun x => heq x a)
    let : Nonempty {x // expose x = expose a} := ⟨⟨a,rfl⟩⟩
    have hmap := TupleAlignment.uniform_map_equiv e
    have h := congrArg (fun law => (law.toOuterMeasure
      {x : ConditionalRestriction.FixedArray (fun d => d ∈ S) a | B x.1}).toReal) hmap
    rw [PMF.toOuterMeasure_map_apply] at h
    have hp : ((PMF.uniformOfFintype {x // expose x = expose a}).toOuterMeasure
        {x | B x.1}).toReal = c := h.trans (hB a)
    rw [probability_eq_sum] at hp
    exact (div_eq_iff (by exact_mod_cast Fintype.card_ne_zero)).mp hp
  have hsum := sum_inter_eq_mul expose E B c
    (fun x y h => hE x y ((heq x y).mp h)) (by
      intro x
      convert hf x using 1 <;> congr 1
      · ext y
        simp only [Finset.mem_univ]
      · congr 1
        unfold Fintype.card
        congr 1
        ext y
        simp only [Finset.mem_univ])
  simp only [probability_eq_sum]
  calc
    _ = (c * ∑ x, if E x then (1 : ℝ) else 0) / Fintype.card (D → A) := by
      congr 1
      convert hsum using 1
      all_goals try with_reducible_and_instances rfl
      congr 1
      funext x
      split_ifs <;> rfl
    _ = _ := by ring

end
end Balanced.FiniteUniformFibers

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateMixedExternal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateMixedExternal

noncomputable section
open scoped Classical BigOperators
open CandidateExposure CandidateValidityWitness CandidateExposedWitness

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def tupleTarget (g : Direction F) (T : FourTuple F) (M : MergedPairs F) : Line F :=
  (g, lineEval g (tuplePoint M T 0))

def mixedExternalEvent (g : Direction F) (T : FourTuple F)
    (d e : Direction F) (i j : Fin 4) : Set (MergedPairs F) :=
  {M | M ∈ successfulInDirection T g ∧ ∃ x : Point F,
    OnLine x (tupleTarget g T M) ∧
    x ∉ designated M ⟨tupleTarget g T M, T⟩ ∧ i ≠ j ∧
    PairWitness M d x (tuplePoint M T i) ∧
    PairWitness M e x (tuplePoint M T j)}

def forcedFreshEvent (g : Direction F) (T : FourTuple F) (a : MergedPairs F)
    (d e : Direction F) (j : Fin 4) (σ τ : Bool) : Set (MergedPairs F) :=
  {M | M ∈ successfulInDirection T g ∧
    OnLine (forcedPoint a (tupleTarget g T M) d σ) (constituent M e τ) ∧
    OnLine (tuplePoint M T j) (constituent M e (!τ))}

def freshWitnessDirections (g : Direction F) (T : FourTuple F)
    (D : Finset (Direction F)) : Finset (Direction F) :=
  Finset.univ.filter (fun e => e ∉ D ∧ e ≠ g ∧ e ∉ generatorSet T)

def oldWitnessDirections (g : Direction F) (T : FourTuple F)
    (D : Finset (Direction F)) : Finset (Direction F) :=
  D.filter (fun d => d ≠ g ∧ d ∉ generatorSet T)

def mixedExternalProbabilitySum (g : Direction F)
    (D : Finset (Direction F)) (a : MergedPairs F) : ℝ :=
  ∑ T ∈ (eligibleTuples g).filter
      (fun T => 0 < (PartialAlignment.exposedTupleIndices T D).card),
    ∑ d ∈ oldWitnessDirections g T D,
      ∑ e ∈ freshWitnessDirections g T D, ∑ i : Fin 4, ∑ j : Fin 4,
        conditionalProbability D a (mixedExternalEvent g T d e i j)

end
end Balanced.CandidateMixedExternal

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_MixedExternalAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateMixedExternal

noncomputable section
open scoped Classical BigOperators
open MeasureTheory CandidateExposure CandidateValidityWitness ExternalAssembly
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
local instance mixedAssemblyMeasurableSpace : MeasurableSpace F := ⊤

def mixedOverlapFilter (D : Finset (Direction F)) (w : WitnessKey F) : Prop :=
  0 < (PartialAlignment.exposedTupleIndices w.1.1 D).card ∧
    w.2.1 ∈ D ∧ w.2.2 ∉ D

def mixedOverlapCount (g : Direction F) (D : Finset (Direction F))
    (M : MergedPairs F) : ℕ :=
  ((witnesses g M).filter (mixedOverlapFilter D)).card

def mixedOverlapKeys (g : Direction F) (D : Finset (Direction F)) :
    Finset (WitnessKey F) :=
  Finset.univ.filter fun w =>
    w.1.1 ∈ (eligibleTuples g).filter
      (fun T => 0 < (PartialAlignment.exposedTupleIndices T D).card) ∧
    w.2.1 ∈ oldWitnessDirections g w.1.1 D ∧
    w.2.2 ∈ freshWitnessDirections g w.1.1 D

end
end Balanced.CandidateMixedExternal

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_ExternalWitnessMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.ExternalAssembly

noncomputable section
open scoped Classical BigOperators
open MeasureTheory CandidateExposure PartialAlignment
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def exposureConstant (m : ℕ) : ℝ :=
  5242880 * ((m : ℝ) + 1)^4 + 2 *
    (262144 * (m : ℝ)^2 * ((m : ℝ) + 1)^4 +
     2097152 * ((m : ℝ) + 1)^5 +
     (8192 * (m : ℝ)^2 + 32768 * m))

end
end Balanced.ExternalAssembly

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_ConstituentOffsets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

abbrev ConstituentOffsets (D K : Type*) := D → K × K

def AllConstituentPairsDistinct {D K : Type*} (M : ConstituentOffsets D K) : Prop :=
  ∀ d, (M d).1 ≠ (M d).2

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_Concentration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Real
open scoped BigOperators

namespace Balanced
open scoped _root_.Balanced

universe u

def BoundedDriftConcentration : Prop :=
  ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ) (T : ℕ) (L : ℝ),
    1 ≤ T → 0 < L →
    (∀ j ≤ T, StronglyMeasurable[ℱ j] (X j)) →
    (∀ j < T, ∀ᵐ ω ∂μ, |X (j + 1) ω - X j ω| ≤ L) →
    ∀ (u : ℝ), 0 < u → ∀ (t : ℕ), t ≤ T →
      μ.real {ω | u ≤ |X t ω - X 0 ω - ∑ j ∈ Finset.range t,
        μ[fun ω ↦ X (j + 1) ω - X j ω | ℱ j] ω|} ≤
        2 * exp (-u ^ 2 / (8 * (T : ℝ) * L ^ 2))

end Balanced

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

variable [Fintype F] [DecidableEq F]

abbrev TransverseDirections (l : Line F) := {d : Direction F // d ≠ l.1}

omit [Field F] in
@[simp] theorem card_transverseDirections (l : Line F) :
    Fintype.card (TransverseDirections l) = Fintype.card F := by
  simp [TransverseDirections, Fintype.card_subtype_compl]

end Balanced.LineOccupancy

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateProbabilityAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateProbability

open Filter
open scoped Topology

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def GeometricGood (M : MergedPairs F) : Prop :=
  (∀ p, sampledMultiplicity M p ≤ ⌈Real.log (Fintype.card F : ℝ)⌉₊) ∧
  (∀ l, l ∉ initialDeletedLines M →
    (1 / 5 : ℝ) * Fintype.card F ≤ ((linePoints l ∩ initiallyRetained M).card : ℝ))

universe u

end
end Balanced.CandidateProbability

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_CandidateIncidenceProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped Topology Classical

namespace Balanced.CandidateIncidenceTests

universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]

local instance incidenceMeasurableSpace : MeasurableSpace F := ⊤

end Balanced.CandidateIncidenceTests

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_CandidateIncidenceCountTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateIncidence

noncomputable section
open scoped Classical BigOperators
open MeasureTheory TupleAlignment CandidateRetentionTransport

universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
local instance incidenceTransportMeasurableSpace : MeasurableSpace F := ⊤

def choiceTest (R : Test F) (M : MergedPairs F) (C : SplitChoice F) : Prop :=
  R C.tuple C.line.1 (tuplePoint M C.tuple)

end
end Balanced.CandidateIncidence

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateLineHitFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateIncidenceTests

noncomputable section
open MeasureTheory
universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
local instance lineHitFamilyMeasurableSpace : MeasurableSpace F := ⊤

end
end Balanced.CandidateIncidenceTests

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_CandidatePointIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidatePointIncidence

noncomputable section
open scoped Classical BigOperators
open CandidateExposure PartialAlignment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def pointEvent (T : FourTuple F) (g : Direction F) (y : Point F) :
    Set (MergedPairs F) :=
  successfulInDirection T g ∩ {M | ∃ i, tuplePoint M T i = y}

def pointLineEvent (T : FourTuple F) (g : Direction F) (y : Point F) (K : Line F) :
    Set (MergedPairs F) :=
  {M | (∀ i, OnLine (tuplePoint M T i) (lineThrough g y)) ∧
    Function.Injective (tuplePoint M T) ∧ ∃ i, OnLine (tuplePoint M T i) K}

end
end Balanced.CandidatePointIncidence

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_CandidatePointIncidenceMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidatePointIncidence

noncomputable section
open scoped Classical BigOperators
open CandidateExposure PartialAlignment MeasureTheory

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def pointTest (y : Point F) : CandidateIncidence.Test F := fun _ _ p => ∃ i, p i = y

def pointLineTest (y : Point F) (K : Line F) : CandidateIncidence.Test F :=
  fun _ g p => (∀ i, OnLine (p i) (lineThrough g y)) ∧ ∃ i, OnLine (p i) K

end
end Balanced.CandidatePointIncidence

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidatePointFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateIncidenceTests

noncomputable section
open scoped Classical
open MeasureTheory TupleAlignment CandidateRetentionTransport CandidateIncidence
open CandidatePointIncidence
universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
local instance pointFamilyMeasurableSpace : MeasurableSpace F := ⊤

end
end Balanced.CandidateIncidenceTests

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_PartialIncidenceCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.PartialAlignment
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

abbrev IncidenceCode (F : Type*) :=
  ((Fin 4 → Direction F) × (Fin 4 → Bool)) × Direction F

end
end Balanced.PartialAlignment

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_CandidateIncidenceInitialSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateIncidenceSums

noncomputable section
open scoped Classical BigOperators
open PartialAlignment TupleAlignment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def admissibleCodes (D : Finset (Direction F)) (j : ℕ) : Finset (IncidenceCode F) :=
  ((tupleCodesWithOldCount D j).product Finset.univ).filter
    (fun z => Function.Injective z.1.1 ∧ ∀ i, z.1.1 i ≠ z.2)

def probability (D : Finset (Direction F)) (a : MergedPairs F)
    (E : Set (MergedPairs F)) : ℝ :=
  (((offsetLaw F).filter {M | ∀ d, d ∈ D → M d = a d}
    (canonical_exposure_supported D a)).toOuterMeasure E).toReal

def codeEvent (P : Direction F → (Fin 4 → Point F) → Prop)
    (z : IncidenceCode F) : Set (MergedPairs F) :=
  {M | SuccessfulPositions (tuplePoint M ⟨z.1.1,z.1.2⟩) z.2 ∧
    P z.2 (tuplePoint M ⟨z.1.1,z.1.2⟩)}

def incidenceSum (D : Finset (Direction F)) (a : MergedPairs F) (j : ℕ)
    (P : Direction F → (Fin 4 → Point F) → Prop) : ℝ :=
  ∑ z ∈ admissibleCodes D j, probability D a (codeEvent P z)

def hitsTwoLines (L K : Line F) : Direction F → (Fin 4 → Point F) → Prop :=
  fun _ p => ∃ i j : Fin 4, i ≠ j ∧ OnLine (p i) L ∧ OnLine (p j) K

end
end Balanced.CandidateIncidenceSums

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_CandidateIncidenceRootSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateIncidenceSums

noncomputable section
open scoped Classical BigOperators
open PartialAlignment TupleAlignment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

abbrev TargetPrescription (F : Type*) := Σ g : Direction F, RootPrescription g

def rootCodes (D : Finset (Direction F)) (j : ℕ) : Finset (TargetPrescription F) :=
  Finset.univ.filter (fun r => (exposedTupleIndices r.2.tuple D).card = j)

def rootCode (r : TargetPrescription F) : IncidenceCode F :=
  ((r.2.tuple.generator,r.2.tuple.side),r.1)

def rootIncidenceSum (D : Finset (Direction F)) (a : MergedPairs F) (j : ℕ)
    (P : Direction F → (Fin 4 → Point F) → Prop) : ℝ :=
  ∑ r ∈ rootCodes D j, probability D a
    {M | SuccessfulPositions (tuplePoint M r.2.tuple) r.1 ∧
      P r.1 (tuplePoint M r.2.tuple)}

end
end Balanced.CandidateIncidenceSums

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_PatternAllowedGate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped BigOperators

namespace Balanced.PatternModel

universe u
noncomputable section
attribute [local instance] Classical.propDecidable

def gateInitialEvent (P : PatternModel.{u}) (K₀ : Finset P.Color)
    (S : Set P.Sample) (hS : MeasurableSet S)
    (hdepends : ∀ x y, (∀ c ∈ K₀, x c = y c) → (x ∈ S ↔ y ∈ S)) :
    PatternModel.{u} where
  Color := P.Color
  colorFintype := P.colorFintype
  colorDecidableEq := P.colorDecidableEq
  Value := P.Value
  valueMeasurable := P.valueMeasurable
  law := P.law
  lawProbability := P.lawProbability
  Label := P.Label
  labelFintype := P.labelFintype
  support a := K₀ ∪ P.support a
  event a := S ∩ P.event a
  eventMeasurable a := hS.inter (P.eventMeasurable a)
  dependsOn a x y hxy := and_congr
    (hdepends x y (fun c hc => hxy c (Finset.mem_union_left _ hc)))
    (P.dependsOn a x y (fun c hc => hxy c (Finset.mem_union_right _ hc)))

variable (P : PatternModel.{u}) (K₀ : Finset P.Color)
    (S : Set P.Sample) (hS : MeasurableSet S)
    (hdepends : ∀ x y, (∀ c ∈ K₀, x c = y c) → (x ∈ S ↔ y ∈ S))

@[simp] theorem gateInitialEvent_measure :
    (P.gateInitialEvent K₀ S hS hdepends).measure = P.measure := rfl

@[simp] theorem gateInitialEvent_fixCoordinates (K : Finset P.Color) (x ω : P.Sample) :
    (P.gateInitialEvent K₀ S hS hdepends).fixCoordinates K x ω =
      P.fixCoordinates K x ω := rfl

@[simp] theorem gateInitialEvent_indicator (a : P.Label) (ω : P.Sample) :
    (P.gateInitialEvent K₀ S hS hdepends).indicator a ω =
      if ω ∈ S then P.indicator a ω else 0 := by
  by_cases h : ω ∈ S <;>
    simp [indicator, gateInitialEvent, Set.indicator_apply, h]

@[simp] theorem gateInitialEvent_count (ω : P.Sample) :
    (P.gateInitialEvent K₀ S hS hdepends).count ω =
      if ω ∈ S then P.count ω else 0 := by
  change (∑ label : P.Label, (P.gateInitialEvent K₀ S hS hdepends).indicator label ω) =
    if ω ∈ S then (∑ label : P.Label, P.indicator label ω) else 0
  simp_rw [P.gateInitialEvent_indicator K₀ S hS hdepends]
  by_cases hmem : ω ∈ S <;> simp [hmem]

@[simp] theorem gateInitialEvent_freshSupport (a : P.Label) :
    (P.gateInitialEvent K₀ S hS hdepends).support a \ K₀ = P.support a \ K₀ := by
  change (K₀ ∪ P.support a) \ K₀ = P.support a \ K₀
  ext c
  simp only [Finset.mem_sdiff, Finset.mem_union]
  tauto

@[simp] theorem gateInitialEvent_overlapCount (K : Finset P.Color) (ω : P.Sample) :
    (P.gateInitialEvent K₀ S hS hdepends).overlapCount K₀ K ω =
      if ω ∈ S then P.overlapCount K₀ K ω else 0 := by
  change (∑ a : P.Label, if Disjoint ((K₀ ∪ P.support a) \ K₀) K then 0 else
      (S ∩ P.event a).indicator (fun _ => (1 : ℝ)) ω) =
    if ω ∈ S then (∑ a : P.Label, if Disjoint (P.support a \ K₀) K then 0 else
      P.indicator a ω) else 0
  have hs (a : P.Label) : (K₀ ∪ P.support a) \ K₀ = P.support a \ K₀ := by
    ext c
    simp only [Finset.mem_sdiff, Finset.mem_union]
    tauto
  simp_rw [hs]
  by_cases h : ω ∈ S <;> simp [Set.indicator_apply, indicator, h]

end
end Balanced.PatternModel

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateTwoLineMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateIncidenceSums

noncomputable section
open scoped Classical BigOperators
open PartialAlignment TupleAlignment CandidateExposure CandidateIncidence MeasureTheory

universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
local instance twoLineMeasurableSpace : MeasurableSpace F := ⊤

def tupleIncidenceSum (D : Finset (Direction F)) (a : MergedPairs F) (j : ℕ)
    (P : Direction F → (Fin 4 → Point F) → Prop) : ℝ :=
  ∑ g : Direction F, ∑ T ∈ tuplesWithExposure g D j, conditionalProbability D a
    {M | M ∈ successfulInDirection T g ∧ P g (tuplePoint M T)}

def twoLineTest (L K : Line F) : Test F := fun _ g p => hitsTwoLines L K g p

def twoLineInitial (L K : Line F) : Finset (Direction F) := {L.1,K.1}

def twoLineAllowed (L K : Line F) : Set (MergedPairs F) :=
  {M | L ≠ K ∧ (∀ b, M L.1 b ≠ L.2) ∧ (∀ b, M K.1 b ≠ K.2)}

omit [Field F] [Fintype F] in
theorem twoLineAllowed_depends (L K : Line F) (x y : MergedPairs F)
    (h : ∀ d ∈ twoLineInitial L K, x d = y d) :
    x ∈ twoLineAllowed L K ↔ y ∈ twoLineAllowed L K := by
  have hL := h L.1 (by simp [twoLineInitial])
  have hK := h K.1 (by simp [twoLineInitial])
  simp only [twoLineAllowed, Set.mem_ofPred_eq, hL, hK]

abbrev twoLineModel (L K : Line F) : PatternModel.{u} :=
  (allModel (twoLineTest L K)).gateInitialEvent (twoLineInitial L K)
    (twoLineAllowed L K) (Set.toFinite _).measurableSet (twoLineAllowed_depends L K)

end
end Balanced.CandidateIncidenceSums

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateTwoLineFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateIncidenceTests

noncomputable section
open scoped Classical
open MeasureTheory
universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
local instance twoLineRawMeasurableSpace : MeasurableSpace F := ⊤

end
end Balanced.CandidateIncidenceTests

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_CandidateSmallIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace Balanced.CandidateIncidenceTests

universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
local instance smallFamilyMeasurableSpace : MeasurableSpace F := ⊤

def smallMomentConstant (s : ℕ) : ℝ :=
  max ((60000 * (((s-1)*4 : ℕ)+1)^4 : ℝ)^s)
    (max ((40960 * ((((s-1)*6 : ℕ) : ℝ)+3)^4)^s)
      (max ((32768 * (((s-1)*4 : ℕ)+3)^4 : ℝ)^s)
        ((32768 * (((s-1)*4 : ℕ)+1)^4 : ℝ)^s)))

end Balanced.CandidateIncidenceTests

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateGraphEndpoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Balanced
open scoped _root_.Balanced

open Filter
open scoped Topology

universe u

namespace CandidateGraphEndpoint

def externalMomentConstant : ℝ :=
  (ExternalAssembly.exposureConstant (399 * 6)) ^ 400

end CandidateGraphEndpoint

end Balanced

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateSelectionBridge
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

abbrev AvailableCandidate (M : MergedPairs F) :=
  {v : CandidateVertex F // v ∈ candidateVertices M}

end
end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_CoreRepresentatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced
namespace Configuration

noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable (C : Configuration F)

def coreRepresentative : BlockLabel F → Finset (Line F)
  | Sum.inl l => {l}
  | Sum.inr (Sum.inl d) => {constituent C.merged d false}
  | Sum.inr (Sum.inr _) => ∅

def RepresentedThrough (P : ProjectivePoint F) (b : BlockLabel F) : Prop :=
  ∃ l ∈ C.coreRepresentative b, ThroughProjective l P

end
end Configuration
end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_AffinePencilForcing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

noncomputable section
attribute [local instance] Classical.propDecidable
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

@[simp] lemma mem_linePoints_iff (p : Point F) (l : Line F) :
    p ∈ linePoints l ↔ OnLine p l := by simp [linePoints]

end
end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_DeletedConstituentForcing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced
namespace Configuration

noncomputable section
attribute [local instance] Classical.propDecidable
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable (C : Configuration F)

@[simp] lemma on_line_iff_mem (p : Point F) (l : Line F) :
    p ∈ linePoints l ↔ OnLine p l := by simp [linePoints]

end
end Configuration
end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Construction_BlockPartitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Configuration.BlockPartitions

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {C : Configuration F}

theorem split_direction (hV : C.Valid) (s : Slot F) : (C.choice s).line.1 = s.1 :=
  (hV.2 s).1

theorem point_on_split_designated (hC : C.Compatible) {p : Point F}
    (hp : p ∈ C.points) (s : Slot F) (hs : OnLine p (C.choice s).line) :
    p ∈ designated C.merged (C.choice s) := by
  classical
  rcases Finset.mem_union.mp hp with hp | hp
  · have hr := (Finset.mem_filter.mp hp).2
    exact (hr _ (Finset.mem_image.mpr ⟨s, Finset.mem_univ _, rfl⟩) hs).elim
  · rcases Finset.mem_biUnion.mp hp with ⟨t, ht, hp⟩
    by_cases hst : s = t
    · simpa [hst] using hp
    · exact (hC.1 s t hst p hp hs).elim

theorem block_exists (hV : C.Valid) (hC : C.Compatible)
    {p : Point F} (hp : p ∈ C.points) (d : Direction F) :
    ∃ b ∈ C.labelsInDirection d, p ∈ C.blockPoints b := by
  classical
  let l := lineThrough d p
  have hl : OnLine p l := rfl
  have hld : l.1 = d := rfl
  by_cases hs : l ∈ C.splitLines
  · rcases Finset.mem_image.mp hs with ⟨s, _, hsl⟩
    have hd : s.1 = d := (split_direction hV s).symm.trans
      ((congrArg Prod.fst hsl).trans hld)
    have hps : OnLine p (C.choice s).line := by rw [hsl]; exact hl
    have hdes := point_on_split_designated hC hp s hps
    rcases Finset.mem_image.mp hdes with ⟨i, _, hi⟩
    refine ⟨Sum.inr (Sum.inr (s, decide (i.val % 2 = 1))), ?_, ?_⟩
    · exact Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, trivial⟩, hd⟩
    · fin_cases i <;> simp [blockPoints, ← hi]
  · by_cases hm : l ∈ constituentLines C.merged
    · rcases Finset.mem_image.mp hm with ⟨⟨g, b⟩, _, hgl⟩
      have hgd : g = d := (congrArg Prod.fst hgl).trans hld
      refine ⟨Sum.inr (Sum.inl d), ?_, ?_⟩
      · exact Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, trivial⟩, rfl⟩
      · apply Finset.mem_inter.mpr
        refine ⟨?_, hp⟩
        have hconst : OnLine p (constituent C.merged d b) := by
          rw [← hgd, hgl]
          exact hl
        have hmem : p ∈ linePoints (constituent C.merged d b) := by
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hconst⟩
        cases b
        · exact Finset.mem_union_left _ hmem
        · exact Finset.mem_union_right _ hmem
    · refine ⟨Sum.inl l, ?_, ?_⟩
      · exact Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, fun hmem => (Finset.mem_union.mp hmem).elim hs hm⟩, hld⟩
      · exact Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl⟩, hp⟩

noncomputable def pointLabel (hV : C.Valid) (hC : C.Compatible)
    (d : Direction F) (p : {p // p ∈ C.points}) :
    {b // b ∈ C.labelsInDirection d} :=
  ⟨Classical.choose (block_exists hV hC p.property d),
    (Classical.choose_spec (block_exists hV hC p.property d)).1⟩

end Balanced.Configuration.BlockPartitions

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

namespace Balanced.Configuration
open scoped _root_.Balanced

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def Represents (C : Configuration F)
    (H : PartiteHypergraph (Fintype.card F + 1) (Fintype.card F + 1)) : Prop :=
  ∃ eDir : Direction F ≃ Fin (Fintype.card F + 1),
  ∃ eLabel : ∀ d, {b // b ∈ C.labelsInDirection d} ≃ Fin (Fintype.card F + 1),
  ∃ ePoint : {p // p ∈ C.points} ≃ {e // e ∈ H.edges},
    ∀ p d b, p.val ∈ C.blockPoints b.val ↔
      (ePoint p).val (eDir d) = eLabel d b

end Balanced.Configuration

end

section

namespace Balanced
open scoped _root_.Balanced

universe u

structure ConfigurationRealization
    {F : Type u} [Field F] [Fintype F] [DecidableEq F]
    (C : Configuration F)
    (H : PartiteHypergraph (Fintype.card F + 1) (Fintype.card F + 1)) where
  directionEquiv : Direction F ≃ Fin (Fintype.card F + 1)
  labelEquiv : {b : Configuration.BlockLabel F // b ∈ C.blockLabels} ≃
    PartiteHypergraph.Vertex (Fintype.card F + 1) (Fintype.card F + 1)
  edgeEquiv : {p : Point F // p ∈ C.points} ≃ {e // e ∈ H.edges}
  label_direction : ∀ b,
    (labelEquiv b).1 = directionEquiv (Configuration.blockDirection b.val)
  incidence : ∀ p b,
    p.val ∈ C.blockPoints b.val ↔
      (edgeEquiv p).val (labelEquiv b).1 = (labelEquiv b).2

end Balanced

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Construction_PartitionEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

def encodeAssignment {G X : Type*} {Label : G → Type*} {r n : ℕ}
    (eG : G ≃ Fin r) (eL : ∀ g, Label g ≃ Fin n)
    (label : (g : G) → X → Label g) (x : X) : Fin r → Fin n :=
  fun i => eL (eG.symm i) (label (eG.symm i) x)

@[simp] theorem encodeAssignment_apply_index
    {G X : Type*} {Label : G → Type*} {r n : ℕ}
    (eG : G ≃ Fin r) (eL : ∀ g, Label g ≃ Fin n)
    (label : (g : G) → X → Label g) (x : X) (g : G) :
    encodeAssignment eG eL label x (eG g) = eL g (label g x) := by
  exact congrArg (fun g => eL g (label g x)) (eG.symm_apply_apply g)

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Construction_PartitionHypergraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

variable {G X : Type*} [Fintype X] {Label : G → Type*} {r n : ℕ}

def partitionHypergraph (eG : G ≃ Fin r) (eL : ∀ g, Label g ≃ Fin n)
    (label : (g : G) → X → Label g) : PartiteHypergraph r n where
  edges := Finset.univ.image (encodeAssignment eG eL label)

@[simp] theorem mem_partitionHypergraph_edges
    (eG : G ≃ Fin r) (eL : ∀ g, Label g ≃ Fin n)
    (label : (g : G) → X → Label g) (e : Fin r → Fin n) :
    e ∈ (partitionHypergraph eG eL label).edges ↔
      ∃ x, encodeAssignment eG eL label x = e := by
  classical
  simp [partitionHypergraph]

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_ConfigurationStructure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced
namespace ConfigurationStructure

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable (C : Configuration F)

theorem designated_slot_unique (hC : C.Compatible) {i j : Slot F} {p : Point F}
    (hpi : p ∈ designated C.merged (C.choice i)) (hpj : OnLine p (C.choice j).line) :
    i = j := by
  by_contra hij
  exact hC.1 j i (Ne.symm hij) p hpi hpj

theorem choice_line_injective (hV : C.Valid) (hC : C.Compatible) :
    Function.Injective (fun s => (C.choice s).line) := by
  intro i j hij
  change (C.choice i).line = (C.choice j).line at hij
  apply designated_slot_unique C hC (p := tuplePoint C.merged (C.choice i).tuple 0)
  · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  · rw [← hij]
    exact (hV.2 i).2.2.2.2.2.1 0

theorem split_multiplicity_eq_slots (hV : C.Valid) (hC : C.Compatible) (p : Point F) :
    C.splitMultiplicity p =
      (Finset.univ.filter (fun s : Slot F => OnLine p (C.choice s).line)).card := by
  unfold Configuration.splitMultiplicity Configuration.splitLinesAt Configuration.splitLines
  rw [Finset.filter_image,
    Finset.card_image_of_injective _ (choice_line_injective C hV hC)]

end ConfigurationStructure
end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_ConfigurationBlockCardinality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Configuration

noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable (C : Configuration F)

lemma choice_line_direction (hV : C.Valid) (s : Slot F) :
    (C.choice s).line.1 = s.1 := (hV.2 s).1

lemma choice_line_not_constituent (hV : C.Valid) (s : Slot F) :
    (C.choice s).line ∉ constituentLines C.merged := (hV.2 s).2.1

lemma tuplePoint_on_choice (hV : C.Valid) (s : Slot F) (i : Fin 4) :
    OnLine (tuplePoint C.merged (C.choice s).tuple i) (C.choice s).line :=
  (hV.2 s).2.2.2.2.2.1 i

omit [Field F] in
lemma constituent_mem_lines (d : Direction F) (s : Bool) :
    constituent C.merged d s ∈ constituentLines C.merged := by
  exact Finset.mem_image.mpr ⟨(d, s), Finset.mem_univ _, rfl⟩

lemma choice_line_injective (hV : C.Valid) (hC : C.Compatible) :
    Function.Injective (fun s => (C.choice s).line) := by
  intro i j hij
  by_contra hne
  let p := tuplePoint C.merged (C.choice j).tuple 0
  have hp : p ∈ designated C.merged (C.choice j) :=
    Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  apply hC.1 i j hne p hp
  simpa [hij] using C.tuplePoint_on_choice hV j 0

lemma constituent_ne_choice (hV : C.Valid) (d : Direction F) (b : Bool) (s : Slot F) :
    constituent C.merged d b ≠ (C.choice s).line := by
  intro h
  exact C.choice_line_not_constituent hV s (h ▸ C.constituent_mem_lines d b)

lemma split_disjoint_constituent (hV : C.Valid) :
    Disjoint C.splitLines (constituentLines C.merged) := by
  rw [Finset.disjoint_left]
  intro l hl hm
  rcases Finset.mem_image.mp hl with ⟨s, _, rfl⟩
  exact C.choice_line_not_constituent hV s hm

lemma split_line_same_direction_iff (hV : C.Valid) (d : Direction F) (l : Line F)
    (hld : l.1 = d) :
    l ∈ C.splitLines ↔ l = (C.choice (d, false)).line ∨ l = (C.choice (d, true)).line := by
  constructor
  · intro hl
    rcases Finset.mem_image.mp hl with ⟨⟨g, b⟩, _, rfl⟩
    have hgd : g = d := (C.choice_line_direction hV (g, b)).symm.trans hld
    subst g
    cases b <;> simp
  · rintro (rfl | rfl) <;> exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩

omit [Field F] in
lemma constituent_line_same_direction_iff (d : Direction F) (l : Line F)
    (hld : l.1 = d) :
    l ∈ constituentLines C.merged ↔
      l = constituent C.merged d false ∨ l = constituent C.merged d true := by
  constructor
  · intro hl
    rcases Finset.mem_image.mp hl with ⟨⟨g, b⟩, _, rfl⟩
    change g = d at hld
    subst g
    cases b <;> simp
  · rintro (rfl | rfl) <;> exact C.constituent_mem_lines _ _

def specialLines (d : Direction F) : Finset (Line F) :=
  {(C.choice (d, false)).line, (C.choice (d, true)).line,
    constituent C.merged d false, constituent C.merged d true}

lemma specialLines_card (hV : C.Valid) (hC : C.Compatible) (d : Direction F) :
    (C.specialLines d).card = 4 := by
  have hsplit : (C.choice (d, false)).line ≠ (C.choice (d, true)).line := by
    intro h
    have := C.choice_line_injective hV hC h
    simp at this
  have hmerge : constituent C.merged d false ≠ constituent C.merged d true := by
    intro h
    exact hV.1 d (congrArg Prod.snd h)
  have h00 := (C.constituent_ne_choice hV d false (d, false)).symm
  have h01 := (C.constituent_ne_choice hV d true (d, false)).symm
  have h10 := (C.constituent_ne_choice hV d false (d, true)).symm
  have h11 := (C.constituent_ne_choice hV d true (d, true)).symm
  simp [specialLines, hsplit, hmerge, h00, h01, h10, h11]

lemma specialLines_subset_direction (hV : C.Valid) (d : Direction F) :
    C.specialLines d ⊆ linesInDirection d := by
  intro l hl
  simp only [specialLines, Finset.mem_insert, Finset.mem_singleton] at hl
  rcases hl with rfl | rfl | rfl | rfl
  all_goals simp [linesInDirection, C.choice_line_direction hV, constituent]

omit [Field F] in
lemma linesInDirection_card (d : Direction F) :
    (linesInDirection d).card = Fintype.card F := by
  have heq : linesInDirection d = Finset.univ.image (fun b : F => (d, b)) := by
    ext l
    rcases l with ⟨g, b⟩
    simp [linesInDirection, Prod.mk.injEq, eq_comm]
  rw [heq, Finset.card_image_of_injective]
  · simp
  · intro b b' h
    exact (Prod.mk.inj h).2

def regularLines (d : Direction F) : Finset (Line F) :=
  (linesInDirection d).filter (fun l => C.IsBlockLabel (Sum.inl l))

lemma regularLines_eq_sdiff (hV : C.Valid) (d : Direction F) :
    C.regularLines d = linesInDirection d \ C.specialLines d := by
  ext l
  simp only [regularLines, Finset.mem_filter, Finset.mem_sdiff]
  by_cases hld : l.1 = d
  · have hs := C.split_line_same_direction_iff hV d l hld
    have hm := C.constituent_line_same_direction_iff d l hld
    simp [linesInDirection, hld, IsBlockLabel, specialLines, hs, hm, and_assoc]
  · simp [linesInDirection, hld]

lemma regularLines_card (hV : C.Valid) (hC : C.Compatible) (d : Direction F) :
    (C.regularLines d).card = Fintype.card F - 4 := by
  rw [C.regularLines_eq_sdiff hV, Finset.card_sdiff_of_subset
    (C.specialLines_subset_direction hV d), C.specialLines_card hV hC,
    linesInDirection_card]

def splitLabels (d : Direction F) : Finset (Slot F × Bool) :=
  Finset.univ.image (fun b : Bool × Bool => ((d, b.1), b.2))

omit [Field F] [Fintype F] in
lemma mem_splitLabels (d : Direction F) (s : Slot F) (b : Bool) :
    (s, b) ∈ splitLabels d ↔ s.1 = d := by
  rcases s with ⟨g, a⟩
  simp [splitLabels, Prod.mk.injEq, eq_comm]

omit [Field F] [Fintype F] in
lemma splitLabels_card (d : Direction F) : (splitLabels d).card = 4 := by
  rw [splitLabels, Finset.card_image_of_injective]
  · simp
  · rintro ⟨a, b⟩ ⟨a', b'⟩ h
    simpa only [Prod.mk.injEq, true_and] using h

omit [Field F] in
lemma labelsInDirection_decomposition (d : Direction F) :
    C.labelsInDirection d = (C.regularLines d).disjSum
      (({d} : Finset (Direction F)).disjSum (splitLabels d)) := by
  ext label
  simp only [labelsInDirection, blockLabels, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases label with line | (direction | ⟨slot, side⟩)
  · simp [regularLines, linesInDirection, blockDirection, and_comm]
  · simp [IsBlockLabel, blockDirection]
  · simp [IsBlockLabel, blockDirection, mem_splitLabels]

theorem labelsInDirection_card (hV : C.Valid) (hC : C.Compatible)
    (hq : 4 ≤ Fintype.card F) (d : Direction F) :
    (C.labelsInDirection d).card = Fintype.card F + 1 := by
  rw [C.labelsInDirection_decomposition]
  simp only [Finset.card_disjSum, Finset.card_singleton, splitLabels_card,
    C.regularLines_card hV hC]
  omega

end
end Balanced.Configuration

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_PointLabelInjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Configuration.BlockPartitions

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {C : Configuration F}

noncomputable def mergedDirectionsAt (C : Configuration F) (p : Point F) :
    Finset (Direction F) :=
  ((constituentLines C.merged).filter (OnLine p)).image Prod.fst

end Balanced.Configuration.BlockPartitions

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Construction_ConfigurationHypergraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Configuration

open BlockPartitions

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable (C : Configuration F)

noncomputable def directionEquiv : Direction F ≃ Fin (Fintype.card F + 1) :=
  Fintype.equivFinOfCardEq (by simp [Direction])

noncomputable def blockLabelEquiv (hV : C.Valid) (hC : C.Compatible)
    (hq : 4 ≤ Fintype.card F) (d : Direction F) :
    {b // b ∈ C.labelsInDirection d} ≃ Fin (Fintype.card F + 1) :=
  Fintype.equivFinOfCardEq (by
    rw [Fintype.card_coe]
    exact C.labelsInDirection_card hV hC hq d)

noncomputable def constructedHypergraph (hV : C.Valid) (hC : C.Compatible)
    (hq : 4 ≤ Fintype.card F) :
    PartiteHypergraph (Fintype.card F + 1) (Fintype.card F + 1) :=
  partitionHypergraph (directionEquiv (F := F)) (C.blockLabelEquiv hV hC hq)
    (pointLabel hV hC)

end Balanced.Configuration

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Construction_ConfigurationRealizationBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Configuration

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable (C : Configuration F)

noncomputable def blockLabelDirectionEquiv :
    {b : BlockLabel F // b ∈ C.blockLabels} ≃
      (d : Direction F) × {b // b ∈ C.labelsInDirection d} := by
  classical
  refine {
    toFun := fun b => ⟨blockDirection b.val,
      ⟨b.val, Finset.mem_filter.mpr ⟨b.property, rfl⟩⟩⟩
    invFun := fun db => ⟨db.2.val, (Finset.mem_filter.mp db.2.property).1⟩
    left_inv := ?_
    right_inv := ?_
  }
  · intro b
    rfl
  · rintro ⟨d, b, hb⟩
    have hd : blockDirection b = d := (Finset.mem_filter.mp hb).2
    subst d
    rfl

end Balanced.Configuration

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Construction_LocalCoverObstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Configuration

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable (C : Configuration F)

def labelLocalPiece : BlockLabel F → LocalPiece F
  | Sum.inl l => Sum.inr (Sum.inl l)
  | Sum.inr (Sum.inl d) => Sum.inr (Sum.inr d)
  | Sum.inr (Sum.inr s) => Sum.inl (C.blockPoints (Sum.inr (Sum.inr s)))

end
end Balanced.Configuration

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

def IsDeletionSet (k : ℕ) (D : Finset (Line F)) : Prop :=
  ∀ d : Direction F, (D.filter fun l => l.1 = d).card = k

def DeletionSet (F : Type u) [Field F] [Fintype F] [DecidableEq F] (k : ℕ) :=
  {D : Finset (Line F) // IsDeletionSet k D}

instance instFiniteDeletionSet (k : ℕ) : Finite (DeletionSet F k) := by
  unfold DeletionSet
  infer_instance

noncomputable instance instFintypeDeletionSet (k : ℕ) : Fintype (DeletionSet F k) := Fintype.ofFinite _

def uncoveredBy (D : Finset (Line F)) : Finset (Point F) :=
  Finset.univ.filter fun x => ∀ l ∈ D, ¬ OnLine x l

noncomputable def uniformDeletionMass (k : ℕ) : ℝ :=
  1 / (Fintype.card (DeletionSet F k) : ℝ)

def DeletionDominated (k : ℕ) (K : ℝ) (Q : PMF (DeletionSet F k)) : Prop :=
  ∀ D, (Q D).toReal ≤ Real.exp (K * (Fintype.card F : ℝ)) *
    uniformDeletionMass (F := F) k

noncomputable def deletionEventProbability {k : ℕ} (Q : PMF (DeletionSet F k))
    (E : DeletionSet F k → Prop) : ℝ := by
  classical
  exact ∑ D, if E D then (Q D).toReal else 0

def BadCoreCover (δ : ℝ) (D : Finset (Line F)) : Prop :=
  ∃ C : Finset (Line F), Disjoint C D ∧ C.card ≤ Fintype.card F ∧
    CoversPoints C (uncoveredBy D) ∧
    δ * (Fintype.card F : ℝ) ^ 2 ≤ ((uncoveredBy C).card : ℝ)

end Balanced

end

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

def uncoveredPoints (C : Finset (Line F)) : Finset (Point F) :=
  Finset.univ.filter (fun p => ∀ l ∈ C, ¬ OnLine p l)

def pencilSize (C : Finset (Line F)) (P : ProjectivePoint F) : ℕ :=
  (C.filter (fun l => ThroughProjective l P)).card

def CorePencilEvent (ζ : ℝ) (D : Finset (Line F)) : Prop :=
  ∀ C : Finset (Line F), Disjoint C D → C.card ≤ Fintype.card F →
    CoversPoints C (uncoveredPoints D) →
    ∃ P : ProjectivePoint F,
      (1 - ζ) * (Fintype.card F : ℝ) ≤ (pencilSize C P : ℝ)

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Deletion_ConfigurationDeletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Configuration

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable (C : Configuration F)

theorem choice_line_injective_of_valid_compatible
    (hV : C.Valid) (hC : C.Compatible) :
    Function.Injective (fun s => (C.choice s).line) := by
  intro i j hij
  by_contra hne
  let p := tuplePoint C.merged (C.choice j).tuple 0
  have hp : p ∈ designated C.merged (C.choice j) :=
    Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  have hon : OnLine p (C.choice j).line := (hV.2 j).2.2.2.2.2.1 0
  apply hC.1 i j hne p hp
  simpa only [hij] using hon

theorem splitLines_filter_direction (hV : C.Valid) (d : Direction F) :
    C.splitLines.filter (fun l => l.1 = d) =
      Finset.univ.image (fun b : Bool => (C.choice (d, b)).line) := by
  classical
  ext l
  constructor
  · intro hl
    obtain ⟨hl, hdir⟩ := Finset.mem_filter.mp hl
    obtain ⟨⟨e, b⟩, _, he⟩ := Finset.mem_image.mp hl
    have hed : e = d := by
      calc
        e = (C.choice (e, b)).line.1 := (hV.2 (e, b)).1.symm
        _ = l.1 := congrArg Prod.fst he
        _ = d := hdir
    subst e
    exact Finset.mem_image.mpr ⟨b, Finset.mem_univ _, he⟩
  · intro hl
    obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hl
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨(d, b), Finset.mem_univ _, hb⟩
    · exact hb ▸ (hV.2 (d, b)).1

theorem card_splitLines_filter_direction (hV : C.Valid) (hC : C.Compatible)
    (d : Direction F) :
    (C.splitLines.filter (fun l => l.1 = d)).card = 2 := by
  rw [C.splitLines_filter_direction hV d]
  have hinj : Function.Injective (fun b : Bool => (C.choice (d, b)).line) := by
    intro a b hab
    exact congrArg Prod.snd (C.choice_line_injective_of_valid_compatible hV hC hab)
  rw [Finset.card_image_of_injective _ hinj]
  simp

theorem splitLines_disjoint_constituents (hV : C.Valid) :
    Disjoint C.splitLines (constituentLines C.merged) := by
  classical
  apply Finset.disjoint_left.mpr
  intro l hl hm
  obtain ⟨s, _, hs⟩ := Finset.mem_image.mp hl
  exact (hV.2 s).2.1 (hs ▸ hm)

omit [Field F] in

theorem deletedLines_filter_direction (d : Direction F) :
    C.deletedLines.filter (fun l => l.1 = d) =
      (C.splitLines.filter (fun l => l.1 = d)) ∪ {constituent C.merged d true} := by
  classical
  rw [deletedLines, Finset.filter_union]
  congr 1
  ext l
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  constructor
  · rintro ⟨⟨e, he⟩, hdir⟩
    have hed : e = d := by
      calc
        e = l.1 := congrArg Prod.fst he
        _ = d := hdir
    exact hed ▸ he.symm
  · intro hl
    exact ⟨⟨d, hl.symm⟩, hl ▸ rfl⟩

theorem deletedLines_isDeletionSet (hV : C.Valid) (hC : C.Compatible) :
    IsDeletionSet 3 C.deletedLines := by
  classical
  intro d
  rw [C.deletedLines_filter_direction d]
  have hdis : Disjoint (C.splitLines.filter (fun l => l.1 = d))
      {constituent C.merged d true} := by
    apply Finset.disjoint_left.mpr
    intro l hl hm
    have hc : l ∈ constituentLines C.merged := by
      have he : l = constituent C.merged d true := Finset.mem_singleton.mp hm
      exact he ▸ Finset.mem_image.mpr ⟨(d, true), Finset.mem_univ _, rfl⟩
    exact Finset.disjoint_left.mp (C.splitLines_disjoint_constituents hV)
      (Finset.mem_filter.mp hl).1 hc
  rw [Finset.card_union_of_disjoint hdis, C.card_splitLines_filter_direction hV hC]
  simp

end Balanced.Configuration

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

def assemble (D : I → Finset A) : Finset (I × A) :=
  univ.filter (fun l => l.2 ∈ D l.1)

def fiber (S : Finset (I × A)) (i : I) : Finset A :=
  univ.filter (fun a => (i, a) ∈ S)

omit [DecidableEq I] in
@[simp] theorem mem_assemble (D : I → Finset A) (l : I × A) :
    l ∈ assemble D ↔ l.2 ∈ D l.1 := by simp [assemble]

omit [Fintype I] in
@[simp] theorem mem_fiber (S : Finset (I × A)) (i : I) (a : A) :
    a ∈ fiber S i ↔ (i, a) ∈ S := by simp [fiber]

@[simp] theorem fiber_assemble (D : I → Finset A) : fiber (assemble D) = D := by
  funext i
  ext a
  simp

end Balanced.DeletionCoordinates

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_InjectionExposureLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace Balanced.InjectionExposureLaw

noncomputable section

variable {ι α : Type*} [Fintype ι] [Fintype α]
  [DecidableEq ι] [DecidableEq α]

def history (S : Finset ι) (h : ι ↪ α) : Finset (ι ↪ α) :=
  Finset.univ.filter fun f => ∀ j ∈ S, f j = h j

@[simp] theorem mem_history (S : Finset ι) (h f : ι ↪ α) :
    f ∈ history S h ↔ ∀ j ∈ S, f j = h j := by simp [history]

@[simp] theorem self_mem_history (S : Finset ι) (h : ι ↪ α) :
    h ∈ history S h := by simp

def permutationHistory (S : Finset α) (h : Equiv.Perm α) :
    Finset (Equiv.Perm α) :=
  Finset.univ.filter fun σ => ∀ j ∈ S, σ j = h j

end
end Balanced.InjectionExposureLaw

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_ElementaryIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
noncomputable section

open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def affineIntersectionCount (U : Finset (Point F)) (l : Line F) : ℕ :=
  (U.filter (fun p => OnLine p l)).card

def affineDirectionalVariance (U : Finset (Point F)) (d : Direction F) : ℝ :=
  (1 / (Fintype.card F : ℝ)) *
    ∑ b : F, ((affineIntersectionCount U (d, b) : ℝ) -
      (U.card : ℝ) / (Fintype.card F : ℝ)) ^ 2

def AffineSecondMoment (F : Type*) [Field F] [Fintype F] [DecidableEq F] : Prop :=
  ∀ U : Finset (Point F),
    let q : ℝ := Fintype.card F
    let N : ℝ := U.card
    (∑ l : Line F, (affineIntersectionCount U l : ℝ)) = (q + 1) * N ∧
    (∑ l : Line F, (affineIntersectionCount U l : ℝ) ^ 2) = N ^ 2 + q * N ∧
    (∑ l : Line F, ((affineIntersectionCount U l : ℝ) - N / q) ^ 2) =
      q * N - N ^ 2 / q ∧
    (∑ l : Line F, ((affineIntersectionCount U l : ℝ) - N / q) ^ 2) ≤ q ^ 3 / 4 ∧
    (∑ d : Direction F, affineDirectionalVariance U d) = N - N ^ 2 / q ^ 2 ∧
    (∑ d : Direction F, affineDirectionalVariance U d) ≤ N ∧
    N ≤ q ^ 2

end
end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_CountingExposureKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
namespace Balanced.CountingExposureKernel
noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

def uniformSetWeight (s : Finset α) (a : α) : ℝ :=
  if a ∈ s then (s.card : ℝ)⁻¹ else 0

variable {F : Type*} [Fintype F] [DecidableEq F]

def available (used : Finset F) : Finset F := Finset.univ \ used

@[simp] theorem card_available (used : Finset F) :
    (available used).card = Fintype.card F - used.card := by
  simp only [available, Finset.card_sdiff_of_subset (Finset.subset_univ used),
    Finset.card_univ]

def tokenWeight (r : Direction F → ℕ) (used : Direction F → Finset F)
    (l : Line F) : ℝ :=
  (r l.1 : ℝ) / (∑ d, (r d : ℝ)) * uniformSetWeight (available (used l.1)) l.2

variable [Field F]

def markedLines (U : Finset (Point F)) (ε : ℝ) : Finset (Line F) :=
  Finset.univ.filter fun l => ε <
    |(affineIntersectionCount U l : ℝ) / Fintype.card F -
      (U.card : ℝ) / (Fintype.card F : ℝ) ^ 2|

end
end Balanced.CountingExposureKernel

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_CountingExposurePosterior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace Balanced.CountingExposurePosterior

noncomputable section
attribute [local instance] Classical.propDecidable
open InjectionExposureLaw

variable {G ι α : Type*} [Fintype G] [Fintype ι] [Fintype α]
  [DecidableEq G] [DecidableEq ι] [DecidableEq α]

def exposedIndices (S : Finset (G × ι)) (d : G) : Finset ι :=
  Finset.univ.filter fun j => (d, j) ∈ S

abbrev OffsetHistory (S : Finset (G × ι)) (h : G → ι ↪ α) :=
  ∀ d, {f : ι ↪ α // f ∈ history (exposedIndices S d) (h d)}

abbrev Experiment := Equiv.Perm (G × ι) × (G → ι ↪ α)

def countingHistory (P : Finset (G × ι)) (π : Equiv.Perm (G × ι))
    (h : G → ι ↪ α) : Finset (Experiment (G := G) (ι := ι) (α := α)) :=
  Finset.univ.filter fun ω =>
    ω.1 ∈ permutationHistory P π ∧
    ∀ d, ω.2 d ∈ history (exposedIndices (P.map π.toEmbedding) d) (h d)

def historyEquiv (P : Finset (G × ι)) (π : Equiv.Perm (G × ι))
    (h : G → ι ↪ α) :
    ↥(countingHistory P π h) ≃
      ↥(permutationHistory P π) × OffsetHistory (P.map π.toEmbedding) h where
  toFun ω := ⟨⟨ω.val.1, (Finset.mem_filter.mp ω.property).2.1⟩,
    fun d => ⟨ω.val.2 d, (Finset.mem_filter.mp ω.property).2.2 d⟩⟩
  invFun x := ⟨(x.1.val, fun d => (x.2 d).val),
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.1.property, fun d => (x.2 d).property⟩⟩
  left_inv ω := by apply Subtype.ext; rfl
  right_inv x := by
    apply Prod.ext
    · apply Subtype.ext; rfl
    · funext d; apply Subtype.ext; rfl

def nextLine (ω : Experiment (G := G) (ι := ι) (α := α)) (i : G × ι) : G × α :=
  ((ω.1 i).1, ω.2 (ω.1 i).1 (ω.1 i).2)

def remainingTokens (S : Finset (G × ι)) (d : G) : ℕ :=
  (Finset.univ.filter fun j : ι => (d, j) ∉ S).card

def usedOffsets (S : Finset (G × ι)) (h : G → ι ↪ α) (d : G) : Finset α :=
  (exposedIndices S d).map (h d)

end
end Balanced.CountingExposurePosterior

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Deletion_UniformDeletionEnumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace Balanced.UniformDeletionEnumeration

noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {k : ℕ}

def lineEmbedding (f : Direction F → Fin k ↪ F) : (Direction F × Fin k) ↪ Line F where
  toFun t := (t.1, f t.1 t.2)
  inj' := by
    rintro ⟨d, i⟩ ⟨e, j⟩ he
    have hde : d = e := congrArg Prod.fst he
    subst e
    have hij : i = j := (f d).injective (congrArg Prod.snd he)
    subst j
    rfl

def selectedLines (f : Direction F → Fin k ↪ F) : Finset (Line F) :=
  Finset.univ.map (lineEmbedding f)

omit [Field F] [DecidableEq F] in
@[simp] theorem mem_selectedLines (f : Direction F → Fin k ↪ F) (l : Line F) :
    l ∈ selectedLines f ↔ ∃ j, f l.1 j = l.2 := by
  simp only [selectedLines, Finset.mem_map, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨d, j⟩, hj⟩
    have hd : d = l.1 := congrArg Prod.fst hj
    subst d
    exact ⟨j, congrArg Prod.snd hj⟩
  · rintro ⟨j, hj⟩
    refine ⟨(l.1, j), ?_⟩
    change (l.1, f l.1 j) = l
    exact Prod.ext rfl hj

omit [Field F] [DecidableEq F] in

theorem card_tokens : Fintype.card (Direction F × Fin k) = k * (Fintype.card F + 1) := by
  simp [Direction, Nat.mul_comm]

def timeToToken : Fin (k * (Fintype.card F + 1)) ≃ (Direction F × Fin k) :=
  (Fintype.equivFinOfCardEq card_tokens).symm

end
end Balanced.UniformDeletionEnumeration

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_AffinePairEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.PairEvaluation

variable {F : Type*} [Field F]

theorem eval_intersection (d e : Direction F) (hde : d ≠ e) (a b : F) :
    (lineEval d (lineIntersection (d, a) (e, b)),
      lineEval e (lineIntersection (d, a) (e, b))) = (a, b) := by
  cases d with
  | none =>
      cases e with
      | none => exact False.elim (hde rfl)
      | some m =>
          apply Prod.ext <;> simp [lineEval, lineIntersection]
  | some m =>
      cases e with
      | none =>
          apply Prod.ext <;> simp [lineEval, lineIntersection]
      | some n =>
          have hmn : m - n ≠ 0 := sub_ne_zero.mpr (fun h => hde (congrArg some h))
          apply Prod.ext
          · simp [lineEval, lineIntersection]
          · simp only [lineEval, lineIntersection]
            field_simp
            ring

theorem intersection_eval (d e : Direction F) (hde : d ≠ e) (p : Point F) :
    lineIntersection (d, lineEval d p) (e, lineEval e p) = p := by
  rcases p with ⟨x, y⟩
  cases d with
  | none =>
      cases e with
      | none => exact False.elim (hde rfl)
      | some m =>
          apply Prod.ext <;> simp [lineEval, lineIntersection]
  | some m =>
      cases e with
      | none =>
          apply Prod.ext <;> simp [lineEval, lineIntersection]
      | some n =>
          have hmn : m - n ≠ 0 := sub_ne_zero.mpr (fun h => hde (congrArg some h))
          have hx : ((y - n * x) - (y - m * x)) / (m - n) = x := by
            apply (div_eq_iff hmn).mpr
            ring
          apply Prod.ext
          · exact hx
          · simp only [lineEval, lineIntersection]
            rw [hx]
            ring

def lineCoordinateEquiv (d e : Direction F) (hde : d ≠ e) (a : F) :
    {p : Point F // OnLine p (d, a)} ≃ F where
  toFun p := lineEval e p.1
  invFun b := ⟨lineIntersection (d, a) (e, b),
    congrArg Prod.fst (eval_intersection d e hde a b)⟩
  left_inv p := by
    apply Subtype.ext
    have hp : lineEval d p.1 = a := p.2
    simpa [hp] using intersection_eval d e hde p.1
  right_inv b := congrArg Prod.snd (eval_intersection d e hde a b)

@[simp] theorem lineCoordinateEquiv_apply (d e : Direction F) (hde : d ≠ e)
    (a : F) (p : {p : Point F // OnLine p (d, a)}) :
    lineCoordinateEquiv d e hde a p = lineEval e p.1 := rfl

end Balanced.PairEvaluation

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

def lineMultiplicity (C : Finset (Line F)) (x : Point F) : ℕ :=
  (C.filter (fun l => OnLine x l)).card

universe u

end Balanced

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_AffineProfileExposure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.AffineProfileExposure

universe u

noncomputable section
open scoped Classical
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def targetExposureMean (D C : Finset (Line F)) (l : Line F) (d c : ℕ) : ℝ :=
  (∑ S ∈ ((D.erase l).powersetCard (d - 1)) ×ˢ (C.powersetCard c),
    (((linePoints l).filter (fun p =>
      (∀ m ∈ D.erase l \ S.1, ¬ OnLine p m) ∧
      (∀ m ∈ C \ S.2, ¬ OnLine p m))).card : ℝ) /
        ((((D.erase l).powersetCard (d - 1)) ×ˢ (C.powersetCard c)).card : ℝ)) /
    (Fintype.card F : ℝ)

def targetPowerMean (D C : Finset (Line F)) (l : Line F) (d c : ℕ) : ℝ :=
  (∑ p ∈ linePoints l,
    ((d : ℝ) / D.card) ^ (lineMultiplicity D p - 1) *
      ((c : ℝ) / C.card) ^ lineMultiplicity C p) / (Fintype.card F : ℝ)

end
end Balanced.AffineProfileExposure

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_AffinePermutationExposure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.AffinePermutationExposure

universe u

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def targetOrderMean (D C : Finset (Line F))
    (I : Finset D) (J : Finset C) (i l : D) : ℝ :=
  (𝔼 σ ∈ Finset.univ.filter (fun σ : Equiv.Perm D => σ i = l),
    𝔼 τ : Equiv.Perm C,
      (((linePoints l.1).filter (fun p =>
        (∀ m ∈ (Finset.univ.erase l) \ I.map σ.toEmbedding, ¬ OnLine p m.1) ∧
        (∀ m ∈ Finset.univ \ J.map τ.toEmbedding, ¬ OnLine p m.1))).card : ℝ)) /
    (Fintype.card F : ℝ)

end
end Balanced.AffinePermutationExposure

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_AffinePlaneOrderExposure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.AffinePlaneOrderExposure

universe u
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
open AffinePermutationExposure

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def planeOrderMean (D C : Finset (Line F))
    (I : Finset D) (J : Finset C) (i l : D) : ℝ :=
  (𝔼 σ ∈ Finset.univ.filter (fun σ : Equiv.Perm D => σ i = l),
    𝔼 τ : Equiv.Perm C,
      (((Finset.univ : Finset (Point F)).filter (fun p =>
        (∀ m ∈ (Finset.univ.erase l) \ I.map σ.toEmbedding, ¬ OnLine p m.1) ∧
        (∀ m ∈ Finset.univ \ J.map τ.toEmbedding, ¬ OnLine p m.1))).card : ℝ)) /
    (Fintype.card F : ℝ) ^ 2

def planePowerMean (D C : Finset (Line F)) (d c : ℕ) : ℝ :=
  (∑ p : Point F, ((d : ℝ) / D.card) ^ lineMultiplicity D p *
    ((c : ℝ) / C.card) ^ lineMultiplicity C p) / (Fintype.card F : ℝ) ^ 2

def erasedPlanePowerMean (D C : Finset (Line F)) (l : Line F) (d c : ℕ) : ℝ :=
  (∑ p : Point F, ((d : ℝ) / D.card) ^ lineMultiplicity (D.erase l) p *
    ((c : ℝ) / C.card) ^ lineMultiplicity C p) / (Fintype.card F : ℝ) ^ 2

end
end Balanced.AffinePlaneOrderExposure

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_CorePencil
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

universe u

def CorePencilResult : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ K : ℝ, 0 ≤ K → ∀ ζ : ℝ, 0 < ζ →
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
        Nat.Prime (Fintype.card F) →
        N ≤ Fintype.card F → k ≤ Fintype.card F →
        ∀ Q : PMF (DeletionSet F k), DeletionDominated k K Q →
          deletionEventProbability Q (fun D => ¬ CorePencilEvent ζ D.val) < ε

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_SinglePencilObstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced
namespace Configuration

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def NonsplitThrough (C : Configuration F) (p : Point F) : BlockLabel F → Prop
  | Sum.inl l => OnLine p l
  | Sum.inr (Sum.inl d) => ∃ s : Bool, OnLine p (constituent C.merged d s)
  | Sum.inr (Sum.inr _) => False

end Configuration
end Balanced

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

def SmallReuseOrder {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (A : ι → Finset α) : List ι → Prop
  | [] => True
  | i :: l => SmallReuseOrder A l ∧ (A i ∩ l.toFinset.biUnion A).card ≤ 1

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_AlignedListProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.AlignedListProbability

open TupleAlignment PartialAlignment ConditionalRestriction
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem partial_alignment_probability_eq (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (hg : ∀ i, d i ≠ g) (c : F)
    (J : Finset (Fin 4)) (hJ : J.card ≤ 1) (a : Fin 4 → Bool → F) :
    ((PMF.uniformOfFintype (PartialOffsets J a)).toOuterMeasure
      {o | ∀ i, OnLine (tuplePositionEquiv d hd σ o.1 i) (g,c)}).toReal =
      (Fintype.card F : ℝ)⁻¹ ^ 4 := by
  rcases J.eq_empty_or_nonempty with rfl | ⟨j, hj⟩
  · let e : PartialOffsets ∅ a ≃ (Fin 4 → Bool → F) :=
      Equiv.subtypeUnivEquiv (by simp)
    have h := congrArg (fun law => (law.toOuterMeasure
      {o | ∀ i, OnLine (tuplePositionEquiv d hd σ o i) (g,c)}).toReal)
      (uniform_map_equiv e)
    rw [PMF.toOuterMeasure_map_apply] at h
    exact h.trans (alignedOffsets_outer_probability d hd σ g c)
  · have heq : J = {j} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      exact ⟨hj, fun k hk => Finset.card_le_one.mp hJ k hk j hj⟩
    subst J
    let e : PartialOffsets {j} a ≃ ChildOffsetsAt j (a j) :=
      Equiv.subtypeEquivRight (by intro o; simp)
    have h := congrArg (fun law => (law.toOuterMeasure
      {o : ChildOffsetsAt j (a j) |
        ∀ i, OnLine (tuplePositionEquiv d hd σ o.1 i) (g,c)}).toReal)
      (uniform_map_equiv e)
    rw [PMF.toOuterMeasure_map_apply] at h
    exact h.trans (alignedChildOffsetsAt_pmf_probability d hd σ g j (hg j) c (a j))

theorem global_conditional_alignment_probability_eq (T : FourTuple F)
    (hT : Function.Injective T.generator) (g : Direction F)
    (hg : ∀ i, T.generator i ≠ g) (c : F)
    (D : Finset (Direction F)) (hD : (exposedTupleIndices T D).card ≤ 1)
    (a : MergedPairs F) :
    (((PMF.uniformOfFintype (MergedPairs F)).filter {M | ∀ d, d ∈ D → M d = a d}
      (fixed_supported (fun d => d ∈ D) a)).toOuterMeasure
      {M | ∀ i, OnLine (tuplePoint M T i) (g,c)}).toReal =
      (Fintype.card F : ℝ)⁻¹ ^ 4 := by
  let hd := adjacent_ne_of_injective T hT
  let E : Set (Fin 4 → Bool → F) :=
    {o | ∀ i, OnLine (tuplePositionEquiv T.generator hd T.side o i) (g,c)}
  have h := congrArg (fun law => (law.toOuterMeasure E).toReal)
    (global_exposed_tuple_law T hT D a)
  rw [PMF.toOuterMeasure_map_apply] at h
  calc
    _ = (((PMF.uniformOfFintype (Fin 4 → Bool → F)).filter
        {o | ∀ i ∈ exposedTupleIndices T D, o i = a (T.generator i)}
        (partialOffsets_supported (exposedTupleIndices T D)
          (fun i => a (T.generator i)))).toOuterMeasure E).toReal := h
    _ = _ := by
      rw [partialOffsets_conditional_law, PMF.toOuterMeasure_map_apply]
      exact partial_alignment_probability_eq T.generator hd T.side g hg c
        (exposedTupleIndices T D) hD (fun i => a (T.generator i))

omit [Field F] [Fintype F] in

theorem card_exposedTupleIndices (T : FourTuple F)
    (hT : Function.Injective T.generator) (D : Finset (Direction F)) :
    (exposedTupleIndices T D).card = (generatorSet T ∩ D).card := by
  have heq : (exposedTupleIndices T D).image T.generator = generatorSet T ∩ D := by
    ext d
    simp only [exposedTupleIndices, generatorSet, Finset.mem_image,
      Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, rfl⟩, hi⟩
    · rintro ⟨⟨i, rfl⟩, hi⟩
      exact ⟨i, hi, rfl⟩
  rw [← heq, Finset.card_image_of_injective _ hT]

omit [Fintype F] in

theorem tuplePoint_eq_of_agree (T : FourTuple F) (M N : MergedPairs F)
    (h : ∀ d ∈ generatorSet T, M d = N d) (j : Fin 4) :
    tuplePoint M T j = tuplePoint N T j := by
  have hj : T.generator j ∈ generatorSet T := by simp [generatorSet]
  have hn : T.generator (j+1) ∈ generatorSet T := by simp [generatorSet]
  simp only [tuplePoint, constituent, h _ hj, h _ hn]

def ListAligned {ι : Type*} (T : ι → FourTuple F) (L : ι → Line F)
    (l : List ι) (M : MergedPairs F) : Prop :=
  ∀ i ∈ l, ∀ j, OnLine (tuplePoint M (T i) j) (L i)

omit [Fintype F] in
theorem listAligned_agree {ι : Type*} [DecidableEq ι]
    (T : ι → FourTuple F) (L : ι → Line F) (l : List ι)
    (M N : MergedPairs F)
    (h : ∀ d ∈ l.toFinset.biUnion (fun i => generatorSet (T i)), M d = N d) :
    ListAligned T L l M ↔ ListAligned T L l N := by
  have hp (i : ι) (hi : i ∈ l) (j : Fin 4) :
      tuplePoint M (T i) j = tuplePoint N (T i) j := by
    apply tuplePoint_eq_of_agree
    intro d hd
    exact h d (Finset.mem_biUnion.mpr ⟨i, List.mem_toFinset.mpr hi, hd⟩)
  constructor <;> intro ha i hi j
  · rw [← hp i hi j]
    exact ha i hi j
  · rw [hp i hi j]
    exact ha i hi j

theorem fixed_alignment_probability_eq (T : FourTuple F)
    (hT : Function.Injective T.generator) (g : Direction F)
    (hg : ∀ i, T.generator i ≠ g) (c : F)
    (D : Finset (Direction F)) (hD : (exposedTupleIndices T D).card ≤ 1)
    (a : MergedPairs F) :
    ((PMF.uniformOfFintype (FixedArray (fun d => d ∈ D) a)).toOuterMeasure
      {M | ∀ j, OnLine (tuplePoint M.1 T j) (g,c)}).toReal =
        (Fintype.card F : ℝ)⁻¹ ^ 4 := by
  have h := global_conditional_alignment_probability_eq T hT g hg c D hD a
  rw [uniform_fixed_filter, PMF.toOuterMeasure_map_apply] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  exact FiniteUniformFibers.probability_fintype_congr _ _ rfl

theorem alignment_inter_probability_eq (T : FourTuple F)
    (hT : Function.Injective T.generator) (g : Direction F)
    (hg : ∀ i, T.generator i ≠ g) (c : F)
    (D : Finset (Direction F)) (hD : (exposedTupleIndices T D).card ≤ 1)
    (E : MergedPairs F → Prop)
    (hE : ∀ M N, (∀ d ∈ D, M d = N d) → (E M ↔ E N)) :
    ((PMF.uniformOfFintype (MergedPairs F)).toOuterMeasure
      {M | E M ∧ ∀ j, OnLine (tuplePoint M T j) (g,c)}).toReal =
      (Fintype.card F : ℝ)⁻¹ ^ 4 *
        ((PMF.uniformOfFintype (MergedPairs F)).toOuterMeasure {M | E M}).toReal := by
  apply FiniteUniformFibers.fixed_probability_inter D E _ _ hE
  intro a
  convert fixed_alignment_probability_eq T hT g hg c D hD a using 1
  all_goals try with_reducible_and_instances rfl
  exact FiniteUniformFibers.probability_fintype_congr _ _ rfl

theorem list_alignment_probability {ι : Type*} [DecidableEq ι]
    (T : ι → FourTuple F) (L : ι → Line F) (l : List ι)
    (hT : ∀ i ∈ l, Function.Injective (T i).generator)
    (hg : ∀ i ∈ l, ∀ j, (T i).generator j ≠ (L i).1)
    (horder : SmallReuseOrder (fun i => generatorSet (T i)) l) :
    ((PMF.uniformOfFintype (MergedPairs F)).toOuterMeasure
      {M | ListAligned T L l M}).toReal =
      ((Fintype.card F : ℝ)⁻¹ ^ 4) ^ l.length := by
  induction l with
  | nil =>
      simp [ListAligned]
  | cons i l ih =>
      have hTi := hT i (by simp)
      have hgi := hg i (by simp)
      have htailT : ∀ j ∈ l, Function.Injective (T j).generator :=
        fun j hj => hT j (by simp [hj])
      have htailg : ∀ j ∈ l, ∀ k, (T j).generator k ≠ (L j).1 :=
        fun j hj => hg j (by simp [hj])
      have hD : (exposedTupleIndices (T i)
          (l.toFinset.biUnion (fun j => generatorSet (T j)))).card ≤ 1 := by
        rw [card_exposedTupleIndices (T i) hTi]
        exact horder.2
      have hevent : {M | ListAligned T L (i :: l) M} =
          {M | ListAligned T L l M ∧ ∀ j, OnLine (tuplePoint M (T i) j) (L i)} := by
        ext M
        simp only [ListAligned, List.mem_cons, forall_eq_or_imp, Set.mem_ofPred_eq]
        exact and_comm
      rw [hevent]
      have hstep := alignment_inter_probability_eq (T i) hTi (L i).1 hgi (L i).2
        (l.toFinset.biUnion (fun j => generatorSet (T j))) hD (ListAligned T L l)
        (listAligned_agree T L l)
      simpa only [Prod.eta, ih htailT htailg horder.1, List.length_cons,
        pow_succ, mul_comm] using hstep

end
end Balanced.AlignedListProbability

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_AlignedFreeCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.AlignedListProbability

open TupleAlignment PartialAlignment
noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem card_alignedPartialOffsets_eq (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (hg : ∀ i, d i ≠ g) (c : F)
    (J : Finset (Fin 4)) (hJ : J.card ≤ 1) (a : Fin 4 → Bool → F) :
    Fintype.card (AlignedPartialOffsets d hd σ g c J a) =
      Fintype.card F ^ (freePositions J).card := by
  have hp := partial_alignment_probability_eq d hd σ g hg c J hJ a
  rw [PMF.toOuterMeasure_uniformOfFintype_apply, ENNReal.toReal_div] at hp
  simp only [ENNReal.toReal_natCast] at hp
  change (Fintype.card (AlignedPartialOffsets d hd σ g c J a) : ℝ) /
    Fintype.card (PartialOffsets J a) = (Fintype.card F : ℝ)⁻¹ ^ 4 at hp
  rw [card_partialOffsets, Nat.cast_pow] at hp
  have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hc := (div_eq_iff (pow_ne_zero _ hq)).mp hp
  have hcycle : (freePositions J).card + 4 = 2 * (freshGenerators J).card := by
    have h : ∀ K : Finset (Fin 4), K.card ≤ 1 →
        (freePositions K).card + 4 = 2 * (freshGenerators K).card := by decide
    exact h J hJ
  have hr : (Fintype.card (AlignedPartialOffsets d hd σ g c J a) : ℝ) =
      (Fintype.card F : ℝ) ^ (freePositions J).card := by
    rw [hc, ← hcycle, pow_add]
    calc
      _ = (Fintype.card F : ℝ) ^ (freePositions J).card *
          ((Fintype.card F : ℝ)⁻¹ ^ 4 * (Fintype.card F : ℝ) ^ 4) := by ring
      _ = _ := by rw [← mul_pow, inv_mul_cancel₀ hq, one_pow, mul_one]
  exact_mod_cast hr

def alignedFreeCoordinatesEquiv (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (hg : ∀ i, d i ≠ g) (c : F)
    (J : Finset (Fin 4)) (hJ : J.card ≤ 1) (a : Fin 4 → Bool → F) :
    AlignedPartialOffsets d hd σ g c J a ≃ ({i : Fin 4 // i ∈ freePositions J} → F) :=
  Equiv.ofBijective (alignedFreeCoordinates d hd σ g c J a)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨alignedFreeCoordinates_injective d hd σ g hg c J a, by
        rw [card_alignedPartialOffsets_eq d hd σ g hg c J hJ a]
        simp⟩)

end
end Balanced.AlignedListProbability

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_AlignedPointExposure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.AlignedListProbability

open TupleAlignment PartialAlignment
noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def generatedOffsets (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (hg : ∀ i, d i ≠ g) (c : F)
    (J : Finset (Fin 4)) (hJ : J.card ≤ 1) (a : Fin 4 → Bool → F)
    (x : {i : Fin 4 // i ∈ freePositions J} → F) : Fin 4 → Bool → F :=
  ((alignedFreeCoordinatesEquiv d hd σ g hg c J hJ a).symm x).1.1

def generatedPositions (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (hg : ∀ i, d i ≠ g) (c : F)
    (J : Finset (Fin 4)) (hJ : J.card ≤ 1) (a : Fin 4 → Bool → F)
    (x : {i : Fin 4 // i ∈ freePositions J} → F) : Fin 4 → Point F :=
  tuplePositionEquiv d hd σ (generatedOffsets d hd σ g hg c J hJ a x)

end
end Balanced.AlignedListProbability

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_ConditionalOrderVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace Balanced.ConditionalOrderVariance

section Affine

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def populationLines (U : Finset (Line F)) (S : Finset U) : Finset (Line F) :=
  S.map ⟨Subtype.val, Subtype.val_injective⟩

omit [Field F] [Fintype F] in
@[simp] theorem populationLines_insert (U : Finset (Line F)) (S : Finset U) (a : U) :
    populationLines U (insert a S) = insert a.val (populationLines U S) := by
  simp [populationLines]

omit [Field F] [Fintype F] in
@[simp] theorem populationLines_erase (U : Finset (Line F)) (S : Finset U) (a : U) :
    populationLines U (S.erase a) = (populationLines U S).erase a.val := by
  simp [populationLines, Finset.map_erase]

abbrev OrderPair (U V : Finset (Line F)) := Equiv.Perm U × Equiv.Perm V

noncomputable def conditionedOrderLaw (U V : Finset (Line F)) (i x : U) :
    PMF (OrderPair U V) :=
  PMF.uniformOfFinset
    ((Finset.univ.filter (fun σ : Equiv.Perm U => σ i = x)) ×ˢ
      (Finset.univ : Finset (Equiv.Perm V)))
    ⟨(Equiv.swap i x, Equiv.refl V), by simp⟩

end Affine

end Balanced.ConditionalOrderVariance

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

def witnesses (F : Type*) [Field F] [Fintype F] [DecidableEq F] (m : ℕ) :
    Finset (Finset (Line F)) := (Finset.univ : Finset (Line F)).powersetCard m

@[simp] theorem mem_witnesses (m : ℕ) (C : Finset (Line F)) :
    C ∈ witnesses F m ↔ C.card = m := by
  simp [witnesses]

@[simp] theorem card_witnesses (m : ℕ) :
    (witnesses F m).card =
      (Fintype.card F * (Fintype.card F + 1)).choose m := by
  simp [witnesses, Line, Direction, Nat.mul_comm]

end
end Balanced.ProfileWitnessPayment

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_CountingJointLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CountingJointLaw

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
open UniformDeletionEnumeration CountingExposurePosterior

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {k m : ℕ}

def deletionArray (ω : Experiment (G := Direction F) (ι := Fin k) (α := F)) :
    Fin (k * (Fintype.card F + 1)) → Line F :=
  fun i => nextLine ω (timeToToken i)

def coverArray (e : Fin m ↪ Line F) (σ : Equiv.Perm (Line F)) : Fin m → Line F :=
  fun i => σ (e i)

def fixedPairMean
    (g : (Fin (k * (Fintype.card F + 1)) → Line F) → (Fin m → Line F) → ℝ)
    (D : DeletionSet F k) (C : Finset (Line F)) : ℝ :=
  𝔼 d : Fin (k * (Fintype.card F + 1)) ≃ D.val,
    𝔼 c : Fin m ≃ C, g (fun i => (d i).val) (fun i => (c i).val)

end
end Balanced.CountingJointLaw

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_CoverCountingExposure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CoverCountingExposure

noncomputable section
open Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def Marked (U : Finset (Point F)) (ε : ℝ) (l : Line F) : Prop :=
  ε < |(affineIntersectionCount U l : ℝ) / (Fintype.card F : ℝ) -
    (U.card : ℝ) / (Fintype.card F : ℝ) ^ 2|

def pastUncovered (D : Finset (Line F)) (I : Finset (Line F))
    (σ : Equiv.Perm (Line F)) : Finset (Point F) :=
  uncoveredBy (D ∪ I.map σ.toEmbedding)

end
end Balanced.CoverCountingExposure

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_CylinderConditioning
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
open MeasureTheory

namespace Balanced
open scoped _root_.Balanced
namespace CylinderConditioning

variable {ι Ω : Type*} [DecidableEq ι]

def avoid (B : ι → Set Ω) (S : Finset ι) : Set Ω :=
  {ω | ∀ i ∈ S, ω ∉ B i}

omit [DecidableEq ι] in
@[simp] theorem mem_avoid (B : ι → Set Ω) (S : Finset ι) (ω : Ω) :
    ω ∈ avoid B S ↔ ∀ i ∈ S, ω ∉ B i := Iff.rfl

omit [DecidableEq ι] in
@[simp] theorem avoid_empty (B : ι → Set Ω) : avoid B ∅ = Set.univ := by
  ext ω
  simp [avoid]

@[simp] theorem avoid_insert (B : ι → Set Ω) (S : Finset ι) (i : ι) :
    avoid B (insert i S) = avoid B S \ B i := by
  ext ω
  simp [avoid, and_comm]

omit [DecidableEq ι] in
theorem avoid_antitone (B : ι → Set Ω) {S T : Finset ι} (hST : S ⊆ T) :
    avoid B T ⊆ avoid B S := by
  intro ω hω i hi
  exact hω i (hST hi)

theorem product_lower_bound (f : Finset ι → ℝ) (x : ι → ℝ)
    (hx : ∀ i, x i ≤ 1)
    (hstep : ∀ S i, i ∉ S → (1 - x i) * f S ≤ f (insert i S))
    (T U : Finset ι) (hdisj : Disjoint T U) :
    f T * ∏ i ∈ U, (1 - x i) ≤ f (T ∪ U) := by
  induction U using Finset.induction_on with
  | empty => simp
  | @insert i U hi ih =>
      have hiT : i ∉ T := by
        intro hiT
        exact Finset.disjoint_left.mp hdisj hiT (Finset.mem_insert_self _ _)
      have hdisj' : Disjoint T U :=
        Finset.disjoint_of_subset_right (Finset.subset_insert _ _) hdisj
      have hiTU : i ∉ T ∪ U := by simp [hiT, hi]
      calc
        f T * ∏ j ∈ insert i U, (1 - x j) =
            (1 - x i) * (f T * ∏ j ∈ U, (1 - x j)) := by
              rw [Finset.prod_insert hi]
              ring
        _ ≤ (1 - x i) * f (T ∪ U) :=
          mul_le_mul_of_nonneg_left (ih hdisj') (sub_nonneg.mpr (hx i))
        _ ≤ f (insert i (T ∪ U)) := hstep _ _ hiTU
        _ = f (T ∪ insert i U) := by rw [Finset.union_insert]

section Measure

variable [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]

theorem avoidance_step (B : ι → Set Ω) (x : ι → ℝ)
    (hB : ∀ i, MeasurableSet (B i))
    (hbound : ∀ S i, i ∉ S →
      μ.real (avoid B S ∩ B i) ≤ x i * μ.real (avoid B S)) :
    ∀ S i, i ∉ S →
      (1 - x i) * μ.real (avoid B S) ≤ μ.real (avoid B (insert i S)) := by
  intro S i hi
  have hsplit := measureReal_inter_add_sdiff (μ := μ) (s := avoid B S) (hB i)
  have hle := hbound S i hi
  rw [avoid_insert]
  nlinarith

theorem conditional_event_bound (B : ι → Set Ω) (x : ι → ℝ)
    (hB : ∀ i, MeasurableSet (B i))
    (hx : ∀ i, x i < 1)
    (hbound : ∀ S i, i ∉ S →
      μ.real (avoid B S ∩ B i) ≤ x i * μ.real (avoid B S))
    (C : Set Ω) (T U : Finset ι) (hdisj : Disjoint T U)
    (hpositive : 0 < μ.real (avoid B (T ∪ U)))
    (hindep : μ.real (C ∩ avoid B T) = μ.real C * μ.real (avoid B T)) :
    μ.real (C ∩ avoid B (T ∪ U)) / μ.real (avoid B (T ∪ U)) ≤
      μ.real C * ∏ i ∈ U, (1 - x i)⁻¹ := by
  have hprod : 0 < ∏ i ∈ U, (1 - x i) :=
    Finset.prod_pos fun i _ => sub_pos.mpr (hx i)
  have hlower := product_lower_bound (fun S => μ.real (avoid B S)) x
    (fun i => (hx i).le) (avoidance_step μ B x hB hbound) T U hdisj
  have hbase : μ.real (avoid B T) ≤
      μ.real (avoid B (T ∪ U)) / (∏ i ∈ U, (1 - x i)) :=
    (le_div_iff₀ hprod).2 hlower
  have hnum : μ.real (C ∩ avoid B (T ∪ U)) ≤
      μ.real C * μ.real (avoid B T) := by
    rw [← hindep]
    exact measureReal_mono (Set.inter_subset_inter_right C
      (avoid_antitone B Finset.subset_union_left))
  apply (div_le_iff₀ hpositive).2
  calc
    μ.real (C ∩ avoid B (T ∪ U)) ≤ μ.real C * μ.real (avoid B T) := hnum
    _ ≤ μ.real C *
        (μ.real (avoid B (T ∪ U)) / ∏ i ∈ U, (1 - x i)) :=
      mul_le_mul_of_nonneg_left hbase measureReal_nonneg
    _ = (μ.real C * ∏ i ∈ U, (1 - x i)⁻¹) *
        μ.real (avoid B (T ∪ U)) := by
      rw [Finset.prod_inv_distrib]
      ring

end Measure
end CylinderConditioning
end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_ForcedNonsplitLabels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced
namespace Configuration

noncomputable section
attribute [local instance] Classical.propDecidable
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable (C : Configuration F)

def forcedNonsplitLabel (p : Point F) (d : Direction F) : BlockLabel F :=
  if lineThrough d p ∈ constituentLines C.merged then Sum.inr (Sum.inl d)
  else Sum.inl (lineThrough d p)

@[simp] theorem forcedNonsplitLabel_direction (p : Point F) (d : Direction F) :
    blockDirection (C.forcedNonsplitLabel p d) = d := by
  unfold forcedNonsplitLabel
  split <;> rfl

def nonsplitDirections (p : Point F) : Finset (Direction F) :=
  Finset.univ.filter (fun d => lineThrough d p ∉ C.splitLines)

def forcedNonsplitLabels (p : Point F) : Finset (BlockLabel F) :=
  (C.nonsplitDirections p).image (C.forcedNonsplitLabel p)

end
end Configuration
end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_ParallelBlockCapacity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Configuration

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable (C : Configuration F)

def parallelDesignated (g : Direction F) : Finset (Point F) :=
  designated C.merged (C.choice (g, false)) ∪ designated C.merged (C.choice (g, true))

end
end Balanced.Configuration

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_ThinningTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace Balanced.BernoulliTail

noncomputable def thinningCutoff (β : ℝ) (q : ℕ) : ℕ :=
  Nat.floor ((q : ℝ) ^ β) + 1

end Balanced.BernoulliTail

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

abbrev Index := ℕ × ℕ

def weight (i : Index) : ℝ := i.1 + i.2

def profiles (M : ℝ) : Set (Index → ℝ) :=
  {p | (∀ i, 0 ≤ p i) ∧ HasSum p 1 ∧
    ∀ s : Finset Index, ∑ i ∈ s, weight i * p i ≤ M}

end Balanced.ProfileMomentCompactness

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileEmpiricalMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Finset MeasureTheory Filter
open scoped NNReal Topology

namespace Balanced
open scoped _root_.Balanced

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

abbrev BoundedProfile (M : ℝ) := ProfileMomentCompactness.profiles M

end Balanced

end

end OAI
end


