-- Prove2me | Definitions.Def_OAIQ63Br001
-- name    : OAIQ63Br001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T00:05:06.719171+00:00
-- url     : https://prove2.me/theorems/2e4f108f-c8d2-432e-9150-dee78062801a
-- title:
--   Definitions bundle OAIQ63Br001 of the split of OpenAI, Balanced counterexamples to Ryser's conjecture at prime orders (result family 162)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Balanced.main_result`, carved from OpenAI's openai/math development (OpenAI, *Balanced counterexamples to Ryser's conjecture at prime orders (result family 162)*, OpenAI Math Release, September 27, 2026, result family 162, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 477 declarations of OpenAI's Lean: 306 definitions, 7 inductive types or structures, 11 instances and 153 theorems. The definitions and types are `OAI.Balanced.DeletionLaw.uniformDeletionMass`, `OAI.Balanced.DependencyExtraction.coordinateSwap`, `OAI.Balanced.ExposedExternalFresh.externalFreshMeasurableSpace`, `OAI.Balanced.ExposureInterleaving.Before`, `OAI.Balanced.ExposureInterleaving.Step`, `OAI.Balanced.ExposureInterleaving.beforeStrictTotalOrder`, `OAI.Balanced.ExposureInterleaving.countLE`, `OAI.Balanced.ExposureInterleaving.countLT`, `OAI.Balanced.ExposureInterleaving.coverGrid`, `OAI.Balanced.ExposureInterleaving.grid`, `OAI.Balanced.ExposureInterleaving.parameter`, `OAI.Balanced.ExposureInterleaving.previousC`, `OAI.Balanced.ExposureInterleaving.previousD`, `OAI.Balanced.ExposureInterleaving.remainingC`, `OAI.Balanced.ExposureInterleaving.remainingD`, `OAI.Balanced.ExposureInterleaving.typeRank`, `OAI.Balanced.ExternalAssembly.externalModelMeasurableSpace`, `OAI.Balanced.ExternalAssembly.freshGeneratorMeasurableSpace`, `OAI.Balanced.ExternalAssembly.instMeasurableSpace_solutions`, `OAI.Balanced.ExternalAssembly.instMeasurableSpace_solutions_1`, `OAI.Balanced.ExternalAssembly.instMeasurableSpace_solutions_2`, `OAI.Balanced.ExternalWitnessTail.instMeasurableSpace_solutions`, `OAI.Balanced.FiniteAffine.Plane`, `OAI.Balanced.FiniteAffine.Plane.linePoints`, `OAI.Balanced.FiniteFieldPresentation`, `OAI.Balanced.FiniteHistory.Path`, `OAI.Balanced.FiniteHistory.Prefix`, `OAI.Balanced.FiniteHistory.additiveTrack`, `OAI.Balanced.FiniteHistory.filtration`, `OAI.Balanced.FiniteHistory.historyKernel`, `OAI.Balanced.FiniteHistory.pathLaw`, `OAI.Balanced.FiniteHistory.stepObservable`, `OAI.Balanced.FiniteKernelPotential.advance`, `OAI.Balanced.FiniteKernelPotential.weights`, `OAI.Balanced.FinitePushforward.cylinderMass`, `OAI.Balanced.FinitePushforward.mapChoices`, `OAI.Balanced.FinitePushforward.pushWeight`, `OAI.Balanced.FiniteUniformTower.average`, `OAI.Balanced.FiniteUniformTower.fiberMean`, `OAI.Balanced.FourCycle.Consecutive` and 273 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `BalancedRyser_Candidates_ConstituentOffsets`, `BalancedRyser_Candidates_ExposedExternalFresh`, `BalancedRyser_Candidates_ExternalFreshGeneratorBound`, `BalancedRyser_Candidates_ExternalWitnessModel`, `BalancedRyser_Candidates_ExternalWitnessMoments`, `BalancedRyser_Candidates_ExternalWitnessOldBridge`, `BalancedRyser_Candidates_ExternalWitnessTail`, `BalancedRyser_Candidates_OppositeAssembly`, `BalancedRyser_Candidates_OppositeFreshMean`, `BalancedRyser_Candidates_OppositeTail`, `BalancedRyser_Construction_ExternalWitnessPartition`, `BalancedRyser_Construction_PartitionEncoding`, `BalancedRyser_Construction_RootChildPartition`, `BalancedRyser_Deletion_Deletion`, `BalancedRyser_Deletion_DeletionDomination`, `BalancedRyser_Incidence_AlignedGeneratorIncidence`, `BalancedRyser_Incidence_FiniteAffinePlane`, `BalancedRyser_Incidence_ProjectiveNormalization`, `BalancedRyser_Incidence_Stability`, `BalancedRyser_Incidence_StabilityLeadingPart`, `BalancedRyser_Incidence_StabilityPolynomial2`, `BalancedRyser_Incidence_UnusedOffsetIncidence`, `BalancedRyser_Local_AlignedGlobalCardinality`, `BalancedRyser_Local_AlignedGlobalProduct`, `BalancedRyser_Local_InjectionAuxiliaryExposure`, `BalancedRyser_Local_InjectionExposure`, `BalancedRyser_Local_InjectionExposureLaw`, `BalancedRyser_Local_Local`, `BalancedRyser_Local_LocalAnchorExclusion`, `BalancedRyser_Local_LocalConditionSpec`, `BalancedRyser_Local_LocalDirectionAssignments`, `BalancedRyser_Local_LocalFourEvents`, `BalancedRyser_Local_LocalLemma`, `BalancedRyser_Local_LocalParentMap`, `BalancedRyser_Local_LocalPatternCodes`, `BalancedRyser_Local_LocalSpecificationProbability`, `BalancedRyser_Local_LocalTiming`, `BalancedRyser_Local_LocalTupleReindex`, `BalancedRyser_Local_LocalUsedEventUnion`, `BalancedRyser_Local_LowReuseOrder`, `BalancedRyser_Local_PartialAlignment`, `BalancedRyser_Local_ReuseExtensionSum`, `BalancedRyser_Local_ReuseExtensionTable`, `BalancedRyser_Local_ReuseOrdering`, `BalancedRyser_Local_ReusePatternCounting`, `BalancedRyser_Local_ReusePrescriptions`, `BalancedRyser_Local_ReuseTower`, `BalancedRyser_Local_ReuseWeightedBound`, `BalancedRyser_Probability_AcyclicProductBound`, `BalancedRyser_Probability_EqualityPatternOrdering`, `BalancedRyser_Probability_ExposureInterleaving`, `BalancedRyser_Probability_ExposureScheduleOrder`, `BalancedRyser_Probability_FiniteHistory`, `BalancedRyser_Probability_FiniteHistoryAdditive`, `BalancedRyser_Probability_FiniteKernelPotential`, `BalancedRyser_Probability_FiniteUniformTower`, `BalancedRyser_Probability_FourCycle`, `BalancedRyser_Probability_FreshCoordinatePrescription`, `BalancedRyser_Probability_GeneratorEnumeration`, `BalancedRyser_Probability_IndependentTrialReassembly`, `BalancedRyser_Probability_IndependentTrials`, `BalancedRyser_Probability_IndependentTrials3`, `BalancedRyser_Probability_PatternMoments`, `BalancedRyser_Probability_PatternOrderingAdapter`, `BalancedRyser_Probability_PermutationHistoryLaw`, `BalancedRyser_Probability_PermutationSubsetLaw`, `BalancedRyser_Probability_RootChildDependence`, `BalancedRyser_Probability_RootPatternModel`, `BalancedRyser_Probability_ScheduledCountingExposure`, `BalancedRyser_Probability_SlotConditionedLaw`, `BalancedRyser_Probability_SlotProbability`, `BalancedRyser_Probability_SlotProbability2`, `BalancedRyser_Probability_TailConditioning`, `BalancedRyser_Probability_TailConditioning2`, `BalancedRyser_Probability_TailEvents`, `BalancedRyser_Probability_TailEvents2`, `BalancedRyser_Probability_TailGraph`, `BalancedRyser_Probability_TailGraphWeights`, `BalancedRyser_Probability_TailPrescriptions`, `BalancedRyser_Probability_UncoveredExchange`, `BalancedRyser_Probability_UniformConditionalProduct`, `BalancedRyser_Probability_UniformKernel`, `BalancedRyser_Probability_UniformOrderedSubset`, `BalancedRyser_Probability_UniformThreshold`, `BalancedRyser_Probability_VacantBins`, `BalancedRyser_Probability_WithoutReplacementCoupling`, `BalancedRyser_Profiles_DetectionThresholds`, `BalancedRyser_Profiles_MarkedExposure`, `BalancedRyser_Profiles_MarkedExposureNumerics`, `BalancedRyser_Profiles_Profile`, `BalancedRyser_Profiles_ProfileClassMargin`, `BalancedRyser_Profiles_ProfileCoordinates`, `BalancedRyser_Profiles_ProfileDetection`, `BalancedRyser_Profiles_ProfileDetectionBridge`, `BalancedRyser_Profiles_ProfileDetectionLimit`, `BalancedRyser_Profiles_ProfileEmpirical`, `BalancedRyser_Profiles_ProfileEmpiricalMeasure`, `BalancedRyser_Profiles_ProfileGridDetection`, `BalancedRyser_Profiles_ProfileGridMeasures`, `BalancedRyser_Profiles_ProfileIdentifiability`, `BalancedRyser_Profiles_ProfileOrderComplements`, `BalancedRyser_Profiles_ProfileParameterLaw`, `BalancedRyser_Profiles_ProfileScheduledMargin`, `BalancedRyser_Profiles_ProfileWeakDetection`, `BalancedRyser_Selection_PlaneSelectionOccupancy`, `BalancedRyser_Selection_Selection`, `BalancedRyser_Selection_SelectionAuxiliaryConcentration`, `BalancedRyser_Selection_SelectionAuxiliaryTracks`, `BalancedRyser_Selection_SelectionCensoredJumps`, `BalancedRyser_Selection_SelectionCensoredMeans`, `BalancedRyser_Selection_SelectionConcentrationAsymptotics`, `BalancedRyser_Selection_SelectionCylinder`, `BalancedRyser_Selection_SelectionFinalLaw`, `BalancedRyser_Selection_SelectionFirstAbort`, `BalancedRyser_Selection_SelectionHistory`, `BalancedRyser_Selection_SelectionLaw`, `BalancedRyser_Selection_SelectionOccupancy2`, `BalancedRyser_Selection_SelectionOccupancyBound`, `BalancedRyser_Selection_SelectionOccupancyTail`, `BalancedRyser_Selection_SelectionOccupancyTrack`, `BalancedRyser_Selection_SelectionPostabort`, `BalancedRyser_Selection_SelectionPostcheckTail`, `BalancedRyser_Selection_SelectionProcess`, `BalancedRyser_Selection_SelectionProcessLaw`, `BalancedRyser_Selection_SelectionPushforward`, `BalancedRyser_Selection_SelectionPushforward2`, `BalancedRyser_Selection_SelectionScales`, `BalancedRyser_Selection_SelectionState`, `BalancedRyser_Selection_SelectionTailCompletion`, `BalancedRyser_Selection_SelectionTailCylinder`, `BalancedRyser_Selection_SelectionThinning`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ63Br002` and `OAIQ63Br003`; the statements `OAI.Balanced.ExternalWitnessTail.candidateSlots_of_uniform_moment` and `OAI.Balanced.Selection.Process.exists_uniformConcentratedPath_estimate`.
-- source:
--   OpenAI, Balanced counterexamples to Ryser's conjecture at prime orders (result family 162), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 162; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Balanced-Counterexamples-to-Rysers-Conjecture-at-Prime-Orders-September-27-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ063_BR.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h

/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
/-- The first projection of a probability measure on a product: found by instance search in d13f23b
(total `Measure.map`), here a measurable map. -/
instance isProbabilityMeasure_map_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.fst) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
instance isProbabilityMeasure_map_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.snd) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
instance isProbabilityMeasure_map_subtype_val {α : Type*} [MeasurableSpace α] {p : α → Prop}
    {μ : MeasureTheory.Measure {a // p a}} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Subtype.val) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
/-- Mathlib d13f23b's `YoungDiagram.card_transpose`. -/
@[simp]
theorem _root_.YoungDiagram.card_transpose (μ : YoungDiagram) : μ.transpose.card = μ.card := by
  unfold YoungDiagram.card
  apply Finset.card_bij (fun c _ => c.swap)
  · intro c hc
    have : c ∈ μ.transpose := hc
    rw [YoungDiagram.mem_transpose] at this
    exact this
  · intro a _ b _ h
    simpa using h
  · intro b hb
    refine ⟨b.swap, ?_, by simp⟩
    show b.swap ∈ μ.transpose
    rw [YoungDiagram.mem_transpose]
    simpa using hb
/-- For a measurable equivalence `e`, `IsProbabilityMeasure (μ.map e)` is found by instance search
(Mathlib d13f23b finds it for every map `f`: there `Measure.map` of a non-measurable map is a Dirac
mass, here it is `0`, so only the measurable case can be shimmed). -/
instance isProbabilityMeasure_map_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    (e : α ≃ᵐ β) : MeasureTheory.IsProbabilityMeasure (μ.map e) :=
  MeasureTheory.Measure.isProbabilityMeasure_map e.measurable.aemeasurable
/-- `simp` closes `2 ≤ ∞` in `WithTop ℕ∞` (the smoothness order) in Mathlib d13f23b; ours has the
lemma only for `1` and casts (AffineBernstein, `isSymmSndFDerivAt (by simp)`, 2026-10-26). -/
@[simp]
theorem ofNat_le_infty (n : ℕ) [n.AtLeastTwo] : (no_index (OfNat.ofNat n) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  ENat.LEInfty.out
end OAICompat434

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

noncomputable def finiteUniformProbability {Ω : Type*} [Fintype Ω]
    (E : Ω → Prop) : ℝ :=
  (Nat.card {ω // E ω} : ℝ) / Nat.card Ω

end Balanced

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

variable {F : Type*}

def fixedPositions (J : Finset (Fin 4)) : Finset (Fin 4) :=
  Finset.univ.filter (fun i => i ∈ J ∧ i + 1 ∈ J)

end Balanced.PartialAlignment

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_ReuseOrdering
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

open Finset

def reuseSaving (j : ℕ) : ℕ :=
  if j ≤ 2 then j else if j = 3 then 2 else 1

def reuseExposureScore {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (A : ι → Finset α) : List ι → ℕ
  | [] => 0
  | i :: l => reuseExposureScore A l +
      reuseSaving ((A i ∩ l.toFinset.biUnion A).card)

theorem family_reuse_insert {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (A : ι → Finset α) (s : Finset ι) (i : ι) (hi : i ∉ s) :
    (∑ j ∈ insert i s, (A j).card) - ((insert i s).biUnion A).card =
      ((∑ j ∈ s, (A j).card) - (s.biUnion A).card) +
        (A i ∩ s.biUnion A).card := by
  rw [Finset.sum_insert hi, Finset.biUnion_insert]
  have hsum : (s.biUnion A).card ≤ ∑ j ∈ s, (A j).card := Finset.card_biUnion_le
  have hcard := Finset.card_union_add_card_inter (A i) (s.biUnion A)
  have hinter := Finset.card_le_card (Finset.inter_subset_left : A i ∩ s.biUnion A ⊆ A i)
  omega

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_ReuseExtensionTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

def fixedGeneratorPositions (old : Finset (Fin 4)) : Finset (Fin 4) :=
  old.filter (fun i => i + 1 ∈ old)

end Balanced

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

def restrictedGeneratorLabels (old : Finset α) (mask : Finset (Fin 4)) :
    Finset (Fin 4 → α) :=
  Fintype.piFinset (fun i => if i ∈ mask then old else Finset.univ)

end FiniteLabels

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_FourCycle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.FourCycle

def opposite (i : Fin 4) : Fin 4 := i + 2

def SameBlock (i j : Fin 4) : Prop := i.val % 2 = j.val % 2

def Consecutive (i j : Fin 4) : Prop := j = i + 1 ∨ i = j + 1

variable {α : Type*}

def designated [DecidableEq α] (u : Fin 4 → α) : Finset α :=
  Finset.univ.image u

def evenBlock [DecidableEq α] (u : Fin 4 → α) : Finset α := {u 0, u 2}

def oddBlock [DecidableEq α] (u : Fin 4 → α) : Finset α := {u 1, u 3}

section Finsets
variable [DecidableEq α] (u : Fin 4 → α)

@[simp] theorem mem_designated (x : α) :
    x ∈ designated u ↔ ∃ i, u i = x := by
  simp [designated]

end Finsets

end Balanced.FourCycle

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_ExposedExternalFresh
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.ExposedExternalFresh

noncomputable section
open scoped Classical BigOperators
attribute [local instance] Classical.propDecidable
open MeasureTheory

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
local instance externalFreshMeasurableSpace : MeasurableSpace F := ⊤

end
end Balanced.ExposedExternalFresh

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

local instance instMeasurableSpace_solutions : MeasurableSpace F := ⊤

end Balanced.TupleAlignment

end

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
open MeasureTheory
attribute [local instance] Classical.propDecidable

universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
local instance externalModelMeasurableSpace : MeasurableSpace F := ⊤

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
open MeasureTheory
open ExposedExternalFresh
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
local instance freshGeneratorMeasurableSpace : MeasurableSpace F := ⊤

end
end Balanced.ExternalAssembly

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

open MeasureTheory
local instance instMeasurableSpace_solutions : MeasurableSpace F := ⊤

end
end Balanced.ExternalAssembly

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_ExternalWitnessOldBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.ExternalAssembly

noncomputable section
open scoped Classical BigOperators
open MeasureTheory PartialAlignment
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
local instance instMeasurableSpace_solutions_1 : MeasurableSpace F := ⊤

end
end Balanced.ExternalAssembly

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_FreshCoordinatePrescription
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.FreshCoordinate

noncomputable section
open scoped Classical
attribute [local instance] Classical.propDecidable

variable {D A : Type*} [DecidableEq D]

def prescriptionEquiv (d : D) (E : (D → A) → Prop) (b : (D → A) → A)
    (hE : ∀ f a, E (Function.update f d a) ↔ E f)
    (hb : ∀ f a, b (Function.update f d a) = b f) :
    {f : D → A // E f} ≃ {f : D → A // E f ∧ f d = b f} × A where
  toFun f := (⟨Function.update f.1 d (b f.1),
    (hE f.1 (b f.1)).mpr f.2, by simp [hb]⟩, f.1 d)
  invFun p := ⟨Function.update p.1.1 d p.2, (hE p.1.1 p.2).mpr p.1.2.1⟩
  left_inv f := by
    apply Subtype.ext
    simp
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      simp only [hb, Function.update_idem]
      rw [← p.1.2.2]
      simp
    · simp

end
end Balanced.FreshCoordinate

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
open MeasureTheory PartialAlignment
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
local instance instMeasurableSpace_solutions_2 : MeasurableSpace F := ⊤

end
end Balanced.ExternalAssembly

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_PatternMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.PatternMoments

open scoped BigOperators

variable {Ω A Y : Type*} [Fintype Ω] [Fintype A] [Fintype Y]

def expectation (p : Ω → ℝ) (f : Ω → ℝ) : ℝ := ∑ ω, p ω * f ω

def scheduledWeight (W : List A → ℝ) (overlap : List A → A → Prop)
    [∀ pre a, Decidable (overlap pre a)] :
    List Bool → List A → ℝ
  | [], pre => W pre
  | root :: rest, pre => ∑ a,
      if root = true ∨ overlap pre a then
        scheduledWeight W overlap rest (a :: pre) else 0

def scheduleCost (M L : ℝ) : List Bool → ℝ
  | [] => 1
  | root :: rest => (if root then M else L) * scheduleCost M L rest

def rootCount : List Bool → ℕ
  | [] => 0
  | root :: rest => (if root then 1 else 0) + rootCount rest

attribute [local instance] Classical.propDecidable

def scheduleAllowed (overlap : List A → A → Prop) :
    List Bool → List A → List A → Prop
  | [], [], _ => True
  | root :: rest, a :: labels, pre =>
      (root = true ∨ overlap pre a) ∧ scheduleAllowed overlap rest labels (a :: pre)
  | _, _, _ => False

def tuplePermutation {n : ℕ} (π : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n → A) where
  toFun a i := a (π i)
  invFun a i := a (π.symm i)
  left_inv a := by funext i; simp
  right_inv a := by funext i; simp

end Balanced.PatternMoments

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_PatternOrderingAdapter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.PatternMoments

open scoped BigOperators

variable {A γ : Type*}

variable [DecidableEq γ]

def supportOverlap (C : A → Finset γ) (K₀ : Finset γ)
    (pre : List A) (a : A) : Prop :=
  ¬ Disjoint (C a \ K₀) (pre.foldr (fun b U => U ∪ (C b \ K₀)) ∅)

end Balanced.PatternMoments

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
open MeasureTheory

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
local instance instMeasurableSpace_solutions : MeasurableSpace F := ⊤

end
end Balanced.OppositeAssembly

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_OppositeAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.OppositeAssembly

noncomputable section
open scoped Classical BigOperators
open MeasureTheory

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
local instance instMeasurableSpace_solutions_1 : MeasurableSpace F := ⊤

def meanBound (m : ℕ) : ℝ :=
  327680 * ((m : ℝ)+1)^4 + 2048 * m + 65536 * m * ((m : ℝ)+1)^4

end
end Balanced.OppositeAssembly

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_OppositeTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.OppositeTail

noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Filter OppositeAssembly

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
local instance instMeasurableSpace_solutions : MeasurableSpace F := ⊤

def tailConstant : ℝ := (meanBound ((300 - 1) * 5))^300

end
end Balanced.OppositeTail

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_ExternalWitnessTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.ExternalWitnessTail

noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Filter ExternalAssembly

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
local instance instMeasurableSpace_solutions : MeasurableSpace F := ⊤

end
end Balanced.ExternalWitnessTail

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

def encodeLabel {G : Type*} {Label : G → Type*} {r n : ℕ}
    (eG : G ≃ Fin r) (eL : ∀ g, Label g ≃ Fin n) :
    Sigma Label ≃ Fin r × Fin n :=
  (Equiv.sigmaCongr eG eL).trans (Equiv.sigmaEquivProd (Fin r) (Fin n))

@[simp] theorem encodeLabel_apply
    {G : Type*} {Label : G → Type*} {r n : ℕ}
    (eG : G ≃ Fin r) (eL : ∀ g, Label g ≃ Fin n) (g : G) (l : Label g) :
    encodeLabel eG eL ⟨g, l⟩ = (eG g, eL g l) := rfl

end Balanced

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

variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]

def logBudget (F : Type u) [Fintype F] : ℕ := Nat.ceil (Real.log (Fintype.card F))

structure EqualityPattern (b κ : ℕ) where
  classOf : Fin b → Fin 4 → Fin (4 * b - κ)
  everyClass : Function.Surjective (fun ij : Fin b × Fin 4 => classOf ij.1 ij.2)
  withinTuple : ∀ i, Function.Injective (classOf i)
  pairOverlap : ∀ i j, i ≠ j →
    ((Finset.univ.image (classOf i)) ∩ (Finset.univ.image (classOf j))).card ≤ 1

abbrev Bits (b : ℕ) := Fin b → Fin 4 → Bool

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

theorem family_reuse_erase {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (A : ι → Finset α) (s : Finset ι) (i : ι) (hi : i ∈ s) :
    (∑ j ∈ s, (A j).card) - (s.biUnion A).card =
      ((∑ j ∈ s.erase i, (A j).card) - ((s.erase i).biUnion A).card) +
        (A i ∩ (s.erase i).biUnion A).card := by
  simpa only [Finset.insert_erase hi] using
    family_reuse_insert A (s.erase i) i (Finset.notMem_erase i s)

theorem exists_low_reuse_leaf {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (A : ι → Finset α) (s : Finset ι) (hs : s.Nonempty)
    (hcompat : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (A i ∩ A j).card ≤ 1)
    (hexcess : (∑ i ∈ s, (A i).card) - (s.biUnion A).card ≤ 2) :
    ∃ i ∈ s, (A i ∩ (s.erase i).biUnion A).card ≤ 1 := by
  obtain ⟨i, hi⟩ := hs
  by_cases hsmall : (A i ∩ (s.erase i).biUnion A).card ≤ 1
  · exact ⟨i, hi, hsmall⟩
  have hdecomp := family_reuse_erase A s i hi
  have hzero : (∑ j ∈ s.erase i, (A j).card) -
      ((s.erase i).biUnion A).card = 0 := by omega
  have hrest : (s.erase i).Nonempty := by
    by_contra h
    have he : s.erase i = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp [he] at hsmall
  obtain ⟨j, hj⟩ := hrest
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  have hjs : j ∈ s := (Finset.mem_erase.mp hj).2
  have hjdecomp := family_reuse_erase A (s.erase i) j hj
  have hjzero : (A j ∩ ((s.erase i).erase j).biUnion A).card = 0 := by omega
  have hjempty : A j ∩ ((s.erase i).erase j).biUnion A = ∅ :=
    Finset.card_eq_zero.mp hjzero
  refine ⟨j, hjs, (Finset.card_le_card ?_).trans (hcompat j hjs i hi hji)⟩
  intro x hx
  obtain ⟨hxj, hxrest⟩ := Finset.mem_inter.mp hx
  obtain ⟨k, hk, hxk⟩ := Finset.mem_biUnion.mp hxrest
  by_cases hki : k = i
  · exact Finset.mem_inter.mpr ⟨hxj, hki ▸ hxk⟩
  · have hk' : k ∈ (s.erase i).erase j := by
      obtain ⟨hkj, hks⟩ := Finset.mem_erase.mp hk
      exact Finset.mem_erase.mpr ⟨hkj, Finset.mem_erase.mpr ⟨hki, hks⟩⟩
    have hxin : x ∈ A j ∩ ((s.erase i).erase j).biUnion A :=
      Finset.mem_inter.mpr ⟨hxj, Finset.mem_biUnion.mpr ⟨k, hk', hxk⟩⟩
    simp only [hjempty, Finset.notMem_empty] at hxin

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Construction_RootChildPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.RootChildPartition

open scoped BigOperators

variable {ι α : Type*} [DecidableEq ι] [DecidableEq α]

def DisjointRoots (A : ι → Finset α) (R : Finset ι) : Prop :=
  ∀ i ∈ R, ∀ j ∈ R, i ≠ j → Disjoint (A i) (A j)

end Balanced.RootChildPartition

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

noncomputable def deletionPoissonMass (k n : ℕ) : ℝ :=
  (ProbabilityTheory.poissonMeasure (k : ℝ≥0)).real {n}

end Balanced

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Deletion_DeletionDomination
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Balanced.DeletionLaw

def uniformDeletionMass (q n : ℕ) : ℝ :=
  ((Nat.choose q 3 : ℝ) ^ n)⁻¹

end Balanced.DeletionLaw

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_InjectionExposure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.InjectionExposure

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

noncomputable def completions (K : Finset I) (base : I ↪ J) : Finset (I ↪ J) :=
  Finset.univ.filter (fun e => ∀ j ∈ K, e j = base j)

def remaining (K : Finset I) (base : I ↪ J) : Finset J :=
  Finset.univ \ K.image base

@[simp] theorem mem_completions (K : Finset I) (base e : I ↪ J) :
    e ∈ completions K base ↔ ∀ j ∈ K, e j = base j := by
  simp [completions]

omit [Fintype I] [DecidableEq I] in
@[simp] theorem mem_remaining (K : Finset I) (base : I ↪ J) (a : J) :
    a ∈ remaining K base ↔ a ∉ K.image base := by
  simp [remaining]

theorem completions_nonempty (K : Finset I) (base : I ↪ J) :
    (completions K base).Nonempty := by
  exact ⟨base, by simp⟩

end Balanced.InjectionExposure

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_InjectionAuxiliaryExposure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.InjectionExposure

variable {I J Z : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def DependsOnExposed (K : Finset I) (noise : (I ↪ J) → PMF Z) : Prop :=
  ∀ e f, (∀ j ∈ K, e j = f j) → noise e = noise f

noncomputable def auxiliaryLaw (K : Finset I) (base : I ↪ J)
    (noise : (I ↪ J) → PMF Z) : PMF ((I ↪ J) × Z) :=
  (PMF.uniformOfFinset (completions K base) (completions_nonempty K base)).bind
    (fun e => (noise e).map (fun z => (e, z)))

end Balanced.InjectionExposure

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

abbrev DirectionToken (b κ : ℕ) := Fin b ⊕ Fin (4 * b - κ)

section CrossEquality

variable {I G J : Type*} [Fintype I] [Fintype G] [Fintype J]
  [DecidableEq I] [DecidableEq G] [DecidableEq J]

def crossEqualityEquiv (i : I) (j : G) :
    {a : (I → J) × (G → J) // a.1 i = a.2 j} ≃
      (({k : I // k ≠ i} → J) × (G → J)) where
  toFun a := (fun k => a.val.1 k, a.val.2)
  invFun a := ⟨(fun k => if h : k = i then a.2 j else a.1 ⟨k, h⟩, a.2), by simp⟩
  left_inv a := by
    apply Subtype.ext
    apply Prod.ext
    · funext k
      by_cases hk : k = i
      · subst k; simp [a.property]
      · simp [hk]
    · rfl
  right_inv a := by
    apply Prod.ext
    · funext k
      simp [k.property]
    · rfl

end CrossEquality

end Balanced.Local

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_AlignedGeneratorIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.TokenExposure

open PartialAlignment
noncomputable section
attribute [local instance] Classical.propDecidable
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ}

def purposefulIndex (σ : Fin 4 → Bool) (j : Fin 4) (s : Bool) : Fin 4 :=
  if s = σ j then j else j - 1

end
end Balanced.Local.TokenExposure

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_FiniteAffinePlane
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
namespace FiniteAffine

noncomputable section
attribute [local instance] Classical.propDecidable

structure Plane (q : ℕ) (P D L : Type*) [Fintype P] [Fintype D] [Fintype L] where
  direction : L → D
  incident : P → L → Prop
  card_points : Fintype.card P = q ^ 2
  card_directions : Fintype.card D = q + 1
  card_lines_direction : ∀ d,
    (Finset.univ.filter (fun ℓ : L => direction ℓ = d)).card = q
  card_points_line : ∀ ℓ,
    (Finset.univ.filter (fun p : P => incident p ℓ)).card = q
  unique_line_direction : ∀ p d, ∃! ℓ, direction ℓ = d ∧ incident p ℓ
  unique_join : ∀ p r, p ≠ r → ∃! ℓ, incident p ℓ ∧ incident r ℓ

variable {q : ℕ} {P D L : Type*} [Fintype P] [Fintype D] [Fintype L]

def Plane.linePoints (A : Plane q P D L) (ℓ : L) : Finset P :=
  Finset.univ.filter (fun p => A.incident p ℓ)

end
end FiniteAffine
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

abbrev V (F : Type*) := Fin 3 → F

def coordAdd (i j : Fin 3) (hij : i ≠ j) (c : F) : V F ≃ₗ[F] V F where
  toFun v k := v k + if k = i then c * v j else 0
  invFun v k := v k - if k = i then c * v j else 0
  map_add' v w := by
    ext k
    by_cases hk : k = i
    · simp [hk]
      ring
    · simp [hk]
  map_smul' a v := by
    ext k
    by_cases hk : k = i
    · simp [hk, smul_eq_mul]
      ring
    · simp [hk]
  left_inv v := by
    ext k
    by_cases hk : k = i
    · subst k; simp [hij.symm]
    · simp [hk]
  right_inv v := by
    ext k
    by_cases hk : k = i
    · subst k; simp [hij.symm]
    · simp [hk]

def coordPerm (e : Equiv.Perm (Fin 3)) : V F ≃ₗ[F] V F where
  toFun v i := v (e i)
  invFun v i := v (e.symm i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv v := by ext i; simp
  right_inv v := by ext i; simp

end ProjectiveNormalization
end Balanced

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

noncomputable def stabilityDensity (ζ : ℝ) : ℝ := min (ζ / 4) (1 / 100)

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_StabilityPolynomial2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.StabilityPolynomial

open MvPolynomial

variable {F σ : Type*} [Field F]

noncomputable def pairExponent (a : ℕ × ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 a.1 + Finsupp.single 1 a.2

def trianglePairs (d : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (d + 1)).biUnion Finset.HasAntidiagonal.antidiagonal

end Balanced.StabilityPolynomial

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_StabilityLeadingPart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.StabilityPolynomial

open MvPolynomial
open scoped BigOperators

variable {F σ : Type*} [Field F]

noncomputable def dehomogenize : MvPolynomial (Fin 2) F →ₐ[F] Polynomial F :=
  MvPolynomial.aeval ![Polynomial.X, 1]

noncomputable def leadingSpecialization (n : ℕ) (p : MvPolynomial (Fin 2) F) :
    Polynomial F := dehomogenize (homogeneousComponent n p)

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

def probability {Ω : Type*} [Fintype Ω] (E : Ω → Prop) : ℝ := by
  classical
  exact ((Finset.univ.filter E).card : ℝ) / Fintype.card Ω

end Balanced.UnusedOffsetIncidence

end

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

def classSet {b κ : ℕ} (P : EqualityPattern b κ) (i : Fin b) :
    Finset (Fin (4 * b - κ)) := Finset.univ.image (P.classOf i)

@[simp]
theorem card_classSet {b κ : ℕ} (P : EqualityPattern b κ) (i : Fin b) :
    (P.classSet i).card = 4 := by
  rw [classSet, Finset.card_image_of_injective _ (P.withinTuple i)]
  simp

theorem biUnion_classSet {b κ : ℕ} (P : EqualityPattern b κ) :
    Finset.univ.biUnion P.classSet = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro a
  obtain ⟨⟨i, j⟩, hij⟩ := P.everyClass a
  apply Finset.mem_biUnion.mpr
  refine ⟨i, Finset.mem_univ _, ?_⟩
  exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hij⟩

@[simp]
theorem card_biUnion_classSet {b κ : ℕ} (P : EqualityPattern b κ) :
    (Finset.univ.biUnion P.classSet).card = 4 * b - κ := by
  rw [P.biUnion_classSet]
  simp

@[simp]
theorem sum_card_classSet {b κ : ℕ} (P : EqualityPattern b κ) :
    (∑ i : Fin b, (P.classSet i).card) = 4 * b := by
  simp [Nat.mul_comm]

theorem classSet_reuse_le {b κ : ℕ} (P : EqualityPattern b κ) :
    (∑ i : Fin b, (P.classSet i).card) -
      (Finset.univ.biUnion P.classSet).card ≤ κ := by
  rw [P.sum_card_classSet, P.card_biUnion_classSet]
  omega

end Balanced.Local.EqualityPattern

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_UniformConditionalProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.UniformConditionalProduct

open TupleAlignment

noncomputable section
attribute [local instance] Classical.propDecidable

def subtypeFirstEquiv {A B : Type*} (E : A → Prop) :
    {z : A × B // E z.1} ≃ {a : A // E a} × B where
  toFun z := (⟨z.1.1, z.2⟩, z.1.2)
  invFun z := ⟨(z.1.1, z.2), z.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def conditionedSplitEquiv {X A B : Type*} (e : X ≃ A × B) (E : A → Prop) :
    {x : X // E (e x).1} ≃ {a : A // E a} × B :=
  (e.subtypeEquiv (fun _ => Iff.rfl)).trans (subtypeFirstEquiv E)

@[simp] theorem conditionedSplitEquiv_symm_val {X A B : Type*}
    (e : X ≃ A × B) (E : A → Prop) (z : {a : A // E a} × B) :
    ((conditionedSplitEquiv e E).symm z).1 = e.symm (z.1.1, z.2) := rfl

def arraySplitEquiv {D V : Type*} (P : D → Prop) :
    (D → V) ≃ ({d : D // P d} → V) × ({d : D // ¬ P d} → V) :=
  Equiv.piEquivPiSubtypeProd P (fun _ => V)

@[simp] theorem arraySplitEquiv_first {D V : Type*} (P : D → Prop)
    (o : D → V) (d : {d : D // P d}) :
    (arraySplitEquiv P o).1 d = o d.1 := rfl

@[simp] theorem arraySplitEquiv_second {D V : Type*} (P : D → Prop)
    (o : D → V) (d : {d : D // ¬ P d}) :
    (arraySplitEquiv P o).2 d = o d.1 := rfl

end
end Balanced.UniformConditionalProduct

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_RootChildDependence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.RootChildPartition

open scoped BigOperators

def touchedPositions (J : Finset (Fin 4)) : Finset (Fin 4) :=
  Finset.univ.filter fun i => i ∈ J ∨ i + 1 ∈ J

def rootGeneratorIndices {b κ : ℕ} (P : Local.EqualityPattern b κ)
    (R : Finset (Fin b)) (i : Fin b) : Finset (Fin 4) :=
  Finset.univ.filter fun j => P.classOf i j ∈ R.biUnion P.classSet

def dependentOccurrences {b κ : ℕ} (P : Local.EqualityPattern b κ)
    (R : Finset (Fin b)) : Finset (Fin b × Fin 4) :=
  (Finset.univ \ R).biUnion fun i =>
    (touchedPositions (rootGeneratorIndices P R i)).image fun j => (i, j)

@[simp] theorem mem_dependentOccurrences {b κ : ℕ} (P : Local.EqualityPattern b κ)
    (R : Finset (Fin b)) (ij : Fin b × Fin 4) :
    ij ∈ dependentOccurrences P R ↔ ij.1 ∉ R ∧
      (P.classOf ij.1 ij.2 ∈ R.biUnion P.classSet ∨
        P.classOf ij.1 (ij.2 + 1) ∈ R.biUnion P.classSet) := by
  rcases ij with ⟨i, j⟩
  simp [dependentOccurrences, touchedPositions, rootGeneratorIndices]

end Balanced.RootChildPartition

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

open RootChildPartition

noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

abbrev FreeCoordinates {b : ℕ} (D : Finset (Fin b × Fin 4)) :=
  {ij : Fin b × Fin 4 // ij ∉ D} → F

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

open TupleAlignment RootChildPartition
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

abbrev FreeIndex {b κ : ℕ} (P : EqualityPattern b κ) (R : Finset (Fin b)) :=
  {ij : Fin b × Fin 4 // ij ∉ dependentOccurrences P R}

end
end Balanced.Local.AlignedGlobal

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_PermutationSubsetLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace Balanced.PermutationSubsetLaw

variable {α : Type*} [DecidableEq α]

def postcompose (τ : Equiv.Perm α) : Equiv.Perm α ≃ Equiv.Perm α where
  toFun σ := σ.trans τ
  invFun σ := σ.trans τ.symm
  left_inv σ := by ext a; simp
  right_inv σ := by ext a; simp

end Balanced.PermutationSubsetLaw

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

def available (S : Finset ι) (h : ι ↪ α) : Finset α :=
  Finset.univ \ S.map h

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem mem_available (S : Finset ι) (h : ι ↪ α) (x : α) :
    x ∈ available S h ↔ x ∉ S.map h := by simp [available]

def postcompose (τ : Equiv.Perm α) : (ι ↪ α) ≃ (ι ↪ α) where
  toFun f := f.trans τ.toEmbedding
  invFun f := f.trans τ.symm.toEmbedding
  left_inv f := by ext j; simp
  right_inv f := by ext j; simp

omit [Fintype ι] [Fintype α] [DecidableEq ι] [DecidableEq α] in
@[simp] theorem postcompose_apply (τ : Equiv.Perm α) (f : ι ↪ α) (j : ι) :
    postcompose τ f j = τ (f j) := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem card_available (S : Finset ι) (h : ι ↪ α) :
    (available S h).card = Fintype.card α - S.card := by
  simp [available, Finset.card_sdiff_of_subset (Finset.subset_univ (S.map h))]

def selfEmbeddingEquivPerm : (α ↪ α) ≃ Equiv.Perm α where
  toFun f := Equiv.ofBijective f ⟨f.injective, Finite.surjective_of_injective f.injective⟩
  invFun σ := σ.toEmbedding
  left_inv f := by ext x; rfl
  right_inv σ := by ext x; rfl

end
end Balanced.InjectionExposureLaw

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalAnchorExclusion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.AnchorExclusion

noncomputable section
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ} (P : EqualityPattern b κ)
variable (bits : Bits b)

def Purposeful (c : Fin (4 * b - κ)) (ij : Fin b × Fin 4) : Prop :=
  P.classOf ij.1 ij.2 = c ∨ P.classOf ij.1 (ij.2 + 1) = c

end
end Balanced.Local.AnchorExclusion

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

def classUseCount (P : EqualityPattern b κ) (c : Fin (4 * b - κ)) : ℕ :=
  (Finset.univ.filter (fun i => ∃ j, P.classOf i j = c)).card

end
end Balanced.Local.FourEvents

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

def endpointIndex (r : Fin 4) (σ t : Bool) : Fin 4 :=
  if t = σ then r else r - 1

variable {b : ℕ}

def dependent (child : Fin b) (s : Fin 4) : Finset (Fin b × Fin 4) :=
  {(child, s), (child, s - 1)}

def underlying (root child : Fin b) (r s : Fin 4) (σ τ : Bool)
    (ij : Fin b × Fin 4) : Fin b × Fin 4 :=
  if ij = (child, s) then (root, endpointIndex r σ τ)
  else if ij = (child, s - 1) then (root, endpointIndex r σ (!τ)) else ij

theorem underlying_first (root child : Fin b) (r s : Fin 4) (σ τ : Bool) :
    underlying root child r s σ τ (child, s) = (root, endpointIndex r σ τ) := by
  simp [underlying]

theorem underlying_second (root child : Fin b) (r s : Fin 4) (σ τ : Bool) :
    underlying root child r s σ τ (child, s - 1) =
      (root, endpointIndex r σ (!τ)) := by
  simp [underlying]

theorem underlying_fixed (root child : Fin b) (r s : Fin 4) (σ τ : Bool)
    {ij : Fin b × Fin 4} (h : ij ∉ dependent child s) :
    underlying root child r s σ τ ij = ij := by
  simp only [dependent, Finset.mem_insert, Finset.mem_singleton, not_or] at h
  simp [underlying, h.1, h.2]

theorem underlying_not_dependent (root child : Fin b) (r s : Fin 4) (σ τ : Bool)
    (hne : root ≠ child) (ij : Fin b × Fin 4) :
    underlying root child r s σ τ ij ∉ dependent child s := by
  by_cases hfirst : ij = (child, s)
  · subst ij
    simp [underlying_first, dependent, hne]
  · by_cases hsecond : ij = (child, s - 1)
    · subst ij
      simp [underlying_second, dependent, hne]
    · simp [underlying, hfirst, hsecond, dependent]

end
end Balanced.Local.ParentMap

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

abbrev Position (b : ℕ) := Fin b × Fin 4

abbrev Code (b κ : ℕ) := Unit ⊕
  ((Position b × Position b) ⊕ (Position b ⊕ (Fin (4 * b - κ) × Position b)))

def anchors {b κ : ℕ} : Code b κ → Finset (Position b)
  | Sum.inl _ => ∅
  | Sum.inr (Sum.inl xy) => {xy.1, xy.2}
  | Sum.inr (Sum.inr (Sum.inl x)) => {x}
  | Sum.inr (Sum.inr (Sum.inr cx)) => {cx.2}

def underlyingAnchors {b κ : ℕ} (u : Position b → Position b)
    (z : Code b κ) : Finset (Position b) := (anchors z).image u

end
end Balanced.Local.ConditionSpec

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalLemma
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.LocalLemma

open scoped BigOperators

variable {ι : Type*} [DecidableEq ι]

theorem extension_lower_bound (a : Finset ι → ℝ) (r : ι → ℝ)
    (S : Finset ι) (hr : ∀ i ∈ S, 0 ≤ r i)
    (hstep : ∀ T ⊆ S, ∀ i ∈ S, i ∉ T → a T * r i ≤ a (insert i T))
    (T : Finset ι) (hTS : T ⊆ S) :
    a T * ∏ i ∈ S \ T, r i ≤ a S := by
  have haux : ∀ U : Finset ι, U ⊆ S → Disjoint T U →
      a T * ∏ i ∈ U, r i ≤ a (T ∪ U) := by
    intro U
    induction U using Finset.induction_on with
    | empty => simp
    | @insert i U hi ih =>
      intro hUS hd
      have hiS : i ∈ S := hUS (by simp)
      have hUi : U ⊆ S := fun j hj => hUS (by simp [hj])
      have hdi : i ∉ T := by
        intro hiT
        exact Finset.disjoint_left.mp hd hiT (by simp)
      have hdU : Disjoint T U := hd.mono_right (by intro j hj; simp [hj])
      have hiTU : i ∉ T ∪ U := by simp [hdi, hi]
      have hTU : T ∪ U ⊆ S := Finset.union_subset hTS hUi
      calc
        a T * ∏ j ∈ insert i U, r j = (a T * ∏ j ∈ U, r j) * r i := by
          rw [Finset.prod_insert hi]; ring
        _ ≤ a (T ∪ U) * r i := mul_le_mul_of_nonneg_right (ih hUi hdU) (hr i hiS)
        _ ≤ a (insert i (T ∪ U)) := hstep (T ∪ U) hTU i hiS hiTU
        _ = a (T ∪ insert i U) := by rw [Finset.union_insert]
  simpa [Finset.union_sdiff_of_subset hTS] using
    haux (S \ T) Finset.sdiff_subset (by simp [Finset.disjoint_left]; tauto)

theorem avoidance_induction (a : Finset ι → ℝ) (p x : ι → ℝ)
    (N : ι → Finset ι)
    (hempty : a ∅ = 1)
    (ha : ∀ S, 0 ≤ a S)
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
    (hp : ∀ i, p i ≤ x i * ∏ j ∈ N i, (1 - x j))
    (hdep : ∀ S i, i ∉ S →
      a S - a (insert i S) ≤ p i * a (S \ N i)) :
    ∀ S, 0 < a S ∧ ∀ i, i ∉ S →
      a S * (1 - x i) ≤ a (insert i S) := by
  intro S
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    have hstep : ∀ T ⊆ S, ∀ i ∈ S, i ∉ T →
        a T * (1 - x i) ≤ a (insert i T) := by
      intro T hTS i hiS hiT
      have hproper : T ⊂ S := Finset.ssubset_iff_subset_ne.mpr ⟨hTS, by
        intro heq; exact hiT (heq ▸ hiS)⟩
      exact (ih T hproper).2 i hiT
    have hpositive : 0 < a S := by
      have hlower := extension_lower_bound a (fun i => 1 - x i) S
        (fun i _ => le_of_lt (sub_pos.mpr (hx1 i))) hstep ∅ (Finset.empty_subset S)
      have hprod : 0 < ∏ i ∈ S, (1 - x i) :=
        Finset.prod_pos (fun i _ => sub_pos.mpr (hx1 i))
      simpa [hempty] using lt_of_lt_of_le hprod (by simpa [hempty] using hlower)
    refine ⟨hpositive, ?_⟩
    intro i hiS
    have hratio := extension_lower_bound a (fun j => 1 - x j) S
      (fun j _ => le_of_lt (sub_pos.mpr (hx1 j))) hstep
      (S \ N i) Finset.sdiff_subset
    have hprod : 0 < ∏ j ∈ S \ (S \ N i), (1 - x j) :=
      Finset.prod_pos (fun j _ => sub_pos.mpr (hx1 j))
    have hsubset : S \ (S \ N i) ⊆ N i := by
      intro j hj
      simp only [Finset.mem_sdiff] at hj
      by_contra hjN
      exact hj.2 ⟨hj.1, hjN⟩
    have hprod_le : (∏ j ∈ N i, (1 - x j)) ≤
        ∏ j ∈ S \ (S \ N i), (1 - x j) := by
      exact Finset.prod_le_prod_of_subset_of_le_one hsubset
        (fun j _ => le_of_lt (sub_pos.mpr (hx1 j)))
        (fun j _ _ => by linarith [hx0 j])
    have hpi : p i ≤ x i * ∏ j ∈ S \ (S \ N i), (1 - x j) :=
      (hp i).trans (mul_le_mul_of_nonneg_left hprod_le (hx0 i))
    have hbound : p i * a (S \ N i) ≤ x i * a S := by
      calc
        p i * a (S \ N i) ≤
            (x i * ∏ j ∈ S \ (S \ N i), (1 - x j)) * a (S \ N i) :=
          mul_le_mul_of_nonneg_right hpi (ha _)
        _ = x i * (a (S \ N i) * ∏ j ∈ S \ (S \ N i), (1 - x j)) := by ring
        _ ≤ x i * a S := mul_le_mul_of_nonneg_left hratio (hx0 i)
    have hd := (hdep S i hiS).trans hbound
    nlinarith

end Balanced.LocalLemma

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_ReusePatternCounting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace Balanced.ReusePatternCounting

noncomputable section
open scoped Classical

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

def changedSet (base f : α → β) : Finset α :=
  Finset.univ.filter (fun i => f i ≠ base i)

def fillOn (base : α → β) (s : Finset α) (v : s → β) (i : α) : β :=
  if hi : i ∈ s then v ⟨i, hi⟩ else base i

section Representatives

variable {ι γ : Type*} [Fintype ι] [LinearOrder ι] [DecidableEq γ]

def firstRepresentative (f : ι → γ) (i : ι) : ι :=
  (Finset.univ.filter (fun j => f j = f i)).min'
    ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, rfl⟩⟩

theorem value_firstRepresentative (f : ι → γ) (i : ι) :
    f (firstRepresentative f i) = f i := by
  exact (Finset.mem_filter.mp (Finset.min'_mem
    (Finset.univ.filter (fun j => f j = f i)) _)).2

theorem firstRepresentative_le (f : ι → γ) (i : ι) :
    firstRepresentative f i ≤ i := by
  exact Finset.min'_le (Finset.univ.filter (fun j => f j = f i)) i
    (Finset.mem_filter.mpr ⟨Finset.mem_univ i, rfl⟩)

theorem firstRepresentative_eq_of_value_eq (f : ι → γ) {i j : ι}
    (h : f i = f j) : firstRepresentative f i = firstRepresentative f j := by
  unfold firstRepresentative
  simp only [h]

theorem firstRepresentative_idempotent (f : ι → γ) (i : ι) :
    firstRepresentative f (firstRepresentative f i) = firstRepresentative f i :=
  firstRepresentative_eq_of_value_eq f (value_firstRepresentative f i)

theorem representative_image_eq_fixed (f : ι → γ) :
    Finset.univ.image (firstRepresentative f) =
      Finset.univ.filter (fun i => firstRepresentative f i = i) := by
  ext i
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
  constructor
  · rintro ⟨j, rfl⟩
    exact firstRepresentative_idempotent f j
  · intro hi
    exact ⟨i, hi⟩

theorem card_representative_image (f : ι → γ) :
    (Finset.univ.image (firstRepresentative f)).card = (Finset.univ.image f).card := by
  apply Finset.card_bij (fun i _ => f i)
  · intro i _
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  · intro i hi j hj hij
    have hri : firstRepresentative f i = i := by
      rw [representative_image_eq_fixed] at hi
      exact (Finset.mem_filter.mp hi).2
    have hrj : firstRepresentative f j = j := by
      rw [representative_image_eq_fixed] at hj
      exact (Finset.mem_filter.mp hj).2
    rw [← hri, ← hrj]
    exact firstRepresentative_eq_of_value_eq f hij
  · intro y hy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
    refine ⟨firstRepresentative f i, Finset.mem_image.mpr
      ⟨i, Finset.mem_univ i, rfl⟩, value_firstRepresentative f i⟩

theorem card_changed_firstRepresentative (f : ι → γ) :
    (changedSet id (firstRepresentative f)).card =
      Fintype.card ι - (Finset.univ.image f).card := by
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := Finset.univ) (fun i => firstRepresentative f i ≠ i)
  have hfixed : (Finset.univ.filter (fun i => firstRepresentative f i = i)).card =
      (Finset.univ.image f).card := by
    rw [← representative_image_eq_fixed]
    exact card_representative_image f
  simp only [not_not, Finset.card_univ] at hpartition
  simp only [changedSet, id_eq]
  omega

abbrev CanonicalPattern (ι : Type*) [Fintype ι] [LinearOrder ι] (κ : ℕ) :=
  {r : ι → ι // (∀ i, r i ≤ i ∧ r (r i) = r i) ∧ (changedSet id r).card = κ}

end Representatives

end
end Balanced.ReusePatternCounting

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalPatternCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.PatternCodes

open ReusePatternCounting
open scoped Classical
noncomputable section

variable {b κ : ℕ}

def occurrenceEquiv (b : ℕ) : Fin b × Fin 4 ≃ Fin (4 * b) :=
  (Equiv.prodComm (Fin b) (Fin 4)).trans finProdFinEquiv

def flatClasses (P : EqualityPattern b κ) (i : Fin (4 * b)) : Fin (4 * b - κ) :=
  P.classOf ((occurrenceEquiv b).symm i).1 ((occurrenceEquiv b).symm i).2

theorem flatClasses_surjective (P : EqualityPattern b κ) :
    Function.Surjective (flatClasses P) := by
  intro c
  obtain ⟨ij, hij⟩ := P.everyClass c
  refine ⟨occurrenceEquiv b ij, ?_⟩
  simpa only [flatClasses, Equiv.symm_apply_apply] using hij

def canonicalCode (P : EqualityPattern b κ) (hκ : κ ≤ 4 * b) :
    CanonicalPattern (Fin (4 * b)) κ :=
  ⟨firstRepresentative (flatClasses P), by
    refine ⟨fun i => ⟨firstRepresentative_le _ i,
      firstRepresentative_idempotent _ i⟩, ?_⟩
    rw [card_changed_firstRepresentative,
      Finset.image_univ_of_surjective (flatClasses_surjective P)]
    simp only [Finset.card_univ, Fintype.card_fin]
    omega⟩

theorem classOf_injective : Function.Injective
    (fun P : EqualityPattern b κ => P.classOf) := by
  intro P Q h
  cases P
  cases Q
  cases h
  rfl

local instance instFintypeEqualityPattern : Fintype (EqualityPattern b κ) :=
  Fintype.ofInjective (fun P : EqualityPattern b κ => P.classOf) classOf_injective

end
end Balanced.Local.PatternCodes

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_AcyclicProductBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace Balanced.DependencyExtraction

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [Nonempty β]

def coordinateSwap (i : α) : ((α → β) × β) ≃ ((α → β) × β) where
  toFun z := (Function.update z.1 i z.2, z.1 i)
  invFun z := (Function.update z.1 i z.2, z.1 i)
  left_inv z := by
    ext j
    · by_cases h : j = i <;> simp [h]
    · simp
  right_inv z := by
    ext j
    · by_cases h : j = i <;> simp [h]
    · simp

end Balanced.DependencyExtraction

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalSpecificationProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.ConditionSpec

noncomputable section
open scoped Classical BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {b κ n : ℕ}

def GoodSpecification (u : Position b → α) (I : Finset (Position b))
    (σ : Fin n → Position b × Code b κ) : Prop :=
  Function.Injective (fun k => u (σ k).1) ∧
    (∀ k, (σ k).1 ∈ I) ∧
    ∃ rank : α → ℕ, ∀ i j,
      u (σ j).1 ∈ (anchors (σ i).2).image u →
        rank (u (σ i).1) < rank (u (σ j).1)

end
end Balanced.Local.ConditionSpec

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_LocalTiming
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.Timing

open scoped Classical

variable {b κ : ℕ}

def earlierTuples (rank : Fin b → ℕ) (i : Fin b) : Finset (Fin b) :=
  Finset.univ.filter (fun j => rank j < rank i)

def rootsFirstRank (R : Finset (Fin b)) (i : Fin b) : ℕ :=
  if i ∈ R then i.val else b + i.val

end Balanced.Local.Timing

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

namespace EqualityPattern

variable {b κ : ℕ}

def reindex (P : EqualityPattern b κ) (σ : Equiv.Perm (Fin b)) :
    EqualityPattern b κ where
  classOf i := P.classOf (σ i)
  everyClass := by
    intro c
    obtain ⟨⟨i, j⟩, hc⟩ := P.everyClass c
    exact ⟨(σ.symm i, j), by simpa using hc⟩
  withinTuple i := P.withinTuple (σ i)
  pairOverlap i j hij := P.pairOverlap (σ i) (σ j) (fun h => hij (σ.injective h))

end EqualityPattern

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ} (P : EqualityPattern b κ) (σ : Equiv.Perm (Fin b))

def reindexBits (bits : Bits b) : Bits b := bits ∘ σ

def reindexPositions : (Fin b × Fin 4) ≃ (Fin b × Fin 4) :=
  Equiv.prodCongr σ (Equiv.refl _)

end
end Balanced.Local

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

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ}

abbrev UsedWitness (b κ : ℕ) :=
  Fin (4 * b - κ) × (Fin b × Fin 4) × Bool

abbrev TripleWitness (b : ℕ) :=
  (Fin b × Fin 4) × (Fin b × Fin 4) × (Fin b × Fin 4)

end
end Balanced.Local.UsedEventUnion

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_ReuseExtensionSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced
open PartialAlignment

noncomputable section
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem cyclic_index_ne_next (i : Fin 4) : i ≠ i + 1 := by
  have h : ∀ i : Fin 4, i ≠ i + 1 := by decide
  exact h i

end
end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_ReuseTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.ReuseTower

open scoped BigOperators
noncomputable section
open scoped Classical

section FiniteTower
variable {Ω Y A : Type*} [Fintype Ω] [Nonempty Ω] [Fintype Y] [DecidableEq Y]
  [Fintype A]

omit [Fintype Y] [DecidableEq Y] in
theorem fiber_supported (expose : Ω → Y) (a : Ω) :
    ∃ ω ∈ {ω | expose ω = expose a},
      ω ∈ (PMF.uniformOfFintype Ω).support :=
  ⟨a, rfl, PMF.mem_support_uniformOfFintype _⟩

end FiniteTower
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

open Local
open scoped BigOperators

noncomputable section
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def allLists (α : Type*) [Fintype α] [DecidableEq α] : ℕ → Finset (List α)
  | 0 => {[]}
  | n + 1 => Finset.univ.biUnion (fun a => (allLists α n).image (List.cons a))

@[simp] theorem mem_allLists {α : Type*} [Fintype α] [DecidableEq α]
    (l : List α) (n : ℕ) : l ∈ allLists α n ↔ l.length = n := by
  induction n generalizing l with
  | zero => simp [allLists]
  | succ n ih =>
    cases l with
    | nil => simp [allLists]
    | cons a l => simp [allLists, ih]

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

def extensionConstant : ℝ := 4 * (4096 * 24 ^ 4)

def reuseBoundConstant (K : ℝ) : ℝ :=
  19531 * (max 1 (extensionConstant * K)) ^ 6

end
end Balanced.ReuseTower

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_ExposureInterleaving
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace Balanced.ExposureInterleaving

def grid {n : ℕ} (i : Fin n) : ℝ := (i.val + 1 : ℝ) / n

def countLE (n : ℕ) (x : ℝ) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => grid i ≤ x)).card

def countLT (n : ℕ) (x : ℝ) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => grid i < x)).card

theorem grid_pos {n : ℕ} (i : Fin n) : 0 < grid i := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt i.isLt
  unfold grid
  positivity

theorem grid_strictMono {n : ℕ} : StrictMono (@grid n) := by
  intro i j hij
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt i.isLt
  apply (div_lt_div_iff_of_pos_right hn).2
  have h : (i.val : ℝ) < (j.val : ℝ) := by exact_mod_cast hij
  linarith

def coverGrid {m : ℕ} (γ : ℝ) (i : Fin m) : ℝ := grid i ^ γ⁻¹

theorem coverGrid_strictMono {m : ℕ} {γ : ℝ} (hγ : 0 < γ) :
    StrictMono (@coverGrid m γ) := by
  intro i j hij
  exact (Real.rpow_lt_rpow_iff (grid_pos i).le (grid_pos j).le
    (inv_pos.mpr hγ)).2 (grid_strictMono hij)

abbrev Step (n m : ℕ) := Fin n ⊕ Fin m

def parameter {n m : ℕ} (γ : ℝ) : Step n m → ℝ
  | Sum.inl i => grid i
  | Sum.inr j => coverGrid γ j

def Before {n m : ℕ} (γ : ℝ) : Step n m → Step n m → Prop
  | Sum.inl i, Sum.inl j => j < i
  | Sum.inl i, Sum.inr j => coverGrid γ j ≤ grid i
  | Sum.inr i, Sum.inl j => grid j < coverGrid γ i
  | Sum.inr i, Sum.inr j => j < i

def remainingD {n m : ℕ} (γ : ℝ) (s : Step n m) : Finset (Fin n) :=
  Finset.univ.filter (fun i => ¬ Before γ (Sum.inl i) s)

def remainingC {n m : ℕ} (γ : ℝ) (s : Step n m) : Finset (Fin m) :=
  Finset.univ.filter (fun i => ¬ Before γ (Sum.inr i) s)

@[simp] theorem remainingC_zero {n : ℕ} (γ : ℝ) (s : Step n 0) :
    remainingC γ s = ∅ := by
  exact Finset.eq_empty_of_forall_notMem (fun i => Fin.elim0 i)

def typeRank {n m : ℕ} : Step n m → ℕ
  | Sum.inl _ => 0
  | Sum.inr _ => 1

theorem before_iff {n m : ℕ} {γ : ℝ} (hγ : 0 < γ) (s t : Step n m) :
    Before γ s t ↔ parameter γ t < parameter γ s ∨
      parameter γ s = parameter γ t ∧ typeRank s < typeRank t := by
  cases s with
  | inl i =>
    cases t with
    | inl j => simp [Before, parameter, typeRank, grid_strictMono.lt_iff_lt]
    | inr j =>
      simp only [Before, parameter, typeRank, Nat.zero_lt_one, and_true]
      exact le_iff_lt_or_eq.trans (or_congr_right eq_comm)
  | inr i =>
    cases t with
    | inl j => simp [Before, parameter, typeRank]
    | inr j =>
      simp [Before, parameter, typeRank, (coverGrid_strictMono hγ).lt_iff_lt]

theorem before_irrefl {n m : ℕ} (γ : ℝ) (s : Step n m) : ¬ Before γ s s := by
  cases s <;> simp [Before]

theorem before_trans {n m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {s t u : Step n m} (hst : Before γ s t) (htu : Before γ t u) :
    Before γ s u := by
  rw [before_iff hγ] at hst htu ⊢
  rcases hst with hst | ⟨hst, hst'⟩ <;> rcases htu with htu | ⟨htu, htu'⟩
  · exact Or.inl (htu.trans hst)
  · exact Or.inl (htu ▸ hst)
  · exact Or.inl (hst ▸ htu)
  · exact Or.inr ⟨hst.trans htu, hst'.trans htu'⟩

theorem before_trichotomy {n m : ℕ} (γ : ℝ) (s t : Step n m) :
    Before γ s t ∨ s = t ∨ Before γ t s := by
  cases s with
  | inl i =>
    cases t with
    | inl j =>
      rcases lt_trichotomy j i with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (congrArg Sum.inl h.symm))
      · exact Or.inr (Or.inr h)
    | inr j =>
      rcases le_or_gt (coverGrid γ j) (grid i) with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
  | inr i =>
    cases t with
    | inl j =>
      rcases lt_or_ge (grid j) (coverGrid γ i) with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    | inr j =>
      rcases lt_trichotomy j i with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (congrArg Sum.inr h.symm))
      · exact Or.inr (Or.inr h)

def previousD {n m : ℕ} (γ : ℝ) (s : Step n m) : Finset (Fin n) :=
  Finset.univ.filter (fun i => Before γ (Sum.inl i) s)

def previousC {n m : ℕ} (γ : ℝ) (s : Step n m) : Finset (Fin m) :=
  Finset.univ.filter (fun i => Before γ (Sum.inr i) s)

@[simp] theorem currentD_not_previousD {n m : ℕ} (γ : ℝ) (i : Fin n) :
    i ∉ previousD γ (Sum.inl i : Step n m) := by
  simp [previousD, before_irrefl]

@[simp] theorem currentC_not_previousC {n m : ℕ} (γ : ℝ) (i : Fin m) :
    i ∉ previousC γ (Sum.inr i : Step n m) := by
  simp [previousC, before_irrefl]

end Balanced.ExposureInterleaving

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_ExposureScheduleOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.ExposureInterleaving

noncomputable section
attribute [local instance] Classical.propDecidable

variable {n m : ℕ} {γ : ℝ}

abbrev beforeStrictTotalOrder (hγ : 0 < γ) :
    IsStrictTotalOrder (Step n m) (Before γ) where
  irrefl := before_irrefl γ
  trans := fun _ _ _ => before_trans hγ
  trichotomous := fun a b hab hba =>
    ((before_trichotomy γ a b).resolve_left hab).resolve_right hba

end
end Balanced.ExposureInterleaving

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_FiniteHistory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Preorder
open scoped MeasureTheory ProbabilityTheory ENNReal BigOperators

namespace Balanced.FiniteHistory

variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

abbrev Prefix (S : Type*) (n : ℕ) := Finset.Iic n → S
abbrev Path (S : Type*) := ℕ → S

def historyKernel (step : ℕ → S → PMF S) (n : ℕ) : Kernel (Prefix S n) S :=
  Kernel.ofFunOfCountable (fun h => (step n (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩)).toMeasure)

instance historyKernel_isMarkov (step : ℕ → S → PMF S) (n : ℕ) :
    IsMarkovKernel (historyKernel step n) :=
  ⟨fun h => by
    change IsProbabilityMeasure ((step n (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩)).toMeasure)
    infer_instance⟩

def pathLaw (step : ℕ → S → PMF S) (s₀ : S) : Measure (Path S) :=
  Kernel.traj (X := fun _ => S) (historyKernel step) 0 (fun _ => s₀)

instance pathLaw_isProbability (step : ℕ → S → PMF S) (s₀ : S) :
    IsProbabilityMeasure (pathLaw step s₀) := by
  unfold pathLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def filtration : Filtration ℕ (inferInstance : MeasurableSpace (Path S)) :=
  Filtration.piLE

def stepObservable (n : ℕ) (f : Prefix S n → S → ℝ) (ω : Path S) : ℝ :=
  f (frestrictLe n ω) (ω (n + 1))

end Balanced.FiniteHistory

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_FiniteHistoryAdditive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Preorder
open scoped MeasureTheory ProbabilityTheory BigOperators

namespace Balanced.FiniteHistory

variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

def additiveTrack (x₀ : ℝ) (f : (n : ℕ) → Prefix S n → S → ℝ)
    (t : ℕ) (ω : Path S) : ℝ :=
  x₀ + ∑ j ∈ Finset.range t, stepObservable j (f j) ω

omit [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S] in
@[simp] theorem additiveTrack_zero (x₀ : ℝ)
    (f : (n : ℕ) → Prefix S n → S → ℝ) (ω : Path S) :
    additiveTrack x₀ f 0 ω = x₀ := by simp [additiveTrack]

omit [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S] in
@[simp] theorem additiveTrack_increment (x₀ : ℝ)
    (f : (n : ℕ) → Prefix S n → S → ℝ) (t : ℕ) (ω : Path S) :
    additiveTrack x₀ f (t + 1) ω - additiveTrack x₀ f t ω =
      stepObservable t (f t) ω := by
  simp only [additiveTrack, Finset.sum_range_succ]
  ring

end Balanced.FiniteHistory

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_FiniteKernelPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace Balanced.FiniteKernelPotential

noncomputable section

variable {X : Type*} [Fintype X]

def advance (K : X → X → ℝ) (w : X → ℝ) (y : X) : ℝ :=
  ∑ x, w x * K x y

def weights (K : ℕ → X → X → ℝ) (w₀ : X → ℝ) : ℕ → X → ℝ
  | 0 => w₀
  | t + 1 => advance (K t) (weights K w₀ t)

@[simp] theorem weights_zero (K : ℕ → X → X → ℝ) (w₀ : X → ℝ) :
    weights K w₀ 0 = w₀ := rfl

@[simp] theorem weights_succ (K : ℕ → X → X → ℝ) (w₀ : X → ℝ) (t : ℕ) :
    weights K w₀ (t + 1) = advance (K t) (weights K w₀ t) := rfl

end
end Balanced.FiniteKernelPotential

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_FiniteUniformTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.FiniteUniformTower

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def fiberMean {Ω Y : Type*} [Fintype Ω] (expose : Ω → Y)
    (g : Ω → ℝ) (z : Y) : ℝ :=
  (∑ x : {x // expose x = z}, g x) / Fintype.card {x // expose x = z}

def average {Ω : Type*} [Fintype Ω] (g : Ω → ℝ) : ℝ :=
  (∑ x, g x) / Fintype.card Ω

end
end Balanced.FiniteUniformTower

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_IndependentTrials
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped MeasureTheory ProbabilityTheory

namespace Balanced
namespace IndependentTrials

universe u v

variable {T : ℕ} {Ω : Type u} [mΩ : MeasurableSpace Ω]
  {A : Fin T → Type v} [∀ i, MeasurableSpace (A i)]

def trialVector (ξ : (i : Fin T) → Ω → A i) (ω : Ω) : (i : Fin T) → A i :=
  fun i ↦ ξ i ω

def prefixIndices (T n : ℕ) : Finset (Fin T) :=
  Finset.univ.filter (fun i ↦ i.val < n)

def prefixFiltration (ξ : (i : Fin T) → Ω → A i)
    (hξ : ∀ i, Measurable (ξ i)) : Filtration ℕ mΩ where
  seq n := (Filtration.piFinset (X := A) (prefixIndices T n)).comap (trialVector ξ)
  mono' n k hnk := by
    apply MeasurableSpace.comap_mono
    apply Filtration.mono
    intro i hi
    simp only [prefixIndices, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact lt_of_lt_of_le hi hnk
  le' n := by
    exact (MeasurableSpace.comap_mono (Filtration.piFinset.le (prefixIndices T n))).trans
      (Measurable.of_eval hξ).comap_le

def doobProcess (ξ : (i : Fin T) → Ω → A i)
    (hξ : ∀ i, Measurable (ξ i)) (Y : Ω → ℝ) (μ : Measure Ω) (n : ℕ) : Ω → ℝ :=
  μ[Y | prefixFiltration ξ hξ n]

def CoordinateOscillation (F : ((i : Fin T) → A i) → ℝ) (c : Fin T → ℝ) : Prop :=
  ∀ i x y, (∀ j, j ≠ i → x j = y j) → |F x - F y| ≤ c i

end IndependentTrials

open IndependentTrials

universe u v

def IndependentTrialJumps : Prop :=
  ∀ (T : ℕ) (Ω : Type u) (_mΩ : MeasurableSpace Ω) (μ : Measure Ω),
  ∀ [IsProbabilityMeasure μ],
  ∀ (A : Fin T → Type v) (_mA : ∀ i, MeasurableSpace (A i)),
  ∀ (ξ : (i : Fin T) → Ω → A i) (hξ : ∀ i, Measurable (ξ i)),
  ∀ (F : ((i : Fin T) → A i) → ℝ), Measurable F →
    ProbabilityTheory.iIndepFun ξ μ →
    Integrable (fun ω ↦ F (trialVector ξ ω)) μ →
  ∀ (c : Fin T → ℝ), (∀ i, 0 ≤ c i) → CoordinateOscillation F c →
    let Y : Ω → ℝ := fun ω ↦ F (trialVector ξ ω)
    let D := doobProcess ξ hξ Y μ
    (D 0 =ᵐ[μ] fun _ ↦ ∫ ω, Y ω ∂μ) ∧
    (D T =ᵐ[μ] Y) ∧
    (∀ i : Fin T,
      (∀ᵐ ω ∂μ, |D (i.val + 1) ω - D i.val ω| ≤ c i) ∧
      (∀ᵐ ω ∂μ, ProbabilityTheory.condVar (prefixFiltration ξ hξ i.val)
        (fun x ↦ D (i.val + 1) x - D i.val x) μ ω ≤ (c i) ^ 2)) ∧
    (∀ (L u : ℝ), 1 ≤ T → 0 < L → (∀ i, c i ≤ L) → 0 < u →
      μ.real {ω | u ≤ |Y ω - ∫ x, Y x ∂μ|} ≤
        2 * Real.exp (-(u ^ 2) / (8 * (T : ℝ) * L ^ 2)))

end Balanced

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_IndependentTrialReassembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory

namespace Balanced.IndependentTrials

variable {T : ℕ} {A : Fin T → Type*}

def reassembleAt (i : Fin T)
    (x : ∀ j : {j : Fin T // j.val < i.val}, A j)
    (z : A i) (v : ∀ j : {j : Fin T // i.val < j.val}, A j) : ∀ j, A j :=
  fun j => if h : j.val < i.val then x ⟨j, h⟩ else
    if e : j = i then e.symm ▸ z else v ⟨j, by omega⟩

end Balanced.IndependentTrials

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_IndependentTrials3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped MeasureTheory ProbabilityTheory

namespace Balanced.IndependentTrials

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure Ω}

section RevealEndpoints

variable {T : ℕ} {A : Fin T → Type*} [∀ i, MeasurableSpace (A i)]
  (ξ : (i : Fin T) → Ω → A i) (hξ : ∀ i, Measurable (ξ i))

@[simp] theorem prefixIndices_zero : prefixIndices T 0 = ∅ := by
  simp [prefixIndices]

@[simp] theorem prefixIndices_full : prefixIndices T T = Finset.univ := by
  ext i
  simp [prefixIndices]

@[simp] theorem prefixFiltration_zero : prefixFiltration ξ hξ 0 = ⊥ := by
  change (Filtration.piFinset (X := A) (prefixIndices T 0)).comap (trialVector ξ) = ⊥
  rw [prefixIndices_zero]
  have hempty : Filtration.piFinset (X := A) ∅ = ⊥ := by
    change MeasurableSpace.comap (Finset.restrict (∅ : Finset (Fin T))) _ = ⊥
    have hconst : Finset.restrict (∅ : Finset (Fin T)) =
        (fun _ : (i : Fin T) → A i ↦ fun i : (∅ : Finset (Fin T)) ↦
          False.elim (Finset.notMem_empty i.val i.property)) := by
      funext x i
      exact False.elim (Finset.notMem_empty i.val i.property)
    rw [hconst, MeasurableSpace.comap_const]
  rw [hempty, MeasurableSpace.comap_bot]

end RevealEndpoints

end Balanced.IndependentTrials

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_PermutationHistoryLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace Balanced.PermutationHistoryLaw

noncomputable section
open Finset PermutationSubsetLaw

variable {α : Type*} [Fintype α] [DecidableEq α]

def histories (I : Finset α) (σ₀ : Equiv.Perm α) : Finset (Equiv.Perm α) :=
  Finset.univ.filter fun σ => ∀ j ∈ I, σ j = σ₀ j

@[simp] theorem mem_histories (I : Finset α) (σ₀ σ : Equiv.Perm α) :
    σ ∈ histories I σ₀ ↔ ∀ j ∈ I, σ j = σ₀ j := by
  simp [histories]

def unused (I : Finset α) (σ₀ : Equiv.Perm α) : Finset α :=
  Finset.univ \ I.map σ₀.toEmbedding

@[simp] theorem card_unused (I : Finset α) (σ₀ : Equiv.Perm α) :
    (unused I σ₀).card = Fintype.card α - I.card := by
  simp [unused, Finset.card_sdiff_of_subset (Finset.subset_univ _)]

end
end Balanced.PermutationHistoryLaw

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_MarkedExposure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators ENNReal
open MeasureTheory

namespace Balanced.MarkedExposure

variable {Ω ι : Type*}

noncomputable def atLeast (s : Finset ι) (E : ι → Set Ω) (r : ℕ) : Set Ω :=
  by
    classical
    exact {ω | r ≤ (s.filter fun i => ω ∈ E i).card}

end Balanced.MarkedExposure

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_MarkedExposureNumerics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.MarkedExposureNumerics

open scoped BigOperators ENNReal Classical
open MeasureTheory

noncomputable def exponentialCost (A B ξ : ℝ) : ℝ :=
  A * Real.log 2 + (1 + ξ) * Real.log (max 1 B)

end Balanced.MarkedExposureNumerics

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
open ExposureInterleaving

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {k m : ℕ}

abbrev Steps (F : Type*) [Fintype F] (k m : ℕ) :=
  Step (k * (Fintype.card F + 1)) m

end
end Balanced.ScheduledCountingExposure

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_SlotProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Balanced.Slots

universe u v

variable {ι : Type u} (V : ι → Type v)

abbrev Assignment := (i : ι) → V i

def law [Fintype ι] [∀ i, Fintype (V i)] [∀ i, MeasurableSpace (V i)] :
    Measure (Assignment V) :=
  Measure.pi (fun i => uniformOn (Set.univ : Set (V i)))

def cylinder (J : Finset ι) (a : Assignment V) : Set (Assignment V) :=
  {ω | ∀ i ∈ J, ω i = a i}

def DependsOn (J : Finset ι) (A : Set (Assignment V)) : Prop :=
  ∀ ω ω', (∀ i ∈ J, ω i = ω' i) → (ω ∈ A ↔ ω' ∈ A)

def pairEvent (i j : ι) (a : V i) (b : V j) : Set (Assignment V) :=
  {ω | ω i = a ∧ ω j = b}

end Balanced.Slots

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_SlotProbability2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace Balanced.Slots

universe u v
variable {ι : Type u} {V : ι → Type v}
variable [Fintype ι] [∀ i, Fintype (V i)] [∀ i, Nonempty (V i)]
variable [∀ i, MeasurableSpace (V i)] [∀ i, MeasurableSingletonClass (V i)]

instance law_isProbabilityMeasure : IsProbabilityMeasure (law V) := by
  unfold law
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

omit [∀ i, MeasurableSingletonClass (V i)] in

theorem independent_coordinates :
    iIndepFun (fun i (ω : Assignment V) => ω i) (law V) := by
  exact iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)

theorem law_cylinder (J : Finset ι) (a : Assignment V) :
    law V (cylinder V J a) = ∏ i ∈ J, (Fintype.card (V i) : ℝ≥0∞)⁻¹ := by
  have hc : cylinder V J a = (J : Set ι).pi (fun i => {a i}) := by
    ext ω
    simp [cylinder, Set.mem_pi]
  rw [hc, law, Measure.pi_pi_finset]
  apply Finset.prod_congr rfl
  intro i hi
  simp [uniformOn_univ]

theorem law_real_cylinder (J : Finset ι) (a : Assignment V) :
    (law V).real (cylinder V J a) = ∏ i ∈ J, (Fintype.card (V i) : ℝ)⁻¹ := by
  simp [Measure.real, law_cylinder, ENNReal.toReal_prod]

omit [∀ i, MeasurableSingletonClass (V i)] in

theorem independent_restrictions (S T : Finset ι) (hST : Disjoint S T) :
    IndepFun (fun (ω : Assignment V) (i : S) => ω i)
      (fun (ω : Assignment V) (i : T) => ω i) (law V) := by
  exact independent_coordinates.indepFun_finset S T hST (fun i => measurable_pi_apply i)

omit [∀ i, MeasurableSpace (V i)] [Fintype ι] [∀ i, Fintype (V i)] [∀ i, MeasurableSingletonClass (V i)] in

theorem dependsOn_representation (S : Finset ι) (A : Set (Assignment V))
    (hA : DependsOn V S A) :
    ∃ B : Set ((i : S) → V i),
      A = (fun (ω : Assignment V) (i : S) => ω i) ⁻¹' B := by
  classical
  let base : Assignment V := fun i => Classical.choice (inferInstance : Nonempty (V i))
  let extend : ((i : S) → V i) → Assignment V :=
    fun f i => if h : i ∈ S then f ⟨i, h⟩ else base i
  refine ⟨{f | extend f ∈ A}, ?_⟩
  ext ω
  apply hA ω (extend (fun i : S => ω i))
  intro i hi
  simp [extend, hi]

theorem independent_events_of_disjoint (S T : Finset ι) (hST : Disjoint S T)
    (A B : Set (Assignment V)) (hA : DependsOn V S A) (hB : DependsOn V T B) :
    IndepSet A B (law V) := by
  classical
  obtain ⟨A', rfl⟩ := dependsOn_representation S A hA
  obtain ⟨B', rfl⟩ := dependsOn_representation T B hB
  have hS : Measurable (fun (ω : Assignment V) (i : S) => ω i) :=
    Measurable.of_eval (fun index => measurable_pi_apply (index : ι))
  have hT : Measurable (fun (ω : Assignment V) (i : T) => ω i) :=
    Measurable.of_eval (fun index => measurable_pi_apply (index : ι))
  exact (indepFun_iff_indepSet_preimage hS hT).mp
    (independent_restrictions S T hST) A' B'
    (Set.toFinite A').measurableSet (Set.toFinite B').measurableSet

theorem law_real_inter_of_disjoint (S T : Finset ι) (hST : Disjoint S T)
    (A B : Set (Assignment V)) (hA : DependsOn V S A) (hB : DependsOn V T B) :
    (law V).real (A ∩ B) = (law V).real A * (law V).real B := by
  have h := (independent_events_of_disjoint S T hST A B hA hB).measure_inter_eq_mul
  simpa [Measure.real, ENNReal.toReal_mul] using congrArg ENNReal.toReal h

omit [∀ i, MeasurableSpace (V i)] [Fintype ι] [∀ i, Fintype (V i)] [∀ i, Nonempty (V i)]
  [∀ i, MeasurableSingletonClass (V i)] in

theorem cylinder_dependsOn (J : Finset ι) (a : Assignment V) :
    DependsOn V J (cylinder V J a) := by
  intro ω ω' h
  constructor <;> intro hc i hi
  · rw [← h i hi]
    exact hc i hi
  · rw [h i hi]
    exact hc i hi

omit [∀ i, MeasurableSpace (V i)] [Fintype ι] [∀ i, Fintype (V i)] [∀ i, Nonempty (V i)]
  [∀ i, MeasurableSingletonClass (V i)] in

theorem DependsOn.compl {J : Finset ι} {A : Set (Assignment V)}
    (h : DependsOn V J A) : DependsOn V J Aᶜ := by
  intro ω ω' heq
  exact not_congr (h ω ω' heq)

omit [∀ i, MeasurableSpace (V i)] [Fintype ι] [∀ i, Fintype (V i)] [∀ i, Nonempty (V i)]
  [∀ i, MeasurableSingletonClass (V i)] in

theorem dependsOn_biInter [DecidableEq ι] {κ : Type*} (E : Finset κ)
    (support : κ → Finset ι) (A : κ → Set (Assignment V))
    (hA : ∀ e ∈ E, DependsOn V (support e) (A e)) :
    DependsOn V (E.biUnion support) (⋂ e ∈ E, A e) := by
  classical
  intro ω ω' heq
  simp only [Set.mem_iInter]
  constructor <;> intro h e he
  · exact (hA e he ω ω' (fun i hi => heq i (Finset.mem_biUnion.mpr ⟨e, he, hi⟩))).mp (h e he)
  · exact (hA e he ω ω' (fun i hi => heq i (Finset.mem_biUnion.mpr ⟨e, he, hi⟩))).mpr (h e he)

omit [∀ i, Nonempty (V i)] in

theorem law_eq_uniformOn : law V = uniformOn (Set.univ : Set (Assignment V)) := by
  classical
  apply Measure.ext_of_singleton
  intro a
  simp only [law, Measure.pi_singleton, uniformOn_univ, Measure.count_singleton,
    one_div, Assignment, Fintype.card_pi, Nat.cast_prod]
  symm
  apply ENNReal.prod_inv_distrib
  intro i hi j hj hij
  exact Or.inr (ENNReal.natCast_ne_top _)

theorem law_coordinate (i : ι) (a : V i) :
    law V {ω | ω i = a} = (Fintype.card (V i) : ℝ≥0∞)⁻¹ := by
  have hm := (measurePreserving_eval
    (fun j => uniformOn (Set.univ : Set (V j))) i).map_eq
  have h := congrArg (fun μ => μ {a}) hm
  simpa [Measure.map_apply (measurable_pi_apply i) (measurableSet_singleton a),
    uniformOn_univ, law, Set.preimage, Set.mem_singleton_iff] using h

theorem law_pairEvent (i j : ι) (hij : i ≠ j) (a : V i) (b : V j) :
    law V (pairEvent V i j a b) =
      (Fintype.card (V i) : ℝ≥0∞)⁻¹ * (Fintype.card (V j) : ℝ≥0∞)⁻¹ := by
  have h := (independent_coordinates (V := V)).indepFun hij
  have heq := h.measure_inter_preimage_eq_mul {a} {b}
    (measurableSet_singleton a) (measurableSet_singleton b)
  change law V (pairEvent V i j a b) =
    law V {ω | ω i = a} * law V {ω | ω j = b} at heq
  rw [heq, law_coordinate, law_coordinate]

theorem law_real_pairEvent (i j : ι) (hij : i ≠ j) (a : V i) (b : V j) :
    (law V).real (pairEvent V i j a b) =
      (Fintype.card (V i) : ℝ)⁻¹ * (Fintype.card (V j) : ℝ)⁻¹ := by
  simp [Measure.real, law_pairEvent i j hij a b, ENNReal.toReal_mul]

theorem law_real_inter_avoidance [DecidableEq ι] {κ : Type*}
    (J : Finset ι) (A : Set (Assignment V)) (hA : DependsOn V J A)
    (E : Finset κ) (support : κ → Finset ι) (bad : κ → Set (Assignment V))
    (hbad : ∀ e ∈ E, DependsOn V (support e) (bad e))
    (hdisjoint : ∀ e ∈ E, Disjoint J (support e)) :
    (law V).real (A ∩ ⋂ e ∈ E, (bad e)ᶜ) =
      (law V).real A * (law V).real (⋂ e ∈ E, (bad e)ᶜ) := by
  classical
  apply law_real_inter_of_disjoint J (E.biUnion support) _ A _ hA
  · exact dependsOn_biInter E support (fun e => (bad e)ᶜ)
      (fun e he => (hbad e he).compl)
  · apply Finset.disjoint_left.mpr
    intro i hiJ hiUnion
    obtain ⟨e, he, hi⟩ := Finset.mem_biUnion.mp hiUnion
    exact Finset.disjoint_left.mp (hdisjoint e he) hiJ hi

omit [∀ i, Nonempty (V i)] in

theorem law_real_finset [DecidableEq ι] (A : Finset (Assignment V)) :
    (law V).real (A : Set (Assignment V)) =
      ∑ _ω ∈ A, (Fintype.card (Assignment V) : ℝ)⁻¹ := by
  classical
  rw [law_eq_uniformOn]
  simp [Measure.real, uniformOn_univ, Measure.count_apply_finset,
    div_eq_mul_inv]

end Balanced.Slots

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_SlotConditionedLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Classical

namespace Balanced.Slots

universe u v
variable {ι : Type u} {V : ι → Type v}
variable [Fintype ι] [∀ i, Fintype (V i)]
variable [∀ i, MeasurableSpace (V i)] [∀ i, MeasurableSingletonClass (V i)]

variable [∀ i, Nonempty (V i)]

theorem law_real_pos_iff_nonempty (G : Finset (Assignment V)) :
    0 < (law V).real (G : Set (Assignment V)) ↔ G.Nonempty := by
  classical
  rw [law_real_finset]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hc : (0 : ℝ) < Fintype.card (Assignment V) := by
    exact_mod_cast Fintype.card_pos
  constructor
  · intro h
    by_contra hn
    have he : G = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    simp [he] at h
  · intro h
    exact mul_pos (by exact_mod_cast h.card_pos) (inv_pos.mpr hc)

end Balanced.Slots

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_TailGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
namespace TailGraph

variable {V I : Type*} [Fintype V] [DecidableEq V] [DecidableEq I]

def slotVertices (slot : V → I) (i : I) : Finset V :=
  Finset.univ.filter (fun v => slot v = i)

def slotSize (slot : V → I) (i : I) : ℕ :=
  (slotVertices slot i).card

def edgeSlots (slot : V → I) (e : Sym2 V) : Finset I :=
  e.toFinset.image slot

noncomputable def edgeWeight (slot : V → I) : Sym2 V → ℝ :=
  Sym2.lift ⟨fun u v =>
    2 / ((slotSize slot (slot u) : ℝ) * (slotSize slot (slot v) : ℝ)),
    fun u v => by simp only [mul_comm]⟩

def slotEdges (G : SimpleGraph V) [DecidableRel G.Adj] (slot : V → I) (i : I) :
    Finset (Sym2 V) :=
  G.edgeFinset.filter (fun e => i ∈ edgeSlots slot e)

def touchingEdges (G : SimpleGraph V) [DecidableRel G.Adj] (slot : V → I)
    (J : Finset I) : Finset (Sym2 V) :=
  G.edgeFinset.filter (fun e => ∃ i ∈ J, i ∈ edgeSlots slot e)

def dependencyEdges (G : SimpleGraph V) [DecidableRel G.Adj] (slot : V → I)
    (e : Sym2 V) : Finset (Sym2 V) :=
  (touchingEdges G slot (edgeSlots slot e)).erase e

def NoWithinSlotEdges (G : SimpleGraph V) (slot : V → I) : Prop :=
  ∀ ⦃u v⦄, G.Adj u v → slot u ≠ slot v

end TailGraph
end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_TailConditioning
attribute [-instance] _root_.OAI.Balanced.Slots.law_isProbabilityMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
namespace TailConditioning

universe u v
variable {I : Type u} (Q : I → Type v)

def independentTransversals (G : SimpleGraph (Sigma Q)) : Set (Slots.Assignment Q) :=
  {ω | ∀ i j, ¬ G.Adj ⟨i, ω i⟩ ⟨j, ω j⟩}

noncomputable def conditionalCylinder [Fintype I] [∀ i, Fintype (Q i)]
    [∀ i, MeasurableSpace (Q i)]
    (G : SimpleGraph (Sigma Q)) (J : Finset I) (a : Slots.Assignment Q) : ℝ :=
  (Slots.law Q).real (Slots.cylinder Q J a ∩ independentTransversals Q G) /
    (Slots.law Q).real (independentTransversals Q G)

end TailConditioning
end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_TailEvents
attribute [-instance] _root_.OAI.Balanced.Slots.law_isProbabilityMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.TailGraph

variable {I : Type*} (Q : I → Type*)

def edgeEvent (e : Sym2 (Sigma Q)) : Set (Slots.Assignment Q) :=
  {ω | ∀ v ∈ e, ω v.1 = v.2}

end Balanced.TailGraph

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_TailGraphWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace Balanced
open scoped _root_.Balanced
namespace TailGraph

variable {V I : Type*} [Fintype V] [DecidableEq V] [DecidableEq I]

omit [DecidableEq V] in
@[simp] theorem mem_slotVertices (slot : V → I) (i : I) (v : V) :
    v ∈ slotVertices slot i ↔ slot v = i := by
  simp [slotVertices]

omit [DecidableEq V] in
@[simp] theorem edgeWeight_mk (slot : V → I) (u v : V) :
    edgeWeight slot s(u, v) =
      2 / ((slotSize slot (slot u) : ℝ) * (slotSize slot (slot v) : ℝ)) := rfl

omit [DecidableEq V] in
theorem edgeWeight_nonneg (slot : V → I) (e : Sym2 V) :
    0 ≤ edgeWeight slot e := by
  induction e using Sym2.inductionOn with
  | _ u v => simp only [edgeWeight_mk]; positivity

omit [Fintype V] in
theorem edgeSlots_card_le_two (slot : V → I) (e : Sym2 V) :
    (edgeSlots slot e).card ≤ 2 := by
  apply Finset.card_image_le.trans
  rw [Sym2.card_toFinset]
  split_ifs <;> omega

omit [DecidableEq V] in
theorem edgeWeight_le_of_mem (slot : V → I) (L : ℕ) (hL : 0 < L)
    (hsize : ∀ i, L ≤ slotSize slot i) (u : V) (e : Sym2 V) (hu : u ∈ e) :
    edgeWeight slot e ≤ 2 / ((slotSize slot (slot u) : ℝ) * (L : ℝ)) := by
  rw [← Sym2.other_spec hu, edgeWeight_mk]
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have husize : (0 : ℝ) < slotSize slot (slot u) := by
    exact_mod_cast lt_of_lt_of_le hL (hsize (slot u))
  apply div_le_div_of_nonneg_left (by norm_num)
  · positivity
  · exact mul_le_mul_of_nonneg_left (by exact_mod_cast hsize (slot (Sym2.Mem.other hu)))
      husize.le

theorem incidence_weight_le (G : SimpleGraph V) [DecidableRel G.Adj] (slot : V → I)
    (L : ℕ) (hL : 0 < L) (hsize : ∀ i, L ≤ slotSize slot i) (u : V) :
    ∑ e ∈ G.incidenceFinset u, edgeWeight slot e ≤
      (G.degree u : ℝ) * (2 / ((slotSize slot (slot u) : ℝ) * (L : ℝ))) := by
  classical
  calc
    _ ≤ ∑ _e ∈ G.incidenceFinset u,
        2 / ((slotSize slot (slot u) : ℝ) * (L : ℝ)) := by
      apply Finset.sum_le_sum
      intro e he
      exact edgeWeight_le_of_mem slot L hL hsize u e
        ((G.mem_incidenceFinset u _).mp he).2
    _ = _ := by simp

omit [DecidableEq V] in
theorem edgeWeight_le_half (slot : V → I) (hsize : ∀ i, 3 ≤ slotSize slot i)
    (e : Sym2 V) : edgeWeight slot e ≤ 1 / 2 := by
  induction e using Sym2.inductionOn with
  | _ u v =>
    rw [edgeWeight_mk]
    have hu : (3 : ℝ) ≤ slotSize slot (slot u) := by exact_mod_cast hsize (slot u)
    have hv : (3 : ℝ) ≤ slotSize slot (slot v) := by exact_mod_cast hsize (slot v)
    have hp : (0 : ℝ) < (slotSize slot (slot u) : ℝ) * (slotSize slot (slot v) : ℝ) := by
      positivity
    apply (div_le_iff₀ hp).2
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ (slotSize slot (slot u) : ℝ) - 3 by linarith)
      (show (0 : ℝ) ≤ (slotSize slot (slot v) : ℝ) - 3 by linarith)]

theorem mem_dependencyEdges_iff (G : SimpleGraph V) [DecidableRel G.Adj]
    (slot : V → I) (e f : Sym2 V) :
    f ∈ dependencyEdges G slot e ↔
      f ∈ G.edgeFinset ∧ f ≠ e ∧ ¬ Disjoint (edgeSlots slot e) (edgeSlots slot f) := by
  classical
  simp only [dependencyEdges, Finset.mem_erase, touchingEdges, Finset.mem_filter]
  rw [Finset.not_disjoint_iff]
  aesop

def liftEdges (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset (Sym2 V)) :
    Finset G.edgeSet := Finset.univ.filter (fun e => e.val ∈ s)

@[simp] theorem mem_liftEdges (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Finset (Sym2 V)) (e : G.edgeSet) :
    e ∈ liftEdges G s ↔ e.val ∈ s := by simp [liftEdges]

theorem sum_liftEdges (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Finset (Sym2 V)) (hs : s ⊆ G.edgeFinset) (w : Sym2 V → ℝ) :
    ∑ e ∈ liftEdges G s, w e.val = ∑ e ∈ s, w e := by
  classical
  apply Finset.sum_bij (fun e _ => e.val)
  · intro e he
    exact (mem_liftEdges G s e).mp he
  · intro e he f hf hef
    exact Subtype.ext hef
  · intro e he
    refine ⟨⟨e, G.mem_edgeFinset.mp (hs he)⟩, ?_, rfl⟩
    exact (mem_liftEdges G s _).mpr he
  · intro e he
    rfl

theorem touchingEdges_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    (slot : V → I) (J : Finset I) : touchingEdges G slot J ⊆ G.edgeFinset :=
  Finset.filter_subset _ _

theorem dependencyEdges_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    (slot : V → I) (e : Sym2 V) : dependencyEdges G slot e ⊆ G.edgeFinset :=
  (Finset.erase_subset _ _).trans (touchingEdges_subset G slot (edgeSlots slot e))

end TailGraph
end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_TailEvents2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
open MeasureTheory

namespace Balanced.TailGraph

variable {I : Type*} {Q : I → Type*}
variable [Fintype I] [DecidableEq I]
variable [∀ i, Fintype (Q i)] [∀ i, DecidableEq (Q i)] [∀ i, Nonempty (Q i)]
variable [∀ i, MeasurableSpace (Q i)] [∀ i, MeasurableSingletonClass (Q i)]

omit [Fintype I] [DecidableEq I] [∀ index, Fintype (Q index)]
  [∀ index, DecidableEq (Q index)] [∀ index, Nonempty (Q index)]
  [∀ index, MeasurableSpace (Q index)] [∀ index, MeasurableSingletonClass (Q index)] in
@[simp] theorem edgeEvent_mk (u v : Sigma Q) :
    edgeEvent Q s(u, v) = Slots.pairEvent Q u.1 v.1 u.2 v.2 := by
  ext ω
  simp only [edgeEvent, Slots.pairEvent, Set.mem_ofPred_eq, Sym2.mem_iff]
  constructor
  · intro h
    exact ⟨h u (Or.inl rfl), h v (Or.inr rfl)⟩
  · rintro ⟨hu, hv⟩ w (rfl | rfl)
    · exact hu
    · exact hv

omit [∀ index, Nonempty (Q index)] [∀ index, MeasurableSpace (Q index)]
  [∀ index, MeasurableSingletonClass (Q index)] in
@[simp] theorem slotSize_sigma (i : I) :
    slotSize (Sigma.fst : Sigma Q → I) i = Fintype.card (Q i) := by
  have heq : slotVertices (Sigma.fst : Sigma Q → I) i =
      Finset.univ.image (Sigma.mk i : Q i → Sigma Q) := by
    ext ⟨j, v⟩
    constructor
    · intro h
      have hji : j = i := (mem_slotVertices _ _ _).mp h
      subst j
      simp
    · intro h
      obtain ⟨a, _, ha⟩ := Finset.mem_image.mp h
      apply (mem_slotVertices _ _ _).mpr
      exact (congrArg Sigma.fst ha).symm
  unfold slotSize
  rw [heq, Finset.card_image_of_injective _ (by intro a b h; exact eq_of_heq (Sigma.mk.inj_iff.mp h).2)]
  exact Finset.card_univ

omit [Fintype I] [∀ index, Fintype (Q index)] [∀ index, Nonempty (Q index)]
  [∀ index, MeasurableSpace (Q index)] [∀ index, MeasurableSingletonClass (Q index)] in
theorem edgeEvent_dependsOn (e : Sym2 (Sigma Q)) :
    Slots.DependsOn Q (edgeSlots Sigma.fst e) (edgeEvent Q e) := by
  intro ω ω' heq
  constructor <;> intro h v hv
  · rw [← heq v.1 (Finset.mem_image.mpr ⟨v, by simpa using hv, rfl⟩)]
    exact h v hv
  · rw [heq v.1 (Finset.mem_image.mpr ⟨v, by simpa using hv, rfl⟩)]
    exact h v hv

theorem law_real_edgeEvent (G : SimpleGraph (Sigma Q))
    (hno : NoWithinSlotEdges G Sigma.fst) (e : Sym2 (Sigma Q)) (he : e ∈ G.edgeSet) :
    (Slots.law Q).real (edgeEvent Q e) = edgeWeight Sigma.fst e / 2 := by
  induction e using Sym2.inductionOn with
  | _ u v =>
    rw [edgeEvent_mk, Slots.law_real_pairEvent _ _ (hno (G.mem_edgeSet.mp he)),
      edgeWeight_mk, slotSize_sigma, slotSize_sigma]
    ring

end Balanced.TailGraph

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_TailConditioning2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
open MeasureTheory

namespace Balanced
open scoped _root_.Balanced
namespace TailConditioning

universe u v
variable {I : Type u} {Q : I → Type v}

theorem slotSize_sigma [Fintype I] [DecidableEq I] [∀ i, Fintype (Q i)]
    [∀ i, DecidableEq (Q i)] (i : I) :
    TailGraph.slotSize (Sigma.fst : Sigma Q → I) i = Fintype.card (Q i) := by
  let e : {v : Sigma Q // v.1 = i} ≃ Q i :=
    { toFun := fun v => v.2 ▸ v.1.2
      invFun := fun a => ⟨⟨i, a⟩, rfl⟩
      left_inv := by
        rintro ⟨⟨j, a⟩, h⟩
        dsimp at h
        subst j
        rfl
      right_inv := by intro a; rfl }
  simpa [TailGraph.slotSize, TailGraph.slotVertices, Fintype.card_subtype] using Fintype.card_congr e

end TailConditioning
end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_TailPrescriptions
attribute [-instance] _root_.OAI.Balanced.Slots.law_isProbabilityMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.TailConditioning

universe u v w
variable {I : Type u} (Q : I → Type v) {V : Type w}

def ambientCylinder (embed : ∀ i, Q i → V) (J : Finset I) (a : I → V) :
    Set (Slots.Assignment Q) :=
  {ω | ∀ i ∈ J, embed i (ω i) = a i}

noncomputable def conditionalAmbientCylinder [Fintype I] [∀ i, Fintype (Q i)]
    [∀ i, MeasurableSpace (Q i)] (G : SimpleGraph (Sigma Q))
    (embed : ∀ i, Q i → V) (J : Finset I) (a : I → V) : ℝ :=
  (Slots.law Q).real (ambientCylinder Q embed J a ∩ independentTransversals Q G) /
    (Slots.law Q).real (independentTransversals Q G)

end Balanced.TailConditioning

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_UncoveredExchange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace Balanced.UncoveredExchange

def missed {Point Line : Type*} (A : Finset Point) (D : Finset Line)
    (On : Point → Line → Prop) [DecidableRel On] : Finset Point :=
  A.filter (fun p => ∀ l ∈ D, ¬ On p l)

end Balanced.UncoveredExchange

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_UniformKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced
namespace UniformKernel

open Finset

variable {U V W : Type*} [Fintype U] [Fintype V]

noncomputable def fiberMass (κ : U → V → W → ℝ) (v : V) (w : W) : ℝ :=
  (∑ u, κ u v w) / ((Fintype.card U : ℝ) * Fintype.card V)

end UniformKernel
end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_UniformOrderedSubset
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.UniformOrderedSubset

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq ι] [DecidableEq α]

def imageFiberEquiv (C : Finset α) :
    {f : ι ↪ α // Finset.univ.map f = C} ≃ (ι ≃ C) where
  toFun f := Equiv.ofBijective
    (fun i => (⟨f.val i, by
      exact (Finset.ext_iff.mp f.property _).mp
        (Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩)⟩ : C))
    ⟨fun _ _ h => f.val.injective (congrArg Subtype.val h), by
      intro x
      have hx : x.val ∈ Finset.univ.map f.val :=
        (Finset.ext_iff.mp f.property _).mpr x.property
      obtain ⟨i, _, hi⟩ := Finset.mem_map.mp hx
      exact ⟨i, Subtype.ext hi⟩⟩
  invFun e := ⟨e.toEmbedding.trans (Function.Embedding.subtype _), by
    ext x
    simp only [Finset.mem_map, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      exact (e i).property
    · intro hx
      exact ⟨e.symm ⟨x, hx⟩, by simp⟩⟩
  left_inv f := by
    apply Subtype.ext
    apply Function.Embedding.ext
    intro i
    rfl
  right_inv e := by
    apply Equiv.ext
    intro i
    rfl

def enumerationEquiv (e : ι ≃ α) : Equiv.Perm α ≃ (ι ≃ α) where
  toFun p := e.trans p
  invFun c := e.symm.trans c
  left_inv p := by ext x; simp
  right_inv c := by ext i; simp

end
end Balanced.UniformOrderedSubset

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_UniformThreshold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

open Filter Topology

universe u

structure FiniteFieldPresentation where
  carrier : Type u
  field : Field carrier
  finite : Fintype carrier
  decidable : DecidableEq carrier

attribute [instance] FiniteFieldPresentation.field FiniteFieldPresentation.finite
  FiniteFieldPresentation.decidable

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_VacantBins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.VacantBins

open scoped BigOperators

variable {I A : Type*} [Fintype I] [Fintype A] [DecidableEq I] [DecidableEq A]

noncomputable def missed (f : I → A) : Finset A := by
  classical
  exact Finset.univ.filter (fun a => ∀ i, f i ≠ a)

noncomputable def missedCount (f : I → A) : ℕ := (missed f).card

omit [DecidableEq I] in
@[simp] theorem mem_missed (f : I → A) (a : A) :
    a ∈ missed f ↔ ∀ i, f i ≠ a := by
  classical
  simp [missed]

def avoidingEquiv (a : A) :
    {f : I → A // ∀ i, f i ≠ a} ≃ (I → {b : A // b ≠ a}) where
  toFun f i := ⟨f.val i, f.property i⟩
  invFun f := ⟨fun i => (f i).val, fun i => (f i).property⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def uniformMean (Y : (I → A) → ℝ) : ℝ :=
  (∑ f : I → A, Y f) / Fintype.card (I → A)

end Balanced.VacantBins

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_WithoutReplacementCoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace Balanced.WithoutReplacement

variable {α : Type*} [DecidableEq α]

def swapSet (x y : α) (S : Finset α) : Finset α :=
  (Equiv.swap x y).finsetCongr S

@[simp] theorem mem_swapSet (x y z : α) (S : Finset α) :
    z ∈ swapSet x y S ↔ Equiv.swap x y z ∈ S := by
  simp [swapSet, Finset.mem_map_equiv]

@[simp] theorem card_swapSet (x y : α) (S : Finset α) :
    (swapSet x y S).card = S.card := by
  simp [swapSet]

@[simp] theorem swapSet_involutive (x y : α) (S : Finset α) :
    swapSet x y (swapSet x y S) = S := by
  ext z
  simp

@[simp] theorem swapSet_insert (x y z : α) (S : Finset α) :
    swapSet x y (insert z S) = insert (Equiv.swap x y z) (swapSet x y S) := by
  simp [swapSet]

noncomputable def completionAverage (U : Finset α) (r : ℕ) (x : α)
    (f : Finset α → ℝ) : ℝ :=
  𝔼 S ∈ (U.erase x).powersetCard r, f (insert x S)

noncomputable def finiteVariance {β : Type*} (s : Finset β) (f : β → ℝ) : ℝ :=
  𝔼 x ∈ s, (f x - (𝔼 y ∈ s, f y)) ^ 2

end Balanced.WithoutReplacement

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_DetectionThresholds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter Set
open scoped Topology

namespace Balanced.ProfileDetection

def cutoffDetection {Ω : Type*} (z h : Ω → ℝ) (n : ℕ) : Set Ω :=
  {x | 1 / ((n : ℝ) + 1) < z x ∧ z x < 1 ∧ 3 / ((n : ℝ) + 1) < |h x|}

def positiveDetection {Ω : Type*} (z h : Ω → ℝ) : Set Ω :=
  {x | 0 < z x ∧ z x < 1 ∧ h x ≠ 0}

end Balanced.ProfileDetection

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

abbrev Profile := ℕ × ℕ → ℝ

def IsBoundedProfile (M : ℝ) (p : Profile) : Prop :=
  (∀ ij, 0 ≤ p ij) ∧ HasSum p 1 ∧
  Summable (fun ij => ((ij.1 + ij.2 : ℕ) : ℝ) * p ij) ∧
  (∑' ij, ((ij.1 + ij.2 : ℕ) : ℝ) * p ij) ≤ M

def deletionInvisible (P x : Profile) : Prop :=
  ∀ i j, x (i, j) = if i = 0 then 0 else P (i - 1, j)

def coverInvisible (P x : Profile) : Prop :=
  ∀ i j, x (i, j) = if j = 0 then 0 else P (i, j - 1)

def deletionVisible (P : Profile) : Set Profile := {x | ¬ deletionInvisible P x}
def coverVisible (P : Profile) : Set Profile := {x | ¬ coverInvisible P x}

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def profileDirac (p : Profile) : FiniteMeasure Profile :=
  ⟨Measure.dirac p, inferInstance⟩

universe u

end Balanced

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileEmpirical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Finset

namespace Balanced
open scoped _root_.Balanced

theorem hasSum_card_fibers {α β : Type*} [DecidableEq β]
    (s : Finset α) (f : α → β) :
    HasSum (fun b => ((s.filter (fun a => f a = b)).card : ℝ)) (s.card : ℝ) := by
  classical
  have hsum : (∑ b ∈ s.image f, ((s.filter (fun a => f a = b)).card : ℝ)) = s.card := by
    exact_mod_cast (Finset.card_eq_sum_card_image f s).symm
  rw [← hsum]
  apply hasSum_sum_of_ne_finset_zero
  intro b hb
  have hempty : s.filter (fun a => f a = b) = ∅ := by
    apply Finset.ext
    intro a
    simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
    rintro ⟨ha, hab⟩
    exact hb (Finset.mem_image.mpr ⟨a, ha, hab⟩)
  simp only [hempty, Finset.card_empty, Nat.cast_zero]

theorem hasSum_normalized_card_fibers {α β : Type*} [DecidableEq β]
    (s : Finset α) (hs : s.Nonempty) (f : α → β) :
    HasSum (fun b => ((s.filter (fun a => f a = b)).card : ℝ) / (s.card : ℝ)) 1 := by
  have hc : (s.card : ℝ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr hs
  simpa only [div_self hc] using (hasSum_card_fibers s f).div_const (s.card : ℝ)

theorem hasSum_weighted_card_fibers {α β : Type*} [DecidableEq β]
    (s : Finset α) (f : α → β) (w : β → ℝ) :
    HasSum (fun b => w b * ((s.filter (fun a => f a = b)).card : ℝ))
      (∑ a ∈ s, w (f a)) := by
  classical
  have hsupport (b : β) (hb : b ∉ s.image f) :
      w b * ((s.filter (fun a => f a = b)).card : ℝ) = 0 := by
    have hempty : s.filter (fun a => f a = b) = ∅ := by
      apply Finset.ext
      intro a
      simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
      rintro ⟨ha, hab⟩
      exact hb (Finset.mem_image.mpr ⟨a, ha, hab⟩)
    simp [hempty]
  have hsum : (∑ b ∈ s.image f, w b * ((s.filter (fun a => f a = b)).card : ℝ)) =
      ∑ a ∈ s, w (f a) := by
    rw [← Finset.sum_fiberwise_of_maps_to (fun a ha => Finset.mem_image_of_mem f ha)
      (fun a => w (f a))]
    apply Finset.sum_congr rfl
    intro b hb
    calc
      w b * ((s.filter (fun a => f a = b)).card : ℝ) =
          ∑ a ∈ s.filter (fun a => f a = b), w b := by simp [mul_comm]
      _ = ∑ a ∈ s.filter (fun a => f a = b), w (f a) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [(Finset.mem_filter.mp ha).2]
  rw [← hsum]
  exact hasSum_sum_of_ne_finset_zero hsupport

end Balanced

end

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

def finiteDirac {X : Type*} [MeasurableSpace X] (x : X) : FiniteMeasure X :=
  ⟨Measure.dirac x, inferInstance⟩

end Balanced

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileDetection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter
open scoped Topology

namespace Balanced.ProfileDetection

noncomputable def profileExponent (n : ℕ × ℕ) : ℝ :=
  n.1 + Real.sqrt 2 * n.2

end Balanced.ProfileDetection

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileIdentifiability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace Balanced.ProfileIdentifiability

noncomputable def laplaceSeries {ι : Type*} (a w : ι → ℝ) (s : ℝ) : ℝ :=
  ∑' i, a i * Real.exp (-w i * s)

end Balanced.ProfileIdentifiability

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileDetectionBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter Set
open scoped Topology

namespace Balanced.ProfileDetectionBridge

noncomputable def planeTest (P : ℕ × ℕ → ℝ) (z : ℝ) : ℝ :=
  ∑' a : ℕ × ℕ, P a * z ^ ((a.1 : ℝ) + Real.sqrt 2 * a.2)

noncomputable def dTest (x : ℕ × ℕ → ℝ) (z : ℝ) : ℝ :=
  ∑' a : ℕ × ℕ, x a * z ^ ((a.1 : ℝ) - 1 + Real.sqrt 2 * a.2)

noncomputable def cTest (x : ℕ × ℕ → ℝ) (z : ℝ) : ℝ :=
  ∑' a : ℕ × ℕ, x a * z ^ ((a.1 : ℝ) + Real.sqrt 2 * ((a.2 : ℝ) - 1))

end Balanced.ProfileDetectionBridge

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileParameterLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set Filter
open scoped Topology

namespace Balanced.ProfileParameterLaw

noncomputable def parameterLaw (γ : ℝ) : Measure ℝ :=
  (volume.restrict (Ioo 0 1)).withDensity (fun z : ℝ => ENNReal.ofReal (γ * z ^ (γ - 1)))

@[simp] theorem parameterLaw_one : parameterLaw 1 = volume.restrict (Ioo 0 1) := by
  simp [parameterLaw]

end Balanced.ProfileParameterLaw

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileDetectionLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set Filter
open scoped Topology

namespace Balanced.ProfileDetectionLimit

open ProfileDetection ProfileDetectionBridge ProfileParameterLaw

noncomputable def dDiscrepancy (P : Profile) (p : Profile × ℝ) : ℝ :=
  dTest p.1 p.2 - planeTest P p.2

noncomputable def cDiscrepancy (P : Profile) (p : Profile × ℝ) : ℝ :=
  cTest p.1 p.2 - planeTest P p.2

end Balanced.ProfileDetectionLimit

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

def cutoffMass (P : Profile) (νD νC : FiniteMeasure Profile) (n : ℕ) : ℝ :=
  ((νD : Measure Profile).prod (parameterLaw 1)).real
      (cutoffDetection Prod.snd (dDiscrepancy P) n) +
    ((νC : Measure Profile).prod (parameterLaw (Real.sqrt 2))).real
      (cutoffDetection Prod.snd (cDiscrepancy P) n)

end Balanced.ProfileClassMargin

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter
open scoped Topology BoundedContinuousFunction

namespace Balanced
open scoped _root_.Balanced

def clippedProfileCoordinate (ij : ℕ × ℕ) : Profile →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => max 0 (min 1 (x ij)))
    (continuous_const.max (continuous_const.min (continuous_apply ij))) 1
    (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)]
      exact max_le (by norm_num) (min_le_left _ _))

@[simp] theorem clippedProfileCoordinate_apply (ij : ℕ × ℕ) (x : Profile) :
    clippedProfileCoordinate ij x = max 0 (min 1 (x ij)) := rfl

def profileCoordinateDeviation (ij : ℕ × ℕ) : Profile →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => min 1 |x ij - clippedProfileCoordinate ij x|)
    (continuous_const.min ((continuous_apply ij).sub
      (clippedProfileCoordinate ij).continuous).abs) 1
    (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (by norm_num) (abs_nonneg _))]
      exact min_le_left _ _)

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileGridMeasures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ENNReal Topology BigOperators
open MeasureTheory Set Filter TopologicalSpace

namespace Balanced.ProfileParameterGrids

noncomputable def rightGridMeasure (n : ℕ) : Measure ℝ :=
  ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ •
    ∑ i ∈ Finset.range (n + 1), Measure.dirac (((i + 1 : ℕ) : ℝ) / (n + 1))

instance rightGrid_probability (n : ℕ) : IsProbabilityMeasure (rightGridMeasure n) := by
  constructor
  simp only [rightGridMeasure, Measure.smul_apply, Measure.coe_finsetSum,
    Finset.sum_apply, Measure.dirac_apply_of_mem (Set.mem_univ _),
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by positivity) (by finiteness)

noncomputable def rightGrid (n : ℕ) : ProbabilityMeasure ℝ :=
  ⟨rightGridMeasure n, (by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩

noncomputable def unitUniform : ProbabilityMeasure ℝ :=
  ⟨volume.restrict (Icc (0 : ℝ) 1), by constructor; simp⟩

noncomputable def powerGrid (γ : ℝ) (hγ : 0 ≤ γ) (n : ℕ) : ProbabilityMeasure ℝ :=
  (rightGrid n).map
    (Real.continuous_rpow_const (inv_nonneg.mpr hγ)).measurable.aemeasurable

noncomputable def powerUniform (γ : ℝ) (hγ : 0 ≤ γ) : ProbabilityMeasure ℝ :=
  unitUniform.map
    (Real.continuous_rpow_const (inv_nonneg.mpr hγ)).measurable.aemeasurable

end Balanced.ProfileParameterGrids

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileWeakDetection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter Set TopologicalSpace
open scoped Topology ENNReal NNReal

namespace Balanced.ProfileWeakDetection

variable {X Y I : Type*} [MeasurableSpace X] [MeasurableSpace Y]

def detectionSet (z h : X → ℝ) (η ε : ℝ) : Set X :=
  {x | η < z x ∧ z x < 1 ∧ ε < |h x|}

end Balanced.ProfileWeakDetection

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

abbrev BoundedSpace (M : ℝ) := {p : Profile | IsBoundedProfile M p}

def clippedParameter (z : ℝ) : Icc (0 : ℝ) 1 := projIcc 0 1 zero_le_one z

def planeClipped {M : ℝ} (p : BoundedSpace M × ℝ) : ℝ :=
  ∑' ij, p.1.val ij * (clippedParameter p.2).val ^
    ((ij.1 : ℝ) + Real.sqrt 2 * ij.2)

def dClipped {M : ℝ} (p : BoundedSpace M × ℝ) : ℝ :=
  ∑' ij, p.1.val ij * (if ij.1 ≠ 0 then (clippedParameter p.2).val ^
    (((ij.1 - 1 : ℕ) : ℝ) + Real.sqrt 2 * ij.2) else 0)

def cClipped {M : ℝ} (p : BoundedSpace M × ℝ) : ℝ :=
  ∑' ij, p.1.val ij * (if ij.2 ≠ 0 then (clippedParameter p.2).val ^
    ((ij.1 : ℝ) + Real.sqrt 2 * (ij.2 - 1 : ℕ)) else 0)

def clippedDiscrepancy {M : ℝ} (G : BoundedSpace M × ℝ → ℝ)
    (p : BoundedSpace M × (BoundedSpace M × ℝ)) : ℝ :=
  G p.2 - planeClipped (p.1,p.2.2)

end Balanced.ProfileGridDetection

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileOrderComplements
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace Balanced.ProfileOrderComplements

universe u

section Finite
variable {α : Type*} [Fintype α] [DecidableEq α]

def future (I : Finset α) (i : α) : Finset α := Finset.univ.erase i \ I

@[simp] theorem current_not_future (I : Finset α) (i : α) : i ∉ future I i := by
  simp [future]

end Finite

end Balanced.ProfileOrderComplements

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

universe u

def threshold (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

end Balanced.ProfileScheduledMargin

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_Selection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter
open scoped Topology

namespace Balanced
namespace Selection

noncomputable section
attribute [local instance] Classical.propDecidable

structure Input (I : Type*) (V : Type*) where
  graph : SimpleGraph V
  slot : V → I
  exceptional : V → Finset V

variable {I V : Type*} [Fintype I] [Fintype V]

def slotVertices (G : Input I V) (i : I) : Finset V :=
  Finset.univ.filter (fun v => G.slot v = i)

def neighbors (G : Input I V) (v : V) : Finset V :=
  Finset.univ.filter (G.graph.Adj v)

def GraphBounds (G : Input I V) (q : ℕ) (c C : ℝ) : Prop :=
  Fintype.card I = 2 * (q + 1) ∧
  (∀ v w, G.slot v = G.slot w → ¬ G.graph.Adj v w) ∧
  (∀ i, c * q ≤ ((slotVertices G i).card : ℝ) ∧ (slotVertices G i).card ≤ q) ∧
  (∀ v, ((neighbors G v).card : ℝ) ≤ C * q) ∧
  (∀ v i, (((neighbors G v) ∩ slotVertices G i).card : ℝ) ≤
    (q : ℝ) ^ (1 / 8 : ℝ)) ∧
  (∀ v, ((G.exceptional v).card : ℝ) ≤ (q : ℝ) ^ (1 / 8 : ℝ)) ∧
  (∀ v w, w ∉ G.exceptional v →
    (((neighbors G v) ∩ neighbors G w).card : ℝ) ≤ (q : ℝ) ^ (1 / 8 : ℝ)) ∧
  (∀ v w, w ∈ G.exceptional v → G.graph.Adj v w ∨ G.slot v = G.slot w)

def IsIndependentTransversal (G : Input I V) (a : I → V) : Prop :=
  (∀ i, G.slot (a i) = i) ∧ ∀ i j, i ≠ j → ¬ G.graph.Adj (a i) (a j)

structure OutputLaw (G : Input I V) where
  weight : (I → V) → ℝ
  nonnegative : ∀ a, 0 ≤ weight a
  mass_le_one : (∑ a, weight a) ≤ 1
  supported : ∀ a, 0 < weight a → IsIndependentTransversal G a

def successMass {G : Input I V} (law : OutputLaw G) : ℝ := ∑ a, law.weight a

def cylinderMass {G : Input I V} (law : OutputLaw G) (J : Finset I)
    (prescribed : I → V) : ℝ :=
  ∑ a ∈ Finset.univ.filter (fun a : I → V => ∀ i ∈ J, a i = prescribed i), law.weight a

variable {q : ℕ} {P D L : Type*} [Fintype P] [Fintype D] [Fintype L]

def LineAssignment (G : Input I V) (A : FiniteAffine.Plane q P D L)
    (index : I ≃ (D × Bool)) (line : V → L) : Prop :=
  (∀ v, A.direction (line v) = (index (G.slot v)).1) ∧
  (∀ v w, G.slot v = G.slot w → line v = line w → v = w)

def TrackedSets (A : FiniteAffine.Plane q P D L) (T : L → Finset P) (c₀ : ℝ) : Prop :=
  ∀ ℓ, T ℓ ⊆ A.linePoints ℓ ∧ c₀ * q ≤ ((T ℓ).card : ℝ)

def finalTracked (A : FiniteAffine.Plane q P D L) (line : V → L)
    (T : L → Finset P) (a : I → V) (ℓ : L) : Finset P :=
  (T ℓ).filter (fun p => ∀ i, line (a i) ≠ ℓ → ¬ A.incident p (line (a i)))

def occupancyFailureMass {G : Input I V} (law : OutputLaw G)
    (A : FiniteAffine.Plane q P D L) (line : V → L) (T : L → Finset P) (ρ : ℝ) : ℝ :=
  ∑ a ∈ Finset.univ.filter (fun a : I → V =>
    ∃ ℓ : L, ((finalTracked A line T a ℓ).card : ℝ) < ρ * q), law.weight a

end
end Selection

def SelectionStatement.{u, v, w} : Prop :=
  ∀ c C c₀ : ℝ, 0 < c → 0 < C → 0 < c₀ → c₀ ≤ 1 →
    ∃ K ρ : ℝ, ∃ ε : ℕ → ℝ, ∃ q₀ : ℕ,
      0 < K ∧ 0 < ρ ∧ (∀ q, 0 ≤ ε q) ∧ Tendsto ε atTop (𝓝 0) ∧
      ∀ q : ℕ, q₀ ≤ q →
      ∀ (I : Type u) (V : Type v) [Fintype I] [Fintype V],
      ∀ G : Selection.Input I V, Selection.GraphBounds G q c C →
      ∃ law : Selection.OutputLaw G,
        1 - ε q ≤ Selection.successMass law ∧
        (∀ (J : Finset I) (prescribed : I → V),
          Selection.cylinderMass law J prescribed ≤ (K / (q : ℝ)) ^ J.card) ∧
        (∀ (P D L : Type w) [Fintype P] [Fintype D] [Fintype L],
          ∀ (A : FiniteAffine.Plane q P D L) (index : I ≃ (D × Bool)) (line : V → L),
          Selection.LineAssignment G A index line →
          ∀ T : L → Finset P, Selection.TrackedSets A T c₀ →
            Selection.occupancyFailureMass law A line T ρ ≤ ε q)

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionOccupancy2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace Balanced.SelectionOccupancy

noncomputable section
attribute [local instance] Classical.propDecidable

variable {P V I : Type*}

def hits (Q : Finset V) (T : Finset P) (R : P → V → Prop) : Finset V :=
  Q.filter (fun v => ∃ p ∈ T, R p v)

def average (slots : Finset I) (Q : I → Finset V) (f : I → V → ℝ) : ℝ :=
  (∑ i ∈ slots, (∑ v ∈ Q i, f i v) / (Q i).card) / slots.card

def hitProbability (slots : Finset I) (Q : I → Finset V)
    (T : Finset P) (R : I → P → V → Prop) : ℝ :=
  (∑ i ∈ slots, ((hits (Q i) T (R i)).card : ℝ) / (Q i).card) / slots.card

end
end Balanced.SelectionOccupancy

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_PlaneSelectionOccupancy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.SelectionOccupancy

noncomputable section
attribute [local instance] Classical.propDecidable

variable {q : ℕ} {P D L I V : Type*}
variable [Fintype P] [Fintype D] [Fintype L]
variable [DecidableEq P] [DecidableEq I] [DecidableEq V]

def afterPlaneLine (A : FiniteAffine.Plane q P D L)
    (T : Finset P) (tracked chosen : L) : Finset P := by
  classical
  exact T.filter (fun p => ¬ (chosen ≠ tracked ∧ A.incident p chosen))

omit [DecidableEq P] in
@[simp] theorem afterPlaneLine_self (A : FiniteAffine.Plane q P D L)
    (T : Finset P) (l : L) : afterPlaneLine A T l l = T := by
  classical
  simp [afterPlaneLine]

end
end Balanced.SelectionOccupancy

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionProcess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Selection.Process

noncomputable section
attribute [local instance] Classical.propDecidable

structure Parameters where
  c : ℝ
  C : ℝ
  c₀ : ℝ
  a : ℝ

namespace Parameters

def Pstar (p : Parameters) : ℝ := 4 * p.C / p.c + 4

def alpha (p : Parameters) (q : ℕ) : ℝ := p.Pstar / q

def smin (p : Parameters) : ℝ := Real.exp (-6 * p.Pstar)

def Bstar (p : Parameters) : ℝ := 2 / (p.smin * p.c)

def rho (p : Parameters) : ℝ := p.c₀ * Real.exp (-6 * p.Bstar) / 4

def Admissible (p : Parameters) : Prop :=
  0 < p.c ∧ 0 < p.C ∧ 0 < p.c₀ ∧ p.c₀ ≤ 1 ∧
  0 < p.a ∧ p.a < min 1 (min (p.rho / 2) (p.c / (100 * (p.C + 1))))

def tailSlots (p : Parameters) (q : ℕ) : ℕ := Nat.ceil (p.a * q)

def lastMainTime (p : Parameters) (q n : ℕ) : ℕ := n - p.tailSlots q

def sizeScale (p : Parameters) (q t : ℕ) : ℝ := (1 - p.alpha q) ^ t

def degreeScale (p : Parameters) (q n t : ℕ) : ℝ :=
  p.sizeScale q t * (n - t : ℕ) / n

end Parameters

structure State (I V : Type*) where
  remaining : Finset I
  alive : Finset V
  recorded : I → Option V
  deriving Fintype

variable {I V : Type*} [Fintype I] [Fintype V]

def initialState : State I V := ⟨Finset.univ, Finset.univ, fun _ => none⟩

def domain (G : Input I V) (S : State I V) (i : I) : Finset V :=
  S.alive.filter (fun v => G.slot v = i)

def currentVertices (G : Input I V) (S : State I V) : Finset V :=
  S.alive.filter (fun v => G.slot v ∈ S.remaining)

def degree (G : Input I V) (S : State I V) (v : V) : ℕ :=
  ((neighbors G v) ∩ currentVertices G S).card

def hazard (G : Input I V) (S : State I V) (v : V) : ℝ :=
  (∑ i ∈ S.remaining, (((neighbors G v) ∩ domain G S i).card : ℝ) /
    (domain G S i).card) / S.remaining.card

def thinningRate (p : Parameters) (q : ℕ) (G : Input I V) (S : State I V) (v : V) : ℝ :=
  if v ∈ currentVertices G S then
    (p.alpha q - hazard G S v) / (1 - hazard G S v)
  else 0

def Precheck (p : Parameters) (q t : ℕ) (G : Input I V) (S : State I V) : Prop :=
  S.remaining.Nonempty ∧ 0 ≤ p.alpha q ∧ p.alpha q < 1 ∧
  (∀ i ∈ S.remaining, (domain G S i).Nonempty ∧
    p.sizeScale q t * p.c * q / 2 ≤ ((domain G S i).card : ℝ)) ∧
  ∀ v ∈ currentVertices G S, hazard G S v ≤ p.alpha q

def drawWeight (G : Input I V) (S : State I V) (i : I) (w : V) : ℝ :=
  if i ∈ S.remaining ∧ w ∈ domain G S i then
    ((S.remaining.card : ℝ) * (domain G S i).card)⁻¹ else 0

def flagsWeight (p : Parameters) (q : ℕ) (G : Input I V) (S : State I V)
    (flags : V → Bool) : ℝ :=
  ∏ v, if flags v then thinningRate p q G S v else 1 - thinningRate p q G S v

def thinned (G : Input I V) (S : State I V) (w : V) (flags : V → Bool) : Finset V :=
  (currentVertices G S).filter (fun v => ¬ G.graph.Adj w v ∧ flags v = true)

def survivors (G : Input I V) (S : State I V) (w : V) (flags : V → Bool) : Finset V :=
  (currentVertices G S).filter (fun v => ¬ G.graph.Adj w v ∧ flags v = false)

def Postcheck (q : ℕ) (G : Input I V) (S : State I V) (w : V)
    (flags : V → Bool) : Prop :=
  (∀ i ∈ S.remaining, (((thinned G S w flags) ∩ domain G S i).card : ℝ) ≤
    (q : ℝ) ^ (1 / 8 : ℝ)) ∧
  (∀ v ∈ currentVertices G S,
    (((thinned G S w flags) ∩ neighbors G v).card : ℝ) ≤ (q : ℝ) ^ (1 / 8 : ℝ))

def update (G : Input I V) (S : State I V) (i : I) (w : V)
    (flags : V → Bool) : State I V where
  remaining := S.remaining.erase i
  alive := (survivors G S w flags).filter (fun v => G.slot v ≠ i)
  recorded := Function.update S.recorded i (some w)

abbrev Noise (I V : Type*) := I × V × (V → Bool)

def noiseWeight (p : Parameters) (q : ℕ) (G : Input I V) (S : State I V)
    (r : Noise I V) : ℝ :=
  drawWeight G S r.1 r.2.1 * flagsWeight p q G S r.2.2

def performedResult (q : ℕ) (G : Input I V) (S : State I V) (r : Noise I V) :
    Option (State I V) :=
  if Postcheck q G S r.2.1 r.2.2 then some (update G S r.1 r.2.1 r.2.2) else none

def stepWeight (p : Parameters) (q t : ℕ) (G : Input I V) (S : State I V)
    (out : Option (State I V)) : ℝ :=
  if Precheck p q t G S then
    ∑ r : Noise I V, if performedResult q G S r = out then noiseWeight p q G S r else 0
  else if out = none then 1 else 0

def transitionWeight (p : Parameters) (q t : ℕ) (G : Input I V)
    (before out : Option (State I V)) : ℝ :=
  match before with
  | none => if out = none then 1 else 0
  | some S => stepWeight p q t G S out

def drawStepWeight (p : Parameters) (q t : ℕ) (G : Input I V)
    (before : Option (State I V)) (draw : Option (Noise I V)) : ℝ :=
  match before with
  | none => if draw = none then 1 else 0
  | some S =>
      if Precheck p q t G S then
        match draw with
        | none => 0
        | some r => noiseWeight p q G S r
      else if draw = none then 1 else 0

def advance (q : ℕ) (G : Input I V) (before : Option (State I V))
    (draw : Option (Noise I V)) : Option (State I V) :=
  match before, draw with
  | some S, some r => performedResult q G S r
  | _, _ => none

abbrev Snapshot (I V : Type*) := Option (State I V) × Option (Noise I V)

def snapshotWeight (p : Parameters) (q t : ℕ) (G : Input I V)
    (before out : Snapshot I V) : ℝ :=
  if out.1 = advance q G before.1 out.2 then
    drawStepWeight p q t G before.1 out.2 else 0

def historyWeight (p : Parameters) (q : ℕ) (G : Input I V) :
    ℕ → Option (State I V) → ℝ
  | 0, out => if out = some initialState then 1 else 0
  | t + 1, out => ∑ before, historyWeight p q G t before * transitionWeight p q t G before out

def mainStageWeight (p : Parameters) (q : ℕ) (G : Input I V) : Option (State I V) → ℝ :=
  historyWeight p q G (p.lastMainTime q (Fintype.card I))

end
end Balanced.Selection.Process

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionThinning
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators Classical

namespace Balanced.SelectionThinning

noncomputable section

variable {V Ω : Type*} [Fintype V] [Fintype Ω]

def bitMass (r : ℝ) (b : Bool) : ℝ := if b then r else 1 - r

def thinningMass (rate : V → ℝ) (b : V → Bool) : ℝ :=
  ∏ v, bitMass (rate v) (b v)

lemma thinningMass_nonneg (rate : V → ℝ) (hrate : ∀ v, 0 ≤ rate v ∧ rate v ≤ 1)
    (b : V → Bool) : 0 ≤ thinningMass rate b := by
  apply Finset.prod_nonneg
  intro v _
  unfold bitMass
  split <;> linarith [(hrate v).1, (hrate v).2]

def thinningRate (α r : ℝ) : ℝ := (α - r) / (1 - r)

lemma thinningRate_bounds {α r : ℝ} (hr : 0 ≤ r) (hra : r ≤ α) (ha : α < 1) :
    0 ≤ thinningRate α r ∧ thinningRate α r ≤ α := by
  have hden : 0 < 1 - r := by linarith
  constructor
  · exact div_nonneg (sub_nonneg.mpr hra) hden.le
  · rw [thinningRate, div_le_iff₀ hden]
    have hprod : 0 ≤ r * (1 - α) := mul_nonneg hr (by linarith)
    nlinarith

def eventMass (p : Ω → ℝ) (E : Ω → Prop) : ℝ :=
  ∑ ω, if E ω then p ω else 0

def jointMass (p : Ω → ℝ) (rate : V → ℝ) (ω : Ω) (b : V → Bool) : ℝ :=
  p ω * thinningMass rate b

end
end Balanced.SelectionThinning

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionProcessLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Selection.Process

noncomputable section
attribute [local instance] Classical.propDecidable

variable {I V : Type*} [Fintype I] [Fintype V]

omit [Fintype I] in
theorem sum_flagsWeight (p : Parameters) (q : ℕ) (G : Input I V) (S : State I V) :
    (∑ flags : V → Bool, flagsWeight p q G S flags) = 1 := by
  have h := Fintype.prod_sum
    (fun v : V => fun b : Bool =>
      if b then thinningRate p q G S v else 1 - thinningRate p q G S v)
  simpa [flagsWeight, Fintype.sum_bool] using h.symm

omit [Fintype I] in
theorem sum_drawWeight_vertex (G : Input I V) (S : State I V)
    (hS : S.remaining.Nonempty) (hdom : ∀ i ∈ S.remaining, (domain G S i).Nonempty)
    (i : I) :
    (∑ w : V, drawWeight G S i w) = if i ∈ S.remaining then (S.remaining.card : ℝ)⁻¹ else 0 := by
  by_cases hi : i ∈ S.remaining
  · have hcardS : (S.remaining.card : ℝ) ≠ 0 := by
      exact_mod_cast Finset.card_ne_zero.mpr hS
    have hcardD : ((domain G S i).card : ℝ) ≠ 0 := by
      exact_mod_cast Finset.card_ne_zero.mpr (hdom i hi)
    simp only [drawWeight, hi, true_and, ite_true]
    rw [← Finset.sum_filter]
    simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_const,
      nsmul_eq_mul]
    field_simp
  · simp [drawWeight, hi]

theorem sum_drawWeight (G : Input I V) (S : State I V)
    (hS : S.remaining.Nonempty) (hdom : ∀ i ∈ S.remaining, (domain G S i).Nonempty) :
    (∑ i : I, ∑ w : V, drawWeight G S i w) = 1 := by
  simp_rw [sum_drawWeight_vertex G S hS hdom]
  rw [← Finset.sum_filter]
  have hcardS : (S.remaining.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hS
  simp [hcardS]

theorem sum_noiseWeight (p : Parameters) (q : ℕ) (G : Input I V) (S : State I V)
    (hS : S.remaining.Nonempty) (hdom : ∀ i ∈ S.remaining, (domain G S i).Nonempty) :
    (∑ r : Noise I V, noiseWeight p q G S r) = 1 := by
  simp only [Noise, Fintype.sum_prod_type, noiseWeight]
  simp_rw [← Finset.mul_sum, sum_flagsWeight, mul_one]
  exact sum_drawWeight G S hS hdom

theorem sum_stepWeight (p : Parameters) (q t : ℕ) (G : Input I V) (S : State I V) :
    (∑ out, stepWeight p q t G S out) = 1 := by
  by_cases hp : Precheck p q t G S
  · simp only [stepWeight, hp, ite_true]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    exact sum_noiseWeight p q G S hp.1 (fun i hi => (hp.2.2.2.1 i hi).1)
  · simp [stepWeight, hp]

theorem sum_transitionWeight (p : Parameters) (q t : ℕ) (G : Input I V)
    (before : Option (State I V)) :
    (∑ out, transitionWeight p q t G before out) = 1 := by
  cases before with
  | none => simp [transitionWeight]
  | some S => exact sum_stepWeight p q t G S

theorem sum_historyWeight (p : Parameters) (q : ℕ) (G : Input I V) (t : ℕ) :
    (∑ out, historyWeight p q G t out) = 1 := by
  induction t with
  | zero => simp [historyWeight]
  | succ t ih =>
    simp only [historyWeight]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, sum_transitionWeight, mul_one]
    exact ih

omit [Fintype I] in
theorem hazard_nonnegative (G : Input I V) (S : State I V) (v : V) :
    0 ≤ hazard G S v := by
  unfold hazard
  positivity

omit [Fintype I] in
theorem thinningRate_bounds_of_precheck (p : Parameters) (q t : ℕ)
    (G : Input I V) (S : State I V) (hp : Precheck p q t G S) (v : V) :
    0 ≤ thinningRate p q G S v ∧ thinningRate p q G S v ≤ p.alpha q := by
  by_cases hv : v ∈ currentVertices G S
  · have h := SelectionThinning.thinningRate_bounds
      (hazard_nonnegative G S v) (hp.2.2.2.2 v hv) hp.2.2.1
    simpa only [thinningRate, hv, ite_true, SelectionThinning.thinningRate] using h
  · simp only [thinningRate, hv, ite_false]
    exact ⟨le_rfl, hp.2.1⟩

omit [Fintype I] in
theorem flagsWeight_nonnegative_of_precheck (p : Parameters) (q t : ℕ)
    (G : Input I V) (S : State I V) (hp : Precheck p q t G S) (flags : V → Bool) :
    0 ≤ flagsWeight p q G S flags := by
  change 0 ≤ SelectionThinning.thinningMass (thinningRate p q G S) flags
  apply SelectionThinning.thinningMass_nonneg
  intro v
  have h := thinningRate_bounds_of_precheck p q t G S hp v
  exact ⟨h.1, h.2.trans hp.2.2.1.le⟩

omit [Fintype I] [Fintype V] in
theorem drawWeight_nonnegative (G : Input I V) (S : State I V) (i : I) (w : V) :
    0 ≤ drawWeight G S i w := by
  unfold drawWeight
  split
  · positivity
  · exact le_rfl

omit [Fintype I] in
theorem noiseWeight_nonnegative_of_precheck (p : Parameters) (q t : ℕ)
    (G : Input I V) (S : State I V) (hp : Precheck p q t G S) (r : Noise I V) :
    0 ≤ noiseWeight p q G S r :=
  mul_nonneg (drawWeight_nonnegative G S r.1 r.2.1)
    (flagsWeight_nonnegative_of_precheck p q t G S hp r.2.2)

theorem stepWeight_nonnegative (p : Parameters) (q t : ℕ) (G : Input I V)
    (S : State I V) (out : Option (State I V)) : 0 ≤ stepWeight p q t G S out := by
  unfold stepWeight
  split
  · rename_i hp
    apply Finset.sum_nonneg
    intro r _
    split
    · exact noiseWeight_nonnegative_of_precheck p q t G S hp r
    · exact le_rfl
  · split <;> norm_num

theorem transitionWeight_nonnegative (p : Parameters) (q t : ℕ) (G : Input I V)
    (before out : Option (State I V)) : 0 ≤ transitionWeight p q t G before out := by
  cases before with
  | none => simp only [transitionWeight]; split <;> norm_num
  | some S => exact stepWeight_nonnegative p q t G S out

theorem historyWeight_nonnegative (p : Parameters) (q : ℕ) (G : Input I V)
    (t : ℕ) (out : Option (State I V)) : 0 ≤ historyWeight p q G t out := by
  induction t generalizing out with
  | zero => simp only [historyWeight]; split <;> norm_num
  | succ t ih =>
    apply Finset.sum_nonneg
    intro before _
    exact mul_nonneg (ih before) (transitionWeight_nonnegative p q t G before out)

theorem sum_drawStepWeight (p : Parameters) (q t : ℕ) (G : Input I V)
    (before : Option (State I V)) : (∑ draw, drawStepWeight p q t G before draw) = 1 := by
  cases before with
  | none => simp [drawStepWeight]
  | some S =>
    by_cases hp : Precheck p q t G S
    · simp only [drawStepWeight, hp, ite_true, Fintype.sum_option]
      simpa only [zero_add] using
        sum_noiseWeight p q G S hp.1 (fun i hi => (hp.2.2.2.1 i hi).1)
    · simp [drawStepWeight, hp]

omit [Fintype I] in
theorem drawStepWeight_nonnegative (p : Parameters) (q t : ℕ) (G : Input I V)
    (before : Option (State I V)) (draw : Option (Noise I V)) :
    0 ≤ drawStepWeight p q t G before draw := by
  cases before with
  | none => simp only [drawStepWeight]; split <;> norm_num
  | some S =>
    by_cases hp : Precheck p q t G S
    · cases draw with
      | none => simp [drawStepWeight, hp]
      | some r => simpa only [drawStepWeight, hp, ite_true] using
        noiseWeight_nonnegative_of_precheck p q t G S hp r
    · simp only [drawStepWeight, hp, ite_false]; split <;> norm_num

omit [Fintype I] in
theorem snapshotWeight_nonnegative (p : Parameters) (q t : ℕ) (G : Input I V)
    (before out : Snapshot I V) : 0 ≤ snapshotWeight p q t G before out := by
  unfold snapshotWeight
  split
  · exact drawStepWeight_nonnegative p q t G before.1 out.2
  · exact le_rfl

theorem sum_snapshotWeight (p : Parameters) (q t : ℕ) (G : Input I V)
    (before : Snapshot I V) : (∑ out, snapshotWeight p q t G before out) = 1 := by
  simp only [Snapshot, Fintype.sum_prod_type, snapshotWeight]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  exact sum_drawStepWeight p q t G before.1

def snapshotPMF (p : Parameters) (q t : ℕ) (G : Input I V)
    (before : Snapshot I V) : PMF (Snapshot I V) :=
  PMF.ofFintype (fun out => ENNReal.ofReal (snapshotWeight p q t G before out)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg
      (fun out _ => snapshotWeight_nonnegative p q t G before out)]
    rw [sum_snapshotWeight]
    simp)

end
end Balanced.Selection.Process

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionHistory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Preorder
open scoped MeasureTheory ProbabilityTheory BigOperators

namespace Balanced.Selection.Process

attribute [local instance] Classical.propDecidable

variable {I V : Type*} [Fintype I] [Fintype V]

instance snapshotMeasurableSpace : MeasurableSpace (Snapshot I V) := ⊤

instance snapshotMeasurableSingletonClass : MeasurableSingletonClass (Snapshot I V) where
  measurableSet_singleton _ := MeasurableSpace.measurableSet_top

def initialSnapshot : Snapshot I V := (some initialState, none)

def snapshotPathLaw (p : Parameters) (q : ℕ) (G : Input I V) :
    Measure (FiniteHistory.Path (Snapshot I V)) :=
  FiniteHistory.pathLaw (fun t => snapshotPMF p q t G) initialSnapshot

instance snapshotPathLaw_isProbability (p : Parameters) (q : ℕ) (G : Input I V) :
    IsProbabilityMeasure (snapshotPathLaw p q G) := by
  unfold snapshotPathLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def snapshotFiltration :
    Filtration ℕ (inferInstance : MeasurableSpace (FiniteHistory.Path (Snapshot I V))) :=
  FiniteHistory.filtration

end Balanced.Selection.Process

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionState
attribute [-instance] _root_.OAI.Balanced.Selection.Process.snapshotPathLaw_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Selection.Process

noncomputable section
attribute [local instance] Classical.propDecidable

variable {I V : Type*} [Fintype I] [Fintype V]

def StateInvariant (G : Input I V) (S : State I V) : Prop :=
  (∀ v ∈ S.alive, G.slot v ∈ S.remaining) ∧
  (∀ i, S.recorded i = none ↔ i ∈ S.remaining) ∧
  (∀ i v, S.recorded i = some v → G.slot v = i) ∧
  (∀ i j v w, S.recorded i = some v → S.recorded j = some w → i ≠ j → ¬ G.graph.Adj v w) ∧
  (∀ i w, S.recorded i = some w → ∀ v ∈ S.alive, ¬ G.graph.Adj w v)

end
end Balanced.Selection.Process

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionAuxiliaryTracks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Preorder
open scoped BigOperators

namespace Balanced.Selection.Process

attribute [local instance] Classical.propDecidable
variable {I V : Type*} [Fintype I] [Fintype V]

def censoredDomainNumerator (q : ℕ) (G : Input I V) (S : State I V)
    (r : Noise I V) (i : I) : ℝ :=
  if (q : ℝ) ^ (1 / 8 : ℝ) <
      (((thinned G S r.2.1 r.2.2) ∩ domain G S i).card : ℝ) then
    (domain G S i).card
  else ((survivors G S r.2.1 r.2.2 ∩ domain G S i).card : ℝ)

def censoredDegreeNumerator (q : ℕ) (G : Input I V) (S : State I V)
    (r : Noise I V) (v : V) : ℝ :=
  if r.2.1 ∈ G.exceptional v ∨ (q : ℝ) ^ (1 / 8 : ℝ) <
      (((thinned G S r.2.1 r.2.2) ∩ neighbors G v).card : ℝ) then
    degree G S v
  else degree G (update G S r.1 r.2.1 r.2.2) v

def domainTrackIncrement (p : Parameters) (q t : ℕ) (G : Input I V) (i : I)
    (before : Option (State I V)) (draw : Option (Noise I V)) : ℝ :=
  match before, draw with
  | some S, some r =>
      if i ∈ S.remaining then
        censoredDomainNumerator q G S r i / p.sizeScale q (t + 1) -
          (domain G S i).card / p.sizeScale q t
      else 0
  | _, _ => 0

def degreeTrackIncrement (p : Parameters) (q t : ℕ) (G : Input I V) (v : V)
    (before : Option (State I V)) (draw : Option (Noise I V)) : ℝ :=
  match before, draw with
  | some S, some r =>
      if v ∈ currentVertices G S then
        censoredDegreeNumerator q G S r v / p.degreeScale q (Fintype.card I) (t + 1) -
          (degree G S v : ℝ) / p.degreeScale q (Fintype.card I) t
      else 0
  | _, _ => 0

def domainTrack (p : Parameters) (q : ℕ) (G : Input I V) (i : I)
    (t : ℕ) (ω : FiniteHistory.Path (Snapshot I V)) : ℝ :=
  ((domain G initialState i).card : ℝ) +
    ∑ j ∈ Finset.range t, domainTrackIncrement p q j G i (ω j).1 (ω (j + 1)).2

def degreeTrack (p : Parameters) (q : ℕ) (G : Input I V) (v : V)
    (t : ℕ) (ω : FiniteHistory.Path (Snapshot I V)) : ℝ :=
  (degree G initialState v : ℝ) +
    ∑ j ∈ Finset.range t, degreeTrackIncrement p q j G v (ω j).1 (ω (j + 1)).2

@[simp] theorem domainTrack_zero (p : Parameters) (q : ℕ) (G : Input I V)
    (i : I) (ω : FiniteHistory.Path (Snapshot I V)) :
    domainTrack p q G i 0 ω = (domain G initialState i).card := by
  simp [domainTrack]

@[simp] theorem degreeTrack_zero (p : Parameters) (q : ℕ) (G : Input I V)
    (v : V) (ω : FiniteHistory.Path (Snapshot I V)) :
    degreeTrack p q G v 0 ω = degree G initialState v := by
  simp [degreeTrack]

end Balanced.Selection.Process

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Balanced.SelectionScales

def domain (P : ℝ) (q t : ℕ) : ℝ := (1 - P / q) ^ t

def degree (P : ℝ) (q n t : ℕ) : ℝ := domain P q t * (n - t : ℕ) / n

end Balanced.SelectionScales

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionCensoredJumps
attribute [-instance] _root_.OAI.Balanced.Selection.Process.snapshotPathLaw_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Selection.Process.CensoredJumps

noncomputable section
attribute [local instance] Classical.propDecidable

variable {I V : Type*} [Fintype I] [Fintype V]

def censoredDomainCount (q : ℕ) (G : Input I V) (S : State I V)
    (i : I) (w : V) (flags : V → Bool) : ℕ :=
  if (((thinned G S w flags) ∩ domain G S i).card : ℝ) ≤ (q : ℝ) ^ (1 / 8 : ℝ)
  then ((survivors G S w flags) ∩ domain G S i).card
  else (domain G S i).card

def censoredDegreeCount (q : ℕ) (G : Input I V) (S : State I V)
    (i : I) (w v : V) (flags : V → Bool) : ℕ :=
  if w ∉ G.exceptional v ∧
      (((thinned G S w flags) ∩ neighbors G v).card : ℝ) ≤ (q : ℝ) ^ (1 / 8 : ℝ)
  then degree G (update G S i w flags) v
  else degree G S v

end
end Balanced.Selection.Process.CensoredJumps

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionCensoredMeans
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators

namespace Balanced.Selection.Process
attribute [local instance] Classical.propDecidable
variable {I V : Type*} [Fintype I] [Fintype V]

def domainOverflowMass (p : Parameters) (q : ℕ) (G : Input I V)
    (S : State I V) (i : I) : ℝ :=
  ∑ r : Noise I V, if (q : ℝ) ^ (1 / 8 : ℝ) <
      (((thinned G S r.2.1 r.2.2) ∩ domain G S i).card : ℝ)
    then noiseWeight p q G S r else 0

def degreeCensorMass (p : Parameters) (q : ℕ) (G : Input I V)
    (S : State I V) (v : V) : ℝ :=
  ∑ r : Noise I V, if r.2.1 ∈ G.exceptional v ∨ (q : ℝ) ^ (1 / 8 : ℝ) <
      (((thinned G S r.2.1 r.2.2) ∩ neighbors G v).card : ℝ)
    then noiseWeight p q G S r else 0

end Balanced.Selection.Process

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionAuxiliaryConcentration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators
namespace Balanced.Selection.Process
attribute [local instance] Classical.propDecidable
variable {I V : Type*} [Fintype I] [Fintype V]

def domainTrackJumpBound (p : Parameters) (q : ℕ) : ℝ :=
  (2 * (q : ℝ) ^ (1 / 8 : ℝ) + p.Pstar) / p.smin

def degreeTrackJumpBound (p : Parameters) (q : ℕ) : ℝ :=
  (3 * (q : ℝ) ^ (1 / 8 : ℝ) + p.C * (p.Pstar + 1 / p.a)) /
    (p.smin * p.a / 3)

end Balanced.Selection.Process

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionConcentrationAsymptotics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
namespace Balanced.Selection.Process

def trackJumpCoefficient (p : Parameters) : ℝ :=
  (2 + p.Pstar) / p.smin +
    (3 + p.C * (p.Pstar + 1 / p.a)) / (p.smin * p.a / 3)

def trackConcentrationError (p : Parameters) (q : ℕ) : ℝ :=
  48 * (q : ℝ) ^ 3 *
    Real.exp (-((q : ℝ) ^ (7 / 20 : ℝ) / (96 * (trackJumpCoefficient p) ^ 2)))

end Balanced.Selection.Process

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionCylinder
attribute [-instance] _root_.OAI.Balanced.Selection.Process.snapshotPathLaw_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Selection.Process

noncomputable section
attribute [local instance] Classical.propDecidable

variable {I V : Type*} [Fintype I] [Fintype V]

def PrescriptionsAgree (J : Finset I) (a : I → V) (S : State I V) : Prop :=
  ∀ i ∈ J, i ∉ S.remaining → S.recorded i = some (a i)

def cylinderPotential (J : Finset I) (a : I → V) (c : ℝ) (S : State I V) : ℝ :=
  if PrescriptionsAgree J a S then c ^ (J ∩ S.remaining).card else 0

def outcomePotential (J : Finset I) (a : I → V) (c : ℝ) : Option (State I V) → ℝ
  | none => 0
  | some S => cylinderPotential J a c S

def cylinderConstant (p : Parameters) : ℝ :=
  max 1 (2 * Real.exp (1 / 2 : ℝ) / (p.smin * p.c))

end
end Balanced.Selection.Process

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionLaw
attribute [-instance] _root_.OAI.Balanced.Selection.Process.snapshotPathLaw_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Selection

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

variable {I V : Type*} [Fintype I] [Fintype V]
variable {G : Input I V} (law : OutputLaw G)

theorem weight_eq_zero_of_not_transversal (a : I → V)
    (ha : ¬ IsIndependentTransversal G a) : law.weight a = 0 := by
  apply le_antisymm _ (law.nonnegative a)
  by_contra h
  exact ha (law.supported a (lt_of_not_ge h))

end
end Balanced.Selection

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

abbrev Slot (S : State I V) := {i : I // i ∈ S.remaining}

abbrev Domain (G : Input I V) (S : State I V) (i : Slot S) :=
  {v : V // v ∈ domain G S i.1}

def value (G : Input I V) (S : State I V) (v : Sigma (Domain G S)) : V := v.2.1

def graph (G : Input I V) (S : State I V) : SimpleGraph (Sigma (Domain G S)) :=
  G.graph.comap (value G S)

omit [Fintype I] [Fintype V] in
@[simp] theorem value_slot (G : Input I V) (S : State I V)
    (v : Sigma (Domain G S)) : G.slot (value G S v) = v.1.1 :=
  (Finset.mem_filter.mp v.2.2).2

omit [Fintype I] [Fintype V] in
theorem value_injective (G : Input I V) (S : State I V) :
    Function.Injective (value G S) := by
  rintro ⟨⟨i, hi⟩, ⟨v, hv⟩⟩ ⟨⟨j, hj⟩, ⟨w, hw⟩⟩ heq
  change v = w at heq
  subst w
  have hij : i = j := (Finset.mem_filter.mp hv).2.symm.trans
    (Finset.mem_filter.mp hw).2
  subst j
  rfl

omit [Fintype I] [Fintype V] in
theorem value_mem_current (G : Input I V) (S : State I V)
    (v : Sigma (Domain G S)) : value G S v ∈ currentVertices G S := by
  apply Finset.mem_filter.mpr
  exact ⟨(Finset.mem_filter.mp v.2.2).1, by rw [value_slot]; exact v.1.2⟩

omit [Fintype I] [Fintype V] in
@[simp] theorem card_domain (G : Input I V) (S : State I V) (i : Slot S) :
    Fintype.card (Domain G S i) = (domain G S i.1).card := by
  simp [Domain]

omit [Fintype I] [Fintype V] in

theorem noWithinSlotEdges (G : Input I V) (S : State I V)
    (hno : ∀ v w, G.slot v = G.slot w → ¬ G.graph.Adj v w) :
    TailGraph.NoWithinSlotEdges (graph G S) Sigma.fst := by
  intro v w hadj hslot
  apply hno (value G S v) (value G S w)
  · rw [value_slot, value_slot, hslot]
  · exact hadj

omit [Fintype I] in

theorem degree_le (G : Input I V) (S : State I V)
    (v : Sigma (Domain G S)) :
    (graph G S).degree v ≤ degree G S (value G S v) := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  unfold degree
  apply Finset.card_le_card_of_injOn (value G S)
  · intro w hw
    apply Finset.mem_inter.mpr
    refine ⟨?_, value_mem_current G S w⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (SimpleGraph.mem_neighborFinset (graph G S) v w).mp hw⟩
  · exact (value_injective G S).injOn

def complete (G : Input I V) (S : State I V) (fixed : I → V)
    (a : Slots.Assignment (Domain G S)) : I → V :=
  fun i => if hi : i ∈ S.remaining then (a ⟨i, hi⟩).1 else fixed i

omit [Fintype I] [Fintype V] in
@[simp] theorem complete_remaining (G : Input I V) (S : State I V) (fixed : I → V)
    (a : Slots.Assignment (Domain G S)) (i : Slot S) :
    complete G S fixed a i.1 = (a i).1 := by simp [complete, i.2]

omit [Fintype I] [Fintype V] in
@[simp] theorem complete_recorded (G : Input I V) (S : State I V) (fixed : I → V)
    (a : Slots.Assignment (Domain G S)) (i : I) (hi : i ∉ S.remaining) :
    complete G S fixed a i = fixed i := by simp [complete, hi]

def successfulAssignments (G : Input I V) (S : State I V) :
    Finset (Slots.Assignment (Domain G S)) :=
  Finset.univ.filter (fun a =>
    a ∈ TailConditioning.independentTransversals (Domain G S) (graph G S))

omit [Fintype I] [Fintype V] in
@[simp] theorem mem_successfulAssignments (G : Input I V) (S : State I V)
    (a : Slots.Assignment (Domain G S)) :
    a ∈ successfulAssignments G S ↔
      a ∈ TailConditioning.independentTransversals (Domain G S) (graph G S) := by
  simp [successfulAssignments]

def completionPMF (G : Input I V) (S : State I V) (fixed : I → V)
    (hG : (successfulAssignments G S).Nonempty) : PMF (I → V) :=
  (PMF.uniformOfFinset (successfulAssignments G S) hG).map (complete G S fixed)

theorem sum_pmf_real (p : PMF (I → V)) : (∑ a, (p a).toReal) = 1 := by
  rw [← ENNReal.toReal_sum (fun a _ => p.apply_ne_top a)]
  have h : (∑ a, p a) = 1 := by simpa only [tsum_fintype] using p.tsum_coe
  rw [h]
  simp

end Balanced.Selection.Process.Tail

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionFinalLaw
attribute [-instance] _root_.OAI.Balanced.Selection.Process.snapshotPathLaw_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Selection.Process

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

variable {I V : Type*} [Fintype I] [Fintype V]

def TailCheck (G : Input I V) (S : State I V) : Prop :=
  ∃ L Δ : ℕ, 3 ≤ L ∧
    (∀ i ∈ S.remaining, L ≤ (domain G S i).card) ∧
    (∀ v ∈ currentVertices G S, degree G S v ≤ Δ) ∧ 8 * Δ ≤ L

def failureLaw (G : Input I V) : OutputLaw G where
  weight _ := 0
  nonnegative _ := le_rfl
  mass_le_one := by simp
  supported _ h := False.elim (lt_irrefl 0 h)

@[simp] theorem successMass_failureLaw (G : Input I V) :
    successMass (failureLaw G) = 0 := by simp [successMass, failureLaw]

section Nonempty
variable [Nonempty V]

def recordedAssignment (S : State I V) : I → V :=
  fun i => (S.recorded i).getD (Classical.choice inferInstance)

omit [Fintype I] [Fintype V] in
theorem recordedAssignment_recorded (G : Input I V) (S : State I V)
    (hS : StateInvariant G S) (i : I) (hi : i ∉ S.remaining) :
    S.recorded i = some (recordedAssignment S i) := by
  have hn : S.recorded i ≠ none := by
    intro h
    exact hi ((hS.2.1 i).mp h)
  cases hr : S.recorded i with
  | none => exact False.elim (hn hr)
  | some v => simp [recordedAssignment, hr]

def SourceTailCheck (p : Parameters) (q : ℕ) (G : Input I V) (S : State I V) : Prop :=
  TailCheck G S ∧ ∀ i ∈ S.remaining,
    p.sizeScale q (p.lastMainTime q (Fintype.card I)) * p.c * q / 2 ≤
      ((domain G S i).card : ℝ)

end Nonempty

end
end Balanced.Selection.Process

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionFirstAbort
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped MeasureTheory ProbabilityTheory

namespace Balanced.Selection.Process.FirstAbort

attribute [local instance] Classical.propDecidable

variable {I V : Type*} [Fintype I] [Fintype V]

def StateConcentration (p : Parameters) (q : ℕ) (G : Input I V)
    (t : ℕ) (S : State I V) : Prop :=
  (∀ i ∈ S.remaining,
    |((domain G S i).card : ℝ) - p.sizeScale q t * (slotVertices G i).card| ≤
      (q : ℝ) ^ ((4 : ℝ) / 5)) ∧
  (∀ v ∈ currentVertices G S,
    (degree G S v : ℝ) ≤ p.degreeScale q (Fintype.card I) t *
      (neighbors G v).card + (q : ℝ) ^ ((4 : ℝ) / 5))

def ConcentratedPath (p : Parameters) (q : ℕ) (G : Input I V) (T : ℕ)
    (ω : FiniteHistory.Path (Snapshot I V)) : Prop :=
  ∀ t ≤ T, ∀ S, (ω t).1 = some S → StateConcentration p q G t S

def NoPostAbort (q : ℕ) (G : Input I V) (T : ℕ)
    (ω : FiniteHistory.Path (Snapshot I V)) : Prop :=
  ∀ t < T, ∀ S r, (ω t).1 = some S → (ω (t + 1)).2 = some r →
    Postcheck q G S r.2.1 r.2.2

def SupportedPath (p : Parameters) (q : ℕ) (G : Input I V)
    (ω : FiniteHistory.Path (Snapshot I V)) : Prop :=
  ω 0 = initialSnapshot ∧
    ∀ t, 0 < snapshotWeight p q t G (ω t) (ω (t + 1))

end Balanced.Selection.Process.FirstAbort

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionOccupancyTrack
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Preorder
open scoped MeasureTheory ProbabilityTheory BigOperators

namespace Balanced.Selection.Process

open FiniteHistory
attribute [local instance] Classical.propDecidable
variable {I V P D L : Type*} [Fintype I] [Fintype V]
  [Fintype P] [Fintype D] [Fintype L]

def occupancyPrefix (q : ℕ) (A : FiniteAffine.Plane q P D L)
    (line : V → L) (l : L) (T : Finset P) (t : ℕ)
    (h : Prefix (Snapshot I V) t) : Finset P :=
  T.filter (fun x => ∀ (j : ℕ) (hj : j < t),
    ∀ r, (h ⟨j + 1, Finset.mem_Iic.mpr (by omega)⟩).2 = some r →
      ¬ (line r.2.1 ≠ l ∧ A.incident x (line r.2.1)))

@[simp] theorem occupancyPrefix_zero (q : ℕ) (A : FiniteAffine.Plane q P D L)
    (line : V → L) (l : L) (T : Finset P) (h : Prefix (Snapshot I V) 0) :
    occupancyPrefix q A line l T 0 h = T := by simp [occupancyPrefix]

def occupancyResponse (p : Parameters) (q : ℕ) (G : Input I V)
    (A : FiniteAffine.Plane q P D L) (line : V → L) (l : L) (T : Finset P)
    (t : ℕ) (h : Prefix (Snapshot I V) t) (out : Snapshot I V) : ℝ :=
  match (h ⟨t, Finset.mem_Iic.mpr le_rfl⟩).1, out.2 with
  | some S, some r => if Precheck p q t G S then
      ((SelectionOccupancy.afterPlaneLine A (occupancyPrefix q A line l T t h)
        l (line r.2.1)).card : ℝ) / (1 - p.Bstar / q) ^ (t + 1) -
      ((occupancyPrefix q A line l T t h).card : ℝ) / (1 - p.Bstar / q) ^ t
    else 0
  | _, _ => 0

def occupancyTrack (p : Parameters) (q : ℕ) (G : Input I V)
    (A : FiniteAffine.Plane q P D L) (line : V → L) (l : L) (T : Finset P) :
    ℕ → Path (Snapshot I V) → ℝ :=
  additiveTrack (T.card : ℝ) (occupancyResponse p q G A line l T)

end Balanced.Selection.Process

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionOccupancyBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Preorder
open scoped MeasureTheory ProbabilityTheory BigOperators

namespace Balanced.Selection.Process
open FiniteHistory
attribute [local instance] Classical.propDecidable
variable {I V P D L : Type*} [Fintype I] [Fintype V]
  [Fintype P] [Fintype D] [Fintype L]

def Parameters.occupancyDecay (p : Parameters) : ℝ :=
  p.c₀ ^ 2 / (96 * ((1 + p.Bstar) / Real.exp (-6 * p.Bstar)) ^ 2)

end Balanced.Selection.Process

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionOccupancyTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Preorder
open scoped MeasureTheory ProbabilityTheory BigOperators

namespace Balanced.Selection.Process
open FiniteHistory
attribute [local instance] Classical.propDecidable
variable {I V P D L : Type*} [Fintype I] [Fintype V]
  [Fintype P] [Fintype D] [Fintype L]

def recordedTracked (q : ℕ) (A : FiniteAffine.Plane q P D L)
    (line : V → L) (T : L → Finset P) (S : State I V) (l : L) : Finset P :=
  (T l).filter (fun x => ∀ i v, S.recorded i = some v →
    ¬ (line v ≠ l ∧ A.incident x (line v)))

end Balanced.Selection.Process

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionPostcheckTail
attribute [-instance] _root_.OAI.Balanced.Selection.Process.snapshotPathLaw_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators Classical

namespace Balanced.Selection.Process

noncomputable section

variable {I V : Type*} [Fintype I] [Fintype V]

def postcheckMean (p : Parameters) : ℝ := p.Pstar * max 1 p.C

end
end Balanced.Selection.Process

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionPostabort
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Preorder
open scoped BigOperators Classical

namespace Balanced.Selection.Process

variable {I V : Type*} [Fintype I] [Fintype V]

def postcheckFailed (q : ℕ) (G : Input I V)
    (before : Option (State I V)) (draw : Option (Noise I V)) : Prop :=
  match before, draw with
  | some S, some r => ¬ Postcheck q G S r.2.1 r.2.2
  | _, _ => False

def postcheckEvent (q : ℕ) (G : Input I V) (t : ℕ) :
    Set (FiniteHistory.Path (Snapshot I V)) :=
  {ω | postcheckFailed q G (ω t).1 (ω (t + 1)).2}

end Balanced.Selection.Process

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionPushforward
attribute [-instance] _root_.OAI.Balanced.Selection.Process.snapshotPathLaw_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Balanced.FinitePushforward

def pushWeight {A B : Type*} [Fintype A] [DecidableEq B]
    (f : A → B) (w : A → ℝ) (b : B) : ℝ :=
  ∑ a, if f a = b then w a else 0

def cylinderMass {I V : Type*} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]
    (w : (I → V) → ℝ) (J : Finset I) (a : I → V) : ℝ :=
  ∑ t, if ∀ i ∈ J, t i = a i then w t else 0

def mapChoices {I V L : Type*} (label : I → V → L) (t : I → V) : I → L :=
  fun i => label i (t i)

end Balanced.FinitePushforward

namespace Balanced.Selection

noncomputable section

def OutputLaw.labelWeight {I V L : Type*} [Fintype I] [DecidableEq I]
    [Fintype V] [Fintype L] [DecidableEq L] {G : Input I V}
    (law : OutputLaw G) (label : I → V → L) : (I → L) → ℝ :=
  FinitePushforward.pushWeight (FinitePushforward.mapChoices label) law.weight

end
end Balanced.Selection

end

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

omit [Fintype B] in
theorem pushWeight_nonneg (f : A → B) (w : A → ℝ) (hw : ∀ a, 0 ≤ w a) (b : B) :
    0 ≤ pushWeight f w b := by
  apply sum_nonneg
  intro a _
  split_ifs
  · exact hw a
  · exact le_rfl

theorem sum_pushWeight (f : A → B) (w : A → ℝ) :
    ∑ b, pushWeight f w b = ∑ a, w a := by
  unfold pushWeight
  rw [sum_comm]
  simp

theorem eventMass_pushWeight (f : A → B) (w : A → ℝ)
    (P : B → Prop) [DecidablePred P] :
    (∑ b, if P b then pushWeight f w b else 0) =
      ∑ a, if P (f a) then w a else 0 := by
  classical
  unfold pushWeight
  calc
    (∑ b, if P b then ∑ a, if f a = b then w a else 0 else 0) =
        ∑ b, ∑ a, if P b then (if f a = b then w a else 0) else 0 := by
      apply sum_congr rfl
      intro b _
      split_ifs <;> simp
    _ = ∑ a, ∑ b, if P b then (if f a = b then w a else 0) else 0 := sum_comm
    _ = ∑ a, if P (f a) then w a else 0 := by
      apply sum_congr rfl
      intro a _
      rw [sum_eq_single (f a)]
      · simp
      · intro b _ hb
        simp [Ne.symm hb]
      · simp

omit [Fintype B] in

theorem exists_positive_preimage (f : A → B) (w : A → ℝ)
    (hw : ∀ a, 0 ≤ w a) (b : B) (hb : 0 < pushWeight f w b) :
    ∃ a, f a = b ∧ 0 < w a := by
  classical
  have hn : ∀ a ∈ (univ : Finset A), 0 ≤ (if f a = b then w a else 0) := by
    intro a _
    split_ifs
    · exact hw a
    · exact le_rfl
  obtain ⟨a, _, ha⟩ := (sum_pos_iff_of_nonneg hn).mp hb
  by_cases he : f a = b
  · exact ⟨a, he, by simpa [he] using ha⟩
  · simp [he] at ha

end Balanced.FinitePushforward

namespace Balanced.Selection

noncomputable section
attribute [local instance] Classical.propDecidable

variable {I V L : Type*} [Fintype I] [Fintype V] [Fintype L]
    {G : Input I V}

theorem labelWeight_nonneg (law : OutputLaw G) (label : I → V → L) (s : I → L) :
    0 ≤ law.labelWeight label s :=
  FinitePushforward.pushWeight_nonneg _ _ law.nonnegative s

theorem sum_labelWeight (law : OutputLaw G) (label : I → V → L) :
    ∑ s, law.labelWeight label s = successMass law :=
  FinitePushforward.sum_pushWeight _ _

theorem sum_labelWeight_le_one (law : OutputLaw G) (label : I → V → L) :
    ∑ s, law.labelWeight label s ≤ 1 := by
  rw [sum_labelWeight]
  exact law.mass_le_one

end
end Balanced.Selection

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionTailCylinder
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

def residualIndices (S : State I V) (J : Finset I) : Finset (Slot S) :=
  Finset.univ.filter (fun i => i.1 ∈ J)

omit [Fintype I] [Fintype V] in
@[simp] theorem mem_residualIndices (S : State I V) (J : Finset I) (i : Slot S) :
    i ∈ residualIndices S J ↔ i.1 ∈ J := by
  simp [residualIndices]

end Balanced.Selection.Process.Tail

end

end OAI
end


