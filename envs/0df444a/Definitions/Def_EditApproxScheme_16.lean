-- Prove2me | Definitions.Def_EditApproxScheme_16
-- name    : EditApproxScheme_16
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-15T16:53:49.862753+00:00
-- url     : https://prove2.me/theorems/ceecba77-2e95-489b-a98d-7ad508f9005b
-- title:
--   Edit-distance approximation scheme, part 16 of 20: output laws and execution work
-- statement:
--   This is **part 16 of 20** of the definitions of a uniform almost-linear approximation scheme for edit distance, which the main statement `OAI.EditApproximation.almostLinearEditDistanceRawBandV3` is about. This part contains the probability laws: the rejection runtime array law, the physical coarse law, the full outcome space and its law `computedFullLaw`, the large-input predicate, family results, the final root value, and the address, coarse, sampling and preparation work of an execution.
--
--   Each part imports the previous one, so importing part 20 brings all definitions into scope. A description of the whole scheme is given in part 20.
--
--   **Formalization Note** These 20 parts replace the single 1.4 MB block `Def_EditApproximation`, which was too large for the platform to import. In the source, the supporting lemmas were pasted as local `have` proofs inside the definition bodies: 948 copies of 145 lemmas. Each lemma is now proved once as a top-level theorem and cited by name; one lemma that nothing used was dropped. The file was then split into sequential parts by deleting declarations. All 1,403 declarations from the source keep exactly the same elaborated types.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/EditApproximation.lean#L9446-L10065 (line numbers refer to the lemma-lifted file, 12,145 lines)

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/EditApproximation.lean
-- Part 16 of 20 of the edit-distance approximation definitions: embedded proof lemmas lifted
-- to top-level theorems (OAI.EditApproximation.Lemmas.*), then split by skeleton subtraction.

import Definitions.Def_EditApproxScheme_15

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

open MeasureTheory ProbabilityTheory

variable {ι : Type u_1} [Fintype ι] (range : ι → ℕ) [∀ i, NeZero (range i)]

noncomputable def rejectionRuntimeArrayLaw : Measure (OAI.EditApproximation.RejectionRuntimeArray range) :=
  (Measure.pi (OAI.EditApproximation.rejectionFailureLaw range)).prod (OAI.EditApproximation.rejectionAcceptedLaw range)

noncomputable def rejectionSelectedBits
    (selected : ι → (∀ i, Fin (range i)) → Prop) (execution : OAI.EditApproximation.RejectionRuntimeArray range) : ℝ :=
  ∑ i, (((execution.1 i : ℝ) + 1) * OAI.EditApproximation.rejectionBitCount (range i)) *
    OAI.EditApproximation.selectionIndicator (selected i execution.2)

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

open MeasureTheory ProbabilityTheory

variable {α : Type u_1} {M J R : ℕ} [NeZero M] (target : List α) (N P F exponent H Q passes copies : ℕ)

abbrev physicalFamilyRange (key : OAI.EditApproximation.PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
    target N P F exponent H Q passes copies) : ℕ :=
  OAI.EditApproximation.physicalScalarRange M J N target.length exponent F Q R (OAI.EditApproximation.localOnlineMassBound M P H) key.2.2

instance physicalFamilyRange_neZero (key : OAI.EditApproximation.PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
    target N P F exponent H Q passes copies) :
    NeZero (OAI.EditApproximation.physicalFamilyRange target N P F exponent H Q passes copies key) := by
  exact OAI.EditApproximation.physicalScalarRangeNeZero M J N target.length exponent F Q R
    (OAI.EditApproximation.localOnlineMassBound M P H) key.2.2

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

open MeasureTheory

abbrev ComputedPhysicalCoarseDraw (source target : List ℕ) (N : ℕ) :=
  OAI.EditApproximation.PhysicalCoarseDraw (M := (OAI.EditApproximation.integerParameters N).M)
    (J := OAI.EditApproximation.intervalTreeDepth (OAI.EditApproximation.integerParameters N).M source.length) source target (OAI.EditApproximation.integerParameters N).B (OAI.EditApproximation.computedPhysicalCoarseDepth source target N)

abbrev ComputedRejectionRuntime (source target : List ℕ) (N : ℕ) :=
  OAI.EditApproximation.RejectionRuntimeArray (OAI.EditApproximation.physicalFamilyRange (M := (OAI.EditApproximation.integerParameters N).M)
    (J := OAI.EditApproximation.intervalTreeDepth (OAI.EditApproximation.integerParameters N).M source.length) (R := OAI.EditApproximation.inputHeight N ^ 2)
    target N (OAI.EditApproximation.integerParameters N).P (OAI.EditApproximation.inputSmallLog N) (40 * OAI.EditApproximation.smallLogExponent N)
    (OAI.EditApproximation.inputHeight N) (OAI.EditApproximation.inputSmallLog N ^ 80) (OAI.EditApproximation.computedSeedPassCount N) (OAI.EditApproximation.inputHeight N ^ 2))

noncomputable def computedPhysicalCoarseLaw (source target : List ℕ) (N : ℕ) :
    Measure (OAI.EditApproximation.ComputedPhysicalCoarseDraw source target N) :=
  OAI.EditApproximation.coarseFullSeedMeasure (OAI.EditApproximation.integerParameters N).B (OAI.EditApproximation.computedPhysicalCoarseDepth source target N)
    (fun entry => OAI.EditApproximation.physicalSource source entry.1)
    (fun entry => OAI.EditApproximation.substring target entry.2.lo entry.2.hi)

abbrev ComputedExecutionOutcome (source target : List ℕ) (N : ℕ) :=
  OAI.EditApproximation.ComputedPhysicalCoarseDraw source target N × OAI.EditApproximation.ComputedRejectionRuntime source target N

noncomputable def computedExecutionLaw (source target : List ℕ) (N : ℕ) :
    Measure (OAI.EditApproximation.ComputedExecutionOutcome source target N) :=
  (OAI.EditApproximation.computedPhysicalCoarseLaw source target N).prod
    (OAI.EditApproximation.rejectionRuntimeArrayLaw (OAI.EditApproximation.physicalFamilyRange (M := (OAI.EditApproximation.integerParameters N).M)
      (J := OAI.EditApproximation.intervalTreeDepth (OAI.EditApproximation.integerParameters N).M source.length) (R := OAI.EditApproximation.inputHeight N ^ 2)
      target N (OAI.EditApproximation.integerParameters N).P (OAI.EditApproximation.inputSmallLog N) (40 * OAI.EditApproximation.smallLogExponent N)
      (OAI.EditApproximation.inputHeight N) (OAI.EditApproximation.inputSmallLog N ^ 80) (OAI.EditApproximation.computedSeedPassCount N) (OAI.EditApproximation.inputHeight N ^ 2)))

abbrev ComputedFullOutcome (source target : List ℕ) (N : ℕ) :=
  Unit ⊕ OAI.EditApproximation.ComputedExecutionOutcome source target N

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

open MeasureTheory ProbabilityTheory

variable {α : Type} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R] (source target : List α) (N P T S H : ℕ)

local notation (name := source_Combinatorics_EditApproximation_Refinement_PhysicalFamilyRuntime_4) "SeedState" => ClampedPhysicalSeed M J target.length N

local notation (name := source_Combinatorics_EditApproximation_Refinement_PhysicalFamilyRuntime_5) "ell" => inputSmallLog N

local notation (name := source_Combinatorics_EditApproximation_Refinement_PhysicalFamilyRuntime_6) "exponent" => (40 * smallLogExponent N : ℕ)

local notation (name := source_Combinatorics_EditApproximation_Refinement_PhysicalFamilyRuntime_7) "passes" => computedSeedPassCount N

local notation (name := source_Combinatorics_EditApproximation_Refinement_PhysicalFamilyRuntime_8) "FamilyRange" => physicalFamilyRange (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes (H ^ 2)

local notation (name := source_Combinatorics_EditApproximation_Refinement_PhysicalFamilyRuntime_9) "Family" => PhysicalFamilyScalarDraw (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes (H ^ 2)

abbrev PhysicalFamilyRuntimeOutcome := SeedState × OAI.EditApproximation.RejectionRuntimeArray FamilyRange

def physicalFamilyRuntimeAccepted
    (execution : OAI.EditApproximation.PhysicalFamilyRuntimeOutcome (M := M) (J := J) (R := R) target N P H) : SeedState × Family :=
  (execution.1, execution.2.2)

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

open MeasureTheory ProbabilityTheory Filter

def physicalLargeInput (N : ℕ) (epsilon : OAI.EditApproximation.BinaryFraction) : Prop :=
  (OAI.EditApproximation.inspectAccuracyWithWork (OAI.EditApproximation.inputHeight N) epsilon).1.isSome = true ∧
    OAI.EditApproximation.largeAccuracyInput N epsilon.value ∧
    Nat.size (OAI.EditApproximation.localOnlineMassBound (OAI.EditApproximation.integerParameters N).M (OAI.EditApproximation.integerParameters N).P
      (OAI.EditApproximation.inputHeight N)) ≤ OAI.EditApproximation.inputHeight N

instance physicalLargeInput_decidable (N : ℕ) (epsilon : OAI.EditApproximation.BinaryFraction) :
    Decidable (OAI.EditApproximation.physicalLargeInput N epsilon) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

open MeasureTheory ProbabilityTheory

variable {α : Type} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R] (source target : List α) (N P T S H : ℕ)

local notation (name := source_Combinatorics_EditApproximation_Refinement_PhysicalFamilyRejectionWork_4) "SeedState" => ClampedPhysicalSeed M J target.length N

local notation (name := source_Combinatorics_EditApproximation_Refinement_PhysicalFamilyRejectionWork_5) "ell" => inputSmallLog N

local notation (name := source_Combinatorics_EditApproximation_Refinement_PhysicalFamilyRejectionWork_6) "exponent" => (40 * smallLogExponent N : ℕ)

local notation (name := source_Combinatorics_EditApproximation_Refinement_PhysicalFamilyRejectionWork_7) "passes" => computedSeedPassCount N

local notation (name := source_Combinatorics_EditApproximation_Refinement_PhysicalFamilyRejectionWork_8) "Key" => PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes (H ^ 2)

local notation (name := source_Combinatorics_EditApproximation_Refinement_PhysicalFamilyRejectionWork_9) "Table" => ChargedPhysicalRequest M J target.length (passes + 1) (H ^ 2) T S

local notation (name := source_Combinatorics_EditApproximation_Refinement_PhysicalFamilyRejectionWork_10) "FamilyRange" => physicalFamilyRange (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes (H ^ 2)

noncomputable def physicalFamilyMemoBits (hH : 0 < H) (bits : ℕ)
    (encode : Sum Key Table → ℕ) (rootQ : OAI.EditApproximation.TargetInterval target.length) (seed : SeedState)
    (execution : OAI.EditApproximation.RejectionRuntimeArray FamilyRange) : ℝ :=
  OAI.EditApproximation.rejectionSelectedBits FamilyRange (fun key accepted => Sum.inl key ∈
    (OAI.EditApproximation.physicalFamilyMemoResult source target N P T S H hH bits encode rootQ (seed, accepted)).freshKeys)
    execution

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

open Filter MeasureTheory

noncomputable def computedFamilyResult (source target : List ℕ) (N : ℕ)
    (input : OAI.EditApproximation.ComputedFamilyInput source target N) :=
  OAI.EditApproximation.physicalFamilyMemoResult source target N (OAI.EditApproximation.integerParameters N).P (OAI.EditApproximation.integerParameters N).T
    (OAI.EditApproximation.integerParameters N).S (OAI.EditApproximation.inputHeight N) (Nat.two_pow_pos _)
    (16384 * OAI.EditApproximation.inputHeight N + 5) (OAI.EditApproximation.computedFamilyMemoCode source target N (OAI.EditApproximation.inputHeight N ^ 2))
    (OAI.EditApproximation.finalTargetState target.length) input

noncomputable def computedFamilyRejectionWork (source target : List ℕ) (N : ℕ)
    (execution : OAI.EditApproximation.PhysicalFamilyRuntimeOutcome (M := (OAI.EditApproximation.integerParameters N).M)
      (J := OAI.EditApproximation.intervalTreeDepth (OAI.EditApproximation.integerParameters N).M source.length) (R := OAI.EditApproximation.inputHeight N ^ 2)
      target N (OAI.EditApproximation.integerParameters N).P (OAI.EditApproximation.inputHeight N)) : ℝ :=
  OAI.EditApproximation.physicalFamilyMemoBits source target N (OAI.EditApproximation.integerParameters N).P (OAI.EditApproximation.integerParameters N).T
    (OAI.EditApproximation.integerParameters N).S (OAI.EditApproximation.inputHeight N) (Nat.two_pow_pos _) (16384 * OAI.EditApproximation.inputHeight N + 5)
    (OAI.EditApproximation.computedFamilyMemoCode source target N (OAI.EditApproximation.inputHeight N ^ 2)) (OAI.EditApproximation.finalTargetState target.length)
    execution.1 execution.2

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

open MeasureTheory

variable {α : Type u_1} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R] (source target : List α) (N P H T S passes copies : ℕ) (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ) (draw : PhysicalFamilyScalarDraw (M := M) (J := J) (R := R)
    target N P (inputSmallLog N) (40 * smallLogExponent N) H (inputSmallLog N ^ 80) passes copies) (B : ℕ) [NeZero B] [MeasurableSpace (Fin B)] [MeasurableSingletonClass (Fin B)] (depth : PhysicalEntry M J target.length → ℕ)

local notation (name := source_Combinatorics_EditApproximation_Refinement_PhysicalFamilyMemoCoarse_5) "ell" => inputSmallLog N

local notation (name := source_Combinatorics_EditApproximation_Refinement_PhysicalFamilyMemoCoarse_6) "exponent" => (40 * smallLogExponent N : ℕ)

local notation (name := source_Combinatorics_EditApproximation_Refinement_PhysicalFamilyMemoCoarse_7) "Key" => PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes copies

local notation (name := source_Combinatorics_EditApproximation_Refinement_PhysicalFamilyMemoCoarse_8) "Table" => ChargedPhysicalRequest M J target.length (passes + 1) copies T S

local notation (name := source_Combinatorics_EditApproximation_Refinement_PhysicalFamilyMemoCoarse_9) "readGroup" => physicalFamilyGroupRead (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes copies

local notation (name := source_Combinatorics_EditApproximation_Refinement_PhysicalFamilyMemoCoarse_10) "readInteger" => physicalFamilyOnlineRead (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes copies

local notation (name := source_Combinatorics_EditApproximation_Refinement_PhysicalFamilyMemoCoarse_11) "answer" => physicalFamilyAnswer target N P ell exponent H (ell ^ 80) passes copies draw

noncomputable def physicalFamilyMemoCoarseWork (bits : ℕ) (encode : Sum Key Table → ℕ)
    (root : Table) (coarse : OAI.EditApproximation.PhysicalCoarseDraw source target B depth) : ℝ :=
  let initial := OAI.EditApproximation.clampedSeedNat (OAI.EditApproximation.physicalCoarseSeedTable source target N B depth coarse)
  let result := OAI.EditApproximation.chargedRandomMemoEvaluate source target N P ell exponent H (ell ^ 80)
    T S (passes + 1) copies factor multiplier tau eta kappa delta readGroup readInteger initial
    answer bits encode root
  ∑ entry, OAI.EditApproximation.selectionIndicator (Sum.inr (Sum.inl entry) ∈ result.freshKeys) *
    (OAI.EditApproximation.coarseInitialArrayWork B (depth entry) (OAI.EditApproximation.initialThresholdQ N) (OAI.EditApproximation.initialLambda N)
      (OAI.EditApproximation.physicalSource source entry.1) (OAI.EditApproximation.substring target entry.2.lo entry.2.hi) (coarse entry) : ℝ)

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

open MeasureTheory

variable {α : Type} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R] (source target : List α) (N P H B : ℕ) (depth : PhysicalEntry M J target.length → ℕ)

abbrev PhysicalCoarseExecution := OAI.EditApproximation.PhysicalCoarseDraw source target B depth ×
  OAI.EditApproximation.RejectionRuntimeArray (OAI.EditApproximation.physicalFamilyRange (M := M) (J := J) (R := R)
    target N P (OAI.EditApproximation.inputSmallLog N) (40 * OAI.EditApproximation.smallLogExponent N) H
      (OAI.EditApproximation.inputSmallLog N ^ 80) (OAI.EditApproximation.computedSeedPassCount N) (H ^ 2))

noncomputable def physicalCoarseExecutionProjection
    (execution : OAI.EditApproximation.PhysicalCoarseExecution (R := R) source target N P H B depth) :
    OAI.EditApproximation.PhysicalFamilyRuntimeOutcome (M := M) (J := J) (R := R) target N P H :=
  (OAI.EditApproximation.physicalCoarseSeedTable source target N B depth execution.1, execution.2)

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

open MeasureTheory

noncomputable def computedExecutionProjection (source target : List ℕ) (N : ℕ) :=
  OAI.EditApproximation.physicalCoarseExecutionProjection (M := (OAI.EditApproximation.integerParameters N).M)
    (J := OAI.EditApproximation.intervalTreeDepth (OAI.EditApproximation.integerParameters N).M source.length) (R := OAI.EditApproximation.inputHeight N ^ 2)
    source target N (OAI.EditApproximation.integerParameters N).P (OAI.EditApproximation.inputHeight N) (OAI.EditApproximation.integerParameters N).B
    (OAI.EditApproximation.computedPhysicalCoarseDepth source target N)

noncomputable def computedFullLaw (source target : List ℕ) (N : ℕ) (epsilon : OAI.EditApproximation.BinaryFraction) :
    Measure (OAI.EditApproximation.ComputedFullOutcome source target N) :=
  if OAI.EditApproximation.physicalLargeInput N epsilon then (OAI.EditApproximation.computedExecutionLaw source target N).map Sum.inr
  else Measure.dirac (Sum.inl ())

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

open MeasureTheory Filter

noncomputable def computedExecutionAccepted (source target : List ℕ) (N : ℕ)
    (execution : OAI.EditApproximation.ComputedExecutionOutcome source target N) : OAI.EditApproximation.ComputedFamilyInput source target N :=
  OAI.EditApproximation.physicalFamilyRuntimeAccepted target N (OAI.EditApproximation.integerParameters N).P (OAI.EditApproximation.inputHeight N)
    (OAI.EditApproximation.computedExecutionProjection source target N execution)

noncomputable def computedExecutionRejectionWork (source target : List ℕ) (N : ℕ) :
    OAI.EditApproximation.ComputedExecutionOutcome source target N → ℝ :=
  OAI.EditApproximation.computedFamilyRejectionWork source target N ∘ OAI.EditApproximation.computedExecutionProjection source target N

def computedFinalRoot (source target : List ℕ) (N : ℕ) : OAI.EditApproximation.ComputedFamilyTableKey source target N :=
  OAI.EditApproximation.localFinalRootRequest (M := (OAI.EditApproximation.integerParameters N).M)
    (J := OAI.EditApproximation.intervalTreeDepth (OAI.EditApproximation.integerParameters N).M source.length) target N
    (OAI.EditApproximation.integerParameters N).T (OAI.EditApproximation.integerParameters N).S (OAI.EditApproximation.inputHeight N) (Nat.two_pow_pos _)
    (OAI.EditApproximation.finalTargetState target.length)

noncomputable def computedExecutionKernelWork (source target : List ℕ) (N : ℕ)
    (cost : OAI.EditApproximation.ComputedFamilyInput source target N → OAI.EditApproximation.ComputedFamilyMemoKey source target N → ℕ)
    (execution : OAI.EditApproximation.ComputedExecutionOutcome source target N) : ℝ :=
  let input := OAI.EditApproximation.computedExecutionAccepted source target N execution
  OAI.EditApproximation.computedFamilyKernelWork source target N input (cost input)

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

open Filter MeasureTheory

noncomputable def computedExecutionDictionaryWork (source target : List ℕ) (N : ℕ)
    (execution : OAI.EditApproximation.ComputedExecutionOutcome source target N) : ℝ :=
  (OAI.EditApproximation.computedFamilyResult source target N (OAI.EditApproximation.computedExecutionAccepted source target N execution)).dictionaryVisits

noncomputable def computedExecutionAddressWork (source target : List ℕ) (N : ℕ)
    (execution : OAI.EditApproximation.ComputedExecutionOutcome source target N) : ℝ :=
  OAI.EditApproximation.computedFamilyAddressWork source target N (OAI.EditApproximation.computedExecutionAccepted source target N execution)

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

open MeasureTheory Filter

variable {M J R B : ℕ} [NeZero M] [NeZero R] [NeZero B] (source target : List ℕ) (N : ℕ) (depth : PhysicalEntry M J target.length → ℕ) (encode : Sum (PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
    target N (integerParameters N).P (inputSmallLog N) (40 * smallLogExponent N)
    (inputHeight N) (inputSmallLog N ^ 80) (computedSeedPassCount N) (inputHeight N ^ 2))
    (ChargedPhysicalRequest M J target.length (computedSeedPassCount N + 1)
      (inputHeight N ^ 2) (integerParameters N).T (integerParameters N).S) → ℕ)

noncomputable def symbolicComputedCoarseWork :=
  fun draw => OAI.EditApproximation.physicalFamilyMemoCoarseWork source target N (OAI.EditApproximation.integerParameters N).P
    (OAI.EditApproximation.inputHeight N) (OAI.EditApproximation.integerParameters N).T (OAI.EditApproximation.integerParameters N).S (OAI.EditApproximation.computedSeedPassCount N)
    (OAI.EditApproximation.inputHeight N ^ 2) (OAI.EditApproximation.scheduledSeedFactor N) (OAI.EditApproximation.scheduledSeedMultiplier N)
    (OAI.EditApproximation.rationalParameters (OAI.EditApproximation.inputSmallLog N)).tau (OAI.EditApproximation.rationalParameters (OAI.EditApproximation.inputSmallLog N)).eta
    (OAI.EditApproximation.rationalParameters (OAI.EditApproximation.inputSmallLog N)).kappa (OAI.EditApproximation.rationalParameters (OAI.EditApproximation.inputSmallLog N)).delta
    draw B depth (16384 * OAI.EditApproximation.inputHeight N + 5) encode
    (OAI.EditApproximation.localFinalRootRequest target N (OAI.EditApproximation.integerParameters N).T (OAI.EditApproximation.integerParameters N).S
      (OAI.EditApproximation.inputHeight N) (Nat.two_pow_pos _) (OAI.EditApproximation.finalTargetState target.length))

noncomputable def symbolicComputedExecutionCoarseWork
    (execution : OAI.EditApproximation.PhysicalCoarseExecution (R := R) source target N
      (OAI.EditApproximation.integerParameters N).P (OAI.EditApproximation.inputHeight N) B depth) : ℝ :=
  OAI.EditApproximation.symbolicComputedCoarseWork source target N depth encode execution.2.2 execution.1

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

open MeasureTheory Filter

noncomputable def computedExecutionCoarseWork (source target : List ℕ) (N : ℕ) :=
  OAI.EditApproximation.symbolicComputedExecutionCoarseWork (M := (OAI.EditApproximation.integerParameters N).M)
    (J := OAI.EditApproximation.intervalTreeDepth (OAI.EditApproximation.integerParameters N).M source.length) (R := OAI.EditApproximation.inputHeight N ^ 2)
    (B := (OAI.EditApproximation.integerParameters N).B) source target N (OAI.EditApproximation.computedPhysicalCoarseDepth source target N)
    (OAI.EditApproximation.computedFamilyMemoCode source target N (OAI.EditApproximation.inputHeight N ^ 2))

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

open Filter MeasureTheory

noncomputable def computedExecutionNonlocalWork (source target : List ℕ) (N : ℕ)
    (execution : OAI.EditApproximation.ComputedExecutionOutcome source target N) : ℝ :=
  OAI.EditApproximation.computedExecutionCoarseWork source target N execution +
    OAI.EditApproximation.computedExecutionRejectionWork source target N execution +
    OAI.EditApproximation.computedExecutionDictionaryWork source target N execution +
    OAI.EditApproximation.computedExecutionAddressWork source target N execution

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

variable {M J R B : ℕ} [NeZero M] [NeZero R] [NeZero B] (source target : List ℕ) (N P H T S passes copies : ℕ) (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ) (draw : PhysicalFamilyScalarDraw (M := M) (J := J) (R := R)
    target N P (inputSmallLog N) (40 * smallLogExponent N) H (inputSmallLog N ^ 80) passes copies) (depth : PhysicalEntry M J target.length → ℕ)

local notation (name := source_Combinatorics_EditApproximation_Refinement_PhysicalIndexedCoarseWork_3) "ell" => inputSmallLog N

local notation (name := source_Combinatorics_EditApproximation_Refinement_PhysicalIndexedCoarseWork_4) "exponent" => (40 * smallLogExponent N : ℕ)

local notation (name := source_Combinatorics_EditApproximation_Refinement_PhysicalIndexedCoarseWork_5) "Key" => PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes copies

local notation (name := source_Combinatorics_EditApproximation_Refinement_PhysicalIndexedCoarseWork_6) "Table" => ChargedPhysicalRequest M J target.length (passes + 1) copies T S

local notation (name := source_Combinatorics_EditApproximation_Refinement_PhysicalIndexedCoarseWork_7) "readGroup" => physicalFamilyGroupRead (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes copies

local notation (name := source_Combinatorics_EditApproximation_Refinement_PhysicalIndexedCoarseWork_8) "readInteger" => physicalFamilyOnlineRead (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes copies

local notation (name := source_Combinatorics_EditApproximation_Refinement_PhysicalIndexedCoarseWork_9) "answer" => physicalFamilyAnswer target N P ell exponent H (ell ^ 80) passes copies draw

noncomputable def physicalFamilyIndexedCoarseWork (bits : ℕ) (encode : Sum Key Table → ℕ)
    (root : Table) (coarse : OAI.EditApproximation.PhysicalCoarseDraw source target B depth) : ℝ :=
  let initial := OAI.EditApproximation.clampedSeedNat (OAI.EditApproximation.physicalCoarseSeedTable source target N B depth coarse)
  let result := OAI.EditApproximation.chargedRandomMemoEvaluate source target N P ell exponent H (ell ^ 80)
    T S (passes + 1) copies factor multiplier tau eta kappa delta readGroup readInteger initial
    answer bits encode root
  OAI.EditApproximation.coarseIndexedEntryCostSum source target N depth coarse
    (fun entry => Sum.inr (Sum.inl entry) ∈ result.freshKeys)

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

open Filter MeasureTheory

variable {M J R B : ℕ} [NeZero M] [NeZero R] [NeZero B] (source target : List ℕ) (N : ℕ) (depth : PhysicalEntry M J target.length → ℕ) (encode : Sum (PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
    target N (integerParameters N).P (inputSmallLog N) (40 * smallLogExponent N)
    (inputHeight N) (inputSmallLog N ^ 80) (computedSeedPassCount N) (inputHeight N ^ 2))
    (ChargedPhysicalRequest M J target.length (computedSeedPassCount N + 1)
      (inputHeight N ^ 2) (integerParameters N).T (integerParameters N).S) → ℕ)

noncomputable def symbolicComputedExecutionIndexedCoarseWork
    (execution : OAI.EditApproximation.PhysicalCoarseExecution (R := R) source target N
      (OAI.EditApproximation.integerParameters N).P (OAI.EditApproximation.inputHeight N) B depth) : ℝ :=
  OAI.EditApproximation.physicalFamilyIndexedCoarseWork source target N (OAI.EditApproximation.integerParameters N).P (OAI.EditApproximation.inputHeight N)
    (OAI.EditApproximation.integerParameters N).T (OAI.EditApproximation.integerParameters N).S (OAI.EditApproximation.computedSeedPassCount N)
    (OAI.EditApproximation.inputHeight N ^ 2) (OAI.EditApproximation.scheduledSeedFactor N) (OAI.EditApproximation.scheduledSeedMultiplier N)
    (OAI.EditApproximation.rationalParameters (OAI.EditApproximation.inputSmallLog N)).tau (OAI.EditApproximation.rationalParameters (OAI.EditApproximation.inputSmallLog N)).eta
    (OAI.EditApproximation.rationalParameters (OAI.EditApproximation.inputSmallLog N)).kappa (OAI.EditApproximation.rationalParameters (OAI.EditApproximation.inputSmallLog N)).delta
    execution.2.2 depth (16384 * OAI.EditApproximation.inputHeight N + 5) encode
    (OAI.EditApproximation.localFinalRootRequest target N (OAI.EditApproximation.integerParameters N).T (OAI.EditApproximation.integerParameters N).S
      (OAI.EditApproximation.inputHeight N) (Nat.two_pow_pos _) (OAI.EditApproximation.finalTargetState target.length)) execution.1

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

open Filter MeasureTheory

noncomputable def computedExecutionIndexedCoarseWork (source target : List ℕ) (N : ℕ) :=
  OAI.EditApproximation.symbolicComputedExecutionIndexedCoarseWork (M := (OAI.EditApproximation.integerParameters N).M)
    (J := OAI.EditApproximation.intervalTreeDepth (OAI.EditApproximation.integerParameters N).M source.length) (R := OAI.EditApproximation.inputHeight N ^ 2)
    (B := (OAI.EditApproximation.integerParameters N).B) source target N (OAI.EditApproximation.computedPhysicalCoarseDepth source target N)
    (OAI.EditApproximation.computedFamilyMemoCode source target N (OAI.EditApproximation.inputHeight N ^ 2))

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

variable {M J R B : ℕ} [NeZero M] [NeZero R] [NeZero B] (source target : List ℕ) (N P H T S passes copies : ℕ) (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ) (draw : PhysicalFamilyScalarDraw (M := M) (J := J) (R := R)
    target N P (inputSmallLog N) (40 * smallLogExponent N) H (inputSmallLog N ^ 80) passes copies) (depth : PhysicalEntry M J target.length → ℕ)

local notation (name := source_Combinatorics_EditApproximation_Refinement_PhysicalCoarseSamplingWork_3) "ell" => inputSmallLog N

local notation (name := source_Combinatorics_EditApproximation_Refinement_PhysicalCoarseSamplingWork_4) "exponent" => (40 * smallLogExponent N : ℕ)

local notation (name := source_Combinatorics_EditApproximation_Refinement_PhysicalCoarseSamplingWork_5) "Key" => PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes copies

local notation (name := source_Combinatorics_EditApproximation_Refinement_PhysicalCoarseSamplingWork_6) "Table" => ChargedPhysicalRequest M J target.length (passes + 1) copies T S

local notation (name := source_Combinatorics_EditApproximation_Refinement_PhysicalCoarseSamplingWork_7) "readGroup" => physicalFamilyGroupRead (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes copies

local notation (name := source_Combinatorics_EditApproximation_Refinement_PhysicalCoarseSamplingWork_8) "readInteger" => physicalFamilyOnlineRead (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes copies

local notation (name := source_Combinatorics_EditApproximation_Refinement_PhysicalCoarseSamplingWork_9) "answer" => physicalFamilyAnswer target N P ell exponent H (ell ^ 80) passes copies draw

noncomputable def physicalFamilyCoarseSamplingWork (bits : ℕ) (encode : Sum Key Table → ℕ)
    (root : Table) (coarse : OAI.EditApproximation.PhysicalCoarseDraw source target B depth) : ℝ :=
  let initial := OAI.EditApproximation.clampedSeedNat (OAI.EditApproximation.physicalCoarseSeedTable source target N B depth coarse)
  let result := OAI.EditApproximation.chargedRandomMemoEvaluate source target N P ell exponent H (ell ^ 80)
    T S (passes + 1) copies factor multiplier tau eta kappa delta readGroup readInteger initial
    answer bits encode root
  ∑ entry, OAI.EditApproximation.selectionIndicator (Sum.inr (Sum.inl entry) ∈ result.freshKeys) *
    ((Nat.size B * OAI.EditApproximation.coarseInitialLabelCount B (depth entry) (OAI.EditApproximation.initialThresholdQ N) (OAI.EditApproximation.initialLambda N)
      (OAI.EditApproximation.physicalSource source entry.1) (OAI.EditApproximation.substring target entry.2.lo entry.2.hi) (coarse entry) : ℕ) : ℝ)

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

open MeasureTheory Filter

variable {M J R B : ℕ} [NeZero M] [NeZero R] [NeZero B] (source target : List ℕ) (N : ℕ) (depth : PhysicalEntry M J target.length → ℕ) (encode : Sum (PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
    target N (integerParameters N).P (inputSmallLog N) (40 * smallLogExponent N)
    (inputHeight N) (inputSmallLog N ^ 80) (computedSeedPassCount N) (inputHeight N ^ 2))
    (ChargedPhysicalRequest M J target.length (computedSeedPassCount N + 1)
      (inputHeight N ^ 2) (integerParameters N).T (integerParameters N).S) → ℕ)

noncomputable def symbolicComputedExecutionCoarseSamplingWork
    (execution : OAI.EditApproximation.PhysicalCoarseExecution (R := R) source target N
      (OAI.EditApproximation.integerParameters N).P (OAI.EditApproximation.inputHeight N) B depth) : ℝ :=
  OAI.EditApproximation.physicalFamilyCoarseSamplingWork source target N (OAI.EditApproximation.integerParameters N).P (OAI.EditApproximation.inputHeight N)
    (OAI.EditApproximation.integerParameters N).T (OAI.EditApproximation.integerParameters N).S (OAI.EditApproximation.computedSeedPassCount N)
    (OAI.EditApproximation.inputHeight N ^ 2) (OAI.EditApproximation.scheduledSeedFactor N) (OAI.EditApproximation.scheduledSeedMultiplier N)
    (OAI.EditApproximation.rationalParameters (OAI.EditApproximation.inputSmallLog N)).tau (OAI.EditApproximation.rationalParameters (OAI.EditApproximation.inputSmallLog N)).eta
    (OAI.EditApproximation.rationalParameters (OAI.EditApproximation.inputSmallLog N)).kappa (OAI.EditApproximation.rationalParameters (OAI.EditApproximation.inputSmallLog N)).delta
    execution.2.2 depth (16384 * OAI.EditApproximation.inputHeight N + 5) encode
    (OAI.EditApproximation.localFinalRootRequest target N (OAI.EditApproximation.integerParameters N).T (OAI.EditApproximation.integerParameters N).S
      (OAI.EditApproximation.inputHeight N) (Nat.two_pow_pos _) (OAI.EditApproximation.finalTargetState target.length)) execution.1

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

open MeasureTheory Filter

noncomputable def computedExecutionCoarseSamplingWork (source target : List ℕ) (N : ℕ) :=
  OAI.EditApproximation.symbolicComputedExecutionCoarseSamplingWork (M := (OAI.EditApproximation.integerParameters N).M)
    (J := OAI.EditApproximation.intervalTreeDepth (OAI.EditApproximation.integerParameters N).M source.length) (R := OAI.EditApproximation.inputHeight N ^ 2)
    (B := (OAI.EditApproximation.integerParameters N).B) source target N (OAI.EditApproximation.computedPhysicalCoarseDepth source target N)
    (OAI.EditApproximation.computedFamilyMemoCode source target N (OAI.EditApproximation.inputHeight N ^ 2))

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

variable {M J R : ℕ} [NeZero M] [NeZero R] (source target : List ℕ) (N P H T S passes copies : ℕ) (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ) (initial : PhysicalEntry M J target.length → ℕ) (draw : PhysicalFamilyScalarDraw (M := M) (J := J) (R := R)
    target N P (inputSmallLog N) (40 * smallLogExponent N) H (inputSmallLog N ^ 80) passes copies)

local notation (name := source_Combinatorics_EditApproximation_Refinement_PhysicalCoarsePreparation_5) "ell" => inputSmallLog N

local notation (name := source_Combinatorics_EditApproximation_Refinement_PhysicalCoarsePreparation_6) "exponent" => (40 * smallLogExponent N : ℕ)

local notation (name := source_Combinatorics_EditApproximation_Refinement_PhysicalCoarsePreparation_7) "Key" => PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes copies

local notation (name := source_Combinatorics_EditApproximation_Refinement_PhysicalCoarsePreparation_8) "Table" => ChargedPhysicalRequest M J target.length (passes + 1) copies T S

local notation (name := source_Combinatorics_EditApproximation_Refinement_PhysicalCoarsePreparation_9) "readGroup" => physicalFamilyGroupRead (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes copies

local notation (name := source_Combinatorics_EditApproximation_Refinement_PhysicalCoarsePreparation_10) "readInteger" => physicalFamilyOnlineRead (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes copies

local notation (name := source_Combinatorics_EditApproximation_Refinement_PhysicalCoarsePreparation_11) "answer" => physicalFamilyAnswer target N P ell exponent H (ell ^ 80) passes copies draw

noncomputable def physicalFamilyCoarsePreparationWork (bits : ℕ) (encode : Sum Key Table → ℕ)
    (root : Table) : ℝ :=
  let result := OAI.EditApproximation.chargedRandomMemoEvaluate source target N P ell exponent H (ell ^ 80)
    T S (passes + 1) copies factor multiplier tau eta kappa delta readGroup readInteger initial
    answer bits encode root
  ∑ entry, OAI.EditApproximation.selectionIndicator (Sum.inr (Sum.inl entry) ∈ result.freshKeys) *
    (OAI.EditApproximation.physicalCoarsePreparationCost source target entry : ℝ)

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

open Filter MeasureTheory

noncomputable def computedFamilyCoarsePreparationWork (source target : List ℕ) (N : ℕ)
    (input : OAI.EditApproximation.ComputedFamilyInput source target N) : ℝ :=
  OAI.EditApproximation.physicalFamilyCoarsePreparationWork source target N (OAI.EditApproximation.integerParameters N).P (OAI.EditApproximation.inputHeight N)
    (OAI.EditApproximation.integerParameters N).T (OAI.EditApproximation.integerParameters N).S (OAI.EditApproximation.computedSeedPassCount N) (OAI.EditApproximation.inputHeight N ^ 2)
    (OAI.EditApproximation.scheduledSeedFactor N) (OAI.EditApproximation.scheduledSeedMultiplier N)
    (OAI.EditApproximation.rationalParameters (OAI.EditApproximation.inputSmallLog N)).tau (OAI.EditApproximation.rationalParameters (OAI.EditApproximation.inputSmallLog N)).eta
    (OAI.EditApproximation.rationalParameters (OAI.EditApproximation.inputSmallLog N)).kappa (OAI.EditApproximation.rationalParameters (OAI.EditApproximation.inputSmallLog N)).delta
    (OAI.EditApproximation.clampedSeedNat input.1) input.2 (16384 * OAI.EditApproximation.inputHeight N + 5)
    (OAI.EditApproximation.computedFamilyMemoCode source target N (OAI.EditApproximation.inputHeight N ^ 2))
    (OAI.EditApproximation.computedFinalRoot source target N)

noncomputable def computedExecutionCoarsePreparationWork (source target : List ℕ) (N : ℕ)
    (execution : OAI.EditApproximation.ComputedExecutionOutcome source target N) : ℝ :=
  OAI.EditApproximation.computedFamilyCoarsePreparationWork source target N (OAI.EditApproximation.computedExecutionAccepted source target N execution)

noncomputable def computedExecutionReadChargedWork (source target : List ℕ) (N : ℕ)
    (execution : OAI.EditApproximation.ComputedExecutionOutcome source target N) : ℝ :=
  OAI.EditApproximation.computedExecutionIndexedCoarseWork source target N execution +
    OAI.EditApproximation.computedExecutionCoarseSamplingWork source target N execution +
    OAI.EditApproximation.computedExecutionNonlocalWork source target N execution +
    OAI.EditApproximation.computedExecutionCoarsePreparationWork source target N execution

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

open MeasureTheory Filter

noncomputable def computedExecutionTotalWork (source target : List ℕ) (N : ℕ)
    (cost : OAI.EditApproximation.ComputedFamilyInput source target N → OAI.EditApproximation.ComputedFamilyMemoKey source target N → ℕ)
    (execution : OAI.EditApproximation.ComputedExecutionOutcome source target N) : ℝ :=
  OAI.EditApproximation.computedExecutionReadChargedWork source target N execution +
    OAI.EditApproximation.computedExecutionKernelWork source target N cost execution

noncomputable def computedFullOutputWork (source target : List ℕ) (N : ℕ)
    (cost : OAI.EditApproximation.ComputedFamilyInput source target N → OAI.EditApproximation.ComputedFamilyMemoKey source target N → ℕ)
    (setup : ℝ) (shared : ℕ) (output : OAI.EditApproximation.ComputedFamilyInput source target N → ℕ)
    (fallbackOutput : ℕ) : OAI.EditApproximation.ComputedFullOutcome source target N → ℝ
  | .inl _ => setup + (OAI.EditApproximation.chargedSuffixDP source target).2 + fallbackOutput
  | .inr execution => setup + shared + OAI.EditApproximation.computedExecutionTotalWork source target N cost execution +
      output (OAI.EditApproximation.computedExecutionAccepted source target N execution)

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

open BitQuery

variable {α : Type u_1} {M J R : ℕ} (target : List α) (N P F exponent H Q passes copies pass copy : ℕ)

def queryFamilyTagAllocation
    (scalar : OAI.EditApproximation.PhysicalScalarKey M J N target.length exponent F Q R (OAI.EditApproximation.localOnlineMassBound M P H)) : ℕ :=
  OAI.EditApproximation.binaryNaturalDivAllocation pass (passes + 1) + OAI.EditApproximation.binaryNaturalDivAllocation copy (copies + 1) +
    OAI.EditApproximation.physicalScalarCodeAllocation scalar + 9

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation.BitQuery.Footprint

def rankedBitMemoCells {κ : Type u_1} (rank : κ → ℕ)
    (program : (key : κ) → OAI.EditApproximation.BitQuery {child : κ // rank child < rank key} OAI.EditApproximation.BinaryFraction)
    (heap : ∀ key, OAI.EditApproximation.BitQuery.Footprint (program key))
    (bits : ℕ) (encode addressCells : κ → ℕ) (key : κ) (memory : OAI.EditApproximation.BinaryMemo OAI.EditApproximation.BinaryFraction) : ℕ :=
  let found := memory.lookupCosted (OAI.EditApproximation.binaryMemoKey bits (encode key))
  match found.1 with
  | some _ => OAI.EditApproximation.memoRequestCells bits (addressCells key)
  | none => OAI.EditApproximation.memoRequestCells bits (addressCells key) + (heap key).runCells
      (fun child previous => OAI.EditApproximation.rankedBitMemoEvaluate rank program bits encode child.val previous)
      (fun child previous => rankedBitMemoCells rank program heap bits encode addressCells child.val previous)
      memory
termination_by rank key
decreasing_by exact child.property

end OAI.EditApproximation.BitQuery.Footprint

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

open BitQuery

local instance queryArityNeZero (N : ℕ) : NeZero (OAI.EditApproximation.integerParameters N).M :=
  ⟨by change 2 ^ (OAI.EditApproximation.heightExponent N / 20) ≠ 0; exact Nat.ne_of_gt (Nat.two_pow_pos _)⟩

end OAI.EditApproximation

end


