-- Prove2me | Definitions.Def_OAIQ045S001
-- name    : OAIQ045S001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T12:19:00.301494+00:00
-- url     : https://prove2.me/theorems/c901a9f5-6da1-4a39-ac2b-07c04e94bb49
-- title:
--   Definitions bundle OAIQ045S001 of the split of OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SharpLogRamsey.main`, carved from OpenAI's openai/math development (OpenAI, *Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)*, OpenAI Math Release, September 24, 2026, result family 170, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 534 declarations of OpenAI's Lean: 406 definitions, 5 inductive types or structures, 17 instances and 106 theorems. The definitions and types are `OAI.SharpLogRamsey.Marking.classCount`, `OAI.SharpLogRamsey.Marking.finiteIterDualProjective`, `OAI.SharpLogRamsey.Marking.finiteIterProjective`, `OAI.SharpLogRamsey.Marking.flat_ActualHighRankClass_3`, `OAI.SharpLogRamsey.Marking.flat_ActualHighRankClass_4`, `OAI.SharpLogRamsey.Marking.flat_ActualHighRankOrdered_3`, `OAI.SharpLogRamsey.Marking.flat_ActualHighRankOrdered_4`, `OAI.SharpLogRamsey.Marking.flat_ActualHighRankStep_3`, `OAI.SharpLogRamsey.Marking.flat_ActualHighRankStep_4`, `OAI.SharpLogRamsey.Marking.gainDualProjective`, `OAI.SharpLogRamsey.Marking.gainProjective`, `OAI.SharpLogRamsey.Marking.jointJ`, `OAI.SharpLogRamsey.Marking.noCtxDualProjective`, `OAI.SharpLogRamsey.Marking.noCtxProjective`, `OAI.SharpLogRamsey.Marking.selectDoubleProjective`, `OAI.SharpLogRamsey.Marking.selectDualProjective`, `OAI.SharpLogRamsey.Marking.selectProjective`, `OAI.SharpLogRamsey.Marking.stepDoubleProjective`, `OAI.SharpLogRamsey.Marking.stepDualProjective`, `OAI.SharpLogRamsey.Marking.stepProjective`, `OAI.SharpLogRamsey.Marking.terminalDualProjective`, `OAI.SharpLogRamsey.Marking.terminalProjective`, `OAI.SharpLogRamsey.Marking.trackDualProjective`, `OAI.SharpLogRamsey.Marking.trackProjective`, `OAI.SharpLogRamsey.Marking.uniformDualProjective`, `OAI.SharpLogRamsey.Marking.uniformProjective`, `OAI.SharpLogRamsey.Marking.witnessDualProjective`, `OAI.SharpLogRamsey.Marking.witnessProjective`, `OAI.SharpLogRamsey.MomentBudgetBridge.anchorBudget`, `OAI.SharpLogRamsey.MomentBudgetBridge.certificateOverhead`, `OAI.SharpLogRamsey.MomentBudgetBridge.shiftOverhead`, `OAI.SharpLogRamsey.NonplaneCertificate.Index`, `OAI.SharpLogRamsey.PencilContrast.degree`, `OAI.SharpLogRamsey.PlanarLearning.Budget`, `OAI.SharpLogRamsey.PlanarLearning.flat_JoinedPlanarBoth_2`, `OAI.SharpLogRamsey.PlanarLearning.flat_JoinedPlanarCover_3`, `OAI.SharpLogRamsey.PlanarLearning.flat_JoinedPlanarCover_4`, `OAI.SharpLogRamsey.PlanarLearning.flat_JoinedPlanarDescription_3`, `OAI.SharpLogRamsey.PlanarLearning.flat_JoinedPlanarGeometry_3`, `OAI.SharpLogRamsey.PlanarLearning.flat_JoinedPlanarGeometry_4` and 371 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/SharpRamsey, in whole or in part: `SharpRamsey_Bounds_SumFiberCenter`, `SharpRamsey_Bounds_Upper`, `SharpRamsey_Construction_GraphWitness`, `SharpRamsey_Entropy_AnchorEventsRealized`, `SharpRamsey_Entropy_CompleteProgramWeight`, `SharpRamsey_Entropy_ComponentLabelWitness`, `SharpRamsey_Entropy_ExternalMass`, `SharpRamsey_Entropy_ForcedHits`, `SharpRamsey_Entropy_HighMoments`, `SharpRamsey_Entropy_IntegralTypicalScoreSq`, `SharpRamsey_Entropy_LabelledFilterCard`, `SharpRamsey_Entropy_LargeCard`, `SharpRamsey_Entropy_MakePair`, `SharpRamsey_Entropy_MarkingTwoEntropy`, `SharpRamsey_Entropy_NewEvents`, `SharpRamsey_Entropy_PatchNotMem`, `SharpRamsey_Entropy_PoissonLaw`, `SharpRamsey_Entropy_ShiftKernelSum`, `SharpRamsey_Entropy_SinglesUnique`, `SharpRamsey_Entropy_TerminalEntropy`, `SharpRamsey_Entropy_TestActualSecondMoment`, `SharpRamsey_Entropy_TreeMessageEntropy`, `SharpRamsey_Entropy_TruncatedTupleIntegrable`, `SharpRamsey_Entropy_TwoAnchorCrossCost`, `SharpRamsey_Entropy_WitnessList`, `SharpRamsey_Execution_PreparedOutput`, `SharpRamsey_Exposure_DivergenceMap`, `SharpRamsey_Exposure_ExposureBudget`, `SharpRamsey_Exposure_ExposureModel`, `SharpRamsey_Exposure_FreshBlockBudgets`, `SharpRamsey_Exposure_PreparedMixture`, `SharpRamsey_Exposure_RemainingEmbedding`, `SharpRamsey_Exposure_RestrictionBudget`, `SharpRamsey_Exposure_RestrictionGeometry`, `SharpRamsey_Exposure_StreamTransport`, `SharpRamsey_Geometry_HessianTangent`, `SharpRamsey_Geometry_PencilGeometry`, `SharpRamsey_Geometry_PreparedRadial`, `SharpRamsey_Geometry_PreparedRadialBounds`, `SharpRamsey_Geometry_PreparedRadialCount`, `SharpRamsey_Geometry_ProjectionCenterBounds`, `SharpRamsey_Geometry_ProjectionPublic`, `SharpRamsey_Geometry_RadialExceptions`, `SharpRamsey_Geometry_TestRadialWeights`, `SharpRamsey_Geometry_TestRowPencils`, `SharpRamsey_Geometry_TotalDegreeCombination`, `SharpRamsey_Geometry_Triple`, `SharpRamsey_Geometry_VectorMap`, `SharpRamsey_Geometry_Weight`, `SharpRamsey_Learning_HighRankPrepared`, `SharpRamsey_Learning_PoissonSupport`, `SharpRamsey_Learning_PreparedDecoder`, `SharpRamsey_Learning_PreparedDescription`, `SharpRamsey_Learning_PreparedGeometry`, `SharpRamsey_Learning_PreparedPointProposals`, `SharpRamsey_Learning_PreparedProposals`, `SharpRamsey_Learning_PreparedResidualBounds`, `SharpRamsey_Learning_PreparedShortRow`, `SharpRamsey_Learning_PreparedTypical`, `SharpRamsey_Learning_PreparedVariance`, `SharpRamsey_Learning_RegularPreparationBounds`, `SharpRamsey_Learning_TestActualMoment`, `SharpRamsey_Learning_TestActualRow`, `SharpRamsey_Learning_TestLearningIncidence`, `SharpRamsey_Learning_TestLearningRowBase`, `SharpRamsey_Learning_TestPointTail`, `SharpRamsey_Learning_TestRowEmpty`, `SharpRamsey_Learning_TestRowScore`, `SharpRamsey_Marking_AtomEscape`, `SharpRamsey_Marking_CardVectorLifts`, `SharpRamsey_Marking_ClassSelection`, `SharpRamsey_Marking_ClassStep`, `SharpRamsey_Marking_GoodRealization`, `SharpRamsey_Marking_HighGoodHistory`, `SharpRamsey_Marking_HighRank`, `SharpRamsey_Marking_HighRankClass`, `SharpRamsey_Marking_HighRankExperiment`, `SharpRamsey_Marking_HighRankOrdered`, `SharpRamsey_Marking_HighRankStep`, `SharpRamsey_Marking_HighRankStream`, `SharpRamsey_Marking_MarkingClassification`, `SharpRamsey_Marking_MarkingMessage`, `SharpRamsey_Marking_OrderedClassLaw`, `SharpRamsey_Marking_SelectedStep`, `SharpRamsey_Marking_TargetEvent`, `SharpRamsey_Marking_TrackedSelection`, `SharpRamsey_Marking_TrackedStep`, `SharpRamsey_Marking_UniformStep`, `SharpRamsey_Parameters_FiniteIteration`, `SharpRamsey_Parameters_NoContext`, `SharpRamsey_Parameters_SourceScales`, `SharpRamsey_Parameters_TerminalGain`, `SharpRamsey_Planar_PlanarBoth`, `SharpRamsey_Planar_PlanarBudget`, `SharpRamsey_Planar_PlanarCover`, `SharpRamsey_Planar_PlanarDescription`, `SharpRamsey_Planar_PlanarGeometry`, `SharpRamsey_Planar_PlanarPublic`, `SharpRamsey_Planar_PlanarRow`, `SharpRamsey_Planar_PlanarTraining`, `SharpRamsey_Planar_PlanarUniform`, `SharpRamsey_Reciprocal_ProdRectangleEvent`, `SharpRamsey_Reciprocal_ReciprocalBands`, `SharpRamsey_Selection_FilteredPredeletion`, `SharpRamsey_Selection_PredeletionMean`, `SharpRamsey_Selection_SupportThreshold`, `SharpRamsey_Spatial_PreparedSpatialRadial`, `SharpRamsey_Spatial_SpatialActualCover`, `SharpRamsey_Spatial_SpatialBudget`, `SharpRamsey_Spatial_SpatialCostsActual`, `SharpRamsey_Spatial_SpatialCover`, `SharpRamsey_Spatial_SpatialGreedy`, `SharpRamsey_Spatial_SpatialHeaderCover`, `SharpRamsey_Spatial_SpatialPreparation`, `SharpRamsey_Spatial_SpatialPublic`, `SharpRamsey_Spatial_SpatialRow`, `SharpRamsey_Spatial_SpatialSourceCover`, `SharpRamsey_Spatial_SpatialTraining`, `SharpRamsey_Trees_TreeDecoder`, `SharpRamsey_Trees_TreePotential`, `SharpRamsey_Trees_TreeShapes`, `SharpRamsey_Validation_ValidationGapCosts`, `SharpRamsey_Validation_ValidationReturn`, `SharpRamsey_Validation_ValidationReverse`, `SharpRamsey_Windows_GoodPopulation`, `SharpRamsey_Windows_IntegerExperiment`, `SharpRamsey_Windows_IntegerOutput`, `SharpRamsey_Windows_IntegerQuarter`, `SharpRamsey_Windows_IntegerRealization`, `SharpRamsey_Windows_OpenExperiment`, `SharpRamsey_Windows_OpenMovement`, `SharpRamsey_Windows_OpenOutput`, `SharpRamsey_Windows_OpenQuarter`, `SharpRamsey_Windows_OpenRealization`, `SharpRamsey_Windows_PopulationSublist`, `SharpRamsey_Windows_PreparedWindows`, `SharpRamsey_Windows_UniformInteger`, `SharpRamsey_Windows_UniformMovement`, `SharpRamsey_Windows_UniformOpen`, `SharpRamsey_Windows_WindowDeletion`, `SharpRamsey_Windows_WindowLayout`, `SharpRamsey_Windows_WindowTransport`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ045S002`; the statements `OAI.SharpLogRamsey.Marking.eventually_high_ordered`, `OAI.SharpLogRamsey.Selection.Windows.eventually_integer_output`, `OAI.SharpLogRamsey.Selection.Windows.eventually_open_output` and `OAI.SharpLogRamsey.SpatialPublic.actual_cover`; the proof of `OAI.SharpLogRamsey.main`.
-- source:
--   OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 170; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-Logarithmic-Exponents-for-Fixed-Off-Diagonal-Ramsey-Numbers-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/SharpRamsey at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ045_SR.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
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
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_VectorMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Incidence bounds for rich lines and finite point configurations. -/

section
section
namespace SharpLogRamsey.ProjectiveBaseChange
open scoped BigOperators
open Finset Classical
noncomputable section
variable {K E : Type*} [Field K] [Field E] [Algebra K E] {n : ℕ}
def vectorMap : (Fin n → K) →ₗ[K] (Fin n → E) where
  toFun v i := algebraMap K E (v i)
  map_add' x y := by ext i; simp
  map_smul' c x := by ext i; simp [Algebra.smul_def]

@[simp] lemma vectorMap_apply (v : Fin n → K) (i : Fin n) :
    vectorMap (K := K) (E := E) v i = algebraMap K E (v i) := rfl

lemma vectorMap_injective : Function.Injective (vectorMap (K := K) (E := E) (n := n)) := by
  intro v w h
  ext i
  exact (algebraMap K E).injective (congrFun h i)

def vectorSemi : (Fin n → K) →ₛₗ[algebraMap K E] (Fin n → E) where
  toFun v i := algebraMap K E (v i)
  map_add' x y := by ext i; simp
  map_smul' c x := by ext i; simp

@[simp] lemma vectorSemi_apply (v : Fin n → K) (i : Fin n) :
    vectorSemi (K := K) (E := E) v i = algebraMap K E (v i) := rfl

lemma vectorSemi_injective : Function.Injective (vectorSemi (K := K) (E := E) (n := n)) :=
  vectorMap_injective

def pointMap : Projectivization K (Fin n → K) → Projectivization E (Fin n → E) :=
  Projectivization.map vectorSemi vectorSemi_injective

def extendDual (f : (Fin n → K) →ₗ[K] K) : (Fin n → E) →ₗ[E] E :=
  ∑ i, algebraMap K E (f (Pi.single i 1)) • LinearMap.proj i

def extendSpace (W : Submodule K (Fin n → K)) : Submodule E (Fin n → E) :=
  Submodule.span E (vectorMap '' (W : Set (Fin n → K)))

end
end SharpLogRamsey.ProjectiveBaseChange
end

section

namespace SharpLogRamsey.ProjectiveAffineChart
open scoped BigOperators
open Finset Classical
noncomputable section
variable {E : Type*} [Field E] {n : ℕ}

def first (a : Fin n → E) : (Fin (n+1) → E) →ₗ[E] E :=
  LinearMap.proj 0 + ∑ i, a i • LinearMap.proj i.succ

lemma first_apply (a : Fin n → E) (v : Fin (n+1) → E) :
    first a v = v 0 + ∑ i, a i*v i.succ := by simp [first]

def lift (a x : Fin n → E) : Fin (n+1) → E :=
  Fin.cons (1-∑ i, a i*x i) x

@[simp] lemma lift_zero (a x : Fin n → E) : lift a x 0 = 1-∑ i, a i*x i := rfl
@[simp] lemma lift_succ (a x : Fin n → E) (i : Fin n) : lift a x i.succ = x i := rfl
@[simp] lemma first_lift (a x : Fin n → E) : first a (lift a x) = 1 := by
  rw [first_apply]
  simp

lemma lift_ne_zero (a x : Fin n → E) : lift a x ≠ 0 := by
  intro h
  have hh := first_lift a x
  rw [h, map_zero] at hh
  exact zero_ne_one hh

def chart (a : Fin n → E) (P : Projectivization E (Fin (n+1) → E)) : Fin n → E :=
  fun i => (first a P.rep)⁻¹ * P.rep i.succ

end
end SharpLogRamsey.ProjectiveAffineChart
end

section

namespace SharpLogRamsey.RationalAffineChart
open scoped BigOperators
open Finset Classical
open SharpLogRamsey.ProjectiveBaseChange SharpLogRamsey.ProjectiveAffineChart
noncomputable section
variable {K E : Type*} [Field K] [Field E] [Algebra K E] {n : ℕ}

abbrev coord (a : Fin n → E) (P : Projectivization K (Fin (n+1) → K)) : Fin n → E :=
  chart a (pointMap (E := E) P)

def Avoids (a : Fin n → E) (P : Projectivization K (Fin (n+1) → K)) : Prop :=
  first a (pointMap (E := E) P).rep ≠ 0

def homogeneousPlane (a : Fin n → E) (F : MvPolynomial (Fin n) E) :
    (Fin (n+1) → E) →ₗ[E] E :=
  F.coeff 0 • first a +
    ∑ i, F.coeff (Finsupp.single i 1) • LinearMap.proj i.succ

end
end SharpLogRamsey.RationalAffineChart
end

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_HessianTangent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Incidence bounds for rich lines and finite point configurations. -/

section
section
section
open Finset Finsupp

open scoped BigOperators
open MvPolynomial Finsupp

open scoped BigOperators
open MvPolynomial
namespace SharpLogRamsey.Translation
variable {σ K : Type*} [Field K]

noncomputable def translate (x : σ → K) :
    MvPolynomial σ K →ₐ[K] MvPolynomial σ K :=
  MvPolynomial.aeval fun i => X i+C (x i)

@[simp] lemma translate_X (x : σ → K) (i : σ) : translate x (X i) = X i+C (x i) := by
  simp [translate]
@[simp] lemma translate_C (x : σ → K) (c : K) : translate x (C c) = C c := by
  simp [translate]

@[simp] lemma translate_neg_translate (x : σ → K) (F : MvPolynomial σ K) :
    translate (-x) (translate x F) = F := by
  induction F using MvPolynomial.induction_on with
  | C c => simp
  | add f g hf hg => simp only [map_add,hf,hg]
  | mul_X f i hf => simp [hf]

@[simp] lemma translate_translate_neg (x : σ → K) (F : MvPolynomial σ K) :
    translate x (translate (-x) F) = F := by
  simpa using translate_neg_translate (-x) F

end SharpLogRamsey.Translation

open scoped BigOperators
open Finset MvPolynomial UniqueFactorizationMonoid
end
end
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_TotalDegreeCombination
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Incidence bounds for rich lines and finite point configurations. -/

section
section
section
open Finset Finsupp
open scoped BigOperators
open MvPolynomial Finsupp
open scoped BigOperators
open MvPolynomial
open scoped BigOperators
open Finset MvPolynomial UniqueFactorizationMonoid

namespace SharpLogRamsey.NonplaneCertificate
open MvPolynomial
variable {K : Type*} [Field K]
noncomputable section

abbrev Index := (Option (Fin 2) ≃ Fin 3) × Fin 2 × Fin 2

end
end SharpLogRamsey.NonplaneCertificate

open scoped BigOperators
open Finset MvPolynomial
end
end
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_Triple
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Incidence bounds for rich lines and finite point configurations. -/

section
section
section
section
namespace SharpLogRamsey.PolynomialCoordinates
open MvPolynomial
variable {K : Type*} [Field K]
noncomputable section
abbrev Triple := Polynomial (Polynomial (Polynomial K))

def encode : MvPolynomial (Fin 3) K ≃ₐ[K] Triple (K := K) :=
  (renameEquiv K (Equiv.swap 0 2)).trans ((finSuccEquiv K 2).trans
    (Polynomial.mapAlgEquiv ((finSuccEquiv K 1).trans
      (Polynomial.mapAlgEquiv (uniqueAlgEquiv K (Fin 1))))))

@[simp] lemma encode_C (a : K) : encode (C a) = Polynomial.C (Polynomial.C (Polynomial.C a)) := by
  simp [encode,finSuccEquiv_apply,uniqueAlgEquiv_apply]

@[simp] lemma encode_X (i : Fin 3) : encode (X i : MvPolynomial (Fin 3) K) =
    ![Polynomial.C (Polynomial.C Polynomial.X), Polynomial.C Polynomial.X, Polynomial.X] i := by
  have h2 : finSuccEquiv K 2 (X 2) = Polynomial.C (X 1) :=
    finSuccEquiv_X_succ (j := 1)
  have h1 : finSuccEquiv K 2 (X 1) = Polynomial.C (X 0) :=
    finSuccEquiv_X_succ (j := 0)
  have h11 : finSuccEquiv K 1 (X 1) = Polynomial.C (X 0) :=
    finSuccEquiv_X_succ (j := 0)
  fin_cases i <;> simp [encode,h2,h1,h11,finSuccEquiv_X_zero,
    uniqueAlgEquiv_apply,Equiv.swap_apply_def]

def changeHom (a b c : K) : MvPolynomial (Fin 3) K →ₐ[K] MvPolynomial (Fin 3) K :=
  aeval ![X 0-C a*X 1+C (a*c-b)*X 2, X 1-C c*X 2, X 2]
def unchangeHom (a b c : K) : MvPolynomial (Fin 3) K →ₐ[K] MvPolynomial (Fin 3) K :=
  aeval ![X 0+C a*X 1+C b*X 2, X 1+C c*X 2, X 2]

lemma unchange_change (a b c : K) (F : MvPolynomial (Fin 3) K) :
    unchangeHom a b c (changeHom a b c F) = F := by
  induction F using MvPolynomial.induction_on with
  | C r => simp [changeHom,unchangeHom]
  | add f g hf hg => simp only [map_add,hf,hg]
  | mul_X f i hf =>
    simp only [map_mul,hf]
    congr 1
    fin_cases i <;> simp [changeHom,unchangeHom] ; ring
lemma change_unchange (a b c : K) (F : MvPolynomial (Fin 3) K) :
    changeHom a b c (unchangeHom a b c F) = F := by
  induction F using MvPolynomial.induction_on with
  | C r => simp [changeHom,unchangeHom]
  | add f g hf hg => simp only [map_add,hf,hg]
  | mul_X f i hf =>
    simp only [map_mul,hf]
    congr 1
    fin_cases i <;> simp [changeHom,unchangeHom] ; ring

def change (a b c : K) : MvPolynomial (Fin 3) K ≃ₐ[K] MvPolynomial (Fin 3) K :=
  AlgEquiv.ofAlgHom (changeHom a b c) (unchangeHom a b c)
    (AlgHom.ext (change_unchange a b c))
    (AlgHom.ext (unchange_change a b c))

end
end SharpLogRamsey.PolynomialCoordinates

end

end

end
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_Weight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Incidence bounds for rich lines and finite point configurations. -/

section
section
section
section
open scoped BigOperators Classical
open Finset
namespace SharpLogRamsey.Sampling
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable def weight (p : ℝ) (f : V → Bool) : ℝ :=
  ∏ v, if f v then p else 1-p

def selected (f : V → Bool) : Finset V := univ.filter (fun v => f v = true)

noncomputable def count (F : Finset (Finset V)) (S : Finset V) : ℕ :=
  (F.filter (· ⊆ S)).card

end SharpLogRamsey.Sampling

end

end

end

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Bounds_Upper
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The off-diagonal Ramsey upper bound. -/

section
open scoped BigOperators Classical
open Finset

open scoped BigOperators Classical
open Finset
namespace SharpLogRamsey.TriangleFree
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

noncomputable def independentSets : Finset (Finset V) :=
  univ.filter (fun S => G.IsIndepSet (S : Set V))

@[simp] theorem mem_independentSets (S : Finset V) :
    S ∈ independentSets G ↔ G.IsIndepSet (S : Set V) := by
  simp [independentSets]

noncomputable def closed (x : V) : Finset V := insert x (G.neighborFinset x)
noncomputable def outside (x : V) (S : Finset V) : Finset V := S \ closed G x
noncomputable def available (x : V) (J : Finset V) : Finset V :=
  (G.neighborFinset x).filter (fun u => ∀ v ∈ J, ¬G.Adj u v)
noncomputable def fiber (x : V) (J : Finset V) : Finset (Finset V) :=
  (independentSets G).filter (fun S => outside G x S = J)

def Admissible (x : V) (J : Finset V) : Prop :=
  G.IsIndepSet (J : Set V) ∧ Disjoint J (closed G x)

@[simp] theorem mem_closed (x u : V) : u ∈ closed G x ↔ u = x ∨ G.Adj x u := by
  simp [closed]
@[simp] theorem mem_outside (x u : V) (S : Finset V) :
    u ∈ outside G x S ↔ u ∈ S ∧ u ≠ x ∧ ¬G.Adj x u := by
  simp [outside]
@[simp] theorem mem_available (x u : V) (J : Finset V) :
    u ∈ available G x J ↔ G.Adj x u ∧ ∀ v ∈ J, ¬G.Adj u v := by
  simp [available]

@[simp] theorem center_not_available (x : V) (J : Finset V) : x ∉ available G x J := by
  simp

end SharpLogRamsey.TriangleFree
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Bounds_SumFiberCenter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The off-diagonal Ramsey upper bound. -/

section
open scoped BigOperators Classical
open Finset
open scoped BigOperators Classical
open Finset
namespace SharpLogRamsey.TriangleFree
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

noncomputable def Z (x : V) (S : Finset V) : ℕ :=
  (available G x (outside G x S)).card

end SharpLogRamsey.TriangleFree

open scoped BigOperators Classical
open Finset
namespace SharpLogRamsey.Sampling
variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V)

noncomputable def internalDegree (S : Finset V) (x : V) : ℕ :=
  (S.filter (G.Adj x)).card

noncomputable def degreeMass (S : Finset V) : ℕ := ∑ x ∈ S, internalDegree G S x

end SharpLogRamsey.Sampling

open scoped BigOperators
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Exposure_ExposureBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Entropy and counting bounds for selected coordinates in finite probability laws. -/

section
open scoped BigOperators
open Finset
open scoped Classical

namespace SharpLogRamsey.Selection

variable {α β : Type*} [Fintype α] [Fintype β]

abbrev Positions (N ℓ : ℕ) := {S : Finset (Fin N) // S.card = ℓ}

noncomputable def positionMap {N ℓ : ℕ} (S : Positions N ℓ) : Fin ℓ ↪ Fin N :=
  (S.val.orderEmbOfFin S.property).toEmbedding

def Occurs {N ℓ : ℕ} (f : Fin ℓ → α) (g : Fin N → α) : Prop :=
  ∃ S : Positions N ℓ, ∀ i, g (positionMap S i) = f i

end SharpLogRamsey.Selection

namespace SharpLogRamsey.Selection
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

theorem mul_log_div_ge {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hab : y = 0 → x = 0) : x-y ≤ x*Real.log (x/y) := by
  rcases hx.eq_or_lt with hx0 | hx0
  · rw [← hx0]; simp [hy]
  have hy0 : 0 < y := lt_of_le_of_ne hy (fun h => hx0.ne' (hab h.symm))
  have h := Real.log_le_sub_one_of_pos (div_pos hy0 hx0)
  rw [Real.log_div hy0.ne' hx0.ne'] at h
  rw [Real.log_div hx0.ne' hy0.ne']
  have hh := mul_le_mul_of_nonneg_left h hx0.le
  have he : x*(y/x-1) = y-x := by field_simp
  rw [he] at hh
  nlinarith

end SharpLogRamsey.Selection

namespace SharpLogRamsey.Selection
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

theorem log_sum {ι : Type*} (s : Finset ι) (x y : ι → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i) (hy : ∀ i ∈ s, 0 ≤ y i)
    (hab : ∀ i ∈ s, y i = 0 → x i = 0) :
    (∑ i ∈ s, x i)*Real.log ((∑ i ∈ s, x i)/(∑ i ∈ s, y i)) ≤
      ∑ i ∈ s, x i*Real.log (x i/y i) := by
  let X := ∑ i ∈ s, x i
  let Y := ∑ i ∈ s, y i
  have hX : 0 ≤ X := sum_nonneg hx
  have hY : 0 ≤ Y := sum_nonneg hy
  by_cases hz : X = 0
  · have hh : ∀ i ∈ s, x i = 0 := (sum_eq_zero_iff_of_nonneg hx).mp hz
    change X*Real.log (X/Y) ≤ _
    rw [hz,zero_mul]
    rw [sum_eq_zero (fun i hi => by rw [hh i hi,zero_mul])]
  have hXp : 0 < X := lt_of_le_of_ne hX (Ne.symm hz)
  have hYp : 0 < Y := by
    by_contra hn
    have hyz : Y = 0 := le_antisymm (le_of_not_gt hn) hY
    have hh := (sum_eq_zero_iff_of_nonneg hy).mp hyz
    apply hz
    apply sum_eq_zero
    intro i hi
    exact hab i hi (hh i hi)
  have hscale : 0 < X/Y := div_pos hXp hYp
  have hterm (i : ι) (hi : i ∈ s) :
      x i-y i*(X/Y) ≤ x i*Real.log (x i/y i)-x i*Real.log (X/Y) := by
    by_cases hxi : x i = 0
    · simp only [hxi,zero_mul,zero_sub,sub_zero]
      exact neg_nonpos.mpr (mul_nonneg (hy i hi) hscale.le)
    have hyi : y i ≠ 0 := fun h => hxi (hab i hi h)
    have h := mul_log_div_ge (hx i hi) (mul_nonneg (hy i hi) hscale.le)
      (fun h => hab i hi ((mul_eq_zero.mp h).resolve_right hscale.ne'))
    have he : Real.log (x i/(y i*(X/Y))) = Real.log (x i/y i)-Real.log (X/Y) := by
      rw [← div_div,Real.log_div (div_ne_zero hxi hyi) hscale.ne']
    rw [he,mul_sub] at h
    exact h
  have hsum := sum_le_sum hterm
  simp only [sum_sub_distrib, ← sum_mul] at hsum
  change X-Y*(X/Y) ≤ (∑ i ∈ s, x i*Real.log (x i/y i))-X*Real.log (X/Y) at hsum
  have he : Y*(X/Y) = X := by field_simp
  rw [he,sub_self] at hsum
  linarith

end SharpLogRamsey.Selection
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Exposure_DivergenceMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Entropy and counting bounds for selected coordinates in finite probability laws. -/

section
open scoped BigOperators
open Finset
open scoped Classical

namespace SharpLogRamsey.Selection
variable {ι β B X : Type*} [Fintype ι] [DecidableEq ι] [Fintype β]
  [Fintype B] [Fintype X] [DecidableEq B]

noncomputable def freshRepresentatives (e : B×X ↪ ι) (f : B→X) : Finset ι :=
  univ.image (fun b => e (b,f b))

noncomputable def otherRepresentatives (e : B×X ↪ ι) (own : ι→Option B)
    (f : B→X) (i : ι) : Finset ι :=
  (univ.filter (fun b => some b≠own i)).image (fun b => e (b,f b))

end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Exposure_RemainingEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Entropy and counting bounds for selected coordinates in finite probability laws. -/

section
open scoped BigOperators
open Finset
open scoped Classical
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical
noncomputable section
variable {B β ι : Type*} [Fintype B] [Fintype β] [Fintype ι] [DecidableEq ι] [DecidableEq B]
def remainingEmbedding {m : ℕ} (e : B×Fin (m+1)  ↪  ι) (f : B → Fin (m+1)) :
    B×Fin m  ↪  ↥((freshRepresentatives e f)ᶜ) where
  toFun z := ⟨e (z.1,(f z.1).succAbove z.2), by
    simp only [mem_compl, freshRepresentatives, mem_image, mem_univ,true_and,not_exists]
    intro b hb
    have he := e.injective hb
    have hb' : b=z.1 := (Prod.mk.inj he).1
    subst b
    exact Fin.succAbove_ne (f z.1) z.2 (Prod.mk.inj he).2.symm⟩
  inj' := by
    intro z w h
    have he := e.injective (congrArg Subtype.val h)
    obtain ⟨hb,hx⟩ := Prod.mk.inj he
    obtain ⟨b,x⟩ := z
    obtain ⟨c,y⟩ := w
    dsimp at hb hx
    subst c
    congr 1
    exact Fin.succAbove_right_injective hx

omit [DecidableEq B] in
lemma remaining_own {m : ℕ} (e : B×Fin (m+1)  ↪  ι) (f : B → Fin (m+1))
    (own : ι → Option B) (hown : ∀ b x,own (e (b,x))= some b) (b : B) (x : Fin m) :
    own (remainingEmbedding e f (b,x))= some b := hown _ _

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Exposure_FreshBlockBudgets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical BigOperators NNReal
noncomputable section
variable {B X ι : Type*} [Fintype B] [Fintype X] [Fintype ι] [DecidableEq B] [DecidableEq ι]

def maximumCharge (c : ι→ι→ℝ≥0) (i : ι) (J : Finset ι) : ℝ≥0 := J.sup (c i)

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Reciprocal_ProdRectangleEvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Classical
open Finset

namespace SharpLogRamsey.Selection
open scoped BigOperators Classical
open Finset
noncomputable section
variable {A B Ω : Type*} [Fintype A] [Fintype B] [Fintype Ω]
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

def orthogonalRectangle (v : B → V) (w : A → Module.Dual K V) (W : Submodule K V) : Finset (A × B) :=
  univ.filter (fun ab => v ab.2 ∈ W ∧ w ab.1 ∈ W.dualAnnihilator)

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_MarkingMessage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open scoped BigOperators Classical
open Finset
noncomputable section
variable {Ω α Γ ι : Type*} [Fintype Ω] [Fintype α] [Fintype Γ] [Fintype ι]

def maskedValues (E : Finset ι) (f : ι → α) : ι → Option α :=
  fun i => if i ∈ E then some (f i) else none

def maskedDomains (E : Finset ι) (D : ι → Finset α) (i : ι) : Finset (Option α) :=
  if i ∈ E then (D i).image some else {none}

end
end SharpLogRamsey.Selection

namespace SharpLogRamsey.Selection
open scoped BigOperators Classical
open Finset
noncomputable section
variable {Ω α Γ M ι : Type*} [Fintype Ω] [Fintype α] [Fintype Γ] [Fintype M] [Fintype ι]

def markingMessage (C : Ω → Γ) (mask : Ω → M) (E : M → Finset ι) (F : Ω → ι → α)
    (x : Ω) : (ι → Option α) × (Γ × M) :=
  (maskedValues (E (mask x)) (F x),(C x,mask x))

def markingDecodedDomains (E : M → Finset ι)
    (cheap : ((ι → Option α) × (Γ × M)) → ι → Finset α)
    (θ : (ι → Option α) × (Γ × M)) (i : ι) : Finset α :=
  if i ∈ E θ.2.2 then (θ.1 i).toFinset else cheap θ i

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Entropy_MarkingTwoEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace SharpLogRamsey.Marking
open scoped BigOperators Classical
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] [Finite K]

abbrev jointJ (K : Type*) (d : ℕ) : ℝ := Real.log (64*(Nat.card K:ℝ)^d)

end
end SharpLogRamsey.Marking

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_ClassSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped BigOperators Classical
noncomputable section
variable {Ω Γ ι κ : Type*} [Fintype Ω] [Fintype Γ] [Fintype κ] [Nonempty κ]

def classSlots (U : Γ→Finset ι) (colour : Γ→ι→κ) (z : Γ) (c : κ) : Finset ι :=
  (U z).filter (fun i=>colour z i=c)

omit [Fintype Ω] [Fintype Γ] [Fintype κ] [Nonempty κ] in

def fixedSubset (A : Finset ι) (n : ℕ) : Finset ι :=
  if hn : n≤A.card then Classical.choose (exists_subset_card_eq hn) else ∅

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Reciprocal_ReciprocalBands
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ReciprocalBands
open Real
noncomputable section

def clamp (d : ℕ) (σ x : ℝ) : ℝ := max σ (min ((d:ℝ)*σ) x)

lemma clamp_range {d : ℕ} (hd : 1≤d) {σ x : ℝ} (hσ : 0≤σ) :
    σ ≤ clamp d σ x ∧ clamp d σ x≤(d:ℝ)*σ := by
  have hd' : (1:ℝ)≤d := by exact_mod_cast hd
  exact ⟨le_max_left _ _,max_le (by nlinarith) (min_le_left _ _)⟩

theorem clamped_caps {d : ℕ} (hd : 1≤d) {σ a b C : ℝ}
    (hσ : 0≤σ) (hb : 0<b) (hC : 1≤C)
    (ha : a≤C*exp ((d:ℝ)*σ)) (hbnd : b≤C*exp ((d:ℝ)*σ))
    (hab : a*b≤C*exp (((d:ℝ)+1)*σ)) :
    σ ≤ clamp d σ (log b) ∧ clamp d σ (log b)≤(d:ℝ)*σ ∧
    a≤C*exp (((d:ℝ)+1)*σ-clamp d σ (log b)) ∧
    b≤C*exp (clamp d σ (log b)) := by
  have hr := clamp_range hd (x:=log b) hσ
  have hCp : 0≤C := le_trans zero_le_one hC
  refine ⟨hr.1,hr.2,?_,?_⟩
  · by_cases hx : log b≤σ
    · have hu : clamp d σ (log b)=σ := max_eq_left ((min_le_right _ _).trans hx)
      rw [hu]
      convert ha using 1
      all_goals try with_reducible_and_instances rfl
      congr 2
      ring
    · have hxu : clamp d σ (log b)≤log b := max_le (le_of_not_ge hx) (min_le_right _ _)
      have ha' : a≤C*exp (((d:ℝ)+1)*σ-log b) := by
        rw [exp_sub,exp_log hb,←mul_div_assoc]
        exact (le_div_iff₀ hb).mpr hab
      exact ha'.trans (mul_le_mul_of_nonneg_left
        (exp_le_exp.mpr (sub_le_sub_left hxu _)) hCp)
  · by_cases hx : log b≤(d:ℝ)*σ
    · have hu : log b ≤ clamp d σ (log b) := by
        unfold clamp
        rw [min_eq_right hx]
        exact le_max_right _ _
      calc
        b = exp (log b) := (exp_log hb).symm
        _ ≤ exp (clamp d σ (log b)) := exp_le_exp.mpr hu
        _ ≤ C*exp (clamp d σ (log b)) := le_mul_of_one_le_left (exp_nonneg _) hC
    · have hu : clamp d σ (log b)=(d:ℝ)*σ := by
        unfold clamp
        rw [min_eq_left (le_of_not_ge hx)]
        exact max_eq_right (hr.1.trans hr.2)
      rw [hu]
      exact hbnd

end
end SharpLogRamsey.ReciprocalBands

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_MarkingClassification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Marking
open Finset
open scoped BigOperators Classical
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] [Finite K]

omit [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] [Finite K] in
lemma exp_nat_log {q : ℝ} (hq : 0<q) (d : ℕ) : Real.exp ((d:ℝ)*Real.log q)=q^d := by
  rw [Real.exp_nat_mul,Real.exp_log hq]

end
end SharpLogRamsey.Marking

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_OrderedClassLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical BigOperators
noncomputable section
variable {Ω Γ α β : Type*} [Fintype Ω] [Fintype Γ] [Fintype α] [Fintype β]

omit [Fintype Ω] [Fintype Γ] [Fintype α] [Fintype β] in

def chosenOrder {N m : ℕ} (S : Γ→Finset (Fin N)) (hm : m≤N) (z : Γ) : Fin m ↪o Fin N :=
  if hs : (S z).card=m then (S z).orderEmbOfFin hs else Fin.castLEOrderEmb hm

omit [Fintype Ω] [Fintype Γ] [Fintype α] [Fintype β] in
def orderedTuple {N m : ℕ} (S : Γ→Finset (Fin N)) (hm : m≤N)
    (θ : Ω→Γ) (F : Ω→Fin N→α) : Ω→Fin m→α :=
  fun x i=>F x (chosenOrder S hm (θ x) i)

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Selection_SupportThreshold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset Real Filter
open scoped Classical BigOperators Topology
noncomputable section

def supportErrorEnvelope (b C C₀ A x : ℝ) : ℝ :=
  (2+100*exp 1)*x^(-2*b)+
  (2*(log (2*C)+2*log (A+2)+2)+100*exp 1*C₀)/x^(4*b)+
  4*log x/x^(4*b)+2*exp 1*exp (-(x^(4*b)))

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_PencilGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PreparedProjectiveGeometry
open scoped BigOperators
open Classical
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedPencilGeometry_1 : Finite (Submodule K V) := by
  let : Finite V := Module.finite_of_finite K
  exact Finite.of_injective (fun W : Submodule K V => (W : Set V)) SetLike.coe_injective
local instance flat_JoinedPencilGeometry_2 : Fintype (Submodule K V) := Fintype.ofFinite _

def RadialLine (x : Projectivization K V) :=
  {W : Submodule K V // Module.finrank K W = 2 ∧ x.submodule ≤ W}

instance radialLineFintype (x : Projectivization K V) : Fintype (RadialLine x) := by
  unfold RadialLine
  infer_instance

def lines (x : Projectivization K V) (H : Projectivization K (Module.Dual K V)) :
    Finset (RadialLine x) :=
  Finset.univ.filter (fun W => W.1 ≤ LinearMap.ker H.rep)

@[simp] lemma mem_lines (x : Projectivization K V)
    (H : Projectivization K (Module.Dual K V)) (W : RadialLine x) :
    W ∈ lines x H ↔ W.1 ≤ LinearMap.ker H.rep := by simp [lines]

omit [Finite K] [FiniteDimensional K V] in
lemma finrank_join (x y : Projectivization K V) (hne : x ≠ y) :
    Module.finrank K (x.submodule ⊔ y.submodule : Submodule K V) = 2 := by
  have hh := finrank_span_eq_card (Projectivization.linearIndependent_pair_iff_ne.mpr hne)
  have he : Set.range ![x.rep,y.rep] = {x.rep,y.rep} := by
    ext v
    simp [or_comm]
  rw [he, Submodule.span_insert] at hh
  rw [x.submodule_eq, y.submodule_eq]
  exact hh

omit [Finite K] in
lemma radial_unique (x y : Projectivization K V) (hne : x ≠ y)
    (W : RadialLine x) (hy : y.submodule ≤ W.1) :
    x.submodule ⊔ y.submodule = W.1 :=
  Submodule.eq_of_le_of_finrank_eq (sup_le W.2.2 hy) ((finrank_join x y hne).trans W.2.1.symm)

def radialFiber (S : Finset (Projectivization K V)) (x : Projectivization K V)
    (W : RadialLine x) : Finset (Projectivization K V) :=
  S.filter (fun y => y ≠ x ∧ y.submodule ≤ W.1)

omit [Finite K] [FiniteDimensional K V] in
@[simp] lemma mem_radialFiber (S : Finset (Projectivization K V)) (x y : Projectivization K V)
    (W : RadialLine x) : y ∈ radialFiber S x W ↔ y ∈ S ∧ y ≠ x ∧ y.submodule ≤ W.1 := by
  simp [radialFiber]

end
end SharpLogRamsey.PreparedProjectiveGeometry

open Finset Classical

namespace SharpLogRamsey.PreparedProjectiveGeometry
open scoped BigOperators
open Classical
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedPencilGeometry_7 : Finite (Module.Dual K V) := Module.finite_of_finite K
local instance flat_JoinedPencilGeometry_8 : Fintype (Projectivization K (Module.Dual K V)) := Fintype.ofFinite _

def strength (S : Finset (Projectivization K V)) (x : Projectivization K V)
    (c : ℝ) (W : RadialLine x) : ℝ := c*(radialFiber S x W).card

def overlap (S : Finset (Projectivization K V)) (x : Projectivization K V)
    (c : ℝ) (H J : Projectivization K (Module.Dual K V)) : ℝ :=
  c*(S.filter (fun y => y ≠ x ∧ y.submodule ≤ LinearMap.ker H.rep ⊓ LinearMap.ker J.rep)).card

def richRadials (S : Finset (Projectivization K V)) (x : Projectivization K V)
    (c a : ℝ) : Finset (RadialLine x) := univ.filter (fun W => a ≤ strength S x c W)

def hyperplanesOn (A : Finset (Projectivization K (Module.Dual K V)))
    (x : Projectivization K V) (W : RadialLine x) :
    Finset (Projectivization K (Module.Dual K V)) := A.filter (fun H => W ∈ lines x H)

def largePairs (S : Finset (Projectivization K V)) (x : Projectivization K V)
    (c a : ℝ) (A : Finset (Projectivization K (Module.Dual K V))) :=
  (A ×ˢ A).filter (fun z => z.1 ≠ z.2 ∧ a ≤ overlap S x c z.1 z.2)

def largeNeighbors (S : Finset (Projectivization K V)) (x : Projectivization K V)
    (c a : ℝ) (A : Finset (Projectivization K (Module.Dual K V)))
    (H : Projectivization K (Module.Dual K V)) :=
  A.filter (fun J => H ≠ J ∧ a ≤ overlap S x c H J)

end
end SharpLogRamsey.PreparedProjectiveGeometry

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Entropy_PoissonLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.StaticCertificates
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
noncomputable def poissonLaw (rate : ι → ℝ≥0) : Measure (ι → ℕ) :=
  Measure.pi (fun i => poissonMeasure (rate i))

instance flat_HighMomentRecovered_3 (rate : ι → ℝ≥0) : IsProbabilityMeasure (poissonLaw rate) := by
  unfold poissonLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)

def positiveEvent (C : Finset ι) : Set (ι → ℕ) :=
  (C : Set ι).pi (fun _ => ({0} : Set ℕ)ᶜ)

noncomputable def certificateIndicator (C : Finset ι) (ω : ι → ℕ) : ℝ :=
  (positiveEvent C).indicator (fun _ => 1) ω

noncomputable def weight (rate : ι → ℝ≥0) (C : Finset ι) : ℝ :=
  ∏ i ∈ C, (rate i : ℝ)

section PairWitnesses

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

def witnessRequirements (T : Finset κ) (S : Finset ι) (f : T → S) : Finset (κ × ι) :=
  T.attach.image (fun r => (r.val, (f r).val))

def dictionary (C : Finset (κ × ι)) : Finset ι := C.image Prod.snd

abbrev AnchorChoice (C : Finset (κ × ι)) (S : Finset ι) :=
  {i // i ∈ S ∩ dictionary C} ⊕ (κ × {i // i ∈ S \ dictionary C})

def AnchorChoice.direction {C : Finset (κ × ι)} {S : Finset ι} : AnchorChoice C S → ι
  | .inl d => d.val
  | .inr rd => rd.2.val

def AnchorChoice.requirements {C : Finset (κ × ι)} {S : Finset ι} :
    AnchorChoice C S → Finset (κ × ι)
  | .inl _ => ∅
  | .inr rd => {(rd.1, rd.2.val)}

noncomputable def AnchorChoice.cost (rate : ι → ℝ≥0)
    {C : Finset (κ × ι)} {S : Finset ι} : AnchorChoice C S → ℝ
  | .inl _ => 1
  | .inr rd => rate rd.2.val

end PairWitnesses
end SharpRamseyFive.StaticCertificates
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Entropy_TwoAnchorCrossCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

open scoped BigOperators
namespace SharpRamseyFive.CertificateEnumeration

universe u v
variable {S : Type u} {A : Type v}

section Dependent
variable (C : S → Type v) (step : (s : S) → C s → S)

def DWord : ℕ → S → Type v
  | 0, _ => PUnit
  | n + 1, s => (a : C s) × DWord n (step s a)

instance flat_HighMomentRecovered_5 [∀ s, Fintype (C s)] (n : ℕ) (s : S) : Fintype (DWord C step n s) := by
  induction n generalizing s with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (Fintype ((a : C s) × DWord C step n (step s a)))

def dFinish : {n : ℕ} → (s : S) → DWord C step n s → S
  | 0, s, _ => s
  | _ + 1, s, w => dFinish (step s w.1) w.2

noncomputable def dWeight (cost : (s : S) → C s → ℝ) :
    {n : ℕ} → (s : S) → DWord C step n s → ℝ
  | 0, _, _ => 1
  | _ + 1, s, w => cost s w.1 * dWeight cost (step s w.1) w.2

def dCharge (c : (s : S) → C s → ℤ) :
    {n : ℕ} → (s : S) → DWord C step n s → ℤ
  | 0, _, _ => 0
  | _ + 1, s, w => c s w.1 + dCharge c (step s w.1) w.2

end Dependent

end SharpRamseyFive.CertificateEnumeration

namespace SharpRamseyFive.WeightedPrograms
open SharpRamseyFive.StaticCertificates
open SharpRamseyFive.CertificateEnumeration
open scoped BigOperators NNReal

variable {V H D B : Type*} [Fintype V] [DecidableEq V]
  [Fintype H] [DecidableEq H] [Fintype D] [DecidableEq D]
  [Fintype B] [DecidableEq B]

abbrev State (V H D B : Type*) := (V → H) × Finset (B × D)

variable (lines : H → Finset D)

abbrev RootChoice := V × H
abbrev OneChoice (s : State V H D B) :=
  (_v : V) × (u : V) × (x : AnchorChoice s.2 (lines (s.1 u))) ×
    {h : H // x.direction ∈ lines h}
abbrev TwoChoice (s : State V H D B) :=
  (_v : V) × (u : V) × (w : V) ×
    (x : AnchorChoice s.2 (lines (s.1 u))) ×
    (y : AnchorChoice s.2 (lines (s.1 w))) ×
    {h : H // x.direction ≠ y.direction ∧ x.direction ∈ lines h ∧ y.direction ∈ lines h}
abbrev PairDirections (s : State V H D B) (h h' : H) :=
  (lines h ∩ lines h') \ dictionary s.2
abbrev PairChoice (K : ℕ) (s : State V H D B) :=
  (_v : V) × (_u : V) × (h : H) × (h' : {h' : H // h' ≠ h}) ×
    (T : {T : Finset B // T ∈ (Finset.univ : Finset B).powersetCard K}) ×
      (T.val → PairDirections lines s h h'.val)
abbrev Action (K : ℕ) (s : State V H D B) :=
  RootChoice (V := V) (H := H) ⊕ OneChoice lines s ⊕ TwoChoice lines s ⊕ PairChoice lines K s

noncomputable instance actionFintype (K : ℕ) (s : State V H D B) :
    Fintype (Action lines K s) := by
  letI : Fintype (RootChoice (V := V) (H := H)) := inferInstance
  letI : Fintype (OneChoice lines s) := inferInstance
  letI : Fintype (TwoChoice lines s) := inferInstance
  letI : Fintype (PairChoice lines K s) := inferInstance
  exact inferInstanceAs (Fintype (RootChoice (V := V) (H := H) ⊕
    OneChoice lines s ⊕ TwoChoice lines s ⊕ PairChoice lines K s))

noncomputable def oneCost (rate : D → ℝ≥0) (denom : ℝ)
    (s : State V H D B) (c : OneChoice lines s) : ℝ :=
  c.2.2.1.cost rate / denom
noncomputable def twoCost (rate : D → ℝ≥0) (denom : ℝ)
    (s : State V H D B) (c : TwoChoice lines s) : ℝ :=
  c.2.2.2.1.cost rate * c.2.2.2.2.1.cost rate / denom
noncomputable def pairCost (rate : D → ℝ≥0) (denom : ℝ) (K : ℕ)
    (s : State V H D B) (c : PairChoice lines K s) : ℝ :=
  weight (fun p : B × D => rate p.2)
    (witnessRequirements c.2.2.2.2.1.val
      (PairDirections lines s c.2.2.1 c.2.2.2.1.val) c.2.2.2.2.2) / denom ^ 2

noncomputable def anchorBudget (_rate : D → ℝ≥0) (s : State V H D B) (mass : ℝ) : ℝ :=
  s.2.card + Fintype.card B * mass

noncomputable def pairMoment (rate : D → ℝ≥0) (K : ℕ) : ℝ :=
  ∑ h : H, ∑ h' : {h' : H // h' ≠ h},
    ((Fintype.card B : ℝ) * ∑ d ∈ lines h ∩ lines h'.val, (rate d : ℝ)) ^ K

end SharpRamseyFive.WeightedPrograms
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Entropy_NewEvents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
namespace SharpRamseyFive.WeightedPrograms
open SharpRamseyFive.StaticCertificates
open SharpRamseyFive.CertificateEnumeration
open scoped BigOperators NNReal
variable {V H D B : Type*} [Fintype V] [DecidableEq V]
  [Fintype H] [DecidableEq H] [Fintype D] [DecidableEq D]
  [Fintype B] [DecidableEq B]
variable (lines : H → Finset D)
def newEvents (K : ℕ) (s : State V H D B) : Action lines K s → Finset (B × D)
  | .inl _ => ∅
  | .inr (.inl c) => c.2.2.1.requirements
  | .inr (.inr (.inl c)) => c.2.2.2.1.requirements ∪ c.2.2.2.2.1.requirements
  | .inr (.inr (.inr c)) => witnessRequirements c.2.2.2.2.1.val
      (PairDirections lines s c.2.2.1 c.2.2.2.1.val) c.2.2.2.2.2

def newValues (K : ℕ) (s : State V H D B) : Action lines K s → V → H
  | .inl c => Function.update s.1 c.1 c.2
  | .inr (.inl c) => Function.update s.1 c.1 c.2.2.2.val
  | .inr (.inr (.inl c)) => Function.update s.1 c.1 c.2.2.2.2.2.val
  | .inr (.inr (.inr c)) =>
      Function.update (Function.update s.1 c.1 c.2.2.1) c.2.1 c.2.2.2.1.val

def advance (K : ℕ) (s : State V H D B) (a : Action lines K s) : State V H D B :=
  (newValues lines K s a, s.2 ∪ newEvents lines K s a)

def degree (K : ℕ) (s : State V H D B) : Action lines K s → ℕ
  | .inr (.inr (.inr _)) => 2
  | _ => 1

def actionCharge (K : ℕ) (s : State V H D B) : Action lines K s → ℤ
  | .inl _ => -8
  | .inr (.inr (.inl _)) => 1
  | _ => 0

noncomputable def rawCost (rate : D → ℝ≥0) (denom : ℝ) (K : ℕ) (low : Bool)
    (s : State V H D B) : Action lines K s → ℝ
  | .inl _ => 1 / denom
  | .inr (.inl c) => if low then oneCost lines rate denom s c else 0
  | .inr (.inr (.inl c)) => twoCost lines rate denom s c
  | .inr (.inr (.inr c)) => pairCost lines rate denom K s c

noncomputable def programCost (rate : D → ℝ≥0) (denom : ℝ) (K : ℕ) (low : Bool)
    (s : State V H D B) (a : Action lines K s) : ℝ :=
  if s.2.card ≤ K * Fintype.card V then rawCost lines rate denom K low s a else 0

noncomputable def uniformAnchorBudget (K : ℕ) (mass : ℝ) : ℝ :=
  K * Fintype.card V + Fintype.card B * mass

noncomputable def branchingBound (rate : D → ℝ≥0) (denom b mass : ℝ)
    (K N₁ N₂ : ℕ) (low : Bool) : ℝ :=
  ((Fintype.card V : ℝ) * Fintype.card H / denom) / b ^ 8 +
    (if low then Fintype.card V ^ 2 * (N₁ : ℝ) *
      uniformAnchorBudget (V := V) (B := B) K mass / denom else 0) +
    (Fintype.card V ^ 3 * (N₂ : ℝ) *
      uniformAnchorBudget (V := V) (B := B) K mass ^ 2 / denom) * b +
    Fintype.card V ^ 2 * pairMoment (B := B) lines rate K / denom ^ 2

end SharpRamseyFive.WeightedPrograms

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace SharpRamseyFive.ResidualCertificate

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def rootProbability : unitInterval := ⟨1 / 20, by norm_num⟩

noncomputable def rootMeasure : Measure (V → Bool) :=
  Measure.pi (fun _ => bernoulliMeasure true false rootProbability)

instance flat_HighMomentRecovered_6 : IsProbabilityMeasure (rootMeasure (V := V)) := by
  unfold rootMeasure
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)

noncomputable def selected (ω : V → Bool) : Finset V :=
  Finset.univ.filter (fun v => ω v = true)

def voidEvent (W : Finset V) : Set (V → Bool) :=
  (W : Set V).pi (fun _ => {false})

noncomputable def voidIndicator (W : Finset V) (ω : V → Bool) : ℝ :=
  (voidEvent W).indicator (fun _ => 1) ω

noncomputable def badIndicator (W : Finset V) (ω : V → Bool) : ℝ :=
  if (W ∩ selected ω).card < 2 then 1 else 0

end SharpRamseyFive.ResidualCertificate
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Entropy_WitnessList
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace SharpRamseyFive.ResidualCertificate
variable {V : Type*} [Fintype V] [DecidableEq V]

section SharedHitGeometry

open scoped Classical

variable {D B : Type*} [Fintype D] [DecidableEq D] [Fintype B] [DecidableEq B]

noncomputable def sharedBatches (s : V → Finset D) (hit : B → D → Prop) (v u : V) : Finset B :=
  Finset.univ.filter (fun r => ∃ d ∈ s v ∩ s u, hit r d)

noncomputable def touchedBatches (s : V → Finset D) (hit : B → D → Prop) (v : V) : Finset B :=
  Finset.univ.filter (fun r => ∃ u, u ≠ v ∧ r ∈ sharedBatches s hit v u)

noncomputable def encodedDirections (s : V → Finset D) (E : Finset V) : Finset D :=
  E.biUnion s

noncomputable def touchedToEncoded (s : V → Finset D) (hit : B → D → Prop)
    (E : Finset V) (v : V) : Finset D :=
  (s v ∩ encodedDirections s E).filter (fun d => ∃ r, hit r d)

noncomputable def batchesOn (hit : B → D → Prop) (T : Finset D) : Finset B :=
  T.biUnion (fun d => Finset.univ.filter (fun r => hit r d))

noncomputable def survivingDirections (s : V → Finset D) (E : Finset V)
    (v : {v // v ∉ E}) : Finset D := s v.val \ encodedDirections s E

noncomputable def outsideDirections (s : V → Finset D) (E : Finset V) (v : V) : Finset D :=
  s v \ encodedDirections s E

inductive EncodingStep (s : V → Finset D) (hit : B → D → Prop)
    (anchorNumber K : ℕ) : Finset V → Finset V → Prop
  | anchor (E : Finset V) (v : V) (hv : v ∉ E)
      (ha : anchorNumber ≤ (touchedToEncoded s hit E v).card) :
      EncodingStep s hit anchorNumber K E (insert v E)
  | pair (E : Finset V) (v u : V) (hv : v ∉ E) (hu : u ∉ E) (hne : v ≠ u)
      (hp : K ≤ (sharedBatches (outsideDirections s E) hit v u).card) :
      EncodingStep s hit anchorNumber K E (insert v (insert u E))

def paidDirections (C : Finset (B × D)) : Finset D := C.image Prod.snd

def Realized (hit : B → D → Prop) (C : Finset (B × D)) : Prop :=
  ∀ p ∈ C, hit p.1 p.2

def DictionaryInvariant (s : V → Finset D) (E : Finset V) (C : Finset (B × D)) : Prop :=
  paidDirections C ⊆ encodedDirections s E

end SharedHitGeometry
end SharpRamseyFive.ResidualCertificate
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Entropy_AnchorEventsRealized
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace SharpRamseyFive.ResidualCertificate
variable {V : Type*} [Fintype V] [DecidableEq V]
section SharedHitGeometry
open scoped Classical
variable {D B : Type*} [Fintype D] [DecidableEq D] [Fintype B] [DecidableEq B]

noncomputable def pairEvents (T : Finset B) (d : T → D) : Finset (B × D) :=
  T.attach.image (fun r => (r.val, d r))

end SharedHitGeometry

end SharpRamseyFive.ResidualCertificate

namespace SharpRamseyFive.CertificateCover
open SharpRamseyFive.StaticCertificates
open SharpRamseyFive.CertificateEnumeration
open SharpRamseyFive.WeightedPrograms
open SharpRamseyFive.ResidualCertificate
open scoped BigOperators

variable {V H D B : Type*} [Fintype V] [DecidableEq V]
  [Fintype H] [DecidableEq H] [Fintype D] [DecidableEq D]
  [Fintype B] [DecidableEq B]
variable (lines : H → Finset D)

 def Agrees (f : V → H) (E : Finset V) (s : State V H D B) : Prop :=
  ∀ v ∈ E, s.1 v = f v

noncomputable def anchorName (C : Finset (B × D)) (S : Finset D)
    (d : D) (hd : d ∈ S) (r : B) : AnchorChoice C S :=
  if he : d ∈ dictionary C then .inl ⟨d, Finset.mem_inter.mpr ⟨hd, he⟩⟩
  else .inr (r, ⟨d, Finset.mem_sdiff.mpr ⟨hd, he⟩⟩)

 def Enabled (K : ℕ) (low : Bool) (s : State V H D B) (a : Action lines K s) : Prop :=
  ∀ c : OneChoice lines s, a = .inr (.inl c) → low = true

 def Coherent (f : V → H) (hit : B → D → Prop) (K : ℕ)
    (E : Finset V) (s : State V H D B) : Prop :=
  Agrees f E s ∧ DictionaryInvariant (fun v => lines (f v)) E s.2 ∧
    Realized hit s.2 ∧ s.2.card ≤ K * E.card
end SharpRamseyFive.CertificateCover
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Entropy_MakePair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace SharpRamseyFive.CertificateCover
open SharpRamseyFive.StaticCertificates
open SharpRamseyFive.CertificateEnumeration
open SharpRamseyFive.WeightedPrograms
open SharpRamseyFive.ResidualCertificate
open scoped BigOperators
variable {V H D B : Type*} [Fintype V] [DecidableEq V]
  [Fintype H] [DecidableEq H] [Fintype D] [DecidableEq D]
  [Fintype B] [DecidableEq B]
variable (lines : H → Finset D)

abbrev Word (K : ℕ) := DWord (Action (V := V) (B := B) lines K) (advance lines K)
abbrev finish (K : ℕ) {n : ℕ} (s : State V H D B) (w : Word lines K n s) :=
  dFinish (Action lines K) (advance lines K) s w
abbrev charge (K : ℕ) {n : ℕ} (s : State V H D B) (w : Word lines K n s) :=
  dCharge (Action lines K) (advance lines K) (actionCharge lines K) s w

 def degreeSum (K : ℕ) : {n : ℕ} → (s : State V H D B) → Word lines K n s → ℕ
  | 0, _, _ => 0
  | _ + 1, s, w => degree lines K s w.1 + degreeSum K (advance lines K s w.1) w.2

 def TraceOK (K : ℕ) (low : Bool) :
    {n : ℕ} → (s : State V H D B) → Word lines K n s → Prop
  | 0, _, _ => True
  | _ + 1, s, w => s.2.card ≤ K * Fintype.card V ∧
      Enabled lines K low s w.1 ∧ TraceOK K low (advance lines K s w.1) w.2

 def append (K : ℕ) {m : ℕ} : {n : ℕ} → (s : State V H D B) →
    (w : Word lines K n s) → Word lines K m (finish lines K s w) → Word lines K (m + n) s
  | 0, _, _, w' => w'
  | _ + 1, s, w, w' => ⟨w.1, append K (advance lines K s w.1) w.2 w'⟩

 def Segment (f : V → H) (hit : B → D → Prop) (K : ℕ) (low : Bool)
    (E F : Finset V) (s : State V H D B) {n : ℕ} (w : Word lines K n s) : Prop :=
  Coherent lines f hit K F (finish lines K s w) ∧
    F.card = E.card + degreeSum lines K s w ∧ TraceOK lines K low s w

abbrev AllPrograms (K : ℕ) (E : Finset V) (s : State V H D B) :=
  (n : Fin (Fintype.card V - E.card + 1)) × Word lines K n.val s

 def CompleteProgram (K : ℕ) (low : Bool) (E : Finset V) (s : State V H D B)
    (c : AllPrograms lines K E s) : Prop :=
  TraceOK lines K low s c.2 ∧ 0 ≤ charge lines K s c.2 ∧
    degreeSum lines K s c.2 = Fintype.card V - E.card

noncomputable def completePrograms (K : ℕ) (low : Bool) (E : Finset V) (s : State V H D B) :=
  {c : AllPrograms lines K E s // CompleteProgram lines K low E s c}

noncomputable instance completePrograms_fintype (K : ℕ) (low : Bool) (E : Finset V)
    (s : State V H D B) : Fintype (completePrograms lines K low E s) := by
  classical
  unfold completePrograms
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)
end SharpRamseyFive.CertificateCover
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Entropy_HighMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace SharpRamseyFive.PoissonScore

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def batchMeasure (rate : ι → ℝ≥0) : Measure (ι → ℕ) :=
  Measure.pi (fun i => poissonMeasure (rate i))

instance flat_HighMomentRecovered_1 (rate : ι → ℝ≥0) : IsProbabilityMeasure (batchMeasure rate) := by
  unfold batchMeasure
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)

def emptyEvent (s : Finset ι) : Set (ι → ℕ) :=
  (s : Set ι).pi (fun _ => {0})

noncomputable def emptyIndicator (s : Finset ι) (ω : ι → ℕ) : ℝ :=
  (emptyEvent s).indicator (fun _ => 1) ω

noncomputable def mass (rate : ι → ℝ≥0) (s : Finset ι) : ℝ :=
  ∑ i ∈ s, (rate i : ℝ)

noncomputable def centeredFactor (s : Finset ι) (b : ℝ) (ω : ι → ℕ) : ℝ :=
  emptyIndicator s ω - b

noncomputable def scheduleMeasure (rate : ι → ℝ≥0) (R : ℕ) :
    Measure (Fin R → ι → ℕ) :=
  Measure.pi (fun _ : Fin R => batchMeasure rate)

instance flat_HighMomentRecovered_2 (rate : ι → ℝ≥0) (R : ℕ) : IsProbabilityMeasure (scheduleMeasure rate R) := by
  unfold scheduleMeasure
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)

noncomputable def scoreTerm {R : ℕ} (s : Finset ι) (b : ℝ) (own : Fin R → Bool)
    (ω : Fin R → ι → ℕ) : ℝ :=
  ∏ r, if own r then centeredFactor s b (ω r) else 0

noncomputable def pairMean (rate : ι → ℝ≥0) (s t : Finset ι) (b : ℝ) : ℝ :=
  (Real.exp (-mass rate s) - b) * (Real.exp (-mass rate t) - b) +
    Real.exp (-(mass rate s + mass rate t)) *
      (Real.exp (mass rate (s ∩ t)) - 1)

variable {κ : Type*}

noncomputable def typicalScore {R : ℕ} (H : Finset κ) (directions : κ → Finset ι)
    (b : ℝ) (own : κ → Fin R → Bool) (ω : Fin R → ι → ℕ) : ℝ :=
  ∑ h ∈ H, scoreTerm (directions h) b (own h) ω

end SharpRamseyFive.PoissonScore
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Entropy_IntegralTypicalScoreSq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.PoissonScore
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*}

noncomputable def maskedFactor (s : Finset ι) (b : ℝ) (own touched : Bool)
    (ω : ι → ℕ) : ℝ :=
  if own then (if touched then -b else centeredFactor s b ω) else 0

noncomputable def maskedTerm {R : ℕ} (s : Finset ι) (b : ℝ)
    (own touched : Fin R → Bool) (ω : Fin R → ι → ℕ) : ℝ :=
  ∏ r, maskedFactor s b (own r) (touched r) (ω r)

def untouchedBatches {R : ℕ} (touched : Fin R → Bool) : Finset (Fin R) :=
  Finset.univ.filter (fun r => touched r = false)

noncomputable def hitIndicator (i : ι) (ω : ι → ℕ) : ℝ :=
  1 - emptyIndicator {i} ω

noncomputable def forcedHits {R : ℕ} (i : ι) (T : Finset (Fin R))
    (ω : Fin R → ι → ℕ) : ℝ := ∏ r ∈ T, hitIndicator i (ω r)

end SharpRamseyFive.PoissonScore
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Entropy_ForcedHits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.PoissonScore
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*}

def hitBatches {R : ℕ} (i : ι) (ω : Fin R → ι → ℕ) : Finset (Fin R) :=
  Finset.univ.filter (fun r => ω r i ≠ 0)

def overloaded {R : ℕ} (s : Finset ι) (J : ℕ) : Set (Fin R → ι → ℕ) :=
  {ω | ∃ i ∈ s, J ≤ (hitBatches i ω).card}

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

noncomputable def partitionEquiv (label : ι → κ) :
    (ι → ℕ) ≃ᵐ (∀ c : κ, {i : ι // label i = c} → ℕ) :=
  (MeasurableEquiv.piCongrLeft (fun _ : ι => ℕ) (Equiv.sigmaFiberEquiv label)).symm.trans
    (MeasurableEquiv.piCurry (fun (c : κ) (_ : {i : ι // label i = c}) => ℕ))

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
@[simp] lemma partitionEquiv_apply (label : ι → κ) (ω : ι → ℕ) (c : κ)
    (i : {i : ι // label i = c}) : partitionEquiv label ω c i = ω i := rfl

noncomputable def externalEquiv (label : ι → Option κ) :
    (ι → ℕ) ≃ᵐ ((∀ c : κ, {i : ι // label i = some c} → ℕ) ×
      ({i : ι // label i = none} → ℕ)) :=
  (partitionEquiv label).trans (MeasurableEquiv.piOptionEquivProd
    (fun c : Option κ => {i : ι // label i = c} → ℕ))

section ComponentGeometry

variable {H : Type*} [Fintype H] [DecidableEq H]

noncomputable def strongGraph (rate : ι → ℝ≥0) (s : H → Finset ι) (t : ℝ) :
    SimpleGraph H where
  Adj h k := h ≠ k ∧ t < mass rate (s h ∩ s k)
  symm := ⟨by
    intro h k hk
    exact ⟨hk.1.symm, by simpa only [Finset.inter_comm] using hk.2⟩⟩
  loopless := ⟨by intro h hh; exact hh.1 rfl⟩

def External (rate : ι → ℝ≥0) (s : H → Finset ι) (t : ℝ) (i : ι) : Prop :=
  ∃ h k : H, i ∈ s h ∧ i ∈ s k ∧
    (strongGraph rate s t).connectedComponentMk h ≠
      (strongGraph rate s t).connectedComponentMk k

noncomputable def externalPart (rate : ι → ℝ≥0) (s : H → Finset ι)
    (t : ℝ) (h : H) : Finset ι := by
  classical
  exact (s h).filter (External rate s t)

noncomputable def internalPart (rate : ι → ℝ≥0) (s : H → Finset ι)
    (t : ℝ) (h : H) : Finset ι := by
  classical
  exact (s h).filter (fun i => ¬ External rate s t i)

noncomputable def otherComponents (rate : ι → ℝ≥0) (s : H → Finset ι)
    (t : ℝ) (h : H) : Finset H := by
  classical
  exact Finset.univ.filter (fun k =>
    (strongGraph rate s t).connectedComponentMk h ≠
      (strongGraph rate s t).connectedComponentMk k)

end ComponentGeometry
end SharpRamseyFive.PoissonScore
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Entropy_ExternalMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.PoissonScore
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*}
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
section ComponentGeometry
variable {H : Type*} [Fintype H] [DecidableEq H]

noncomputable def componentLabel (rate : ι → ℝ≥0) (s : H → Finset ι)
    (t : ℝ) (i : ι) : Option (strongGraph rate s t).ConnectedComponent := by
  classical
  exact if hi : ∃ h, i ∈ s h then
    if External rate s t i then none else
      some ((strongGraph rate s t).connectedComponentMk hi.choose)
    else none

end ComponentGeometry

end SharpRamseyFive.PoissonScore

namespace SharpRamseyFive.TupleComponents
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open SharpRamseyFive.PoissonScore
open Classical
variable {D V C : Type} [Fintype D] [DecidableEq D]
  [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
variable (label : D → Option C) (R : ℕ)

abbrev Block (c : Option C) := {i : Fin R × D // label i.2 = c}
noncomputable def fill (c : C) (z : Block label R none → ℕ)
    (x : Block label R (some c) → ℕ) (r : Fin R) (d : D) : ℕ :=
  if he : label d = none then z ⟨(r,d), he⟩ else
    if hi : label d = some c then x ⟨(r,d), hi⟩ else 0

noncomputable def lineTrunc (J : ℕ) (ω : Fin R → ℕ) : ℝ :=
  if (Finset.univ.filter (fun r => ω r ≠ 0)).card < J then 1 else 0

noncomputable def blockTrunc (J : ℕ) (c : Option C) (ω : Block label R c → ℕ) : ℝ :=
  ∏ d : {d : D // label d = c}, lineTrunc R J (fun r => ω ⟨(r,d), d.property⟩)

variable (color : V → C) (s : V → Finset D) (b : ℝ) (own : V → Fin R → Bool)

noncomputable def componentFactor (J : ℕ) (c : C)
    (z : Block label R none → ℕ) (x : Block label R (some c) → ℕ) : ℝ :=
  blockTrunc label R J (some c) x *
    ∏ v : {v : V // color v = c}, scoreTerm (s v) b (own v) (fill label R c z x)

noncomputable def strongSplit (weight rate : D → ℝ≥0) (t : ℝ) (J : ℕ) : ℝ := by
  classical
  let G := strongGraph weight s t
  let label := componentLabel weight s t
  exact ∫ z, blockTrunc label R J none z * ∏ c : G.ConnectedComponent,
    ∫ x, componentFactor label R G.connectedComponentMk s b own J c z x
      ∂batchMeasure (fun i : Block label R (some c) => rate i.1.2)
      ∂batchMeasure (fun i : Block label R none => rate i.1.2)

noncomputable def touched (_c : C) (S : Finset D) (z : Block label R none → ℕ)
    (r : Fin R) : Bool :=
  decide (∃ d : {d : D // label d = none}, d.val ∈ S ∧ z ⟨(r,d), d.property⟩ ≠ 0)

end SharpRamseyFive.TupleComponents
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Entropy_ComponentLabelWitness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace SharpRamseyFive.TupleComponents
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open SharpRamseyFive.PoissonScore
open Classical
variable {D V C : Type} [Fintype D] [DecidableEq D]
  [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]

variable (label : D → Option C) (R : ℕ) (color : V → C)
  (s : V → Finset D) (own : V → Fin R → Bool)

def hitBatches {R : ℕ} (mask : Fin R → Bool) : Finset (Fin R) :=
  Finset.univ.filter (fun r => mask r = true)

def BAD {R : ℕ} (mask : Fin R → Bool) : Prop := R / 2 ≤ (hitBatches mask).card

end SharpRamseyFive.TupleComponents

namespace SharpRamseyFive.HighMoment
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open SharpRamseyFive.PoissonScore SharpRamseyFive.TupleComponents
open Classical
variable {D H : Type} [Fintype D] [DecidableEq D] [Fintype H] [DecidableEq H]
variable (R : ℕ) (s : H → Finset D) (b : ℝ) (own : H → Fin R → Bool)

noncomputable def allTrunc (J : ℕ) (ω : Fin R × D → ℕ) : ℝ :=
  ∏ d : D, lineTrunc R J (fun r => ω (r,d))

end SharpRamseyFive.HighMoment
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Entropy_TruncatedTupleIntegrable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace SharpRamseyFive.Designations
open MeasureTheory
open scoped BigOperators
open Classical
variable {C Ω : Type*} [Fintype C] [DecidableEq C]

noncomputable def badIndicator (bad : C → Ω → Prop) (c : C) (z : Ω) : ℝ :=
  if bad c z then 1 else 0

variable [MeasurableSpace Ω] [Countable Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]

noncomputable def badMass (T : Ω → ℝ) (bad : C → Ω → Prop) (U : Finset C) : ℝ :=
  ∫ z, T z * ∏ c ∈ U, badIndicator bad c z ∂μ

end SharpRamseyFive.Designations

namespace SharpRamseyFive.AmbientDesignations
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open SharpRamseyFive.PoissonScore SharpRamseyFive.TupleComponents
open SharpRamseyFive.Designations
open Classical
variable {D V : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
variable (weight : D → ℝ≥0) (s : V → Finset D) (t : ℝ)

abbrev Components := (strongGraph weight s t).ConnectedComponent
noncomputable def vertex (c : Components weight s t) : V := c.out

noncomputable def simpleSet : Finset (Components weight s t) :=
  Finset.univ.filter (fun c => ∀ v, (strongGraph weight s t).connectedComponentMk v = c →
    v = vertex weight s t c)

noncomputable def alpha (v : V) : ℝ := mass weight (externalPart weight s t v)
noncomputable def delta (base : ℝ) (v : V) : ℝ := mass weight (s v) - base

end SharpRamseyFive.AmbientDesignations

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Entropy_CompleteProgramWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace SharpRamseyFive.CertificateCover
open SharpRamseyFive.StaticCertificates
open SharpRamseyFive.CertificateEnumeration
open SharpRamseyFive.WeightedPrograms
open SharpRamseyFive.ResidualCertificate
open scoped BigOperators
variable {V H D B : Type*} [Fintype V] [DecidableEq V]
  [Fintype H] [DecidableEq H] [Fintype D] [DecidableEq D]
  [Fintype B] [DecidableEq B]
variable (lines : H → Finset D)

def selectedBadEvent (K J : ℕ) (low : Bool) (E : Finset V) (s : State V H D B)
    (f : V → H) : Set ((B × D) → ℕ) := by
  classical
  exact {ω | Function.Injective f ∧ ∃ hit : B → D → Prop,
    (∀ r d, hit r d → ω (r, d) ≠ 0) ∧ Coherent lines f hit K E s ∧
    (∀ v ∉ E, Fintype.card B / 2 ≤ (touchedBatches (fun v => lines (f v)) hit v).card) ∧
    (low = false → ∀ d, (Finset.univ.filter (fun r => hit r d)).card ≤ J)}

end SharpRamseyFive.CertificateCover

namespace SharpRamseyFive.SelectionBridge
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open SharpRamseyFive.PoissonScore SharpRamseyFive.TupleComponents
open SharpRamseyFive.Designations SharpRamseyFive.AmbientDesignations
open SharpRamseyFive.CertificateCover SharpRamseyFive.WeightedPrograms
open Classical
variable {D V H C : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype H] [DecidableEq H] [Fintype C] [DecidableEq C]

noncomputable def selectedHit (weight : D → ℝ≥0) (s : V → Finset D) (t : ℝ)
    {R : ℕ} (ω : Fin R × D → ℕ) (r : Fin R) (d : D) : Prop :=
  componentLabel weight s t d = none ∧ ω (r,d) ≠ 0

end SharpRamseyFive.SelectionBridge

namespace SharpRamseyFive.SelectionBridge
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open SharpRamseyFive.PoissonScore SharpRamseyFive.TupleComponents
open SharpRamseyFive.Designations SharpRamseyFive.AmbientDesignations
open SharpRamseyFive.CertificateCover SharpRamseyFive.WeightedPrograms
open Classical
variable {D V H : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype H] [DecidableEq H]

def labelled (f : V → H) (v : V) : H × V := (f v, v)

end SharpRamseyFive.SelectionBridge
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Entropy_LabelledFilterCard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace SharpRamseyFive.ResidualElimination
open scoped BigOperators
open Classical
variable {V H : Type} [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H]

def Agrees (E : Finset V) (g f : V → H) : Prop := ∀ v ∉ E, f v = g v

noncomputable def completionSum (E : Finset V) (g : V → H) (F : (V → H) → ℝ) : ℝ :=
  ∑ f : V → H, if Agrees E g f then F f else 0

noncomputable def term (a : V → (V → H) → ℝ) (B : Finset V → (V → H) → ℝ)
    (E S : Finset V) (f : V → H) : ℝ := (∏ u ∈ S, a u f) * B (E \ S) f

end SharpRamseyFive.ResidualElimination

namespace SharpRamseyFive.SingletonEnumeration
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open SharpRamseyFive.PoissonScore SharpRamseyFive.TupleComponents
open SharpRamseyFive.Designations SharpRamseyFive.AmbientDesignations
open SharpRamseyFive.SelectionBridge SharpRamseyFive.WeightedPrograms
open SharpRamseyFive.ResidualElimination
open Classical
variable {D V H : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype H] [DecidableEq H]

noncomputable def shiftKernel (weight : D → ℝ≥0) (lines : H → Finset D) (p K : ℕ)
    (x y : H) : ℝ := min 1 (((p : ℝ) * mass weight (lines x ∩ lines y)) ^ K)

end SharpRamseyFive.SingletonEnumeration
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Entropy_ShiftKernelSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace SharpRamseyFive.WeightedPrograms

open scoped BigOperators

variable {V H D B I : Type*} [Fintype V] [DecidableEq V]
  [Fintype H] [DecidableEq H] [Fintype D] [DecidableEq D]
  [Fintype B] [DecidableEq B] [DecidableEq I]

variable (lines : H → Finset D)

def DistinctPairs (H : Type*) := Σ h : H, {h' : H // h' ≠ h}

instance flat_HighMomentRecovered_7 : Fintype (DistinctPairs H) := by unfold DistinctPairs; infer_instance

noncomputable def strength (a : D → ℝ≥0) (p : DistinctPairs H) : ℝ :=
  ∑ d ∈ lines p.1 ∩ lines p.2.val, (a d : ℝ)

end SharpRamseyFive.WeightedPrograms

namespace SharpRamseyFive.ResidualElimination
open scoped BigOperators
open Classical
variable {V H : Type} [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H]

noncomputable def patch (g : V → H) (T : Finset V) (x : T → H) : V → H :=
  fun u => if hu : u ∈ T then x ⟨u,hu⟩ else g u

end SharpRamseyFive.ResidualElimination
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Entropy_PatchNotMem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace SharpRamseyFive.ResidualElimination
open scoped BigOperators
open Classical
variable {V H : Type} [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H]

noncomputable def badExpansion (a : V → (V → H) → ℝ)
    (B : Finset V → (V → H) → ℝ) (E : Finset V) (f : V → H) : ℝ :=
  ∑ U ∈ E.powerset, (∏ u ∈ E \ U, a u f) * B U f

end SharpRamseyFive.ResidualElimination

namespace SharpRamseyFive.SingletonEnumeration
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open SharpRamseyFive.PoissonScore SharpRamseyFive.TupleComponents
open SharpRamseyFive.Designations SharpRamseyFive.AmbientDesignations
open SharpRamseyFive.SelectionBridge SharpRamseyFive.WeightedPrograms
open SharpRamseyFive.ResidualElimination
open Classical
variable {D V H : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype H] [DecidableEq H]

noncomputable def independentWeight (weight rate : D → ℝ≥0) (lines : H → Finset D)
    (R J : ℕ) (base : ℝ) (h : H) : ℝ :=
  |mass weight (lines h) - base| ^ (R / 2) +
    (if R < J then 0 else ∑ d ∈ lines h, ((R : ℝ) * (rate d : ℝ)) ^ J)

end SharpRamseyFive.SingletonEnumeration

namespace SharpRamseyFive.ComponentPartition
open scoped BigOperators
open Classical
variable {V C : Type} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]

noncomputable def fiber (r : V → C) (c : C) : Finset V :=
  Finset.univ.filter (fun v => r v = c)
noncomputable def singles (r : V → C) : Finset V :=
  Finset.univ.filter (fun v => (fiber r (r v)).card = 1)
noncomputable def largeLabels (r : V → C) : Finset C :=
  Finset.univ.filter (fun c => 2 ≤ (fiber r c).card)

omit [DecidableEq V] [Fintype C] in
@[simp] lemma mem_fiber (r : V → C) (c : C) (v : V) : v ∈ fiber r c ↔ r v = c := by
  simp [fiber]
omit [DecidableEq V] [Fintype C] in
@[simp] lemma mem_singles (r : V → C) (v : V) :
    v ∈ singles r ↔ (fiber r (r v)).card = 1 := by simp [singles]
omit [DecidableEq V] in
@[simp] lemma mem_largeLabels (r : V → C) (c : C) :
    c ∈ largeLabels r ↔ 2 ≤ (fiber r c).card := by simp [largeLabels]
end SharpRamseyFive.ComponentPartition
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Entropy_SinglesUnique
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace SharpRamseyFive.ComponentPartition
open scoped BigOperators
open Classical
variable {V C : Type} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]

variable (G : SimpleGraph V)
noncomputable def componentMap : V → V := fun v => (G.connectedComponentMk v).out

end SharpRamseyFive.ComponentPartition
namespace SharpRamseyFive.ComponentEnumeration
open Classical
open scoped BigOperators
open CertificateEnumeration
variable {V H : Type} [Fintype V] [DecidableEq V] [Fintype H]

variable (R : H → H → Prop)
noncomputable def relationGraph (hsym : Std.Symm R) (f : V → H) : SimpleGraph V where
  Adj u v := u ≠ v ∧ R (f u) (f v)
  symm := ⟨fun _ _ h => ⟨h.1.symm, hsym.symm _ _ h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

abbrev Extension (s : V → H) := (u : V) × V × {h : H // R (s u) h}
noncomputable def extend (s : V → H) (a : Extension R s) : V → H :=
  Function.update s a.2.1 a.2.2.1

abbrev RelatedPair := (h : H) × {h' : H // R h h'}
abbrev Seed := V × V × RelatedPair R
noncomputable def seedStart (z : Seed (V := V) R) : V → H :=
  Function.update (fun _ => z.2.2.1) z.2.1 z.2.2.2.1

end SharpRamseyFive.ComponentEnumeration

namespace SharpRamseyFive.ComponentPartition
open scoped BigOperators
open Classical
open SharpRamseyFive.ComponentEnumeration SharpRamseyFive.ResidualElimination
variable {V H C : Type} [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H]
  [Fintype C] [DecidableEq C]

noncomputable def connectedWeight (R : H → H → Prop) (hsym : Std.Symm R)
    (r : V → C) (c : C) (x : fiber r c → H) : ℝ :=
  if (relationGraph R hsym x).Connected then 1 else 0

end SharpRamseyFive.ComponentPartition

namespace SharpRamseyFive.AmbientEnumeration
open scoped BigOperators NNReal
open Classical
open SharpRamseyFive.PoissonScore SharpRamseyFive.TupleComponents
open SharpRamseyFive.AmbientDesignations SharpRamseyFive.ComponentPartition
open SharpRamseyFive.ComponentEnumeration SharpRamseyFive.ResidualElimination
open SharpRamseyFive.SingletonEnumeration SharpRamseyFive.SelectionBridge
variable {D V H : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype H] [DecidableEq H]

noncomputable def overlapRelation (weight : D → ℝ≥0) (lines : H → Finset D) (t : ℝ)
    (h k : H) : Prop := t < mass weight (lines h ∩ lines k)

omit [Fintype D] [Fintype H] [DecidableEq H] in
lemma overlapRelation_symm (weight : D → ℝ≥0) (lines : H → Finset D) (t : ℝ) :
    Std.Symm (overlapRelation weight lines t) := by
  constructor
  intro h k hh
  simpa only [overlapRelation, Finset.inter_comm] using hh

end SharpRamseyFive.AmbientEnumeration
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Entropy_LargeCard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace SharpLogRamsey.MomentBudgetBridge

def anchorBudget (p : ℕ) (P : ℝ) : ℝ := 200 * (p : ℝ) + 2 * P

def certificateOverhead (p D : ℕ) (P : ℝ) : ℝ :=
  1 + 4 * (p : ℝ)^2 + 4 * (p : ℝ)^3 * anchorBudget p P +
    (p : ℝ)^4 * (anchorBudget p P)^2 +
    (p : ℝ)^4 * ((D : ℝ)+4) * (2*P)^200

def shiftOverhead (p D : ℕ) : ℝ := 4+(D : ℝ)*(200*(p : ℝ))^200

end SharpLogRamsey.MomentBudgetBridge
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_TestRadialWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PreparedProjectiveGeometry
open Finset SharpRamseyFive.PoissonScore
open scoped Classical BigOperators NNReal
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

def radialWeight (S : Finset (Projectivization K V)) (x : Projectivization K V)
    (c : ℝ≥0) (W : RadialLine x) : ℝ≥0 := c*(radialFiber S x W).card

end
end SharpLogRamsey.PreparedProjectiveGeometry

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_TestActualMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PreparedProjectiveGeometry
open Finset
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedTestActualMoment_1 : Finite (Module.Dual K V) := Module.finite_of_finite K
local instance flat_JoinedTestActualMoment_2 : Fintype (Projectivization K (Module.Dual K V)) := Fintype.ofFinite _

end
end SharpLogRamsey.PreparedProjectiveGeometry

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Entropy_TestActualSecondMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PreparedProjectiveGeometry
open Finset MeasureTheory SharpRamseyFive.PoissonScore
open scoped Classical BigOperators NNReal
noncomputable section
variable {K V I : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

def pencilTheta (S : Finset (Projectivization K V)) (x : Projectivization K V)
    (c : ℝ≥0) (H J : Projectivization K (Module.Dual K V)) : ℝ :=
  if H=J then 0 else overlap S x c H J

end
end SharpLogRamsey.PreparedProjectiveGeometry

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_TestPointTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpLogRamsey.PoissonGrouping
open Classical
noncomputable section
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def law (rate : ι → ℝ≥0) : Measure (ι → ℕ) :=
  Measure.pi fun i => poissonMeasure (rate i)

instance probability (rate : ι → ℝ≥0) : IsProbabilityMeasure (law rate) := by
  unfold law
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)

def regroup (g : ι → κ) (ω : ι → ℕ) : (k : κ) → {i // g i = k} → ℕ :=
  fun _ i => ω i

def groupedCount (g : ι → κ) (ω : ι → ℕ) (k : κ) : ℕ :=
  ∑ i : {i // g i = k}, ω i

end
end SharpLogRamsey.PoissonGrouping

namespace SharpLogRamsey.PointScore
open Finset MeasureTheory ProbabilityTheory
open SharpRamseyFive.PoissonScore SharpLogRamsey.PoissonGrouping
open scoped Classical BigOperators NNReal
noncomputable section
variable {A D H : Type*} [Fintype A] [Fintype D] [Fintype H]

def pointEmpty {R : ℕ} (P : A → Prop) (ω : Fin R × A → ℕ) (r : Fin R) : ℝ :=
  if ∀ y,P y → ω (r,y)=0 then 1 else 0

def pointScore {R : ℕ} (own : A → Prop) (inc : H → A → Prop) (b : ℝ)
    (ω : Fin R × A → ℕ) : ℝ :=
  ∑ h,∏ r,pointEmpty (fun y => own y ∧ inc h y) ω r *
    (pointEmpty (fun y => ¬own y ∧ inc h y) ω r-b)

def held {R : ℕ} (own center : A → Prop) (i : Fin R × A) : Prop := own i.2 ∨ center i.2

def outsideGroup {R : ℕ} (own center : A → Prop) (g : {y // ¬(own y ∨ center y)} → D)
    (i : {i : Fin R × A // ¬held own center i}) : Fin R × D :=
  (i.1.1,g ⟨i.1.2,i.2⟩)

def ownBit {R : ℕ} (own center : A → Prop) (inc : H → A → Prop)
    (a : {i : Fin R × A // held own center i} → ℕ) (h : H) (r : Fin R) : Bool :=
  decide (∀ y,∀ ho : own y,inc h y → a ⟨(r,y),Or.inl ho⟩=0)

end
end SharpLogRamsey.PointScore

open MeasureTheory
open scoped BigOperators Classical

namespace SharpLogRamsey.PreparedProjectiveGeometry
open Finset
open scoped Classical BigOperators NNReal
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

def direction (x : Projectivization K V) (y : {y : Projectivization K V // y≠x}) :
    RadialLine x := ⟨x.submodule ⊔ y.1.submodule,finrank_join x y.1 y.2.symm,le_sup_left⟩

omit [Finite K] in
lemma direction_eq_iff (x : Projectivization K V)
    (y : {y : Projectivization K V // y≠x}) (W : RadialLine x) :
    direction x y=W ↔ y.1.submodule ≤ W.1 := by
  constructor
  · intro h
    rw [←h]
    exact le_sup_right
  · intro h
    exact Subtype.ext (radial_unique x y y.2.symm W h)

end
end SharpLogRamsey.PreparedProjectiveGeometry

namespace SharpLogRamsey.PointScore
open Finset
open SharpLogRamsey.PoissonGrouping
open scoped Classical BigOperators NNReal
noncomputable section
variable {A D : Type*} [Fintype A] [Fintype D]

def outsideBatchFiber {R : ℕ} (own center : A → Prop)
    (g : {y // ¬(own y ∨ center y)} → D) (r : Fin R) (d : D) :
    {i : {i : Fin R × A // ¬held own center i} // outsideGroup own center g i=(r,d)} ≃
      {y : {y // ¬(own y ∨ center y)} // g y=d} where
  toFun i := ⟨⟨i.1.1.2,i.1.2⟩,congrArg Prod.snd i.2⟩
  invFun y := ⟨⟨(r,y.1.1),y.1.2⟩,Prod.ext rfl y.2⟩
  left_inv i := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext (congrArg Prod.fst i.2).symm rfl
  right_inv y := by rfl

end
end SharpLogRamsey.PointScore

namespace SharpLogRamsey.PreparedProjectiveGeometry
open Finset
open SharpLogRamsey.PointScore
open scoped Classical BigOperators NNReal
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

def outsideDirection (S O : Finset (Projectivization K V)) (x : Projectivization K V)
    (y : {y : S // ¬(y.1∈O ∨ y.1=x)}) : RadialLine x :=
  direction x ⟨y.1.1,fun h => y.2 (Or.inr h)⟩

def outsideDirectionFiber (S O : Finset (Projectivization K V)) (x : Projectivization K V)
    (W : RadialLine x) :
    {y : {y : S // ¬(y.1∈O ∨ y.1=x)} // outsideDirection S O x y=W} ≃
      radialFiber (S\(O∪{x})) x W where
  toFun y := ⟨y.1.1.1,by
    apply (mem_radialFiber _ _ _ _).mpr
    refine ⟨mem_sdiff.mpr ⟨y.1.1.2,?_⟩,fun h => y.1.2 (Or.inr h),?_⟩
    · simpa only [mem_union,mem_singleton] using y.1.2
    · exact (direction_eq_iff x _ W).mp y.2⟩
  invFun y := ⟨⟨⟨y.1,(mem_sdiff.mp ((mem_radialFiber _ _ _ _).mp y.2).1).1⟩,by
      simpa only [mem_union,mem_singleton] using
        (mem_sdiff.mp ((mem_radialFiber _ _ _ _).mp y.2).1).2⟩,by
    apply (direction_eq_iff x _ W).mpr
    exact ((mem_radialFiber _ _ _ _).mp y.2).2.2⟩
  left_inv y := by apply Subtype.ext; apply Subtype.ext; apply Subtype.ext; rfl
  right_inv y := by apply Subtype.ext; rfl

end
end SharpLogRamsey.PreparedProjectiveGeometry

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_TestLearningIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ProjectiveDuality
open Finset
open scoped Classical BigOperators
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
variable [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))]
local instance flat_JoinedTestLearningIncidence_1 : Fintype (Projectivization K (Module.Dual K (Module.Dual K V))) := by
  let : Finite (Module.Dual K (Module.Dual K V)) := Module.finite_of_finite K
  exact Fintype.ofFinite _

end
end SharpLogRamsey.ProjectiveDuality

namespace SharpLogRamsey.PencilContrast
open Finset
open scoped Classical BigOperators
open SharpLogRamsey.ProjectiveDuality
noncomputable section
variable {A B : Type*}

def degree (R : A → B → Prop) (Z : Finset B) (x : A) : ℝ :=
  ∑ H∈Z,if R x H then 1 else 0

end
end SharpLogRamsey.PencilContrast

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Parameters_SourceScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace SharpLogRamsey.ScaleSelection
open Filter Real
open scoped Topology
open SharpLogRamsey.MomentBudgetBridge

def majorant (x : ℝ) : ℝ :=
  1+4*(x^2)^2+4*(x^2)^3*(202*x^2)+(x^2)^4*(202*x^2)^2+
    (x^2)^4*(x^2+4)*(2*x^2)^200

end SharpLogRamsey.ScaleSelection
end

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_TestLearningRowBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Finset
open scoped Classical
namespace SharpLogRamsey.PoissonSchedules
variable {ι : Type*} [Fintype ι]

noncomputable def scheduleLaw (r : ι → ℝ≥0) : Measure (ι → ℕ) :=
  Measure.pi fun i => poissonMeasure (r i)

instance schedule_probability (r : ι → ℝ≥0) : IsProbabilityMeasure (scheduleLaw r) := by
  unfold scheduleLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)

end SharpLogRamsey.PoissonSchedules

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_TestRowScore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PreparedRow
open Finset MeasureTheory ProbabilityTheory SharpLogRamsey.PointScore
open scoped BigOperators Classical
noncomputable section
variable {A H : Type*} [Fintype A] [Fintype H]

abbrev Schedule (S : Finset A) (R : ℕ) := Fin R × S → ℕ

def extend (S : Finset A) {R : ℕ} (ω : Schedule S R) (r : Fin R) (x : A) : ℕ :=
  if hx : x∈S then ω (r,⟨x,hx⟩) else 0

def sample (S : Finset A) {R : ℕ} (ω : Schedule S R) : Finset A :=
  S.filter (fun x => ∃ r,extend S ω r x≠0)

def empty (S : Finset A) {R : ℕ} (inc : H → A → Prop)
    (ω : Schedule S R) (h : H) : Prop := ∀ r (y : S),inc h y → ω (r,y)=0

def emptySet (S : Finset A) (E : Finset H) {R : ℕ}
    (inc : H → A → Prop) (ω : Schedule S R) : Finset H := E.filter (empty S inc ω)

def score (S O : Finset A) (T : Finset H) {R : ℕ}
    (inc : H → A → Prop) (b : ℝ) (ω : Schedule S R) : ℝ :=
  pointScore (fun y : S => y.1∈O) (fun (h : T) (y : S) => inc h.1 y.1) b ω

end
end SharpLogRamsey.PreparedRow

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_TestRowEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PreparedRow
open Finset MeasureTheory ProbabilityTheory SharpLogRamsey.PoissonSchedules
open scoped BigOperators Classical NNReal
noncomputable section
variable {A H : Type*}

def coordinates (S : Finset A) (R : ℕ) (inc : H → A → Prop) (h : H) :
    Finset (Fin R × S) := univ ×ˢ univ.filter (fun y : S => inc h y.1)

end
end SharpLogRamsey.PreparedRow

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_TestRowPencils
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PreparedRow
open Finset MeasureTheory PreparedProjectiveGeometry
open SharpLogRamsey.PointScore
open scoped BigOperators Classical NNReal
noncomputable section
variable {K V I : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedTestRowPencils_1 : Finite (Module.Dual K V) := Module.finite_of_finite K
local instance flat_JoinedTestRowPencils_2 : Fintype (Projectivization K (Module.Dual K V)) := Fintype.ofFinite _

local instance flat_JoinedTestRowPencils_3_r9c519d_1 : Fintype (Projectivization K V) := by
  have : Finite V := Module.finite_of_finite K
  exact Fintype.ofFinite _
abbrev pencil (x : Projectivization K V) : Finset (Projectivization K (Module.Dual K V)) :=
  univ.filter (fun H => x.submodule ≤ LinearMap.ker H.rep)

abbrev outsideMass (S O : Finset (Projectivization K V)) (x : Projectivization K V)
    (c : ℝ≥0) (H : Projectivization K (Module.Dual K V)) : ℝ :=
  (c:ℝ)*((S\(O∪{x})).filter (fun y => y≠x ∧ y.submodule ≤ LinearMap.ker H.rep)).card

structure SecondPencil (j R : ℕ) (S O : Finset (Projectivization K V))
    (x : Projectivization K V) (c L : ℝ≥0)
    (A : Finset (Projectivization K (Module.Dual K V))) (f B C : ℝ)
    (T : Finset I) (a : I → ℝ) : Prop where
  low : ∀ H∈A,3/4≤outsideMass S O x c H
  upp : ∀ H∈A,outsideMass S O x c H≤2
  deviation : ∀ H∈A,|outsideMass S O x c H-(1-f)|≤1
  squares : (∑ H∈A,(outsideMass S O x c H-(1-f))^2)≤C*B*Real.exp ((L:ℝ)/100)
  cardinal : ((∑ i∈range j,Nat.card K^i):ℝ)≤C*B^2
  positive : ∀ i∈T,0<a i
  cover : ∀ H∈A,∀ J∈A,H≠J → 0<overlap (S\(O∪{x})) x c H J →
    ∃ i∈T,a i≤overlap (S\(O∪{x})) x c H J ∧ overlap (S\(O∪{x})) x c H J≤2*a i
  pairs : ∀ i∈T,((largePairs (S\(O∪{x})) x c (a i) A).card:ℝ)*a i^200≤B^2*Real.exp (((L:ℝ)*R)/50)
  diagonalBudget : C*2^R≤Real.exp ((L:ℝ)*R/20)
  powerBudget : (2*(L:ℝ)^2)^R≤Real.exp ((L:ℝ)*R/25)
  sumBudget : C^2*Real.exp ((L:ℝ)/50)+(T.card:ℝ)*2^R*Real.exp ((L:ℝ)*R/50)≤Real.exp ((L:ℝ)*R/20)
  twoBudget : 2≤Real.exp ((L:ℝ)*R/20)

structure HighPencil (j R p h : ℕ) (S O : Finset (Projectivization K V))
    (x : Projectivization K V) (c L : ℝ≥0)
    (A : Finset (Projectivization K (Module.Dual K V))) (f B : ℝ)
    (T : Finset I) (a : I → ℝ) : Prop where
  low : ∀ H∈A,3/4≤outsideMass S O x c H
  upp : ∀ H∈A,outsideMass S O x c H≤2
  deviation : ∀ H∈A,|outsideMass S O x c H-(1-f)|≤13/100
  squares : (∑ H∈A,(outsideMass S O x c H-(1-f))^2)≤B*Real.exp (((L:ℝ)*R)/100)
  cardinal : ((∑ i∈range j,Nat.card K^i):ℝ)≤4*B^2
  directions : ((∑ i∈range (j-1),Nat.card K^i):ℝ)≤4*B
  nonnegative : ∀ i∈T,0≤a i
  cover : ∀ H∈A,∀ J∈A,H≠J → 0<overlap (S\(O∪{x})) x c H J →
    ∃ i∈T,a i≤overlap (S\(O∪{x})) x c H J ∧ overlap (S\(O∪{x})) x c H J≤2*a i
  pairs : ∀ i∈T,((largePairs (S\(O∪{x})) x c (a i) A).card:ℝ)*a i^200≤B^2*Real.exp (((L:ℝ)*R)/50)
  neighbors : ∀ H∈A,∀ i∈T,((largeNeighbors (S\(O∪{x})) x c (a i) A H).card:ℝ)*a i^200≤B*Real.exp (((L:ℝ)*R)/50)
  strong : ∀ H∈A,((largeNeighbors (S\(O∪{x})) x c (1/(100*(p:ℝ))) A H).card:ℝ)≤B*Real.exp (-3*((L:ℝ)*R))
  certificateBudget : MomentBudgetBridge.certificateOverhead p T.card ((L:ℝ)*R)≤Real.exp (2*((L:ℝ)*R)/25)
  shiftBudget : MomentBudgetBridge.shiftOverhead p T.card≤Real.exp (2*((L:ℝ)*R)/25)
  pBudget : (p:ℝ)^2≤Real.exp (((L:ℝ)*R)/10)
  pSumBudget : 2*(p:ℝ)+3≤Real.exp (((L:ℝ)*R)/10)
  hPositive : 0<h
  hSize : h≤(R/2)/400
  hError : (p:ℝ)*h*(19/20:ℝ)^(h-1)<1/2

end
end SharpLogRamsey.PreparedRow

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_TestActualRow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PreparedRow
open Finset MeasureTheory
open scoped BigOperators Classical NNReal
noncomputable section
variable {K V I : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedTestActualRow_1 : Finite (Module.Dual K V) := Module.finite_of_finite K
local instance flat_JoinedTestActualRow_2 : Fintype (Projectivization K (Module.Dual K V)) := Fintype.ofFinite _
local instance flat_JoinedTestActualRow_3 : Fintype (Projectivization K V) := by
  letI : Finite V := Module.finite_of_finite K
  exact Fintype.ofFinite _

abbrev inc (H : Projectivization K (Module.Dual K V)) (x : Projectivization K V) : Prop :=
  x.submodule≤LinearMap.ker H.rep

end
end SharpLogRamsey.PreparedRow

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_PreparedDecoder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace SharpLogRamsey.PreparedDecoder
open Finset SharpLogRamsey.PreparedRow SharpLogRamsey.PointScore
open scoped Classical BigOperators
noncomputable section
variable {A H B : Type*} [Fintype A] [Fintype H]

def counts (S : Finset A) {R : ℕ} (ω : Schedule S R) : Fin R×A → ℕ :=
  fun rx => extend S ω rx.1 rx.2

def publicSample {R : ℕ} (ω : Fin R×A → ℕ) : Finset A :=
  univ.filter (fun x => ∃ r,ω (r,x)≠0)

def publicScore (own : A → Prop) (T : Finset H) (inc : H → A → Prop)
    (b : ℝ) {R : ℕ} (ω : Fin R×A → ℕ) : ℝ :=
  ∑ h∈T,∏ r,
    (if ∀ y,own y ∧ inc h y → ω (r,y)=0 then (1:ℝ) else 0)*
    ((if ∀ y,¬own y ∧ inc h y → ω (r,y)=0 then (1:ℝ) else 0)-b)

end
end SharpLogRamsey.PreparedDecoder

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_PoissonSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PoissonSupport
open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators Classical NNReal
noncomputable section
variable {ι : Type*} [Fintype ι]

def extend (S : Finset ι) (ω : S → ℕ) (i : ι) : ℕ :=
  if h : i∈S then ω ⟨i,h⟩ else 0

end
end SharpLogRamsey.PoissonSupport

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_PreparedProposals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Classical
open Finset

namespace SharpLogRamsey.PoissonLikelihood
open MeasureTheory ProbabilityTheory Finset
open scoped Classical BigOperators NNReal
noncomputable section
variable {ι : Type*} [Fintype ι]

def law (rate : ι → ℝ≥0) : Measure (ι → ℕ) :=
  Measure.pi (fun i => poissonMeasure (rate i))

instance probability (rate : ι → ℝ≥0) : IsProbabilityMeasure (law rate) := by
  unfold law
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)

def uniformRate (S : Finset ι) (a : ℝ≥0) (i : ι) : ℝ≥0 :=
  if i∈S then a/(S.card:ℝ≥0) else 0

end
end SharpLogRamsey.PoissonLikelihood

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_PreparedPointProposals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PreparedRow
open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical
noncomputable section
variable {A : Type*} [Fintype A]

def ambientCounts (S : Finset A) {R : ℕ} (ω : Schedule S R) : Fin R×A → ℕ :=
  fun rx => extend S ω rx.1 rx.2

local instance flat_JoinedPreparedPointProposals_1_r9c519d_1 (R : ℕ) : DecidableEq (Fin R×A) := Classical.decEq _
def coordinateSupport (S : Finset A) (R : ℕ) : Finset (Fin R×A) := univ ×ˢ S

def ambientRate (S : Finset A) (R : ℕ) (γ : ℝ≥0) (rx : Fin R×A) : ℝ≥0 :=
  if rx.2∈S then γ else 0

end
end SharpLogRamsey.PreparedRow

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_PreparedDescription
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PreparedDescription
open Finset MeasureTheory PreparedRow
open scoped Classical BigOperators NNReal
noncomputable section
variable {K V I B : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedPreparedDescription_1_r9c519d_1 (R : ℕ) : DecidableEq (Fin R × Projectivization K V) := Classical.decEq _
local instance flat_JoinedPreparedDescription_2 : Finite (Module.Dual K V) := Module.finite_of_finite K
local instance flat_JoinedPreparedDescription_3 : Fintype (Projectivization K (Module.Dual K V)) := Fintype.ofFinite _
local instance flat_JoinedPreparedDescription_4 : Fintype (Projectivization K V) := by
  have : Finite V := Module.finite_of_finite K
  exact Fintype.ofFinite _

end
end SharpLogRamsey.PreparedDescription

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_PreparedShortRow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PreparedDescription
open Finset MeasureTheory PreparedRow Real
open scoped Classical BigOperators NNReal
noncomputable section
variable {K V I B : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedPreparedShortRow_1_r9c519d_1 (R : ℕ) : DecidableEq (Fin R × Projectivization K V) := Classical.decEq _
local instance flat_JoinedPreparedShortRow_4 : Fintype (Projectivization K V) := by
  letI : Finite V := Module.finite_of_finite K
  exact Fintype.ofFinite _

end
end SharpLogRamsey.PreparedDescription

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_HighRank
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High-rank geometric supports and entropy estimates. -/

section
open scoped BigOperators Classical
open Finset
section

namespace SharpLogRamsey
namespace RichUnion

noncomputable section

open Module MvPolynomial

section Evaluation
variable {K : Type*} [Field K] {n : ℕ}

def evalOn (Z : Finset (Fin n → K)) : MvPolynomial (Fin n) K →ₗ[K] (Z → K) where
  toFun p z := MvPolynomial.eval z.1 p
  map_add' p q := by ext z; simp
  map_smul' a p := by ext z; simp

@[simp] theorem evalOn_apply (Z : Finset (Fin n → K))
    (p : MvPolynomial (Fin n) K) (z : Z) :
    evalOn Z p z = MvPolynomial.eval z.1 p := rfl

def evalSpace (Z : Finset (Fin n → K)) (m : ℕ) : Submodule K (Z → K) :=
  (MvPolynomial.restrictDegree (Fin n) K m).map (evalOn Z)

def diagonal (Z : Finset (Fin n → K)) (e : Fin n →₀ ℕ) : (Z → K) →ₗ[K] (Z → K) where
  toFun v z := (MvPolynomial.eval z.1 (MvPolynomial.monomial e (1 : K))) * v z
  map_add' v w := by ext z; simp [mul_add]
  map_smul' a v := by ext z; simp [mul_comm, mul_assoc]

def linearCoordinates {r : ℕ} (f : (Fin r → K) →ₗ[K] (Fin n → K))
    (j : Fin n) : MvPolynomial (Fin r) K :=
  ∑ i : Fin r, MvPolynomial.C (f (Pi.single i 1) j) * MvPolynomial.X i

def inSubspace (X : Finset (Fin n → K)) (W : Submodule K (Fin n → K)) :
    Finset (Fin n → K) := by
  classical
  exact X.filter (fun x => x ∈ W)

@[simp] theorem mem_inSubspace (X : Finset (Fin n → K))
    (W : Submodule K (Fin n → K)) (x : Fin n → K) :
    x ∈ inSubspace X W ↔ x ∈ X ∧ x ∈ W := by
  classical
  simp [inSubspace]

end Evaluation
end
end RichUnion
end SharpLogRamsey

namespace SharpLogRamsey.RichUnion
noncomputable section
open Module

section ProjectiveLifts
variable {K : Type*} [Field K] [Fintype K] {n : ℕ}

def vectorLifts (X : Finset (Projectivization K (Fin n → K))) : Finset (Fin n → K) := by
  classical
  exact (Finset.univ.filter (fun v : {v : Fin n → K // v ≠ 0} =>
    Projectivization.mk K v.1 v.2 ∈ X)).map (Function.Embedding.subtype _)

@[simp] theorem mem_vectorLifts (X : Finset (Projectivization K (Fin n → K)))
    (v : Fin n → K) : v ∈ vectorLifts X ↔
      ∃ hv : v ≠ 0, Projectivization.mk K v hv ∈ X := by
  classical
  simp only [vectorLifts, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Function.Embedding.subtype_apply]
  constructor
  · rintro ⟨⟨v, hv⟩, hX, rfl⟩
    exact ⟨hv, hX⟩
  · rintro ⟨hv, hX⟩
    exact ⟨⟨v, hv⟩, hX, rfl⟩

end ProjectiveLifts
end
end SharpLogRamsey.RichUnion
end
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_CardVectorLifts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High-rank geometric supports and entropy estimates. -/

section
open scoped BigOperators Classical
open Finset
section
namespace SharpLogRamsey.RichUnion
noncomputable section
open Module
section ProjectiveLifts
variable {K : Type*} [Field K] [Fintype K] {n : ℕ}

def projectiveIn (X : Finset (Projectivization K (Fin n → K)))
    (W : Submodule K (Fin n → K)) : Finset (Projectivization K (Fin n → K)) := by
  classical
  exact X.filter (fun a => a.submodule ≤ W)
omit [Fintype K] in

@[simp] theorem mem_projectiveIn (X : Finset (Projectivization K (Fin n → K)))
    (W : Submodule K (Fin n → K)) (a : Projectivization K (Fin n → K)) :
    a ∈ projectiveIn X W ↔ a ∈ X ∧ a.submodule ≤ W := by
  classical
  simp [projectiveIn]

def projectivePoints (W : Submodule K (Fin n → K)) :
    Finset (Projectivization K (Fin n → K)) := by
  classical
  letI := Fintype.ofFinite (Projectivization K (Fin n → K))
  exact Finset.univ.filter (fun a => a.submodule ≤ W)

@[simp] theorem mem_projectivePoints (W : Submodule K (Fin n → K))
    (a : Projectivization K (Fin n → K)) :
    a ∈ projectivePoints W ↔ a.submodule ≤ W := by
  classical
  simp [projectivePoints]

def projectiveUnion (𝓥 : Set (Submodule K (Fin n → K))) :
    Finset (Projectivization K (Fin n → K)) := by
  classical
  letI := Fintype.ofFinite (Projectivization K (Fin n → K))
  exact Finset.univ.filter (fun a => ∃ W ∈ 𝓥, a.submodule ≤ W)

@[simp] theorem mem_projectiveUnion (𝓥 : Set (Submodule K (Fin n → K)))
    (a : Projectivization K (Fin n → K)) :
    a ∈ projectiveUnion 𝓥 ↔ ∃ W ∈ 𝓥, a.submodule ≤ W := by
  classical
  simp [projectiveUnion]

def projectiveSubmoduleEquiv (W : Submodule K (Fin n → K)) :
    Projectivization K W ≃ {a : Projectivization K (Fin n → K) // a.submodule ≤ W} := by
  let f : Projectivization K W → {a : Projectivization K (Fin n → K) // a.submodule ≤ W} :=
    fun a => ⟨Projectivization.map W.subtype W.injective_subtype a, by
      induction a using Projectivization.ind with
      | h v hv =>
        rw [Projectivization.map_mk, Projectivization.submodule_mk,
          Submodule.span_singleton_le_iff_mem]
        exact v.property⟩
  apply Equiv.ofBijective f
  constructor
  · intro a b h
    exact Projectivization.map_injective W.subtype W.injective_subtype
      (congrArg Subtype.val h)
  · rintro ⟨a, ha⟩
    have hmem : a.rep ∈ W := ha (by
      rw [Projectivization.submodule_eq]
      exact Submodule.mem_span_singleton_self _)
    let v : W := ⟨a.rep, hmem⟩
    have hv : v ≠ 0 := fun h => a.rep_nonzero (congrArg Subtype.val h)
    refine ⟨Projectivization.mk K v hv, ?_⟩
    apply Subtype.ext
    exact a.mk_rep

end ProjectiveLifts
end
end SharpLogRamsey.RichUnion
end
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_TargetEvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High-rank geometric supports and entropy estimates. -/

section
open scoped BigOperators Classical
open Finset

namespace SharpLogRamsey.ProductLaw
open scoped BigOperators
open Finset Classical
noncomputable section
variable {ι κ Ω : Type*} [Fintype ι] [Fintype κ] [Fintype Ω]

noncomputable def weight (w : Ω → ℝ) (z : ι → Ω) : ℝ := ∏ i, w (z i)

end
end SharpLogRamsey.ProductLaw

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_AtomEscape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High-rank geometric supports and entropy estimates. -/

section
open scoped BigOperators Classical
open Finset

namespace SharpLogRamsey.SimultaneousExtraction
open scoped BigOperators
open Finset Classical
noncomputable section
variable {Ω : Type*} [Fintype Ω]

def retained {k ℓ : ℕ} (S : Finset (Fin ℓ)) (h : k ≤ S.card) : Fin k ↪o Fin ℓ :=
  (Fin.castLEOrderEmb h).comp (S.orderEmbOfFin rfl)

end
end SharpLogRamsey.SimultaneousExtraction

namespace SharpLogRamsey.SimultaneousExtraction
open scoped BigOperators Classical
open Finset
noncomputable section
variable {Ω R F : Type*} [Fintype Ω] [Fintype R] [Fintype F]

def independentWeight (p : Ω → ℝ) (w : R → ℝ) (u : Ω × R) : ℝ := p u.1*w u.2

def missed {ℓ : ℕ} (f : Ω → Fin ℓ → F) (D : R → Finset F) (u : Ω × R) : ℕ :=
  (univ.filter (fun i => f u.1 i ∉ D u.2)).card

end
end SharpLogRamsey.SimultaneousExtraction

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_ProjectionCenterBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Projection
open Finset Real
open scoped Classical BigOperators
noncomputable section

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance finiteDualV : Finite (Module.Dual K V) := Module.finite_of_finite K
local instance flat_JoinedProjectionCenterBounds_1 : Fintype (Projectivization K V) := by
  letI : Finite V := Module.finite_of_finite K
  exact Fintype.ofFinite _
local instance flat_JoinedProjectionCenterBounds_2 : Fintype (Projectivization K (Module.Dual K V)) := Fintype.ofFinite _

end
end SharpLogRamsey.Projection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_ProjectionPublic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Projection
open Finset Real
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedProjectionPublic_1 : Fintype (Projectivization K V) := by
  letI : Finite V := Module.finite_of_finite K
  exact Fintype.ofFinite _

end
end SharpLogRamsey.Projection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Validation_ValidationReturn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Validation
open Finset Real ProjectiveDuality
open scoped Classical BigOperators
noncomputable section
variable {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedValidationReturn_1 : Finite (Module.Dual K V) := Module.finite_of_finite K
local instance flat_JoinedValidationReturn_2 : Fintype (Projectivization K V) := by
  letI : Finite V := Module.finite_of_finite K
  exact Fintype.ofFinite _
local instance flat_JoinedValidationReturn_3 : Fintype (Projectivization K (Module.Dual K V)) := Fintype.ofFinite _
local instance flat_JoinedValidationReturn_4 : Finite (Module.Dual K (Module.Dual K V)) := Module.finite_of_finite K
local instance flat_JoinedValidationReturn_5 : Fintype (Projectivization K (Module.Dual K (Module.Dual K V))) := Fintype.ofFinite _

end
end SharpLogRamsey.Validation

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Validation_ValidationReverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Validation
open Finset Real ProjectiveDuality
open scoped Classical BigOperators
noncomputable section
variable {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedValidationReverse_1 : Finite (Module.Dual K V) := Module.finite_of_finite K
local instance flat_JoinedValidationReverse_3 : Fintype (Projectivization K (Module.Dual K V)) := Fintype.ofFinite _
local instance flat_JoinedValidationReverse_4 : Finite (Module.Dual K (Module.Dual K V)) := Module.finite_of_finite K
local instance flat_JoinedValidationReverse_5 : Fintype (Projectivization K (Module.Dual K (Module.Dual K V))) := Fintype.ofFinite _

end
end SharpLogRamsey.Validation

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Validation_ValidationGapCosts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Validation
open Finset Real
open scoped Classical BigOperators
noncomputable section

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedValidationGapCosts_1 : Fintype (Projectivization K V) := by
  letI : Finite V := Module.finite_of_finite K
  exact Fintype.ofFinite _
local instance flat_JoinedValidationGapCosts_2 : Finite (Module.Dual K V) := Module.finite_of_finite K
local instance flat_JoinedValidationGapCosts_3 : Fintype (Projectivization K (Module.Dual K V)) := Fintype.ofFinite _
local instance flat_JoinedValidationGapCosts_4 : Finite (Module.Dual K (Module.Dual K V)) := Module.finite_of_finite K
local instance flat_JoinedValidationGapCosts_5 : Fintype (Projectivization K (Module.Dual K (Module.Dual K V))) := Fintype.ofFinite _

end
end SharpLogRamsey.Validation

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_PreparedTypical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PreparedTypical
open Finset PreparedRow
open scoped Classical BigOperators NNReal
noncomputable section
variable {A : Type*}

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

def mass (S : Finset (Projectivization K V)) (c : ℝ≥0)
    (H : Projectivization K (Module.Dual K V)) : ℝ :=
  (c:ℝ)*((S.filter (fun y => y.submodule≤LinearMap.ker H.rep)).card:ℝ)

end
end SharpLogRamsey.PreparedTypical

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_PreparedVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace SharpLogRamsey.RegularPencils
open Finset
open scoped Classical BigOperators
noncomputable section
variable {A ι : Type*} [Fintype A] [Fintype ι]

def exceptional (l : A → ℝ) (c : ι → A → ℝ) (f : ι → ℝ) : Finset A :=
  univ.filter (fun H =>  1/10  <  |l H-1| ∨ ∃ i,1/50  <  |c i H-f i|)

end
end SharpLogRamsey.RegularPencils

namespace SharpLogRamsey.PreparedVariance
open Finset PreparedRow PreparedTypical RegularPencils
open scoped Classical BigOperators NNReal
noncomputable section
variable {K V I : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype I]
local instance flat_JoinedPreparedVariance_1 : Finite (Module.Dual K V) := Module.finite_of_finite K
local instance flat_JoinedPreparedVariance_2 : Fintype (Projectivization K (Module.Dual K V)) := Fintype.ofFinite _
local instance flat_JoinedPreparedVariance_3 : Fintype (Projectivization K V) := by
  letI : Finite V := Module.finite_of_finite K
  exact Fintype.ofFinite _

def weights (S : Finset (Projectivization K V)) (C : I→Finset (Projectivization K V))
    (c : ℝ≥0) : Option (Option I)→Projectivization K (Module.Dual K V)→ℝ
  | none,H => min 1 ((mass S c H-1)^2)
  | some none,H => if H∈exceptional (mass S c) (fun i => mass (C i) c)
      (fun i => ((C i).card:ℝ)/(S.card:ℝ)) then 1 else 0
  | some (some i),H => min 1 ((mass (C i) c H-((C i).card:ℝ)/(S.card:ℝ))^2)

end
end SharpLogRamsey.PreparedVariance

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_PreparedGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace SharpLogRamsey.PreparedGeometry
open Finset PreparedRow PreparedTypical PreparedVariance RegularPencils
open scoped Classical BigOperators NNReal
noncomputable section
variable {K V J : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedPreparedGeometry_1 : Finite (Module.Dual K V) := Module.finite_of_finite K
local instance flat_JoinedPreparedGeometry_2 : Fintype (Projectivization K (Module.Dual K V)) := Fintype.ofFinite _

end
end SharpLogRamsey.PreparedGeometry

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_PreparedRadial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PreparedProjectiveGeometry
open Finset
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedPreparedRadial_1 : Finite (Projectivization K V) := by
  let : Finite V := Module.finite_of_finite K
  infer_instance
local instance flat_JoinedPreparedRadial_2 : Fintype (Projectivization K V) := Fintype.ofFinite _
local instance flat_JoinedPreparedRadial_3 : Finite (Submodule K V) := by
  let : Finite V := Module.finite_of_finite K
  exact Finite.of_injective (fun W : Submodule K V => (W : Set V)) SetLike.coe_injective
local instance flat_JoinedPreparedRadial_4 : Fintype (Submodule K V) := Fintype.ofFinite _

def planePoints (W : Submodule K V) : Finset (Projectivization K V) :=
  univ.filter (fun x => x.submodule ≤ W)

@[simp] lemma mem_planePoints {W : Submodule K V} {x : Projectivization K V} :
    x ∈ planePoints W ↔ x.submodule ≤ W := by simp [planePoints]

def ProjectiveLine := {W : Submodule K V // Module.finrank K W = 2}
instance flat_JoinedPreparedRadial_5 : Fintype (ProjectiveLine (K:=K) (V:=V)) := by unfold ProjectiveLine; infer_instance

end
end SharpLogRamsey.PreparedProjectiveGeometry

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_PreparedRadialCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PreparedProjectiveGeometry
open Finset
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedPreparedRadialCount_1 : Finite (Projectivization K V) := by
  have : Finite V := Module.finite_of_finite K
  infer_instance
local instance flat_JoinedPreparedRadialCount_2 : Fintype (Projectivization K V) := Fintype.ofFinite _

end
end SharpLogRamsey.PreparedProjectiveGeometry

namespace SharpLogRamsey.PreparedRadialResidual
open Finset PreparedProjectiveGeometry
open scoped Classical BigOperators
noncomputable section
variable {q : ℕ} [Fact q.Prime]
local instance flat_JoinedPreparedRadialCount_7 : Fintype (Projectivization (ZMod q) (Fin 4→ZMod q)) := Fintype.ofFinite _

end
end SharpLogRamsey.PreparedRadialResidual

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_RadialExceptions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace SharpLogRamsey.PreparedProjectiveGeometry
open Finset
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedRadialExceptions_1 : Finite (Projectivization K V) := by
  let : Finite V := Module.finite_of_finite K
  infer_instance
local instance flat_JoinedRadialExceptions_2 : Fintype (Projectivization K V) := Fintype.ofFinite _

end
end SharpLogRamsey.PreparedProjectiveGeometry

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_PreparedRadialBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PreparedProjectiveGeometry
open Finset
open scoped Classical BigOperators
noncomputable section

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedPreparedRadialBounds_1 : Finite (Projectivization K V) := by
  let : Finite V := Module.finite_of_finite K
  infer_instance
local instance flat_JoinedPreparedRadialBounds_2 : Fintype (Projectivization K V) := Fintype.ofFinite _

end
end SharpLogRamsey.PreparedProjectiveGeometry

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_PreparedResidualBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PreparedRadialResidual
open Finset PreparedProjectiveGeometry
open scoped Classical BigOperators
noncomputable section
variable {q : ℕ} [Fact q.Prime]
local instance flat_JoinedPreparedResidualBounds_3 : Fintype (Projectivization (ZMod q) (Fin 4→ZMod q)) := Fintype.ofFinite _

end
end SharpLogRamsey.PreparedRadialResidual

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Spatial_PreparedSpatialRadial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PreparedProjectiveGeometry
open Finset
open scoped Classical BigOperators
noncomputable section
variable {K V I : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedPreparedSpatialRadial_1 : Finite (Projectivization K V) := by
  let : Finite V := Module.finite_of_finite K
  infer_instance
local instance flat_JoinedPreparedSpatialRadial_2 : Fintype (Projectivization K V) := Fintype.ofFinite _

end
end SharpLogRamsey.PreparedProjectiveGeometry

namespace SharpLogRamsey.PreparedRadialResidual
open Finset PreparedProjectiveGeometry
open scoped Classical BigOperators
noncomputable section
variable {q : ℕ} [Fact q.Prime]
local instance flat_JoinedPreparedSpatialRadial_5 : Fintype (Projectivization (ZMod q) (Fin 4→ZMod q)) := Fintype.ofFinite _

end
end SharpLogRamsey.PreparedRadialResidual

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_RegularPreparationBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PreparedGeometry
open Finset PreparedRow PreparedTypical
open scoped BigOperators Classical NNReal
noncomputable section

variable {K V J : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedRegularPreparationBounds_1 : Finite (Module.Dual K V) := Module.finite_of_finite K
local instance flat_JoinedRegularPreparationBounds_2 : Fintype (Projectivization K (Module.Dual K V)) := Fintype.ofFinite _

end
end SharpLogRamsey.PreparedGeometry

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Planar_PlanarBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PlanarLearning
open Finset Real PreparedRow PreparedGeometry PreparedTypical
open scoped Classical BigOperators NNReal
noncomputable section

structure Budget (σ P : ℝ) (L : ℝ≥0) (R p h : ℕ) : Prop where
  sigma : 2≤σ
  large : 100000000000000≤P
  upper : P≤σ
  B : 2*exp (6*P)≤exp σ
  identity : P=(L:ℝ)*R
  Llarge : 10000≤(L:ℝ)
  Rlarge : 400≤R
  p_pos : 0<p
  p_even : Even p
  order : 10000*σ≤(p:ℝ)*P
  sparseSchedules : (R:ℝ)*exp (-(24/25:ℝ)*(L:ℝ))≤1/10
  diag : 400000*2^R≤exp (P/20)
  pow : (2*(L:ℝ)^2)^R≤exp (P/25)
  sum : (400000:ℝ)^2*exp ((L:ℝ)/50)≤exp (P/20)
  two : 2≤exp (P/20)
  variance : 400000*exp ((L:ℝ)/1000)≤exp (P/100)
  cert : MomentBudgetBridge.certificateOverhead p 0 P≤exp (2*P/25)
  shift : MomentBudgetBridge.shiftOverhead p 0≤exp (2*P/25)
  pb : (p:ℝ)^2≤exp (P/10)
  ps : 2*(p:ℝ)+3≤exp (P/10)
  h_pos : 0<h
  h_small : h≤(R/2)/400
  h_root : (p:ℝ)*h*(19/20:ℝ)^(h-1)<1/2

end
end SharpLogRamsey.PlanarLearning

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Spatial_SpatialBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.SpatialLearning
open Finset Real Filter
open scoped Topology NNReal
noncomputable section

structure Budget (σ P : ℝ) (L : ℝ≥0) (R N p h : ℕ) : Prop where
  sigma : 2≤σ
  large : 100000000000000≤P
  upper : P≤σ
  B : 2*exp (6*P)≤exp σ
  identity : P=(L:ℝ)*R
  Llarge : 10000≤(L:ℝ)
  Rlarge : 400≤R
  p_pos : 0<p
  p_even : Even p
  order : 10000*σ≤(p:ℝ)*P
  sparseSchedules : (R:ℝ)*exp (-(24/25:ℝ)*(L:ℝ))≤1/10
  diag : 400000*2^R≤exp (P/20)
  pow : (2*(L:ℝ)^2)^R≤exp (P/25)
  sum : (400000:ℝ)^2*exp ((L:ℝ)/50)+(N:ℝ)*2^R*exp (P/50)≤exp (P/20)
  two : 2≤exp (P/20)
  variance : 400000*exp ((L:ℝ)/1000)≤exp (P/100)
  cert : MomentBudgetBridge.certificateOverhead p N P≤exp (2*P/25)
  shift : MomentBudgetBridge.shiftOverhead p N≤exp (2*P/25)
  pb : (p:ℝ)^2≤exp (P/10)
  ps : 2*(p:ℝ)+3≤exp (P/10)
  h_pos : 0<h
  h_small : h≤(R/2)/400
  h_root : (p:ℝ)*h*(19/20:ℝ)^(h-1)<1/2

end
end SharpLogRamsey.SpatialLearning

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Spatial_SpatialTraining
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.SpatialLearning
open Finset Real PreparedRow PreparedGeometry PreparedTypical
open scoped Classical BigOperators NNReal
noncomputable section

variable {K V J : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedSpatialTraining_1 : Finite (Module.Dual K V) := Module.finite_of_finite K
local instance flat_JoinedSpatialTraining_2 : Fintype (Projectivization K (Module.Dual K V)) := Fintype.ofFinite _
local instance flat_JoinedSpatialTraining_3 : Fintype (Projectivization K V) := by
  letI : Finite V := Module.finite_of_finite K
  exact Fintype.ofFinite _

end
end SharpLogRamsey.SpatialLearning

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Spatial_SpatialPreparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.SpatialLearning
open Finset Real PreparedRow PreparedGeometry PreparedTypical PreparedProjectiveGeometry
open scoped Classical BigOperators NNReal
noncomputable section
variable {K V J : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedSpatialPreparation_1 : Finite (Module.Dual K V) := Module.finite_of_finite K
local instance flat_JoinedSpatialPreparation_2 : Fintype (Projectivization K (Module.Dual K V)) := Fintype.ofFinite _
local instance flat_JoinedSpatialPreparation_3 : Fintype (Projectivization K V) := by
  letI : Finite V := Module.finite_of_finite K
  exact Fintype.ofFinite _

end
end SharpLogRamsey.SpatialLearning

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Spatial_SpatialRow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.SpatialLearning
open Finset Real PreparedRow PreparedGeometry PreparedTypical
open scoped Classical BigOperators NNReal
noncomputable section
variable {K V J : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedSpatialRow_1_r9c519d_1 (R : ℕ) : DecidableEq (Fin R × Projectivization K V) := Classical.decEq _
local instance flat_JoinedSpatialRow_4 : Fintype (Projectivization K V) := by
  letI : Finite V := Module.finite_of_finite K
  exact Fintype.ofFinite _

end
end SharpLogRamsey.SpatialLearning

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Spatial_SpatialPublic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.SpatialPublic
open Finset Real PreparedRow PreparedProjectiveGeometry SpatialLearning
open scoped Classical BigOperators NNReal
noncomputable section
variable {K V J : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedSpatialPublic_1_r9c519d_1 (R : ℕ) : DecidableEq (Fin R × Projectivization K V) := Classical.decEq _
local instance flat_JoinedSpatialPublic_2 : Finite (Module.Dual K V) := Module.finite_of_finite K
local instance flat_JoinedSpatialPublic_3 : Fintype (Projectivization K (Module.Dual K V)) := Fintype.ofFinite _
local instance flat_JoinedSpatialPublic_4 : Fintype (Projectivization K V) := by
  letI : Finite V := Module.finite_of_finite K
  exact Fintype.ofFinite _

end
end SharpLogRamsey.SpatialPublic

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Spatial_SpatialCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.SpatialPublic
open Finset Real PreparedRow SpatialLearning
open scoped Classical BigOperators NNReal
noncomputable section
variable {K V J : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedSpatialCover_1_r9c519d_1 (R : ℕ) : DecidableEq (Fin R × Projectivization K V) := Classical.decEq _
local instance flat_JoinedSpatialCover_2 : Finite (Module.Dual K V) := Module.finite_of_finite K
local instance flat_JoinedSpatialCover_3 : Fintype (Projectivization K (Module.Dual K V)) := Fintype.ofFinite _
local instance flat_JoinedSpatialCover_4 : Fintype (Projectivization K V) := by
  letI : Finite V := Module.finite_of_finite K
  exact Fintype.ofFinite _

end
end SharpLogRamsey.SpatialPublic

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Spatial_SpatialGreedy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.SpatialLearning
open Finset Real PreparedProjectiveGeometry
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedSpatialGreedy_3 : Finite (Submodule K V) := by
  let : Finite V := Module.finite_of_finite K
  exact Finite.of_injective (fun W : Submodule K V => (W : Set V)) SetLike.coe_injective
local instance flat_JoinedSpatialGreedy_4 : Fintype (Submodule K V) := Fintype.ofFinite _

end
end SharpLogRamsey.SpatialLearning

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Planar_PlanarGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PlanarLearning
open Finset Real PreparedRow PreparedGeometry PreparedTypical
open scoped Classical BigOperators NNReal
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedPlanarGeometry_1_r9c519d_1 (R : ℕ) : DecidableEq (Fin R × Projectivization K V) := Classical.decEq _
local instance flat_JoinedPlanarGeometry_2 : Finite (Module.Dual K V) := Module.finite_of_finite K
local instance flat_JoinedPlanarGeometry_3 : Fintype (Projectivization K (Module.Dual K V)) := Fintype.ofFinite _
local instance flat_JoinedPlanarGeometry_4 : Fintype (Projectivization K V) := by
  letI : Finite V := Module.finite_of_finite K
  exact Fintype.ofFinite _

end
end SharpLogRamsey.PlanarLearning

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Planar_PlanarTraining
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PlanarLearning
open Finset Real PreparedRow PreparedGeometry PreparedTypical
open scoped Classical BigOperators NNReal
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedPlanarTraining_1_r9c519d_1 (R : ℕ) : DecidableEq (Fin R × Projectivization K V) := Classical.decEq _
local instance flat_JoinedPlanarTraining_2 : Finite (Module.Dual K V) := Module.finite_of_finite K
local instance flat_JoinedPlanarTraining_3 : Fintype (Projectivization K (Module.Dual K V)) := Fintype.ofFinite _
local instance flat_JoinedPlanarTraining_4 : Fintype (Projectivization K V) := by
  letI : Finite V := Module.finite_of_finite K
  exact Fintype.ofFinite _

end
end SharpLogRamsey.PlanarLearning

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Planar_PlanarRow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PlanarLearning
open Finset Real PreparedRow PreparedGeometry PreparedTypical
open scoped Classical BigOperators NNReal
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedPlanarRow_1_r9c519d_1 (R : ℕ) : DecidableEq (Fin R × Projectivization K V) := Classical.decEq _
local instance flat_JoinedPlanarRow_4 : Fintype (Projectivization K V) := by
  letI : Finite V := Module.finite_of_finite K
  exact Fintype.ofFinite _

end
end SharpLogRamsey.PlanarLearning

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Planar_PlanarPublic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PlanarLearning
open Finset Real PreparedRow
open scoped Classical BigOperators NNReal
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedPlanarPublic_1_r9c519d_1 (R : ℕ) : DecidableEq (Fin R × Projectivization K V) := Classical.decEq _
local instance flat_JoinedPlanarPublic_2 : Finite (Module.Dual K V) := Module.finite_of_finite K
local instance flat_JoinedPlanarPublic_3 : Fintype (Projectivization K (Module.Dual K V)) := Fintype.ofFinite _
local instance flat_JoinedPlanarPublic_4 : Fintype (Projectivization K V) := by
  letI : Finite V := Module.finite_of_finite K
  exact Fintype.ofFinite _

end
end SharpLogRamsey.PlanarLearning

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Planar_PlanarCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PlanarLearning
open Finset Real PreparedRow
open scoped Classical BigOperators NNReal
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedPlanarCover_1_r9c519d_1 (R : ℕ) : DecidableEq (Fin R × Projectivization K V) := Classical.decEq _
local instance flat_JoinedPlanarCover_2 : Finite (Module.Dual K V) := Module.finite_of_finite K
local instance flat_JoinedPlanarCover_3 : Fintype (Projectivization K (Module.Dual K V)) := Fintype.ofFinite _
local instance flat_JoinedPlanarCover_4 : Fintype (Projectivization K V) := by
  letI : Finite V := Module.finite_of_finite K
  exact Fintype.ofFinite _

end
end SharpLogRamsey.PlanarLearning

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Planar_PlanarDescription
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PlanarLearning
open Finset Real Filter
open scoped Classical BigOperators Topology NNReal
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedPlanarDescription_3 : Fintype (Projectivization K V) := by
  letI : Finite V := Module.finite_of_finite K
  exact Fintype.ofFinite _

end
end SharpLogRamsey.PlanarLearning

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Planar_PlanarUniform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PlanarLearning
open Finset Real Filter
open scoped Classical BigOperators Topology NNReal
noncomputable section
local instance flat_JoinedPlanarUniform_1 {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] : Finite (Module.Dual K V) := Module.finite_of_finite K
local instance flat_JoinedPlanarUniform_2 {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] : Fintype (Projectivization K (Module.Dual K V)) := Fintype.ofFinite _
local instance flat_JoinedPlanarUniform_3 {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] : Fintype (Projectivization K V) := by
  letI : Finite V := Module.finite_of_finite K
  exact Fintype.ofFinite _

end
end SharpLogRamsey.PlanarLearning

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Planar_PlanarBoth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PlanarLearning
open Finset Real Filter
open scoped Classical BigOperators Topology NNReal
noncomputable section
local instance flat_JoinedPlanarBoth_2 {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] : Fintype (Projectivization K V) := by
  letI : Finite V := Module.finite_of_finite K
  exact Fintype.ofFinite _

end
end SharpLogRamsey.PlanarLearning

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Spatial_SpatialHeaderCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.SpatialPublic
open Finset Real PreparedRow SpatialLearning
open scoped Classical BigOperators NNReal
noncomputable section
variable {K V J : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype J]
local instance flat_JoinedSpatialHeaderCover_1_r9c519d_1 (R : ℕ) : DecidableEq (Fin R × Projectivization K V) := Classical.decEq _
local instance flat_JoinedSpatialHeaderCover_2 : Finite (Module.Dual K V) := Module.finite_of_finite K
local instance flat_JoinedSpatialHeaderCover_3 : Fintype (Projectivization K (Module.Dual K V)) := Fintype.ofFinite _
local instance flat_JoinedSpatialHeaderCover_4 : Fintype (Projectivization K V) := by
  let : Finite V := Module.finite_of_finite K
  exact Fintype.ofFinite _

end
end SharpLogRamsey.SpatialPublic

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Spatial_SpatialActualCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.SpatialPublic
open Finset Real Filter SpatialLearning PreparedProjectiveGeometry
open scoped Classical BigOperators Topology NNReal
noncomputable section
local instance flat_JoinedSpatialActualCover_1 (q : ℕ) [Fact q.Prime] :
    Finite (Submodule (ZMod q) (Fin 4→ZMod q)) :=
  Finite.of_injective (fun W : Submodule (ZMod q) (Fin 4→ZMod q) => (W : Set (Fin 4→ZMod q)))
    SetLike.coe_injective
local instance flat_JoinedSpatialActualCover_2 (q : ℕ) [Fact q.Prime] :
    Fintype (Submodule (ZMod q) (Fin 4→ZMod q)) := Fintype.ofFinite _

local instance flat_JoinedSpatialActualCover_3 (q : ℕ) [Fact q.Prime] :
    Fintype (Projectivization (ZMod q) (Fin 4 → ZMod q)) := Fintype.ofFinite _
local instance flat_JoinedSpatialActualCover_4 (q : ℕ) [Fact q.Prime] :
    Fintype (Projectivization (ZMod q) (Module.Dual (ZMod q) (Fin 4 → ZMod q))) := by
  letI : Finite (Module.Dual (ZMod q) (Fin 4 → ZMod q)) := Module.finite_of_finite (ZMod q)
  exact Fintype.ofFinite _

end
end SharpLogRamsey.SpatialPublic

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Spatial_SpatialSourceCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.SpatialPublic
open Finset Real Filter SpatialLearning PreparedProjectiveGeometry
open scoped Classical BigOperators Topology NNReal
noncomputable section
local instance flat_JoinedSpatialSourceCover_1 (q : ℕ) [Fact q.Prime] : Fintype (Projectivization (ZMod q) (Fin 4 → ZMod q)) :=
  Fintype.ofFinite _
local instance flat_JoinedSpatialSourceCover_2 (q : ℕ) [Fact q.Prime] :
    Fintype (Projectivization (ZMod q) (Module.Dual (ZMod q) (Fin 4 → ZMod q))) := by
  letI : Finite (Module.Dual (ZMod q) (Fin 4 → ZMod q)) := Module.finite_of_finite (ZMod q)
  exact Fintype.ofFinite _

end
end SharpLogRamsey.SpatialPublic

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Spatial_SpatialCostsActual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.SpatialPublic
open Finset Real
open scoped Classical BigOperators
noncomputable section
local instance flat_JoinedSpatialCostsActual_1 (q : ℕ) [Fact q.Prime] : Fintype (Projectivization (ZMod q) (Fin 4 → ZMod q)) := Fintype.ofFinite _
local instance flat_JoinedSpatialCostsActual_2 (q : ℕ) [Fact q.Prime] : Finite (Module.Dual (ZMod q) (Fin 4 → ZMod q)) := Module.finite_of_finite (ZMod q)
local instance flat_JoinedSpatialCostsActual_3 (q : ℕ) [Fact q.Prime] : Fintype (Projectivization (ZMod q) (Module.Dual (ZMod q) (Fin 4 → ZMod q))) := Fintype.ofFinite _

end
end SharpLogRamsey.SpatialPublic

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Trees_TreeDecoder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.TreeDecoder
open BinaryTree List
open scoped Classical
noncomputable section
variable {A B I C : Type*}

def population (targets : I → List (A×B)) : BinaryTree I → List (A×B)
  | .nil => []
  | .node i l r => population targets l ++ targets i ++ population targets r

end
end SharpLogRamsey.TreeDecoder

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Trees_TreePotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.TreePotential
open BinaryTree
variable {α : Type*}

def total (f : α → ℝ) : BinaryTree α → ℝ
  | .nil => 0
  | .node a l r => f a + total f l + total f r

def root (f : α → ℝ) : BinaryTree α → ℝ
  | .nil => 0
  | .node a _ _ => f a

def Admissible (f : α → ℝ) (K : ℝ) : BinaryTree α → Prop
  | .nil => True
  | .node a l r => 0≤f a ∧ root f l+root f r≤f a+K ∧
    Admissible f K l ∧ Admissible f K r

end SharpLogRamsey.TreePotential

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Exposure_ExposureModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical BigOperators
noncomputable section

variable {β C ι : Type} [Fintype β] [Fintype C] [Fintype ι] [DecidableEq ι]

def pasteTuple (S : Finset ι) (z : S→β) (x : (Sᶜ:Finset ι)→β) : ι→β :=
  fun i=>if h : i∈S then z ⟨i,h⟩ else x ⟨i,mem_compl.mpr h⟩

omit [Fintype β] in
lemma pasteTuple_compl (S : Finset ι) (z : S→β) (x : (Sᶜ:Finset ι)→β) (i : (Sᶜ:Finset ι)) :
    pasteTuple S z x i=x i := by simp [pasteTuple,mem_compl.mp i.property]

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Trees_TreeShapes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.TreeShapes
open BinaryTree Finset
open scoped Classical

def bits : BinaryTree Unit→List Bool
  | .nil => [false]
  | .node _ l r => true::(bits l++bits r)

lemma bits_length (t : BinaryTree Unit) : (bits t).length=2*t.numNodes+1 := by
  induction t with
  | nil => simp [bits]
  | node _ l r hl hr => simp only [bits,List.length_cons,List.length_append,numNodes,hl,hr]; omega

noncomputable def boundedEncode (N : ℕ) (S : Finset (BinaryTree Unit))
    (hS : ∀ t∈S,t.numNodes≤N) (t : S) : List.Vector Bool (2*N+1) :=
  ⟨bits t.val++List.replicate (2*N+1-(bits t.val).length) false,by
    have ht := hS t.val t.property
    simp only [List.length_append,List.length_replicate,bits_length]
    omega⟩

end SharpLogRamsey.TreeShapes

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Entropy_TreeMessageEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.TreeCodeEntropy
open Finset Real BinaryTree TreeDecoder
open scoped Classical
noncomputable section
variable {A B C Γ : Type*} [Fintype Γ]

def shape (t : BinaryTree C) : BinaryTree Unit := t.map (fun _=>())

end
end SharpLogRamsey.TreeCodeEntropy

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Windows_WindowDeletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset
open scoped Classical BigOperators
noncomputable section
variable {W ι X : Type*} [Fintype W] [Fintype ι] [Fintype X]

def badWindows (e : W×Bool↪ι) (bad : Finset ι) : Finset W :=
  univ.filter (fun i=>e (i,false)∈bad ∨ e (i,true)∈bad)

def goodTargets (target : W×X↪ι) (keep : Finset W) (bad : Finset ι) : Finset ι :=
  ((keep×ˢ(univ:Finset X)).map target)\bad

end
end SharpLogRamsey.Selection.Windows

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Windows_WindowLayout
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset
open scoped Classical BigOperators
noncomputable section

abbrev Slot (w n : ℕ) := Fin w × Fin (4*n)
abbrev Block (w : ℕ) := Fin w × Bool

def quarter (n : ℕ) (b : Bool) (x : Fin n) : Fin (4*n) :=
  if b then ⟨3*n+x.val,by omega⟩ else ⟨x.val,by omega⟩

lemma quarter_injective (n : ℕ) : Function.Injective (fun bx : Bool×Fin n=>quarter n bx.1 bx.2) := by
  rintro ⟨b,x⟩ ⟨c,y⟩ h
  have hv : (quarter n b x).val = (quarter n c y).val := congrArg Fin.val h
  cases b <;> cases c <;> simp only [quarter,Bool.false_eq_true,↓reduceIte] at hv
  · have hh : x = y := Fin.ext hv
    cases hh
    rfl
  · omega
  · omega
  · have hh : x = y := Fin.ext (by omega)
    cases hh
    rfl

def embedding (w n : ℕ) : Block w × Fin n ↪ Slot w n where
  toFun bx := (bx.1.1,quarter n bx.1.2 bx.2)
  inj' := by
    rintro ⟨⟨i,b⟩,x⟩ ⟨⟨j,c⟩,y⟩ h
    have hi : i = j := congrArg Prod.fst h
    have hb : (b,x) = (c,y) := quarter_injective n (congrArg Prod.snd h)
    cases hi
    cases hb
    rfl

def owner (w n : ℕ) (i : Slot w n) : Option (Block w) :=
  if i.2.val < n then some (i.1,false) else
    if 3*n ≤ i.2.val then some (i.1,true) else none

def middle (w n : ℕ) : Fin w × Fin (2*n) ↪ Slot w n where
  toFun ix := (ix.1,⟨n+ix.2.val,by omega⟩)
  inj' := by
    rintro ⟨i,x⟩ ⟨j,y⟩ h
    have hi : i = j := congrArg Prod.fst h
    have hx : n+x.val = n+y.val := congrArg (fun z:Slot w n=>z.2.val) h
    have hxy : x = y := Fin.ext (by omega)
    exact Prod.ext hi hxy

lemma middle_unowned (w n : ℕ) (i : Fin w) (x : Fin (2*n)) :
    owner w n (middle w n (i,x))=none := by
  change (if n+x.val < n then some (i,false) else
    if 3*n ≤ n+x.val then some (i,true) else none) = none
  rw [ite_eq_right (by omega),ite_eq_right (by omega)]

def position {w n : ℕ} (x : Slot w n) : ℕ := x.1.val*(4*n)+x.2.val

end
end SharpLogRamsey.Selection.Windows

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Windows_PreparedWindows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset
open scoped Classical BigOperators
noncomputable section
variable {Ω Θ β : Type} [Fintype Ω] [Fintype Θ] [Fintype β]

variable (w n k : ℕ)
  (θ : Ω→Θ)
  (G : Ω→Slot w (n+k)→β)
  (t : Fin k)

local instance flat_ActualPreparedWindows_1 : DecidableEq (Block w) := Classical.decEq _

end
end SharpLogRamsey.Selection.Windows

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Windows_GoodPopulation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace SharpLogRamsey.Selection.Windows
open Finset TreeDecoder BinaryTree
open scoped Classical BigOperators
noncomputable section
variable {Ω Θ β : Type} [Fintype Ω] [Fintype Θ] [Fintype β]
variable (w n k : ℕ)
  (θ : Ω→Θ)
  (G : Ω→Slot w (n+k)→β)
  (t : Fin k)
local instance finDecC (j : ℕ) : DecidableEq (Fin j) := Classical.decEq _

end
end SharpLogRamsey.Selection.Windows

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_GoodRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace SharpLogRamsey.Selection.Windows
open Finset Real TreeDecoder BinaryTree
open scoped Classical BigOperators
noncomputable section
variable {K V Ω Θ : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]
  [Fintype Ω] [Fintype Θ] {d : ℕ} {b τ P H : ℝ}
local instance goodDec (j : ℕ) : DecidableEq (Fin j) := Classical.decEq _
variable (w n k : ℕ)
  (θ : Ω→Θ)
  (G : Ω→Slot w (n+k)→Projectivization K (Module.Dual K V)×Projectivization K V)
  (t : Fin k)
local instance goodBlockDec : DecidableEq (Block w) := Classical.decEq _

end
end SharpLogRamsey.Selection.Windows

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Exposure_StreamTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace SharpLogRamsey.Selection.Windows
open Finset
open scoped Classical
noncomputable section
variable {α Ω : Type} [Fintype α] [Fintype Ω]

def singleTuple {n : ℕ} (F : Fin (4*n)→α) : Slot 1 n→α := fun i=>F i.2

end
end SharpLogRamsey.Selection.Windows

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_TrackedSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset Real
open scoped Classical BigOperators
noncomputable section
variable {α β Ω : Type} [Fintype α] [Fintype β] [Fintype Ω]

def reverseTuple {n : ℕ} (f : Fin n→α) : Fin n→α:=fun i=>f i.rev

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Exposure_RestrictionBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset Real
open scoped Classical BigOperators
noncomputable section
variable {Ω Θ α : Type} [Fintype Ω] [Fintype Θ] [Fintype α]
local instance restrictionFinDec (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Exposure_RestrictionGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical BigOperators
noncomputable section

variable {Ω Θ α : Type} [Fintype Ω] [Fintype Θ] [Fintype α]

def prefixSet {N m : ℕ} (hm : m≤N) : Finset (Fin N) :=
  univ.image (Fin.castLE hm)

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_HighRankClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Marking
open Finset Real
open scoped Classical BigOperators
noncomputable section

variable {K : Type} [Field K] [Fintype K] {d : ℕ}
local instance flat_ActualHighRankClass_1 : Finite (Module.Dual K (Fin (d+1)→K)) :=
  Finite.of_injective ((↑) : Module.Dual K (Fin (d+1)→K)→((Fin (d+1)→K)→K)) DFunLike.coe_injective
local instance flat_ActualHighRankClass_3 : Fintype (Projectivization K (Fin (d+1)→K)) := Fintype.ofFinite _
local instance flat_ActualHighRankClass_2_r9c519d_1 : Finite (Module.Dual K (Module.Dual K (Fin (d+1)→K))) :=
  Finite.of_injective ((↑) : Module.Dual K (Module.Dual K (Fin (d+1)→K))→(Module.Dual K (Fin (d+1)→K)→K)) DFunLike.coe_injective
local instance flat_ActualHighRankClass_4 : Fintype (Projectivization K (Module.Dual K (Fin (d+1)→K))) := Fintype.ofFinite _

end
end SharpLogRamsey.Marking

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_HighRankPrepared
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset Real Filter
open scoped Classical BigOperators Topology
noncomputable section
local instance flat_ActualHighRankPrepared_1 (w : ℕ) : DecidableEq (Block w) := Classical.decEq _

local instance flat_ActualHighRankPrepared_2 {K : Type} [Field K] [Fintype K] {d : ℕ} : Finite (Module.Dual K (Fin (d+1)→K)) :=
  Finite.of_injective ((↑) : Module.Dual K (Fin (d+1)→K)→((Fin (d+1)→K)→K)) DFunLike.coe_injective
local instance flat_ActualHighRankPrepared_3 {K : Type} [Field K] [Fintype K] {d : ℕ} : Fintype (Projectivization K (Fin (d+1)→K)) := Fintype.ofFinite _
local instance flat_ActualHighRankPrepared_4 {K : Type} [Field K] [Fintype K] {d : ℕ} : Fintype (Projectivization K (Module.Dual K (Fin (d+1)→K))) := Fintype.ofFinite _

end
end SharpLogRamsey.Selection.Windows

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_HighGoodHistory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset Real
open scoped Classical BigOperators
noncomputable section
local instance flat_ActualHighGoodHistory_1 (w : ℕ) : DecidableEq (Block w) := Classical.decEq _
end
end SharpLogRamsey.Selection.Windows

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_HighRankStream
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset Real Filter
open scoped Classical BigOperators Topology
noncomputable section
local instance flat_ActualHighRankStream_1 (w : ℕ) : DecidableEq (Block w) := Classical.decEq _
local instance flat_ActualHighRankStream_2 {K : Type} [Field K] [Fintype K] {d : ℕ} : Finite (Module.Dual K (Fin (d+1)→K)) :=
  Finite.of_injective ((↑) : Module.Dual K (Fin (d+1)→K)→((Fin (d+1)→K)→K)) DFunLike.coe_injective
local instance flat_ActualHighRankStream_3 {K : Type} [Field K] [Fintype K] {d : ℕ} : Fintype (Projectivization K (Fin (d+1)→K)) := Fintype.ofFinite _
local instance flat_ActualHighRankStream_4 {K : Type} [Field K] [Fintype K] {d : ℕ} : Fintype (Projectivization K (Module.Dual K (Fin (d+1)→K))) := Fintype.ofFinite _

end
end SharpLogRamsey.Selection.Windows

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_HighRankExperiment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset Real Filter
open scoped Classical BigOperators Topology
noncomputable section
local instance flat_ActualHighRankExperiment_1_r9c519d_1 (w : ℕ) : DecidableEq (Block w) := Classical.decEq _
local instance flat_ActualHighRankExperiment_2 {K : Type} [Field K] [Fintype K] {d : ℕ} : Finite (Module.Dual K (Fin (d+1)→K)) :=
  Finite.of_injective ((↑) : Module.Dual K (Fin (d+1)→K)→((Fin (d+1)→K)→K)) DFunLike.coe_injective
local instance flat_ActualHighRankExperiment_3 {K : Type} [Field K] [Fintype K] {d : ℕ} : Fintype (Projectivization K (Fin (d+1)→K)) := Fintype.ofFinite _
local instance flat_ActualHighRankExperiment_4 {K : Type} [Field K] [Fintype K] {d : ℕ} : Fintype (Projectivization K (Module.Dual K (Fin (d+1)→K))) := Fintype.ofFinite _

end
end SharpLogRamsey.Selection.Windows

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_HighRankOrdered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Marking
open Finset Real Filter Selection Selection.Windows
open scoped Classical BigOperators Topology
noncomputable section
local instance flat_ActualHighRankOrdered_1 {K : Type} [Field K] [Fintype K] {d : ℕ} : Finite (Module.Dual K (Fin (d+1)→K)) :=
  Finite.of_injective ((↑) : Module.Dual K (Fin (d+1)→K)→((Fin (d+1)→K)→K)) DFunLike.coe_injective
local instance flat_ActualHighRankOrdered_3 {K : Type} [Field K] [Fintype K] {d : ℕ} : Fintype (Projectivization K (Fin (d+1)→K)) := Fintype.ofFinite _
local instance flat_ActualHighRankOrdered_2_r9c519d_1 {K : Type} [Field K] [Fintype K] {d : ℕ} : Finite (Module.Dual K (Module.Dual K (Fin (d+1)→K))) :=
  Finite.of_injective ((↑) : Module.Dual K (Module.Dual K (Fin (d+1)→K))→(Module.Dual K (Fin (d+1)→K)→K)) DFunLike.coe_injective
local instance flat_ActualHighRankOrdered_4 {K : Type} [Field K] [Fintype K] {d : ℕ} : Fintype (Projectivization K (Module.Dual K (Fin (d+1)→K))) := Fintype.ofFinite _
end
end SharpLogRamsey.Marking

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_HighRankStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Marking
open Finset Real Filter Selection Selection.Windows
open scoped Classical BigOperators Topology
noncomputable section
local instance flat_ActualHighRankStep_1 {K : Type} [Field K] [Fintype K] {d : ℕ} : Finite (Module.Dual K (Fin (d+1)→K)) :=
  Finite.of_injective ((↑) : Module.Dual K (Fin (d+1)→K)→((Fin (d+1)→K)→K)) DFunLike.coe_injective
local instance flat_ActualHighRankStep_3 {K : Type} [Field K] [Fintype K] {d : ℕ} : Fintype (Projectivization K (Fin (d+1)→K)) := Fintype.ofFinite _
local instance flat_ActualHighRankStep_2_r9c519d_1 {K : Type} [Field K] [Fintype K] {d : ℕ} : Finite (Module.Dual K (Module.Dual K (Fin (d+1)→K))) :=
  Finite.of_injective ((↑) : Module.Dual K (Module.Dual K (Fin (d+1)→K))→(Module.Dual K (Fin (d+1)→K)→K)) DFunLike.coe_injective
local instance flat_ActualHighRankStep_4 {K : Type} [Field K] [Fintype K] {d : ℕ} : Fintype (Projectivization K (Module.Dual K (Fin (d+1)→K))) := Fintype.ofFinite _
end
end SharpLogRamsey.Marking

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Selection_PredeletionMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset
open scoped Classical BigOperators
noncomputable section
variable {Ω Θ β : Type} [Fintype Ω] [Fintype Θ] [Fintype β]
variable (w n k : ℕ)
  (θ : Ω→Θ)
  (G : Ω→Slot w (n+k)→β)
  (t : Fin k)
local instance preFinDec (j : ℕ) : DecidableEq (Fin j) := Classical.decEq _
local instance preBlockDec : DecidableEq (Block w) := Classical.decEq _

end
end SharpLogRamsey.Selection.Windows

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Exposure_PreparedMixture
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset
open scoped Classical BigOperators
noncomputable section
variable {K V Ω Θ : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype Ω] [Fintype Θ] {d : ℕ} {b : ℝ}
variable (w n k : ℕ)
  (θ : Ω→Θ)
  (G : Ω→Slot w (n+k)→Projectivization K (Module.Dual K V)×Projectivization K V)
  (t : Fin k)
local instance mixBlockDec : DecidableEq (Block w) := Classical.decEq _
end
end SharpLogRamsey.Selection.Windows

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Windows_PopulationSublist
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset TreeDecoder BinaryTree
open scoped Classical BigOperators
noncomputable section

def flattenTuple {β : Type*} {w n : ℕ} (F : Slot w n→β) : Fin (w*(4*n))→β :=
  fun i=>F (finProdFinEquiv.symm i)

end
end SharpLogRamsey.Selection.Windows

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Execution_PreparedOutput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset Real TreeDecoder BinaryTree
open scoped Classical BigOperators
noncomputable section
variable {K V Ω Θ : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]
  [Fintype Ω] [Fintype Θ] {d : ℕ} {b τ P H : ℝ}
local instance prepOutFinDec (j : ℕ) : DecidableEq (Fin j) := Classical.decEq _
end
end SharpLogRamsey.Selection.Windows

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Windows_IntegerRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset Real TreeDecoder BinaryTree ReciprocalBands
open scoped Classical BigOperators
noncomputable section
variable {K V Ω Θ : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]
  [Fintype Ω] [Fintype Θ] {d : ℕ} {b τ P H : ℝ}
local instance intDec (j : ℕ) : DecidableEq (Fin j) := Classical.decEq _
variable (w n k : ℕ)
  (θ : Ω→Θ)
  (G : Ω→Slot w (n+k)→Projectivization K (Module.Dual K V)×Projectivization K V)
  (t : Fin k)
local instance intBlockDec : DecidableEq (Block w) := Classical.decEq _
end
end SharpLogRamsey.Selection.Windows

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Windows_UniformInteger
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset Real Filter TreeDecoder BinaryTree ReciprocalBands
open scoped Classical BigOperators Topology
noncomputable section
local instance uniformIntFinDec (j : ℕ) : DecidableEq (Fin j) := Classical.decEq _
local instance uniformIntBlockDec (w : ℕ) : DecidableEq (Block w) := Classical.decEq _

end
end SharpLogRamsey.Selection.Windows

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Windows_IntegerExperiment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset Real Filter TreeDecoder BinaryTree ReciprocalBands
open scoped Classical BigOperators Topology
noncomputable section
variable {K V Ω Θ : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]
  [Fintype Ω] [Fintype Θ] {d : ℕ} {b τ P H : ℝ}
local instance experimentFinDec (j : ℕ) : DecidableEq (Fin j) := Classical.decEq _
local instance experimentSlotDec (w L : ℕ) : DecidableEq (Slot w L) :=
  @instDecidableEqProd (Fin w) (Fin (4*L)) (@instDecidableEqFin w) (@instDecidableEqFin (4*L))
local instance experimentBlockDec (w : ℕ) : DecidableEq (Block w) := Classical.decEq _
end
end SharpLogRamsey.Selection.Windows

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Windows_IntegerQuarter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset Real Filter TreeDecoder BinaryTree ReciprocalBands
open scoped Classical BigOperators Topology
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] {b : ℝ}
local instance quarterFinDec (j : ℕ) : DecidableEq (Fin j) := Classical.decEq _
local instance quarterSlotDec (w L : ℕ) : DecidableEq (Slot w L) :=
  @instDecidableEqProd (Fin w) (Fin (4*L)) (@instDecidableEqFin w) (@instDecidableEqFin (4*L))
end
end SharpLogRamsey.Selection.Windows

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Windows_IntegerOutput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset Real Filter TreeDecoder BinaryTree ReciprocalBands
open scoped Classical BigOperators Topology
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] {b : ℝ}
local instance outputFinDec_r9c519d_1 (j : ℕ) : DecidableEq (Fin j) := Classical.decEq _
local instance outputSlotDec (w L : ℕ) : DecidableEq (Slot w L) :=
  @instDecidableEqProd (Fin w) (Fin (4*L)) (@instDecidableEqFin w) (@instDecidableEqFin (4*L))
end
end SharpLogRamsey.Selection.Windows

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Selection_FilteredPredeletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset
open scoped Classical BigOperators
noncomputable section
variable {Ω Θ β : Type} [Fintype Ω] [Fintype Θ] [Fintype β]
variable (w n k : ℕ)
  (θ : Ω→Θ)
  (G : Ω→Slot w (n+k)→β)
  (t : Fin k)
local instance filtFinDec (j : ℕ) : DecidableEq (Fin j) := Classical.decEq _
local instance filtBlockDec : DecidableEq (Block w) := Classical.decEq _

end
end SharpLogRamsey.Selection.Windows

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Windows_OpenMovement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset Real ReciprocalBands
open scoped Classical BigOperators
noncomputable section
variable {K V Ω Θ : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype Ω] [Fintype Θ] {d : ℕ}
local instance moveDec (j : ℕ) : DecidableEq (Fin j) := Classical.decEq _
variable (w n k : ℕ)
  (θ : Ω→Θ)
  (G : Ω→Slot w (n+k)→Projectivization K (Module.Dual K V)×Projectivization K V)
  (t : Fin k)
local instance moveBlockDec : DecidableEq (Block w) := Classical.decEq _
end
end SharpLogRamsey.Selection.Windows

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Windows_UniformMovement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset Real Filter ReciprocalBands
open scoped Classical BigOperators Topology
noncomputable section
local instance movementFinDec (j : ℕ) : DecidableEq (Fin j) := Classical.decEq _
local instance movementBlockDec (w : ℕ) : DecidableEq (Block w) := Classical.decEq _

end
end SharpLogRamsey.Selection.Windows

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Windows_OpenRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset Real TreeDecoder BinaryTree ReciprocalBands
open scoped Classical BigOperators
noncomputable section
variable {K V Ω Θ : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]
  [Fintype Ω] [Fintype Θ] {d : ℕ} {b τ P H : ℝ}
local instance openDec (j : ℕ) : DecidableEq (Fin j) := Classical.decEq _
variable (w n k : ℕ)
  (θ : Ω→Θ)
  (G : Ω→Slot w (n+k)→Projectivization K (Module.Dual K V)×Projectivization K V)
  (t : Fin k)
local instance openBlockDec : DecidableEq (Block w) := Classical.decEq _
end
end SharpLogRamsey.Selection.Windows

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Windows_UniformOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset Real Filter TreeDecoder BinaryTree ReciprocalBands
open scoped Classical BigOperators Topology
noncomputable section
local instance uniformIntOpenFinDec (j : ℕ) : DecidableEq (Fin j) := Classical.decEq _
local instance uniformIntOpenBlockDec (w : ℕ) : DecidableEq (Block w) := Classical.decEq _

end
end SharpLogRamsey.Selection.Windows

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Windows_OpenExperiment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset Real Filter TreeDecoder BinaryTree ReciprocalBands
open scoped Classical BigOperators Topology
noncomputable section
variable {K V Ω Θ : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]
  [Fintype Ω] [Fintype Θ] {d : ℕ} {b τ P H : ℝ}
local instance openExpFinDec (j : ℕ) : DecidableEq (Fin j) := Classical.decEq _
local instance openExpSlotDec (w L : ℕ) : DecidableEq (Slot w L) :=
  @instDecidableEqProd (Fin w) (Fin (4*L)) (@instDecidableEqFin w) (@instDecidableEqFin (4*L))
local instance openExpBlockDec (w : ℕ) : DecidableEq (Block w) := Classical.decEq _
end
end SharpLogRamsey.Selection.Windows

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Windows_OpenQuarter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset Real Filter TreeDecoder BinaryTree ReciprocalBands
open scoped Classical BigOperators Topology
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] {b : ℝ}
local instance openQuarterFinDec (j : ℕ) : DecidableEq (Fin j) := Classical.decEq _
local instance openQuarterSlotDec (w L : ℕ) : DecidableEq (Slot w L) :=
  @instDecidableEqProd (Fin w) (Fin (4*L)) (@instDecidableEqFin w) (@instDecidableEqFin (4*L))
end
end SharpLogRamsey.Selection.Windows

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Windows_OpenOutput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset Real Filter TreeDecoder BinaryTree ReciprocalBands
open scoped Classical BigOperators Topology
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] {b : ℝ}
local instance openOutputFinDec_r9c519d_1 (j : ℕ) : DecidableEq (Fin j) := Classical.decEq _
local instance openOutputSlotDec (w L : ℕ) : DecidableEq (Slot w L) :=
  @instDecidableEqProd (Fin w) (Fin (4*L)) (@instDecidableEqFin w) (@instDecidableEqFin (4*L))
end
end SharpLogRamsey.Selection.Windows

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Windows_WindowTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset
open scoped Classical BigOperators
noncomputable section
variable {α Ω Θ : Type} [Fintype Ω] [Fintype Θ] [Fintype α]

def windowTuple {w n : ℕ} (F : Fin (w*(4*n))→α) : Slot w n→α :=
  fun i=>F (finProdFinEquiv i)

end
end SharpLogRamsey.Selection.Windows

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_ClassStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Marking
open Finset Real Filter Selection Selection.Windows
open scoped Classical BigOperators Topology
noncomputable section
local instance stepFiniteDual {K : Type} [Field K] [Fintype K] {d : ℕ} : Finite (Module.Dual K (Fin (d+1)→K)) :=
  Finite.of_injective ((↑) : Module.Dual K (Fin (d+1)→K)→((Fin (d+1)→K)→K)) DFunLike.coe_injective
local instance stepFiniteDouble {K : Type} [Field K] [Fintype K] {d : ℕ} : Finite (Module.Dual K (Module.Dual K (Fin (d+1)→K))) :=
  Finite.of_injective ((↑) : Module.Dual K (Module.Dual K (Fin (d+1)→K))→(Module.Dual K (Fin (d+1)→K)→K)) DFunLike.coe_injective
local instance stepProjective {K : Type} [Field K] [Fintype K] {d : ℕ} : Fintype (Projectivization K (Fin (d+1)→K)) := Fintype.ofFinite _
local instance stepDualProjective {K : Type} [Field K] [Fintype K] {d : ℕ} : Fintype (Projectivization K (Module.Dual K (Fin (d+1)→K))) := Fintype.ofFinite _
local instance stepDoubleProjective {K : Type} [Field K] [Fintype K] {d : ℕ} : Fintype (Projectivization K (Module.Dual K (Module.Dual K (Fin (d+1)→K)))) := Fintype.ofFinite _

end
end SharpLogRamsey.Marking

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_SelectedStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Marking
open Finset Real Filter Selection Selection.Windows
open scoped Classical BigOperators Topology
noncomputable section
local instance selectFiniteDual {K : Type} [Field K] [Fintype K] {d : ℕ} : Finite (Module.Dual K (Fin (d+1)→K)) :=
  Finite.of_injective ((↑) : Module.Dual K (Fin (d+1)→K)→((Fin (d+1)→K)→K)) DFunLike.coe_injective
local instance selectFiniteDouble {K : Type} [Field K] [Fintype K] {d : ℕ} : Finite (Module.Dual K (Module.Dual K (Fin (d+1)→K))) :=
  Finite.of_injective ((↑) : Module.Dual K (Module.Dual K (Fin (d+1)→K))→(Module.Dual K (Fin (d+1)→K)→K)) DFunLike.coe_injective
local instance selectProjective {K : Type} [Field K] [Fintype K] {d : ℕ} : Fintype (Projectivization K (Fin (d+1)→K)) := Fintype.ofFinite _
local instance selectDualProjective {K : Type} [Field K] [Fintype K] {d : ℕ} : Fintype (Projectivization K (Module.Dual K (Fin (d+1)→K))) := Fintype.ofFinite _
local instance selectDoubleProjective {K : Type} [Field K] [Fintype K] {d : ℕ} : Fintype (Projectivization K (Module.Dual K (Module.Dual K (Fin (d+1)→K)))) := Fintype.ofFinite _

def classCount (i : ℕ) : ℕ:=2*(i+4)+(i+4)^2
end
end SharpLogRamsey.Marking

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_UniformStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Marking
open Finset Real Filter Selection Selection.Windows
open scoped Classical BigOperators Topology
noncomputable section
local instance uniformFiniteDual {K : Type} [Field K] [Fintype K] {d : ℕ} : Finite (Module.Dual K (Fin (d+1)→K)) :=
  Finite.of_injective ((↑) : Module.Dual K (Fin (d+1)→K)→((Fin (d+1)→K)→K)) DFunLike.coe_injective
local instance uniformProjective {K : Type} [Field K] [Fintype K] {d : ℕ} : Fintype (Projectivization K (Fin (d+1)→K)) := Fintype.ofFinite _
local instance uniformFiniteDouble_r9c519d_1 {K : Type} [Field K] [Fintype K] {d : ℕ} : Finite (Module.Dual K (Module.Dual K (Fin (d+1)→K))) :=
  Finite.of_injective ((↑) : Module.Dual K (Module.Dual K (Fin (d+1)→K))→(Module.Dual K (Fin (d+1)→K)→K)) DFunLike.coe_injective
local instance uniformDualProjective {K : Type} [Field K] [Fintype K] {d : ℕ} : Fintype (Projectivization K (Module.Dual K (Fin (d+1)→K))) := Fintype.ofFinite _
end
end SharpLogRamsey.Marking

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_TrackedStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Marking
open Finset Real Filter Selection Selection.Windows
open scoped Classical BigOperators Topology
noncomputable section
local instance trackFiniteDual {K : Type} [Field K] [Fintype K] {d : ℕ} : Finite (Module.Dual K (Fin (d+1)→K)) :=
  Finite.of_injective ((↑) : Module.Dual K (Fin (d+1)→K)→((Fin (d+1)→K)→K)) DFunLike.coe_injective
local instance trackProjective {K : Type} [Field K] [Fintype K] {d : ℕ} : Fintype (Projectivization K (Fin (d+1)→K)) := Fintype.ofFinite _
local instance trackFiniteDouble_r9c519d_1 {K : Type} [Field K] [Fintype K] {d : ℕ} : Finite (Module.Dual K (Module.Dual K (Fin (d+1)→K))) :=
  Finite.of_injective ((↑) : Module.Dual K (Module.Dual K (Fin (d+1)→K))→(Module.Dual K (Fin (d+1)→K)→K)) DFunLike.coe_injective
local instance trackDualProjective {K : Type} [Field K] [Fintype K] {d : ℕ} : Fintype (Projectivization K (Module.Dual K (Fin (d+1)→K))) := Fintype.ofFinite _
end
end SharpLogRamsey.Marking

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Parameters_FiniteIteration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Marking
open Finset Real Filter Selection Selection.Windows
open scoped Classical BigOperators Topology
noncomputable section
local instance finiteIterDual {K : Type} [Field K] [Fintype K] {d : ℕ} : Finite (Module.Dual K (Fin (d+1)→K)) :=
  Finite.of_injective ((↑) : Module.Dual K (Fin (d+1)→K)→((Fin (d+1)→K)→K)) DFunLike.coe_injective
local instance finiteIterProjective {K : Type} [Field K] [Fintype K] {d : ℕ} : Fintype (Projectivization K (Fin (d+1)→K)) := Fintype.ofFinite _
local instance finiteIterDouble_r9c519d_1 {K : Type} [Field K] [Fintype K] {d : ℕ} : Finite (Module.Dual K (Module.Dual K (Fin (d+1)→K))) :=
  Finite.of_injective ((↑) : Module.Dual K (Module.Dual K (Fin (d+1)→K))→(Module.Dual K (Fin (d+1)→K)→K)) DFunLike.coe_injective
local instance finiteIterDualProjective {K : Type} [Field K] [Fintype K] {d : ℕ} : Fintype (Projectivization K (Module.Dual K (Fin (d+1)→K))) := Fintype.ofFinite _
end
end SharpLogRamsey.Marking

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Entropy_TerminalEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Marking
open Finset Real Filter Selection Selection.Windows
open scoped Classical BigOperators Topology
noncomputable section
local instance terminalFiniteDual {K : Type} [Field K] [Fintype K] {d : ℕ} : Finite (Module.Dual K (Fin (d+1)→K)) :=
  Finite.of_injective ((↑) : Module.Dual K (Fin (d+1)→K)→((Fin (d+1)→K)→K)) DFunLike.coe_injective
local instance terminalProjective {K : Type} [Field K] [Fintype K] {d : ℕ} : Fintype (Projectivization K (Fin (d+1)→K)) := Fintype.ofFinite _
local instance terminalFiniteDouble_r9c519d_1 {K : Type} [Field K] [Fintype K] {d : ℕ} : Finite (Module.Dual K (Module.Dual K (Fin (d+1)→K))) :=
  Finite.of_injective ((↑) : Module.Dual K (Module.Dual K (Fin (d+1)→K))→(Module.Dual K (Fin (d+1)→K)→K)) DFunLike.coe_injective
local instance terminalDualProjective {K : Type} [Field K] [Fintype K] {d : ℕ} : Fintype (Projectivization K (Module.Dual K (Fin (d+1)→K))) := Fintype.ofFinite _
end
end SharpLogRamsey.Marking

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Parameters_TerminalGain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Marking
open Finset Real Filter Selection Selection.Windows
open scoped Classical BigOperators Topology
noncomputable section
local instance gainFiniteDual {K : Type} [Field K] [Fintype K] {d : ℕ} : Finite (Module.Dual K (Fin (d+1)→K)) :=
  Finite.of_injective ((↑) : Module.Dual K (Fin (d+1)→K)→((Fin (d+1)→K)→K)) DFunLike.coe_injective
local instance gainProjective {K : Type} [Field K] [Fintype K] {d : ℕ} : Fintype (Projectivization K (Fin (d+1)→K)) := Fintype.ofFinite _
local instance gainFiniteDouble_r9c519d_1 {K : Type} [Field K] [Fintype K] {d : ℕ} : Finite (Module.Dual K (Module.Dual K (Fin (d+1)→K))) :=
  Finite.of_injective ((↑) : Module.Dual K (Module.Dual K (Fin (d+1)→K))→(Module.Dual K (Fin (d+1)→K)→K)) DFunLike.coe_injective
local instance gainDualProjective {K : Type} [Field K] [Fintype K] {d : ℕ} : Fintype (Projectivization K (Module.Dual K (Fin (d+1)→K))) := Fintype.ofFinite _

end
end SharpLogRamsey.Marking

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Parameters_NoContext
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Marking
open Finset Real Filter Selection Selection.Windows
open scoped Classical BigOperators Topology
noncomputable section
local instance noCtxFiniteDual {K : Type} [Field K] [Fintype K] {d : ℕ} : Finite (Module.Dual K (Fin (d+1)→K)) :=
  Finite.of_injective ((↑) : Module.Dual K (Fin (d+1)→K)→((Fin (d+1)→K)→K)) DFunLike.coe_injective
local instance noCtxProjective {K : Type} [Field K] [Fintype K] {d : ℕ} : Fintype (Projectivization K (Fin (d+1)→K)) := Fintype.ofFinite _
local instance noCtxFiniteDouble_r9c519d_1 {K : Type} [Field K] [Fintype K] {d : ℕ} : Finite (Module.Dual K (Module.Dual K (Fin (d+1)→K))) :=
  Finite.of_injective ((↑) : Module.Dual K (Module.Dual K (Fin (d+1)→K))→(Module.Dual K (Fin (d+1)→K)→K)) DFunLike.coe_injective
local instance noCtxDualProjective {K : Type} [Field K] [Fintype K] {d : ℕ} : Fintype (Projectivization K (Module.Dual K (Fin (d+1)→K))) := Fintype.ofFinite _
end
end SharpLogRamsey.Marking

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Construction_GraphWitness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Marking
open Finset Real Filter Selection Selection.Windows
open scoped Classical BigOperators Topology
noncomputable section
local instance witnessFiniteDual {K : Type} [Field K] [Fintype K] {d : ℕ} : Finite (Module.Dual K (Fin (d+1)→K)) :=
  Finite.of_injective ((↑) : Module.Dual K (Fin (d+1)→K)→((Fin (d+1)→K)→K)) DFunLike.coe_injective
local instance witnessProjective {K : Type} [Field K] [Fintype K] {d : ℕ} : Fintype (Projectivization K (Fin (d+1)→K)) := Fintype.ofFinite _
local instance witnessFiniteDouble_r9c519d_1 {K : Type} [Field K] [Fintype K] {d : ℕ} : Finite (Module.Dual K (Module.Dual K (Fin (d+1)→K))) :=
  Finite.of_injective ((↑) : Module.Dual K (Module.Dual K (Fin (d+1)→K))→(Module.Dual K (Fin (d+1)→K)→K)) DFunLike.coe_injective
local instance witnessDualProjective {K : Type} [Field K] [Fintype K] {d : ℕ} : Fintype (Projectivization K (Module.Dual K (Fin (d+1)→K))) := Fintype.ofFinite _
end
end SharpLogRamsey.Marking

end

end OAI
end


