-- Prove2me | Definitions.Def_OAIE3v2B084
-- name    : OAIE3v2B084
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:26:22.307549+00:00
-- url     : https://prove2.me/theorems/cfdbbbb3-31f4-4b46-95eb-d9dc8e06c3d7
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 85 of 311
-- statement:
--   Definitions bundle 85 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B038`, `OAIE3v2B039`, `OAIE3v2B040`, `OAIE3v2B042`, `OAIE3v2B044`, `OAIE3v2B045`, `OAIE3v2B048`, `OAIE3v2B049`, `OAIE3v2B059`, `OAIE3v2B061`, `OAIE3v2B063`, `OAIE3v2B064`, `OAIE3v2B065`, `OAIE3v2B066` of this split.
--
--   Modules: `Dynamics/EarlyFiberCapBudget.lean`, `Dynamics/IdealSiteEnvelopeBudget.lean`, `Dynamics/ModeAmplitudeErrorBudget.lean`, `Dynamics/PreparedFiniteNestedSourceLatePowerBudget.lean`, `Estimates/AllocatedFullSiteRadius.lean`, `Estimates/CanonicalScalarSourceEnvelope.lean`, `Estimates/CommonStrideCorrelation.lean`, `Estimates/DenseProgressionInnerFamily.lean`, `Estimates/FiniteCommonStrideFamily.lean`, `Estimates/FiniteInnerProgressionFamily.lean`, `Estimates/JetAxisReference.lean`, `Estimates/LinearLiftSheetCompatibility.lean`, `Estimates/PreparedModularDetectorBadProduct.lean`, `Estimates/PreparedScalarStructuralBasePower.lean`, `Estimates/RectangularCellGeometry.lean`, `Estimates/RowRestrictedDeckSiteMask.lean`, `Fourier/CoefficientEvaluationTorus.lean`, `Fourier/SiteFourierHaarMean.lean`, `Geometry/CoefficientDeckCoordinates.lean`, `Geometry/CommonStrideCoordinates.lean`, `Geometry/IdealSiteBoxRadius.lean`, `Geometry/NormalizedCoordinateCutoff.lean`, `Geometry/PhysicalChartRadiusBudget.lean`, `Geometry/ScalarReferenceNativeDetectionCoordinateEquiv.lean`, `Geometry/SpatialNumericEnvelopeFunctoriality.lean`, `Geometry/SupportedCubeEquivTransport.lean`, `Lattices/AllocatedCoefficientIntegerMarginal.lean`, `Lattices/IntegerRowInterpolationMixture.lean`, `Lattices/JointAffineBooleanSource.lean`, `Lattices/NormalizedLatticeSheet.lean`, `Lattices/PartitionedAffineLogEnvelope.lean`, `Lattices/PhysicalSubboxResidueSlice.lean`, `Lattices/SelectedResidueApproximation.lean`, `Linear/BufferedCoordinateProjection.lean`, `Linear/SpatialMatrixBlockWideProbability.lean`, `Linear/SpatialMatrixCutoffBudget.lean`, `Polynomial/BooleanPolynomialLogBudget.lean`, `Polynomial/EmbeddedMatrixDeterminantPolynomial.lean`, `Polynomial/IntegerPolynomialActiveProfileSupport.lean`, `Polynomial/PreparedUniformDegreeDirectMasterBudget.lean`, `Probability/FiniteConditionedMass.lean`, `Probability/FiniteProbabilityLipschitz.lean`, `Probability/ScalarCubeDensityBudget.lean`, `Sampling/JointMeasureProductiveNarrowSampler.lean`, `Sampling/PreparedShortForecastRawSourceBounds.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B038
import Definitions.Def_OAIE3v2B039
import Definitions.Def_OAIE3v2B040
import Definitions.Def_OAIE3v2B042
import Definitions.Def_OAIE3v2B044
import Definitions.Def_OAIE3v2B045
import Definitions.Def_OAIE3v2B048
import Definitions.Def_OAIE3v2B049
import Definitions.Def_OAIE3v2B059
import Definitions.Def_OAIE3v2B061
import Definitions.Def_OAIE3v2B063
import Definitions.Def_OAIE3v2B064
import Definitions.Def_OAIE3v2B065
import Definitions.Def_OAIE3v2B066

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.FiniteProbabilityLipschitz
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {C Ω : Type*} [MeasurableSpace C] [Fintype Ω]
variable [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
variable (law : C → FiniteProbabilityWeights Ω)

theorem centeredFiniteWeightDensity_measurable
    (hweight : ∀ x, Measurable (fun c => (law c).weight x)) :
    Measurable (centeredFiniteWeightDensity law) :=
  measurable_from_prod_countable_left hweight

omit [MeasurableSpace C] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
theorem centeredFiniteWeightDensity_nonneg (z : C × Ω) :
    0 ≤ centeredFiniteWeightDensity law z := (law z.1).nonneg z.2

theorem centeredFiniteWeightDensity_integrable
    (hweight : ∀ x, Measurable (fun c => (law c).weight x))
    (μ : Measure C) [IsProbabilityMeasure μ] :
    Integrable (centeredFiniteWeightDensity law) (μ.prod Measure.count) := by
  apply (integrable_const (1 : ℝ)).mono'
    (centeredFiniteWeightDensity_measurable law hweight).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun z => by
    rw [Real.norm_of_nonneg (centeredFiniteWeightDensity_nonneg law z)]
    exact centeredFiniteWeightDensity_le_one law z)

theorem centeredFiniteWeightDensity_integral
    (hweight : ∀ x, Measurable (fun c => (law c).weight x))
    (μ : Measure C) [IsProbabilityMeasure μ] :
    (∫ z, centeredFiniteWeightDensity law z ∂μ.prod Measure.count) = 1 := by
  rw [integral_prod _ (centeredFiniteWeightDensity_integrable law hweight μ)]
  simp only [centeredFiniteWeightDensity, integral_count, (law _).total]
  simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.FiniteConditionedMass
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem finite_cell_event_probability_le {Ω X : Type*} [Fintype Ω] [MeasurableSpace X]
    (p : FiniteProbabilityWeights Ω) (E : Ω → Prop)
    (μ : Measure X) (C : Ω → Set X) (A : Set X) (M v : ℝ) (hM : 0 ≤ M)
    (hdis : Pairwise (fun a b => Disjoint (C a) (C b))) (hm : ∀ ω, MeasurableSet (C ω))
    (hfin : ∀ ω, μ (C ω) ≠ ⊤) (hv : ∀ ω, μ.real (C ω) = v)
    (hw : ∀ ω, p.weight ω ≤ M * v) (hsub : ∀ ω, E ω → C ω ⊆ A) (hA : μ A ≠ ⊤) :
    p.eventProbability E ≤ M * μ.real A := by
  classical
  let S := Finset.univ.filter E
  have hc : (S.card : ℝ) * v ≤ μ.real A := by
    have h := disjoint_cells_card_mul_le μ (fun ω : S => C ω.val) A v
      (fun a b hab => hdis (Subtype.coe_injective.ne hab))
      (fun ω => hm ω) (fun ω => hfin ω) (fun ω => hv ω)
      (fun ω => hsub ω (Finset.mem_filter.mp ω.property).2) hA
    simpa only [Fintype.card_coe] using h
  calc
    p.eventProbability E = ∑ ω ∈ S, p.weight ω := by
      simp only [FiniteProbabilityWeights.eventProbability, FiniteProbabilityWeights.mean,
        S, Finset.sum_filter, mul_ite, mul_one, mul_zero]
    _ ≤ ∑ _ω ∈ S, M * v := Finset.sum_le_sum (fun ω _ => hw ω)
    _ = M * ((S.card : ℝ) * v) := by simp [mul_left_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left hc hM

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SupportedCubeEquivTransport
namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {A : Type*} [AddCommGroup A]

variable [DecidableEq A]

omit [DecidableEq A] in
theorem card_supportedCube_le (j : ℕ) (Q : Finset A) :
    Nat.card (SupportedCube j (Q : Set A)) ≤ Q.card ^ (j + 1) := by
  have h := Nat.card_le_card_of_injective SupportedCube.points
    (SupportedCube.points_injective j (Q : Set A))
  simpa [Nat.card_eq_fintype_card, pow_succ, mul_comm] using h

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {A : Type*} [AddCommGroup A] [DecidableEq A]

def supportedCubeDerivativeEquiv (j : ℕ) (Q : Finset A) :
    SupportedCube (j + 1) (Q : Set A) ≃
      Σ h : cubeDifferenceSupport Q, SupportedCube j (derivativeSupport Q h.val : Set A) where
  toFun p := ⟨⟨p.val.1 0, p.first_mem_difference⟩, p.tail⟩
  invFun p := p.2.cons p.1.val
  left_inv p := by
    apply Subtype.ext
    change (Fin.cons (p.val.1 0) (Fin.tail p.val.1), p.val.2) = p.val
    rw [Fin.cons_self_tail]
  right_inv p := by
    rcases p with ⟨h, p⟩
    rfl

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

theorem card_supportedCube_pos (j : ℕ) {Q : Finset A} (hQ : Q.Nonempty) :
    0 < Nat.card (SupportedCube j (Q : Set A)) := by
  obtain ⟨a, ha⟩ := hQ
  let : Nonempty (SupportedCube j (Q : Set A)) :=
    ⟨⟨((fun _ ↦ 0), a), fun ω ↦ by simpa [cubeShift] using ha⟩⟩
  exact Nat.card_pos

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PhysicalSubboxResidueSlice
namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable (T : ι → ℕ) [∀ i, NeZero (T i)]

theorem small_box_card_pow_le_cubeCount (j : ℕ) :
    (integerBox (smallCubeSide T j)).card ^ (j + 1) ≤ integerBoxCubeCount T j := by
  have h := Nat.card_le_card_of_injective (smallBoxCubeMap T j) (smallBoxCubeMap_injective T j)
  change Nat.card ((Fin j → integerBox (smallCubeSide T j)) × integerBox (smallCubeSide T j)) ≤
    integerBoxCubeCount T j at h
  simpa only [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_coe, Fintype.card_fin, pow_succ] using h

theorem card_integerBox_le_small_box (j : ℕ) :
    (integerBox T).card ≤ (j + 1) ^ Fintype.card ι * (integerBox (smallCubeSide T j)).card := by
  have hi (i : ι) : T i ≤ (j + 1) * smallCubeSide T j i := by
    have h := Nat.lt_mul_div_succ (T i - 1) (Nat.succ_pos j)
    change T i - 1 < (j + 1) * ((T i - 1) / (j + 1) + 1) at h
    have hT := Nat.pos_of_ne_zero (NeZero.ne (T i))
    change T i ≤ (j + 1) * ((T i - 1) / (j + 1) + 1)
    omega
  calc
    _ = ∏ i, T i := card_integerBox T
    _ ≤ ∏ i, (j + 1) * smallCubeSide T j i :=
      Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _) (fun i _ ↦ hi i)
    _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const]; simp [card_integerBox]

theorem integerBoxCubeCount_lower (j : ℕ) :
    (integerBox T).card ^ (j + 1) ≤
      (j + 1) ^ (Fintype.card ι * (j + 1)) * integerBoxCubeCount T j := by
  have h := Nat.pow_le_pow_left (card_integerBox_le_small_box T j) (j + 1)
  rw [mul_pow, ← pow_mul] at h
  exact h.trans (Nat.mul_le_mul_left _ (small_box_card_pow_le_cubeCount T j))

omit [∀ i, NeZero (T i)] in
theorem integerBoxCubeCount_upper (j : ℕ) :
    integerBoxCubeCount T j ≤ (integerBox T).card ^ (j + 1) :=
  card_supportedCube_le j (integerBox T)

theorem integerBoxCubeCount_bounds (j : ℕ) :
    ((1 : ℝ) / ((j : ℝ) + 1) ^ (j + 1)) ^ Fintype.card ι *
        ((integerBox T).card : ℝ) ^ (j + 1) ≤ integerBoxCubeCount T j ∧
      (integerBoxCubeCount T j : ℝ) ≤ ((integerBox T).card : ℝ) ^ (j + 1) := by
  constructor
  · have h : ((integerBox T).card : ℝ) ^ (j + 1) ≤
        (((j + 1 : ℕ) : ℝ) ^ (Fintype.card ι * (j + 1))) * integerBoxCubeCount T j := by
      exact_mod_cast integerBoxCubeCount_lower T j
    have he : ((1 : ℝ) / ((j : ℝ) + 1) ^ (j + 1)) ^ Fintype.card ι *
        ((integerBox T).card : ℝ) ^ (j + 1) =
        ((integerBox T).card : ℝ) ^ (j + 1) /
          ((j : ℝ) + 1) ^ (Fintype.card ι * (j + 1)) := by
      rw [div_pow, one_pow, ← pow_mul, Nat.mul_comm (j + 1) (Fintype.card ι)]
      ring
    rw [he]
    apply (div_le_iff₀ (pow_pos (by positivity : 0 < (j : ℝ) + 1) _)).mpr
    simpa only [Nat.cast_add, Nat.cast_one, mul_comm] using h
  · exact_mod_cast integerBoxCubeCount_upper T j

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable (T : ι → ℕ) [∀ i, NeZero (T i)]

omit [∀ i, NeZero (T i)] in
theorem translatedIntegerBox_reflectsPairSums (a : ι → ℤ) :
    ReflectsPairSums (boxReduction T) (translatedIntegerBox a T : Set (ι → ℤ)) :=
  (boxReduction_reflectsPairSums T).translate a

theorem translatedIntegerBox_cubeCount_bounds (a : ι → ℤ) (j : ℕ) :
    ((1 : ℝ) / ((j : ℝ) + 1) ^ (j + 1)) ^ Fintype.card ι *
        ((translatedIntegerBox a T).card : ℝ) ^ (j + 1) ≤
          Nat.card (SupportedCube j (translatedIntegerBox a T : Set (ι → ℤ))) ∧
      (Nat.card (SupportedCube j (translatedIntegerBox a T : Set (ι → ℤ))) : ℝ) ≤
        ((translatedIntegerBox a T).card : ℝ) ^ (j + 1) := by
  simpa only [translatedIntegerBox, card_translateSupport, card_supportedCube_translate,
    integerBoxCubeCount] using integerBoxCubeCount_bounds T j

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RectangularCellGeometry
namespace OAI

section

namespace Erdos3

theorem rectangularLatticeCell_disjoint {I : Type*}
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) :
    Pairwise (fun k l => Disjoint (rectangularLatticeCell a S k) (rectangularLatticeCell a S l)) := by
  intro k l hkl
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact hkl (((rectangularLatticeCell_iff a S hS x k).mp hx).symm.trans
    ((rectangularLatticeCell_iff a S hS x l).mp hy))

theorem rectangularLatticeCell_point_distance {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (δ : ℝ) (hδ : 0 ≤ δ)
    (hmesh : ∀ i, 1 / S i ≤ δ) (k : I → ℤ) (x : I → ℝ)
    (hx : x ∈ rectangularLatticeCell a S k) :
    ‖x - rectangularLatticePoint a S k‖ ≤ δ := by
  have h := rectangularLatticeSample_error a S hS hδ hmesh x
  have hk := (rectangularLatticeCell_iff a S hS x k).mp hx
  rw [rectangularLatticeSample, hk, norm_sub_rev] at h
  exact h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.EmbeddedMatrixDeterminantPolynomial
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem shiftedPolynomial_grid_sublevel_transfer {Ω : Type*} [Fintype Ω] {N : ℕ}
    (p : FiniteProbabilityWeights Ω) (grid : Ω → Fin N → ℤ) (hinj : Function.Injective grid)
    (a S : Fin N → ℝ) (hS : ∀ i, 0 < S i)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ i, 1 / S i ≤ δ)
    (hgrid : ∀ ω i, |rectangularLatticePoint a S (grid ω) i| ≤ 1)
    (P : MvPolynomial (Fin N) ℝ) (M K u : ℝ) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hw : ∀ ω, p.weight ω ≤ M * (∏ i, S i)⁻¹)
    (hLip : ∀ x y : Fin N → ℝ, (∀ i, |x i| ≤ 2) → (∀ i, |y i| ≤ 2) →
      |MvPolynomial.eval x P - MvPolynomial.eval y P| ≤ K * ‖x - y‖) :
    p.eventProbability (fun ω => |MvPolynomial.eval (rectangularLatticePoint a S (grid ω)) P| ≤ u) ≤
      M * volume.real (boxMvPolynomialSublevel P 2 (u + K * δ)) := by
  let cell := fun ω => rectangularLatticeCell a S (grid ω)
  apply finite_cell_event_probability_le p _ volume cell _ M ((∏ i, S i)⁻¹) hM
    (fun v w hvw => rectangularLatticeCell_disjoint a S hS (hinj.ne hvw))
    (fun ω => rectangularLatticeCell_measurable _ _ _)
    (fun ω => rectangularLatticeCell_volume_ne_top _ _ _)
    (fun ω => rectangularLatticeCell_volume a S hS (grid ω)) hw _
    (boxMvPolynomialSublevel_volume_ne_top P (by norm_num) _)
  intro ω hω x hx
  have hd := rectangularLatticeCell_point_distance a S hS δ hδ hmesh (grid ω) x hx
  have hxb (i : Fin N) : |x i| ≤ 2 := by
    have hi0 : |x i - rectangularLatticePoint a S (grid ω) i| ≤
        ‖x - rectangularLatticePoint a S (grid ω)‖ := by
      simpa only [Pi.sub_apply, Real.norm_eq_abs] using
        norm_le_pi_norm (x - rectangularLatticePoint a S (grid ω)) i
    have hi := hi0.trans hd
    have ht := abs_add_le (x i - rectangularLatticePoint a S (grid ω) i)
      (rectangularLatticePoint a S (grid ω) i)
    rw [sub_add_cancel] at ht
    exact ht.trans (by linarith [hgrid ω i])
  have hyb (i : Fin N) : |rectangularLatticePoint a S (grid ω) i| ≤ 2 :=
    (hgrid ω i).trans (by norm_num)
  have he := (hLip x _ hxb hyb).trans (mul_le_mul_of_nonneg_left hd hK)
  refine ⟨hxb, ?_⟩
  have ha := abs_sub_abs_le_abs_sub (MvPolynomial.eval x P)
    (MvPolynomial.eval (rectangularLatticePoint a S (grid ω)) P)
  linarith

theorem shiftedPolynomial_grid_sublevel_bound_of_value {Ω : Type*} [Fintype Ω] {N d : ℕ}
    (hN : 0 < N) (hd : 0 < d)
    (p : FiniteProbabilityWeights Ω) (grid : Ω → Fin N → ℤ) (hinj : Function.Injective grid)
    (a S : Fin N → ℝ) (hS : ∀ i, 0 < S i)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ i, 1 / S i ≤ δ)
    (hgrid : ∀ ω i, |rectangularLatticePoint a S (grid ω) i| ≤ 1)
    (P : MvPolynomial (Fin N) ℝ) (hdeg : ∀ i, P.degreeOf i ≤ d)
    (M K u : ℝ) (hM : 0 ≤ M) (hK : 0 ≤ K) (hu : 0 < u)
    (hw : ∀ ω, p.weight ω ≤ M * (∏ i, S i)⁻¹)
    (hLip : ∀ x y : Fin N → ℝ, (∀ i, |x i| ≤ 2) → (∀ i, |y i| ≤ 2) →
      |MvPolynomial.eval x P - MvPolynomial.eval y P| ≤ K * ‖x - y‖)
    (x₀ : Fin N → ℝ) (hx₀ : ∀ i, |x₀ i| ≤ 1) (hval : 1 ≤ |MvPolynomial.eval x₀ P|) :
    p.eventProbability (fun ω => |MvPolynomial.eval (rectangularLatticePoint a S (grid ω)) P| ≤ u) ≤
      M * (2 ^ N * multivariateSublevelConstant N d *
        ((u + K * δ) * (d + 1 : ℝ) ^ N) ^ (((N * d : ℕ) : ℝ)⁻¹)) := by
  apply (shiftedPolynomial_grid_sublevel_transfer p grid hinj a S hS hδ hδ1 hmesh hgrid
    P M K u hM hK hw hLip).trans
  apply mul_le_mul_of_nonneg_left _ hM
  obtain ⟨t, ht⟩ := exists_coefficient_of_unit_box_value P hdeg x₀ hx₀ zero_lt_one hval
  have h := polynomial_sublevel_box_bound hN hd P hdeg (by norm_num : (1 : ℝ) ≤ 2)
    (add_pos_of_pos_of_nonneg hu (mul_nonneg hK hδ))
    (by positivity : (0 : ℝ) < 1 / (d + 1 : ℝ) ^ N) t ht
  simpa only [div_div_eq_mul_div, div_one] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ScalarCubeDensityBudget
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem scalarCubeInnerBox_subset (I : Type*) [Fintype I] [DecidableEq I] :
    scalarCubeInnerBox I ⊆ scalarCubeDomain I := by
  intro x hx t
  have hr : 0 ≤ 1/(4*((Fintype.card I : ℝ)+1)) := by positivity
  have hn : ‖x-scalarCubeCenter I‖ ≤ 1/(4*((Fintype.card I : ℝ)+1)) := by
    apply (pi_norm_le_iff_of_nonneg hr).mpr
    intro i
    change |x i-scalarCubeCenter I i| ≤ _
    exact abs_le.mpr ⟨by linarith [hx.1 i], by linarith [hx.2 i]⟩
  have hb := scalarCubeValue_sub_bound x (scalarCubeCenter I) hr hn t
  rw [scalarCubeValue_center] at hb
  have he : ((Fintype.card I : ℝ)+1)*(1/(4*((Fintype.card I : ℝ)+1))) = 1/4 := by
    field_simp
  rw [he] at hb
  have ha := abs_le.mp hb
  exact ⟨by linarith [ha.1], by linarith [ha.2]⟩

theorem scalarCubeDomainDensity_le_power (I : Type*) [Fintype I] [DecidableEq I] :
    scalarCubeDomainDensity I ≤ (2*((Fintype.card I : ℝ)+1))^(Fintype.card I+1) := by
  have hv := measureReal_mono (scalarCubeInnerBox_subset I) (scalarCubeDomain_volume_lt_top I).ne
  rw [scalarCubeInnerBox_volume] at hv
  have hp : 0 < (1/(2*((Fintype.card I : ℝ)+1)))^(Fintype.card I+1) := by positivity
  have hi := one_div_le_one_div_of_le hp hv
  simpa only [scalarCubeDomainDensity, one_div, inv_pow, inv_inv] using hi

theorem scalarCubeDomainDensity_le_exp (I : Type*) [Fintype I] [DecidableEq I] :
    scalarCubeDomainDensity I ≤ Real.exp (((Fintype.card I : ℝ)+1)^2) := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hb : 2*((Fintype.card I : ℝ)+1) ≤ Real.exp ((Fintype.card I : ℝ)+1) := by
    calc
      _ ≤ Real.exp 1*Real.exp (Fintype.card I) := by gcongr; exact Real.add_one_le_exp _
      _ = _ := by rw [← Real.exp_add, add_comm]
  calc
    _ ≤ (2*((Fintype.card I : ℝ)+1))^(Fintype.card I+1) := scalarCubeDomainDensity_le_power I
    _ ≤ (Real.exp ((Fintype.card I : ℝ)+1))^(Fintype.card I+1) := by gcongr
    _ = _ := by rw [← Real.exp_nat_mul]; push_cast; congr 1; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NormalizedLatticeSheet
namespace OAI

section

namespace Erdos3

open Module Submodule

variable {I E : Type*} [Fintype I] [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem latticeBasisEquiv_synthesis (Λ : Submodule ℤ E) (b : Basis I ℝ E)
    (hb : span ℤ (Set.range b) = Λ) (z : I → ℤ) :
    (latticeBasisEquiv Λ b hb z).val = b.equivFun.symm (fun i => (z i : ℝ)) := by
  apply b.equivFun.injective
  rw [LinearEquiv.apply_symm_apply]
  funext i
  exact latticeBasisEquiv_coordinates Λ b hb z i

end Erdos3

end

section

namespace Erdos3

open Module Submodule

variable {I E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem integerBasisOfReal_synthesis [Fintype I] (Λ : Submodule ℤ E) (b : Basis I ℝ E)
    (hb : span ℤ (Set.range b) = Λ) (z : I → ℤ) :
    ((integerBasisOfReal Λ b hb).equivFun.symm z).val =
      b.equivFun.symm (fun i => (z i : ℝ)) := by
  simp only [integerBasisOfReal, Basis.map_equivFun, LinearEquiv.trans_symm,
    LinearEquiv.symm_symm, LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply]
  exact latticeBasisEquiv_synthesis (span ℤ (Set.range b)) b rfl z

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LinearLiftSheetCompatibility
namespace OAI

section

namespace Erdos3

open Module Submodule

theorem latticeSheetQuotient_eq_of_lift {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Λ : Submodule ℤ E) (W : Submodule ℝ E) (z : orthogonalLatticeImage Λ Wᗮ)
    (ell : Λ) (hell : Wᗮ.orthogonalProjectionOnto ell.val = z.val) (u : W) :
    latticeSheetQuotient Λ W z u =
      QuotientAddGroup.mk (u - W.orthogonalProjectionOnto ell.val) := by
  have hz : Wᗮ.orthogonalProjectionOnto (ell.val - (projectedLatticeLift Λ W z).val) = 0 := by
    rw [map_sub, hell, projectedLatticeLift_projection, sub_self]
  have hs := W.starProjection_add_starProjection_orthogonal
    (ell.val - (projectedLatticeLift Λ W z).val)
  change (W.orthogonalProjectionOnto (ell.val - (projectedLatticeLift Λ W z).val)).val +
    (Wᗮ.orthogonalProjectionOnto (ell.val - (projectedLatticeLift Λ W z).val)).val = _ at hs
  rw [hz, Submodule.coe_zero, add_zero, map_sub, Submodule.coe_sub] at hs
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  change ((u - projectedLatticeShift Λ W z) - (u - W.orthogonalProjectionOnto ell.val)).val ∈ Λ
  have he : ((u - projectedLatticeShift Λ W z) - (u - W.orthogonalProjectionOnto ell.val)).val =
      ell.val - (projectedLatticeLift Λ W z).val := by
    change u.val - (W.orthogonalProjectionOnto (projectedLatticeLift Λ W z).val).val -
      (u.val - (W.orthogonalProjectionOnto ell.val).val) = _
    calc
      _ = (W.orthogonalProjectionOnto ell.val).val -
          (W.orthogonalProjectionOnto (projectedLatticeLift Λ W z).val).val := by abel
      _ = _ := hs
  rw [he]
  exact Λ.sub_mem ell.property (projectedLatticeLift Λ W z).property

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerRowInterpolationMixture
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem normalizedIntegerInterpolation_lipschitz_bound (K c δ : ℝ)
    (hK : 0 < K) (hδ : 0 < δ)
    (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ δ * K) (u v : ℝ) :
    |normalizedIntegerInterpolation K c δ u - normalizedIntegerInterpolation K c δ v| ≤
      (2 * (probabilityProfileLipschitz : ℝ) / δ ^ 2) * |u - v| := by
  have hZ := shiftedSmoothSampleSum_pos (c * K) hlarge
  have hratio : K / shiftedSmoothSampleSum (c * K) (δ * K) ≤ 2 / δ :=
    (div_le_div_iff₀ hZ hδ).mpr (by nlinarith [(shiftedSmoothSampleSum_bounds (c * K) hlarge).1])
  have hb := smoothProbabilityProfile_lipschitz.dist_le_mul ((u-c)/δ) ((v-c)/δ)
  rw [Real.dist_eq, Real.dist_eq, ← sub_div, sub_sub_sub_cancel_right,
    abs_div, abs_of_pos hδ] at hb
  rw [normalizedIntegerInterpolation, normalizedIntegerInterpolation,
    ← sub_div, ← mul_sub, abs_div, abs_mul, abs_of_pos hK, abs_of_pos hZ]
  calc
    _ ≤ K * ((probabilityProfileLipschitz : ℝ) * (|u-v| / δ)) /
        shiftedSmoothSampleSum (c * K) (δ * K) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb hK.le) hZ.le
    _ = (K / shiftedSmoothSampleSum (c * K) (δ * K)) *
        ((probabilityProfileLipschitz : ℝ) / δ) * |u-v| := by ring
    _ ≤ (2 / δ) * ((probabilityProfileLipschitz : ℝ) / δ) * |u-v| :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hratio
          (show 0 ≤ (probabilityProfileLipschitz : ℝ) / δ by positivity)) (abs_nonneg _)
    _ = _ := by ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.IntegerPolynomialActiveProfileSupport
namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial VectorPolynomial
open scoped BigOperators Classical

theorem modularMonomialArrayPolynomial_selected {E K R A : Type*}
    [Fintype E] [Fintype A] [CommRing R] (exponent : E → K →₀ ℕ)
    (slot : A → E) (hinj : Function.Injective slot)
    (fixed : E → R) (c : A → R) :
    (∑ e, MvPolynomial.monomial (exponent e) (Function.extend slot c fixed e)) =
      (∑ e ∈ Finset.univ.filter (fun e => e ∉ Set.range slot),
        MvPolynomial.monomial (exponent e) (fixed e)) +
      ∑ a, MvPolynomial.monomial (exponent (slot a)) (c a) := by
  let F : E → MvPolynomial K R :=
    fun e => MvPolynomial.monomial (exponent e) (Function.extend slot c fixed e)
  have himage : Finset.univ.filter (fun e => e ∈ Set.range slot) = Finset.univ.image slot := by
    ext e
    simp
  have hsum := Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
    (p := fun e : E => e ∈ Set.range slot) (f := F)
  rw [himage, Finset.sum_image (fun a _ b _ hab => hinj hab)] at hsum
  have hs : (∑ a, F (slot a)) = ∑ a, MvPolynomial.monomial (exponent (slot a)) (c a) := by
    apply Finset.sum_congr rfl
    intro a _
    simp only [F, hinj.extend_apply]
  have hu : (∑ e ∈ Finset.univ.filter (fun e => e ∉ Set.range slot), F e) =
      ∑ e ∈ Finset.univ.filter (fun e => e ∉ Set.range slot),
        MvPolynomial.monomial (exponent e) (fixed e) := by
    apply Finset.sum_congr rfl
    intro e he
    change MvPolynomial.monomial (exponent e) (Function.extend slot c fixed e) = _
    rw [Function.extend_apply' c fixed e (Finset.mem_filter.mp he).2]
  rw [hs, hu] at hsum
  exact hsum.symm.trans (add_comm _ _)

theorem modularBoundedCoefficientPolynomial_selected {K R A : Type*}
    [Fintype K] [Fintype A] [CommRing R] (h : ℕ)
    (slot : A → BoundedCoefficientExponent K h) (hinj : Function.Injective slot)
    (fixed : BoundedCoefficientExponent K h → R) (c : A → R) :
    modularBoundedCoefficientPolynomial h (Function.extend slot c fixed) =
      modularUnselectedCoefficientPolynomial h slot fixed +
        ∑ a, monomial (slot a).val (c a) := by
  let F : BoundedCoefficientExponent K h → MvPolynomial K R :=
    fun e => monomial e.val (Function.extend slot c fixed e)
  have himage : Finset.univ.filter (fun e => e ∈ Set.range slot) = Finset.univ.image slot := by
    ext e
    simp
  have hsum := Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
    (p := fun e : BoundedCoefficientExponent K h => e ∈ Set.range slot) (f := F)
  rw [himage, Finset.sum_image (fun a _ b _ hab => hinj hab)] at hsum
  have hselected : (∑ a, F (slot a)) = ∑ a, monomial (slot a).val (c a) := by
    apply Finset.sum_congr rfl
    intro a _
    simp only [F, hinj.extend_apply]
  have hunselected : (∑ e ∈ Finset.univ.filter (fun e => e ∉ Set.range slot), F e) =
      modularUnselectedCoefficientPolynomial h slot fixed := by
    apply Finset.sum_congr rfl
    intro e he
    change MvPolynomial.monomial e.val (Function.extend slot c fixed e) = _
    rw [Function.extend_apply' c fixed e (Finset.mem_filter.mp he).2]
  rw [hselected, hunselected] at hsum
  exact hsum.symm.trans (add_comm _ _)

theorem modularBoundedCoefficientPolynomial_selected_top {K R A : Type*}
    [Fintype K] [Fintype A] [CommRing R] (h : ℕ)
    (slot : A → BoundedCoefficientExponent K h) (hinj : Function.Injective slot)
    (hdegree : ∀ a, (slot a).val.degree = h)
    (fixed : BoundedCoefficientExponent K h → R) (c : A → R) :
    homogeneousComponent h (modularBoundedCoefficientPolynomial h (Function.extend slot c fixed)) =
      homogeneousComponent h (modularUnselectedCoefficientPolynomial h slot fixed) +
        ∑ a, monomial (slot a).val (c a) := by
  rw [modularBoundedCoefficientPolynomial_selected h slot hinj fixed c, map_add, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  apply homogeneousComponent_eq_self
  exact isHomogeneous_monomial (c a) (hdegree a)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.EarlyFiberCapBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem earlyConstantDensityCap_exp_bound (a n : ℕ) {R V P : ℝ}
    (hP : 0 ≤ P) (hR : 0 < R)
    (ha : (a : ℝ) ≤ P) (hn : (n : ℝ) ≤ P)
    (hA : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (hRP : R⁻¹ ≤ Real.exp P) (hVP : V ≤ Real.exp P) :
    earlyConstantDensityCap a n R V ≤ Real.exp (3 * P ^ 2 + 17 * P) := by
  have h4 : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have h8 : (8 : ℝ) ≤ Real.exp 8 := by linarith [Real.add_one_le_exp (8 : ℝ)]
  have hw : (R / 4)⁻¹ ≤ Real.exp (P + 4) := by
    calc
      _ = 4 * R⁻¹ := by rw [inv_div, div_eq_mul_inv]
      _ ≤ Real.exp 4 * Real.exp P := by gcongr
      _ = _ := by rw [← Real.exp_add, add_comm]
  have hz : 8 * (probabilityProfileLipschitz : ℝ) / (R / 4) ≤ Real.exp (2 * P + 12) := by
    rw [div_eq_mul_inv]
    calc
      _ ≤ Real.exp 8 * Real.exp P * Real.exp (P+4) := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hwp := pow_le_exp_mul_of_le_exp (by positivity) hw (by positivity) a ha
  have hzp := pow_le_exp_mul_of_le_exp (by positivity) hz (by positivity) n hn
  unfold earlyConstantDensityCap
  calc
    _ ≤ Real.exp P * Real.exp (P * (P+4)) * Real.exp (P * (2*P+12)) := by gcongr
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteInnerProgressionFamily
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_finite_inner_interval_family {p : ℝ} (hp : 0 ≤ p) (N : ℕ) :
    ∃ C : Finset (Finset ℤ), (C.card : ℝ) ≤ Real.exp (4 * p + 18) ∧
      (∀ S ∈ C, ∃ a b : ℕ, S = Finset.Ico (a : ℤ) (b : ℤ)) ∧
      ∀ a len : ℕ, a + len ≤ N → 0 < len → Real.exp (-p) * N ≤ (len : ℝ) →
        ∃ S ∈ C, S.Nonempty ∧ S ⊆ Finset.Ico (a : ℤ) (a + len) ∧
          (len : ℝ) ≤ 2 * S.card ∧
          2 * (1 - (S.card : ℝ) / len) ≤ Real.exp (-p) := by
  classical
  by_cases hN : Real.exp (2 * p + 8) ≤ (N : ℝ)
  · obtain ⟨L, hL, hscale, hgrid⟩ := exists_exp_integer_grid_scale hp hN
    let C := (Finset.univ : Finset (Fin (N / L + 2) × Fin (N / L + 2))).image
      (fun c => Finset.Ico (L * c.1.val : ℤ) (L * c.2.val : ℤ))
    refine ⟨C, ?_, ?_, ?_⟩
    · have hc : C.card ≤ (N / L + 2) * (N / L + 2) :=
        (Finset.card_image_le).trans_eq (by simp)
      calc
        (C.card : ℝ) ≤ (N / L + 2 : ℕ) * (N / L + 2 : ℕ) := by exact_mod_cast hc
        _ ≤ Real.exp (2 * p + 5) * Real.exp (2 * p + 5) :=
          mul_le_mul hgrid hgrid (Nat.cast_nonneg _) (Real.exp_nonneg _)
        _ = Real.exp (4 * p + 10) := by rw [← Real.exp_add]; congr 1; ring
        _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
    · intro S hS
      obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hS
      exact ⟨L * c.1.val, L * c.2.val, by simp only [Nat.cast_mul]⟩
    · intro a len hend hlen hdense
      have hrho : Real.exp (-p) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      have hsmall : 4 * (L : ℝ) ≤ Real.exp (-p) * len := by
        calc
          _ ≤ Real.exp (-(2 * p)) * N := hscale
          _ = Real.exp (-p) * (Real.exp (-p) * N) := by
            rw [← mul_assoc, ← Real.exp_add]; congr 2; ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hdense (Real.exp_nonneg _)
      have hsN : 4 * L ≤ len := by
        exact_mod_cast hsmall.trans (mul_le_of_le_one_left (Nat.cast_nonneg _) hrho)
      obtain ⟨hstart, hstop, hne, _, hhalf, hloss⟩ := integer_grid_interval_geometry a len hL hsN
      let S := Finset.Ico (integerGridStart a L : ℤ) (integerGridEnd (a + len) L : ℤ)
      have hcard : S.card = integerGridEnd (a + len) L - integerGridStart a L := by
        simp only [S, Int.card_Ico]
        rw [← Int.natCast_sub hne.le, Int.toNat_natCast]
      have hadiv : a / L ≤ N / L := Nat.div_le_div_right (by omega)
      have hbdiv : (a + len) / L ≤ N / L := Nat.div_le_div_right hend
      refine ⟨S, ?_, ?_, ?_, ?_, ?_⟩
      · exact Finset.mem_image.mpr
          ⟨(⟨a / L + 1, by omega⟩, ⟨(a + len) / L, by omega⟩), Finset.mem_univ _, by
            simp only [S, integerGridStart, integerGridEnd, Nat.cast_mul]⟩
      · apply Finset.card_pos.mp
        rw [hcard]
        exact Nat.sub_pos_of_lt hne
      · intro x hx
        simp only [S, Finset.mem_Ico] at hx ⊢
        constructor <;> omega
      · rw [hcard]
        exact_mod_cast hhalf
      · have hlossR : (len : ℝ) ≤ S.card + 2 * L := by rw [hcard]; exact_mod_cast hloss
        have hlenR : (0 : ℝ) < len := by exact_mod_cast hlen
        have he : 2 * (1 - (S.card : ℝ) / len) = 2 * ((len : ℝ) - S.card) / len := by
          field_simp
        rw [he]
        apply (div_le_iff₀ hlenR).mpr
        linarith
  · let C := (Finset.univ : Finset (Fin (N + 1) × Fin (N + 1))).image
      (fun c => Finset.Ico (c.1.val : ℤ) (c.2.val : ℤ))
    refine ⟨C, ?_, ?_, ?_⟩
    · have h1 : (1 : ℝ) ≤ Real.exp (2 * p + 8) := Real.one_le_exp (by positivity)
      have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      have hNp : (N + 1 : ℕ) ≤ Real.exp (2 * p + 9) := by
        have hs : (N : ℝ) + 1 ≤ 2 * Real.exp (2 * p + 8) := by linarith
        calc
          ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by norm_cast
          _ ≤ 2 * Real.exp (2 * p + 8) := hs
          _ ≤ Real.exp 1 * Real.exp (2 * p + 8) :=
            mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
          _ = _ := by rw [← Real.exp_add]; congr 1; ring
      have hc : C.card ≤ (N + 1) * (N + 1) :=
        (Finset.card_image_le).trans_eq (by simp)
      calc
        (C.card : ℝ) ≤ (N + 1 : ℕ) * (N + 1 : ℕ) := by exact_mod_cast hc
        _ ≤ Real.exp (2 * p + 9) * Real.exp (2 * p + 9) :=
          mul_le_mul hNp hNp (Nat.cast_nonneg _) (Real.exp_nonneg _)
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
    · intro S hS
      obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hS
      exact ⟨c.1.val, c.2.val, rfl⟩
    · intro a len hend hlen _
      have hcard : (Finset.Ico (a : ℤ) (a + len)).card = len := by simp
      refine ⟨Finset.Ico (a : ℤ) (a + len), ?_, ?_, Finset.Subset.refl _, ?_, ?_⟩
      · exact Finset.mem_image.mpr
          ⟨(⟨a, by omega⟩, ⟨a + len, by omega⟩), Finset.mem_univ _, by simp⟩
      · exact Finset.card_pos.mp (by simpa only [hcard] using hlen)
      · rw [hcard]
        nlinarith [Nat.cast_nonneg (α := ℝ) len]
      · rw [hcard, div_self (by exact_mod_cast hlen.ne' : (len : ℝ) ≠ 0)]
        simpa using Real.exp_nonneg (-p)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DenseProgressionInnerFamily
namespace OAI

section

namespace Erdos3

theorem integerProgressionSupport_reindex (r m a H : ℕ) :
    integerProgressionSupport ((r : ℤ) + m * a) m H =
      (Finset.Ico (a : ℤ) (a + H)).image (fun x => (r : ℤ) + m * x) := by
  have he : Finset.Ico (a : ℤ) (a + H) =
      (Finset.Ico (0 : ℤ) H).image (fun x => (a : ℤ) + x) := by
    simpa only [add_zero] using (Finset.image_add_left_Ico (0 : ℤ) H (a : ℤ)).symm
  rw [he, Finset.image_image]
  unfold integerProgressionSupport translateSupport
  rw [Finset.image_image]
  congr 1
  funext x
  change (r : ℤ) + m * a + m * x = r + m * (a + x)
  ring

end Erdos3

end

section

namespace Erdos3

theorem integerProgressionSupport_singleton (c m : ℤ) :
    integerProgressionSupport c m 1 = {c} := by
  have hz : Finset.Ico (0 : ℤ) 1 = {0} := by
    ext x
    simp only [Finset.mem_Ico, Finset.mem_singleton]
    omega
  simp [integerProgressionSupport, translateSupport, hz, integerStrideHom]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SelectedResidueApproximation
namespace OAI

section

namespace Erdos3

theorem residueSmoothWeight_congr {K X : Type*} [Fintype K] [Fintype X]
    (r s : K × X → ℤ) (modulus : X → ℕ) (V : K × X → ℝ)
    (hrs : ∀ z, (modulus z.2 : ℤ) ∣ s z - r z) :
    residueSmoothWeight r modulus V = residueSmoothWeight s modulus V := by
  funext y
  have he : (∀ z, (modulus z.2 : ℤ) ∣ y z - r z) ↔
      ∀ z, (modulus z.2 : ℤ) ∣ y z - s z := by
    constructor
    · intro h z
      have hid : y z - s z = (y z - r z) - (s z - r z) := by ring
      rw [hid]
      exact dvd_sub (h z) (hrs z)
    · intro h z
      have hid : y z - r z = (y z - s z) + (s z - r z) := by ring
      rw [hid]
      exact dvd_add (h z) (hrs z)
  simp only [residueSmoothWeight, he]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.SiteFourierHaarMean
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {K F : Type*} [Fintype K] [Fintype F] {m : ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

theorem coefficientTorusCharacter_norm (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (x : CoefficientTorus (K := K) U) : ‖coefficientTorusCharacter U frequency x‖ = 1 :=
  quotientLinearCharacter_norm _ _ _ _

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CanonicalScalarSourceEnvelope
namespace OAI

section

namespace Erdos3

open scoped NNReal

noncomputable def principalIntervalWeight (K T γ : ℝ) (x : Option Empty → ℝ) : ℝ :=
  (principalIntervalLength K T γ : ℝ) / (K / T) *
    normalizedIntegerInterpolation (K / T) (3 * γ / 2) (γ / 2)
      ((principalIntervalLength K T γ : ℝ) / (K / T) * x none)

variable {K T γ : ℝ} (hK : 0 < K) (hT : 0 < T) (hγ : 0 < γ)
variable (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ (γ / 2) * (K / T))

include hK hT hγ hlarge in
theorem principalIntervalWeight_lipschitz :
    LipschitzWith (128 * probabilityProfileLipschitz) (principalIntervalWeight K T γ) := by
  let a : ℝ := (principalIntervalLength K T γ : ℝ) / (K / T)
  have hL := principalIntervalLength_pos hK hT hγ
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have ha : a ≤ 4 * γ :=
    (div_le_iff₀ (div_pos hK hT)).mpr (principalIntervalLength_bounds hK hT hγ hlarge).2
  have hcoef : a ^ 2 * (2 * (probabilityProfileLipschitz : ℝ) / (γ / 2) ^ 2) ≤
      128 * (probabilityProfileLipschitz : ℝ) := by
    calc
      _ ≤ (4 * γ) ^ 2 * (2 * (probabilityProfileLipschitz : ℝ) / (γ / 2) ^ 2) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha0 ha 2) (by positivity)
      _ = _ := by field_simp; ring
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hxy : |x none - y none| ≤ dist x y := by
    simpa only [Real.dist_eq] using dist_le_pi_dist x y none
  have hb := normalizedIntegerInterpolation_lipschitz_bound (K / T) (3 * γ / 2) (γ / 2)
    (div_pos hK hT) (by positivity) hlarge (a * x none) (a * y none)
  rw [Real.dist_eq]
  change |a * normalizedIntegerInterpolation (K / T) (3 * γ / 2) (γ / 2) (a * x none) -
    a * normalizedIntegerInterpolation (K / T) (3 * γ / 2) (γ / 2) (a * y none)| ≤
      (128 * (probabilityProfileLipschitz : ℝ)) * dist x y
  rw [← mul_sub, abs_mul, abs_of_nonneg ha0]
  calc
    _ ≤ a * ((2 * (probabilityProfileLipschitz : ℝ) / (γ / 2) ^ 2) *
        |a * x none - a * y none|) := mul_le_mul_of_nonneg_left hb ha0
    _ = (a ^ 2 * (2 * (probabilityProfileLipschitz : ℝ) / (γ / 2) ^ 2)) *
        |x none - y none| := by rw [← mul_sub, abs_mul, abs_of_nonneg ha0]; ring
    _ ≤ (128 * (probabilityProfileLipschitz : ℝ)) * dist x y :=
      mul_le_mul hcoef hxy (abs_nonneg _) (by positivity)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoefficientDeckCoordinates
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule

variable {K : Type*} {m : ℕ} {J B : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (B j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

variable (bW : ∀ j, Basis (B j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

theorem coefficientDeckKernelEquiv_coordinate (d : ℕ) (hd : 0 < d)
    (r : CoefficientDeckResidues (K := K) B d)
    (j : Fin m) (e : BoundedCoefficientExponent K (j.val + 1)) :
    euclideanCoefficientEquiv U (coefficientDeckKernelEquiv U bW d hd r).val j e =
      (coverKernelBasisEquiv
        (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup
        (bW j) d hd (r j e)).val := by
  change euclideanCoefficientEquiv U ((euclideanCoefficientEquiv U).symm _) j e = _
  rw [AddEquiv.apply_symm_apply]
  rfl

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ModeAmplitudeErrorBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem modeRemovalRadius_le_error (d : ℕ) {ε : ℝ} (hε : 0 < ε) :
    modeRemovalRadius d ε ≤ ε := by
  have hc := modeRemovalTranslationConstant_nonneg d
  unfold modeRemovalRadius
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith

theorem modeAmplitudeError_bound (d : ℕ) {L ε : ℝ} (hL : 0 ≤ L) (hε : 0 < ε) :
    modeRemovalTranslationConstant d * modeRemovalRadius d (modeAmplitudeAccuracy L ε) +
      L * modeRemovalRadius d (modeAmplitudeAccuracy L ε) +
      modeRemovalBeta (modeAmplitudeAccuracy L ε) ≤ ε := by
  have he := modeAmplitudeAccuracy_pos hL hε
  have hbase := modeRemovalError_bound d he
  have hr := modeRemovalRadius_le_error d he
  have hmul := mul_le_mul_of_nonneg_left hr hL
  have hidentity : (L + 1) * modeAmplitudeAccuracy L ε = ε / 2 := by
    unfold modeAmplitudeAccuracy
    field_simp
  nlinarith

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.BooleanPolynomialLogBudget
namespace OAI

section

namespace Erdos3

noncomputable def booleanToleranceC2Log {D α : Type*} [Fintype D] [Fintype α]
    {B : D → Type*} [∀ d, Fintype (B d)] (Z : Type*) [Fintype Z]
    (h : D → ℕ) (degree : ℕ) (P : ℝ) : ℝ :=
  3*Fintype.card (PolynomialParameter Z (JointBlockParameter B h α))*(degree+2 : ℕ)+
    (2*booleanJetMassLog (Fintype.card α) degree P+1)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.CoefficientEvaluationTorus
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem coefficientEvaluationTorus_constant {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ)
    (y : CoefficientTorus (K := Empty) U) :
    coefficientEvaluationTorus U t (constantCoefficientTorusMap U y) = y := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective (coefficientIntegerLattice U) y
  rw [constantCoefficientTorusMap_mk, coefficientEvaluationTorus_mk,
    coefficientEvaluationArray_constant]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CommonStrideCoordinates
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem affine_interval_eq_progression (r m a b : ℕ) :
    (Finset.Ico (a : ℤ) (b : ℤ)).image (fun x => (r : ℤ) + m * x) =
      integerProgressionSupport ((r : ℤ) + m * a) m (b - a) := by
  by_cases hab : a ≤ b
  · have he : (a : ℤ) + (b - a : ℕ) = b := by omega
    rw [integerProgressionSupport_reindex, he]
  · have hi : Finset.Ico (a : ℤ) (b : ℤ) = ∅ := Finset.Ico_eq_empty_of_le (by omega)
    simp [Nat.sub_eq_zero_of_le (by omega : b ≤ a), hi, integerProgressionSupport, translateSupport]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem commonStridePoint_injective {I : Type*} (c : I → ℤ) {m : ℕ} (hm : 0 < m) :
    Function.Injective (commonStridePoint c m) :=
  Function.LeftInverse.injective (commonStrideIndex_point c hm)

theorem commonStridePoint_mem {I : Type*} [Fintype I] [DecidableEq I]
    (c : I → ℤ) (m : ℕ) (H : I → ℕ) {x : I → ℤ} (hx : x ∈ integerBox H) :
    commonStridePoint c m x ∈ commonStrideBox c m H := by
  rw [commonStrideBox_eq_image]
  exact Finset.mem_image.mpr ⟨x, hx, rfl⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteCommonStrideFamily
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem finiteCommonStrideFamily_shape {I : Type*} [Fintype I] [DecidableEq I]
    (M : ℕ) (C : I → Finset (Finset ℤ))
    (hshape : ∀ i S, S ∈ C i → ∃ a b : ℕ, S = Finset.Ico (a : ℤ) (b : ℤ))
    {A : Finset (I → ℤ)} (hA : A ∈ finiteCommonStrideFamily M C) :
    ∃ (c : I → ℤ) (m : ℕ) (H : I → ℕ), 0 < m ∧ m ≤ M ∧ A = commonStrideBox c m H := by
  obtain ⟨q, _, hq⟩ := Finset.mem_biUnion.mp hA
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hq
  choose a b hab using fun i => hshape i (S i) (Fintype.mem_piFinset.mp hS i)
  refine ⟨(fun i => ((q.2 i).val : ℤ) + (q.1.val + 1 : ℕ) * a i), q.1.val + 1,
    (fun i => b i - a i), by omega, by omega, ?_⟩
  congr 1
  funext i
  rw [hab i, affine_interval_eq_progression]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.IdealSiteBoxRadius
namespace OAI

section

namespace Erdos3

theorem idealSiteBoxRadius_buffer_le_exp (α : Type*) [Fintype α] (degree : ℕ) :
    2 * idealSiteBoxRadius α degree ≤
      Real.exp (((degree : ℝ) + 2) * Fintype.card α + 3) := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hp : (2 : ℝ) ^ Fintype.card α ≤ Real.exp (Fintype.card α : ℝ) := by
    calc
      _ ≤ (Real.exp 1) ^ Fintype.card α := pow_le_pow_left₀ (by norm_num) htwo _
      _ = _ := by rw [← Real.exp_nat_mul]; simp only [mul_one]
  unfold idealSiteBoxRadius
  calc
    _ ≤ Real.exp 1 * (Real.exp (Fintype.card α : ℝ) *
        Real.exp (((degree : ℝ) + 1) * Fintype.card α + 2)) := by
      have hr0 : 0 ≤ partitionedIdealRadius α degree + 1 := by
        have h := partitionedIdealRadius_nonneg α degree
        linarith
      exact mul_le_mul htwo
        (mul_le_mul hp (partitionedIdealRadius_add_one_le_exp α degree) hr0 (Real.exp_pos _).le)
        (mul_nonneg (by positivity) hr0) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.IdealSiteEnvelopeBudget
namespace OAI

section

namespace Erdos3

theorem idealSiteEnvelopeRadius_le_exp (α : Type*) [Fintype α] (degree : ℕ) :
    idealSiteEnvelopeRadius α degree ≤
      Real.exp (((degree : ℝ) + 3) * Fintype.card α + 3) := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hp : (2 : ℝ) ^ Fintype.card α ≤ Real.exp (Fintype.card α : ℝ) := by
    calc
      _ ≤ (Real.exp 1) ^ Fintype.card α := pow_le_pow_left₀ (by norm_num) htwo _
      _ = _ := by rw [← Real.exp_nat_mul]; simp only [mul_one]
  unfold idealSiteEnvelopeRadius
  calc
    _ ≤ Real.exp (Fintype.card α : ℝ) *
        Real.exp (((degree : ℝ) + 2) * Fintype.card α + 3) :=
      mul_le_mul hp (idealSiteBoxRadius_buffer_le_exp α degree)
        (mul_nonneg (by norm_num) (idealSiteBoxRadius_pos α degree).le) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RowRestrictedDeckSiteMask
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {α K : Type*} [DecidableEq α] [Fintype K]
variable {m : ℕ} {O B : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Fintype (B j)]
variable (root : K → ℤ) (D : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)
variable (d period : ℕ) [NeZero d]

noncomputable def coefficientDeckSmallPeriodDensity
    (r : ∀ j, O j → B j → ZMod period) : ℝ :=
  ∏ j, ∏ i : B j, uniformResidueSmallPeriodDensity
    (boundedCoefficientJetMatrix root D (j.val + 1) (rows j)) d period (fun t => r j t i)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical Matrix

variable {α K : Type*} [Fintype α] [DecidableEq α] [Fintype K]
variable {m : ℕ} {O B : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Fintype (B j)]
variable (root : K → ℤ) (D : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)
variable (d period : ℕ) [NeZero d] [NeZero period]

noncomputable def coefficientDeckSiteMask
    (r : Finset α → ∀ j, B j → ZMod period) : ℝ :=
  coefficientDeckSmallPeriodDensity root D rows d period (fun j t i =>
    (integerResidueMatrix (booleanJetExtractionMatrix (rows j)) period *ᵥ (fun s => r s j i)) t)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.JetAxisReference
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical

variable {m : ℕ} (O I : Fin m → Type*) (n : Fin m → ℕ)
variable [∀ j, Fintype (O j)] [∀ j, Fintype (I j)]

def coefficientJetAxisSplit (P : LayerSamplerAxis I n → Prop) [DecidablePred P] :
    (∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ)) ≃ᵐ
      (∀ a : {a // P a}, CoefficientJetAxisRow O a.val) ×
        (∀ a : {a // ¬P a}, CoefficientJetAxisRow O a.val) :=
  (coefficientJetAxisEquiv O I n).trans
    (MeasurableEquiv.piEquivPiSubtypeProd (CoefficientJetAxisRow O) P)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PhysicalChartRadiusBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (α : Type*) [Fintype α]

noncomputable def allocatedPhysicalChartRadius (C : Fin m → ℝ) (H : ℝ) (j : Fin m) : ℝ :=
  1 / (4 * (((Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1) *
    ((2 : ℝ) ^ Fintype.card α * (H + Fintype.card α) ^ (j.val + 1)) *
    ((C j + 1) * ((Fintype.card (I j) : ℝ) + 1))))

theorem allocatedPhysicalChartRadius_pos (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    {H : ℝ} (hH : 1 ≤ H) (j : Fin m) :
    0 < allocatedPhysicalChartRadius (G := G) B α C H j := by
  have hH0 : 0 < H := zero_lt_one.trans_le hH
  have hC0 := hC j
  unfold allocatedPhysicalChartRadius
  positivity

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (α : Type*) [Fintype α]

theorem allocatedPhysicalChartRadius_inv_le_exp (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    {H P : ℝ} (hH : 1 ≤ H) (hP : 0 ≤ P) (hHP : H ≤ Real.exp P)
    (hCP : ∀ j, C j ≤ Real.exp P)
    (hNP : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Real.exp P)
    (hIP : ∀ j, (Fintype.card (I j) : ℝ) ≤ Real.exp P) (j : Fin m) :
    (allocatedPhysicalChartRadius (G := G) B α C H j)⁻¹ ≤
      Real.exp (3 * (P + 1) + Fintype.card α + 2 +
        (j.val + 1 : ℕ) * (P + Fintype.card α + 1)) := by
  have h1 : 1 ≤ Real.exp P := Real.one_le_exp_iff.mpr hP
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hadd {a : ℝ} (ha : a ≤ Real.exp P) : a + 1 ≤ Real.exp (P + 1) := by
    calc
      _ ≤ Real.exp P + Real.exp P := add_le_add ha h1
      _ = 2 * Real.exp P := by ring
      _ ≤ Real.exp 1 * Real.exp P := mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have h4 : (4 : ℝ) ≤ Real.exp 2 := by
    calc
      _ = (2 : ℝ) ^ 2 := by norm_num
      _ ≤ (Real.exp 1) ^ 2 := pow_le_pow_left₀ (by norm_num) h2 2
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have hq : H + Fintype.card α ≤ Real.exp (P + Fintype.card α + 1) := by
    have hq1 : (Fintype.card α : ℝ) + 1 ≤ Real.exp (Fintype.card α + 1) := by
      linarith [Real.add_one_le_exp ((Fintype.card α : ℝ) + 1)]
    calc
      _ ≤ Real.exp P + (Fintype.card α : ℝ) * Real.exp P :=
        add_le_add hHP (by simpa using mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg (Fintype.card α)))
      _ = ((Fintype.card α : ℝ) + 1) * Real.exp P := by ring
      _ ≤ Real.exp (Fintype.card α + 1) * Real.exp P :=
        mul_le_mul_of_nonneg_right hq1 (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hN := hadd (hNP j)
  have hCj := hadd (hCP j)
  have hI := hadd (hIP j)
  have hC0 := hC j
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  simp only [allocatedPhysicalChartRadius, one_div, inv_inv]
  calc
    _ ≤ Real.exp 2 * (Real.exp (P + 1) *
        ((Real.exp 1) ^ Fintype.card α * (Real.exp (P + Fintype.card α + 1)) ^ (j.val + 1)) *
        (Real.exp (P + 1) * Real.exp (P + 1))) := by gcongr
    _ = _ := by
      simp only [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      push_cast
      ring

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedScalarStructuralBasePower
namespace OAI

section

namespace Erdos3

open scoped NNReal ContDiff

theorem exists_normalized_site_cutoff {D : Type*} [Fintype D]
    (r : ℝ≥0) (hr : 0 < r) :
    ∃ χ : (D → ℝ) → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      (∀ v, 0 ≤ χ v ∧ χ v ≤ 1) ∧
      (∀ v, (∀ d, |v d| ≤ (r : ℝ)) → χ v = 1) ∧
      (∀ v, χ v ≠ 0 → ∀ d, |v d| ≤ 2 * (r : ℝ)) ∧
      LipschitzWith (Fintype.card D * normalizedSiteCutoffBound / (2 * r)) χ := by
  obtain ⟨χ, hsmooth, hχ, hone, hzero, hLip⟩ :=
    (Classical.choose_spec exists_smooth_scalar_cutoff).2
  have hr2 : 0 < 2 * (r : ℝ) := by positivity
  refine ⟨coordinateBoxCutoff χ (2 * (r : ℝ)),
    contDiff_coordinateBoxCutoff χ hsmooth _,
    hasCompactSupport_coordinateBoxCutoff χ hzero hr2,
    coordinateBoxCutoff_range χ hχ _, ?_, ?_, ?_⟩
  · intro v hv
    apply coordinateBoxCutoff_eq_one χ hone hr2
    intro d
    have he : 2 * (r : ℝ) / 2 = r := by ring
    rw [he]
    exact hv d
  · intro v hv d
    by_contra! hd
    apply hv
    apply coordinateBoxCutoff_eq_zero χ hzero hr2
    refine ⟨d, ?_⟩
    have hr0 : (0 : ℝ) ≤ r := r.coe_nonneg
    linarith
  · simpa only [NNReal.coe_mul, NNReal.coe_ofNat] using
      lipschitz_coordinateBoxCutoff χ normalizedSiteCutoffBound (2 * r) (by positivity) hχ hLip

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SpatialNumericEnvelopeFunctoriality
namespace OAI

section

namespace Erdos3

open BooleanCubeKernel
open scoped NNReal

noncomputable def spatialThresholdEnvelope {A : Type*} [Semiring A] (p l : A) : A :=
  spatialMeshEnvelope p l + (VectorPolynomial.comparisonProfileBound : ℕ) + 2 * p + l + 16

noncomputable def spatialBoundaryEnvelope {A : Type*} [Semiring A] (p l : A) : A :=
  l + (VectorPolynomial.comparisonProfileBound : ℕ) + 3 * p + 25

end Erdos3

end

section

namespace Erdos3

noncomputable def spatialPrimitiveEnvelope {A : Type*} [Semiring A] (p E l : A) : A :=
  p + E + l + 3 + (p ^ 3 + anisotropicSpatialCapLog p) +
    (coefficientErrorVolumeLog p + 4) + spatialDisplacementEnvelope p +
    spatialDiscretizationEnvelope p l + spatialLipschitzCostEnvelope p l +
    spatialThresholdEnvelope p l + spatialBoundaryEnvelope p l + spatialMovementEnvelope p l

end Erdos3

end

section

namespace Erdos3

section Maps

variable {α β : Type*} [Semiring α] [Semiring β] (f : α →+* β)

@[simp] theorem map_spatialPrimitiveEnvelope (p E l : α) :
    f (spatialPrimitiveEnvelope p E l) = spatialPrimitiveEnvelope (f p) (f E) (f l) := by
  simp [spatialPrimitiveEnvelope, spatialDisplacementEnvelope,
    spatialDiscretizationEnvelope, spatialLipschitzCostEnvelope,
    spatialThresholdEnvelope, spatialBoundaryEnvelope, spatialMovementEnvelope,
    spatialMeshEnvelope, spatialLipschitzEnvelope, spatialFixedProfileEnvelope,
    coefficientErrorVolumeLog, anisotropicSpatialCapLog, map_ofNat]

end Maps

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedFullSiteRadius
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem allocatedSiteRootAllowance_le_exp (α : Type*) [Fintype α] (m : ℕ) :
    allocatedSiteRootAllowance α m ≤ Real.exp (((2 * m : ℕ) + 5) * (Fintype.card α : ℝ) + 5) := by
  let q : ℝ := Fintype.card α
  have hq : 0 ≤ q := Nat.cast_nonneg _
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hp : (2 : ℝ) ^ Fintype.card α ≤ Real.exp q := by
    calc
      _ ≤ (Real.exp 1) ^ Fintype.card α := pow_le_pow_left₀ (by norm_num) htwo _
      _ = _ := by rw [← Real.exp_nat_mul]; simp only [mul_one]; rfl
  have hmain : (2 : ℝ) ^ Fintype.card α * (q + 1) ^ (m + 1) ≤ Real.exp (((m : ℝ) + 2) * q) := by
    calc
      _ ≤ Real.exp q * (Real.exp q) ^ (m + 1) :=
        mul_le_mul hp (pow_le_pow_left₀ (by positivity) (Real.add_one_le_exp q) _)
          (by positivity) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
  let L : ℝ := ((m : ℝ) + 2) * q + (((m : ℝ) + 3) * q + 3)
  have hmainL : ((m : ℝ) + 2) * q ≤ L := by
    dsimp [L]
    have h : 0 ≤ ((m : ℝ) + 3) * q := by positivity
    linarith
  have henvL : ((m : ℝ) + 3) * q + 3 ≤ L := by
    dsimp [L]
    have h : 0 ≤ ((m : ℝ) + 2) * q := by positivity
    linarith
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have henv := (idealSiteEnvelopeRadius_le_exp α m).trans (Real.exp_le_exp.mpr henvL)
  have hunit : 1 ≤ Real.exp L := Real.one_le_exp_iff.mpr hL
  have hthree : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  calc
    _ ≤ 3 * Real.exp L := by
      unfold allocatedSiteRootAllowance
      have hm := hmain.trans (Real.exp_le_exp.mpr hmainL)
      change 1 + (2 : ℝ) ^ Fintype.card α * (q + 1) ^ (m + 1) + idealSiteEnvelopeRadius α m ≤ _
      linarith
    _ ≤ Real.exp 2 * Real.exp L := mul_le_mul_of_nonneg_right hthree (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; dsimp [L, q]; push_cast; ring

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NormalizedCoordinateCutoff
namespace OAI

section

namespace Erdos3

open scoped NNReal ContDiff

noncomputable def normalizedCoordinateCutoff (D : Type*) [Fintype D]
    (r : ℝ≥0) (hr : 0 < r) : (D → ℝ) → ℝ :=
  Classical.choose (exists_normalized_site_cutoff (D := D) r hr)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.BufferedCoordinateProjection
namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {D : Type*} [Fintype D] (P : D → Prop) [DecidablePred P]
variable (r : ℝ≥0) (hr : 0 < r) (f : (D → ℝ) → ℂ)

noncomputable def bufferedCoordinateProjection (z : D → ℝ) : ℂ :=
  (normalizedCoordinateCutoff D r hr z : ℂ) * f (coordinateZeroProjection P z)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonStrideCorrelation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem finiteCorrelation_commonStrideBox {I : Type*} [Fintype I] [DecidableEq I]
    (b : I → ℤ) {d : ℕ} (hd : 0 < d) (K : I → ℕ) (f g : (I → ℤ) → ℂ) :
    finiteCorrelation (commonStrideBox b d K) f g =
      finiteCorrelation (integerBox K) (fun x => f (commonStridePoint b d x))
        (fun x => g (commonStridePoint b d x)) := by
  rw [commonStrideBox_eq_image]
  unfold finiteCorrelation
  exact Finset.expect_image (commonStridePoint_injective b hd).injOn

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.JointAffineBooleanSource
namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators ContDiff NNReal

variable {D α : Type*} [Fintype D] [Fintype α] [decidableEqAlpha : DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]

noncomputable def jointAffineBooleanErrorBudget (h : D → ℕ) (C κ : D → ℝ) (A T : ℝ≥0)
    (r : ∀ d, B d × Fin (h d) → ℝ) (δ : ℝ) : ℝ :=
  let K := jointAffineBooleanInverseBudget (O := O) (α := α) h C κ δ
  let H := jointBooleanDerivativeBudget (B := B) (O := O) (α := α) h C
  1 + 2 * (K : ℝ) * jointBooleanWeightBudget (O := O) (α := α) h C A T r κ +
    (Fintype.card (JointBlockParameter B h α) : ℝ) * ((2 * (K : ℝ)) ^ 2 * ((H : ℝ) + 1))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PartitionedAffineLogEnvelope
namespace OAI

section

namespace Erdos3
open scoped NNReal

variable {D α : Type*} [Fintype D] [Fintype α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]

noncomputable def jointAffineTranslationLog (h : D → ℕ) (P E F : ℝ) : ℝ :=
  Fintype.card (Σ d, O d) + Fintype.card (JointBlockParameter B h α) +
    3 * jointAffineInverseLog (O := O) (α := α) h P E F +
    jointBooleanDerivativeLog (B := B) (O := O) (α := α) h P +
    jointAffineBooleanWeightLog (B := B) (O := O) (α := α) h P E F + 1

noncomputable def jointAffinePerturbationLog (h : D → ℕ) (P E F : ℝ) : ℝ :=
  Fintype.card (JointBlockParameter B h α) +
    3 * jointAffineInverseLog (O := O) (α := α) h P E F +
    jointBooleanDerivativeLog (B := B) (O := O) (α := α) h P +
    jointAffineBooleanWeightLog (B := B) (O := O) (α := α) h P E F + 6

end Erdos3

end

section

namespace Erdos3
open scoped NNReal

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)] [∀ d, Nonempty (O d)]

noncomputable def jointAffineSourceInputLog (h : D → ℕ) (P E F : ℝ) : ℝ :=
  jointAffineTranslationLog (B := B) (O := O) (α := α) h P E F +
    jointAffinePerturbationLog (B := B) (O := O) (α := α) h P E F +
    jointAffineInverseLog (O := O) (α := α) h P E F + Fintype.card (Σ d, O d) + E + 4

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.JointMeasureProductiveNarrowSampler
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_narrow_sampler_threshold (a b : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ P : ℝ, 0 ≤ P →
      (spatialSamplingBudget (2*P) + a)^a ≤ (P+A)^A ∧
      (spatialSamplingBudget (2*P) + b)^b ≤ (P+A)^A ∧
      10*P+128 ≤ (P+A)^A := by
  let base : Polynomial ℕ := 8*Polynomial.X+128
  let cost := (base+Polynomial.C a)^a+(base+Polynomial.C b)^b+10*Polynomial.X+128
  obtain ⟨A, hA, hbudget⟩ := exists_natPolynomial_eval_budget cost
  refine ⟨A, hA, fun P hP => ?_⟩
  have h := hbudget P hP
  have he : spatialSamplingBudget (2*P) = 8*P+128 := by unfold spatialSamplingBudget; ring
  have hc : (spatialSamplingBudget (2*P)+a)^a + (spatialSamplingBudget (2*P)+b)^b +
      10*P+128 ≤ (P+A)^A := by
    rw [he]
    simpa [cost, base, Polynomial.eval₂_pow] using h
  have hQ : 0 ≤ spatialSamplingBudget (2*P) := by unfold spatialSamplingBudget; positivity
  have ha : 0 ≤ (spatialSamplingBudget (2*P)+a)^a := by positivity
  have hb : 0 ≤ (spatialSamplingBudget (2*P)+b)^b := by positivity
  constructor
  · linarith
  constructor <;> linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SpatialMatrixBlockWideProbability
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

variable {G P X : Type*} [Fintype G] [Fintype P] [Fintype X]

theorem spatialMatrixNormalizedEntries_residue (e : Fin 2 × X ↪ G)
    (residue : Option (G ⊕ P) × X → ℤ) (q : X → ℕ) (hq : ∀ x, 0 < q x)
    (V : Option (G ⊕ P) × X → ℝ) (hV : ∀ z, 0 < V z)
    (t : Option (G ⊕ P) × X → ℤ) :
    spatialMatrixNormalizedEntries e V (residueLatticeArray residue q t) =
      rectangularLatticePoint (spatialMatrixIndexCenter e residue q) (spatialMatrixIndexWidth e q V)
        (fun i => t (spatialMatrixBlockSlot e i)) := by
  funext i
  exact (congrFun (residueProfile_point residue q hq V hV t) (spatialMatrixBlockSlot e i)).symm

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem spatialMatrixBlockThreshold_inverse_le_exp {n : ℕ} (hn : 0 < n)
    {η E : ℝ} (hη : 0 < η) (hE : 0 ≤ E) (hηb : η⁻¹ ≤ Real.exp E) :
    (spatialMatrixBlockThreshold n η)⁻¹ ≤
      Real.exp (smoothMatrixBlockThresholdLogBudget (2 * n * n) n 2 E) :=
  smoothMatrixBlock_threshold_inverse_le_exp (by positivity) hn 2 hη hE hηb

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedCoefficientIntegerMarginal
namespace OAI

section

namespace Erdos3
open MeasureTheory

namespace VectorPolynomial
open Module Submodule
open scoped BigOperators Classical

abbrev CoefficientIntegerScalarIndex (K : Type*) {m : ℕ} (n : Fin m → ℕ) :=
  Σ j : Fin m, BoundedCoefficientExponent K (j.val + 1) × Fin (n j)

end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SpatialMatrixCutoffBudget
namespace OAI

section

namespace Erdos3

theorem spatialMatrixBlockCutoff_lip_exp_budget {n : ℕ} (hn : 0 < n)
    {η E : ℝ} (hη : 0 < η) (hE : 0 ≤ E) (hηb : η⁻¹ ≤ Real.exp E) :
    (2 / spatialMatrixBlockThreshold n η) * ((n * n.factorial : ℕ) : ℝ) ≤
      Real.exp (smoothMatrixBlockThresholdLogBudget (2 * n * n) n 2 E +
        ((n : ℝ) + 1) ^ 2 + 1) :=
  determinantCutoff_lip_le_exp n (spatialMatrixBlockThreshold_pos hn hη)
    (spatialMatrixBlockThreshold_inverse_le_exp hn hη hE hηb)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedModularDetectorBadProduct
namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def preparedModularGeneralDetectorLateMaster
    (sourceBudget geometryBudget Qw Pphysical coarseTarget : ℝ) : ℝ :=
  sourceBudget + allocatedWitnessScaleLog geometryBudget Qw + coarseTarget +
    (2 * (spatialPrimitiveEnvelope Pphysical coarseTarget 0 +
      spatialTupleToleranceLog (spatialPrimitiveEnvelope Pphysical coarseTarget 0)) + 4) + 1

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PreparedUniformDegreeDirectMasterBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

noncomputable def preparedUniformDegreeDirectLate
    (Pmaster Pscale Pphysical coarseTarget extraLate : ℝ) : ℝ :=
  max Pmaster (max Pscale (max coarseTarget (max
    (2 * (spatialPrimitiveEnvelope Pphysical coarseTarget 0 +
      spatialTupleToleranceLog (spatialPrimitiveEnvelope Pphysical coarseTarget 0)) + 4)
    extraLate)))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedShortForecastRawSourceBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

structure PreparedForecastSourceScalarBounds
    (P Qearly Pphysical budget master Bstruct Pseed Qw lateTarget Pmin Pscale Plate : ℝ) : Prop where
  struct_input : Bstruct ≤ P
  P_nonneg : 0 ≤ P
  Qearly_nonneg : 0 ≤ Qearly
  physical_nonneg : 0 ≤ Pphysical
  master_nonneg : 0 ≤ master
  budget_master : budget ≤ master
  physical_master : Pphysical ≤ master
  struct_master : Bstruct ≤ master
  seed_nonneg : 0 ≤ Pseed
  Qw_nonneg : 0 ≤ Qw
  lateTarget_nonneg : 0 ≤ lateTarget
  base_nonneg : 0 ≤ preparedModularGeneralDetectorLateMaster master Pseed Qw Pphysical lateTarget
  base_late : preparedModularGeneralDetectorLateMaster master Pseed Qw Pphysical lateTarget ≤ Plate
  master_late : master ≤ Plate
  scale_late : Pscale ≤ Plate
  witness_late : allocatedWitnessScaleLog Pseed Qw + (1 + Pseed ^ 2) * Pmin ≤ Plate
  xi_late : 2 * (spatialPrimitiveEnvelope Pphysical lateTarget 0 +
    spatialTupleToleranceLog (spatialPrimitiveEnvelope Pphysical lateTarget 0)) + 4 ≤ Plate

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedFiniteNestedSourceLatePowerBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

noncomputable def preparedFiniteScheduleWitnessSeed
    (m : ℕ) {K G : Type} [Fintype K] [Fintype G]
    (degree Cdetect : K → ℕ) (nX count : ℕ)
    (Bstruct pnum Qstride Qσ Pmin : ℝ) (u model : K → ℝ) : ℝ :=
  let pRadius := allocatedCommonProductRadiusLog m Bstruct Bstruct
  let D := allocatedComparisonDimension m pnum
  let pDetect := fun k => allocatedModelTestLog (u k) (model k)
  let aDetect := fun k => 2 * u k + 4 * model k + 7
  let gain := fun k => slicedDetectionGainLog (degree k) (Cdetect k) count
    (pDetect k) (pDetect k) (aDetect k)
  let Pk := fun k => scalarKernelLogarithmicBudget (Fin (degree k + 1)) G
    (gain k + pDetect k + 4)
  let physical := fun k => preparedFiniteScheduleLocalPhysical m nX count Qstride (Pk k)
  let target := fun k => gain k + 40 + coefficientErrorSpatialLog (physical k)
  let E := fun k => target k + D * ((m * 2 ^ (m + 1) : ℕ) * Pk k) + 5
  let rho := fun k => 2 * affineProfileInputEnvelope D
    (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E k) (pDetect k + 2) + 2
  let tail := fun k => affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1)
    (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E k) (pDetect k + 2)
  let scale := preparedUniformDegreeScaleLog (D + pRadius) tail Qσ
  let tmod := fun k => ((m + 1 : ℕ) : ℝ) * Pk k + nX * Qstride
  let lengths := fun k => allocatedAffineLengthLog m D scale (rho k) (Pk k)
    (target k) (pDetect k + 2) (tmod k)
  allocatedScaleLog (scale + ∑ k, lengths k + Pmin + 1)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ScalarReferenceNativeDetectionCoordinateEquiv
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {K K' X : Type*}

@[simp] theorem trimmedSpatialWidths_scalarNoiseIndexEquiv
    (e : K ≃ K') (B τ : ℝ) (N : X → ℕ) (i : Option K × X) :
    trimmedSpatialWidths B τ N (scalarNoiseIndexEquiv e i) =
      trimmedSpatialWidths B τ N i := by
  rcases i with ⟨k, x⟩
  cases k <;> rfl

end Erdos3

end

end OAI
end


