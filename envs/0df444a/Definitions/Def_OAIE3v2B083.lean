-- Prove2me | Definitions.Def_OAIE3v2B083
-- name    : OAIE3v2B083
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:23:15.881984+00:00
-- url     : https://prove2.me/theorems/aa34e8e4-50f5-4784-8605-12c515e86f82
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 84 of 311
-- statement:
--   Definitions bundle 84 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B038`, `OAIE3v2B039`, `OAIE3v2B041`, `OAIE3v2B042`, `OAIE3v2B044`, `OAIE3v2B045`, `OAIE3v2B047`, `OAIE3v2B048`, `OAIE3v2B049`, `OAIE3v2B050`, `OAIE3v2B051`, `OAIE3v2B054`, `OAIE3v2B056`, `OAIE3v2B061`, `OAIE3v2B063`, `OAIE3v2B064` of this split.
--
--   Modules: `Dynamics/AllocatedFiniteIdealMaskBudget.lean`, `Dynamics/JointPivotProfileBudget.lean`, `Dynamics/MixedCyclicErrorBudget.lean`, `Dynamics/NormalizedNativeUniformBudget.lean`, `Estimates/ActiveAveragedProfileComparison.lean`, `Estimates/AllocatedFiberCap.lean`, `Estimates/AllocatedScalarLogBounds.lean`, `Estimates/AllocatedShortAxis.lean`, `Estimates/AllocatedSlicedCoarseSource.lean`, `Estimates/BooleanCubeProduct.lean`, `Estimates/CorrelationDerivative.lean`, `Estimates/EmptyLayerDetectionGeometry.lean`, `Estimates/InactiveShortLogBounds.lean`, `Estimates/MixedPairFrozenEquivalence.lean`, `Estimates/NativeSelectedCorrelators.lean`, `Estimates/ProductCutoffLipschitz.lean`, `Fourier/CoefficientEvaluationTorus.lean`, `Fourier/EuclideanCoefficientTorus.lean`, `Fourier/QuadraticFrequencyCoordinates.lean`, `Geometry/AllocatedSpatialProxyCap.lean`, `Geometry/AnisotropicSpatialCapBudget.lean`, `Geometry/BoxCyclicEncoding.lean`, `Geometry/CoarseSpatialPartitionBudget.lean`, `Geometry/CoefficientAmbientCoordinates.lean`, `Geometry/MixedCoefficientSmallSupport.lean`, `Geometry/SpatialNumericEnvelopeFunctoriality.lean`, `Geometry/SpatialTupleErrorBudget.lean`, `Geometry/SupportedCubeEquivTransport.lean`, `Geometry/SupportedCubeUnitBounds.lean`, `Geometry/UnconditionedSpatialWidthBudget.lean`, `Lattices/AffineCoefficientLaw.lean`, `Lattices/IntegerInterpolationExpBounds.lean`, `Lattices/IntegerRowInterpolationMixture.lean`, `Lattices/PhysicalSubboxResidueSlice.lean`, `Lattices/PrincipalIntegerInterpolation.lean`, `Linear/SharedFreeComparisonBasis.lean`, `Probability/CanonicalConstantDensityBound.lean`, `Probability/CoefficientProductLaw.lean`, `Probability/DensityMixtureAELaw.lean`, `Probability/DiagonalImageDensity.lean`, `Probability/MixedDensityInterpolation.lean`, `Probability/RestrictedComplexChartDensityComparison.lean`, `Probability/SampledWeightCellLaw.lean`, `Probability/ScaledArrayLaw.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B038
import Definitions.Def_OAIE3v2B039
import Definitions.Def_OAIE3v2B041
import Definitions.Def_OAIE3v2B042
import Definitions.Def_OAIE3v2B044
import Definitions.Def_OAIE3v2B045
import Definitions.Def_OAIE3v2B047
import Definitions.Def_OAIE3v2B048
import Definitions.Def_OAIE3v2B049
import Definitions.Def_OAIE3v2B050
import Definitions.Def_OAIE3v2B051
import Definitions.Def_OAIE3v2B054
import Definitions.Def_OAIE3v2B056
import Definitions.Def_OAIE3v2B061
import Definitions.Def_OAIE3v2B063
import Definitions.Def_OAIE3v2B064

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.SampledWeightCellLaw
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem independentCoordinateDensity_measure {ι : Type*} [Fintype ι]
    (f : ι → ℝ → ℝ) (hf : ∀ i, Integrable (f i)) (hf0 : ∀ i x, 0 ≤ f i x)
    (hmass : ∀ i, (∫ x, f i x) = 1) :
    Measure.pi (fun i => realDensityMeasure volume (f i)) =
      realDensityMeasure volume (independentCoordinateDensity f) := by
  let : ∀ i, IsProbabilityMeasure (realDensityMeasure volume (f i)) :=
    fun i => realDensityMeasure_probability volume (f i) (hf i) (hf0 i) (hmass i)
  apply Measure.pi_eq
  intro s hs
  have hprod0 (x : ι → ℝ) : 0 ≤ independentCoordinateDensity f x :=
    Finset.prod_nonneg (fun i _ => hf0 i (x i))
  rw [realDensityMeasure_apply volume _ (independentCoordinateDensity_integrable f hf) hprod0
    (MeasurableSet.univ_pi hs)]
  have hint : (∫ x in Set.univ.pi s, independentCoordinateDensity f x) =
      ∏ i, ∫ x in s i, f i x := by
    change (∫ x, (∏ i, f i (x i)) ∂(Measure.pi (fun _ : ι => (volume : Measure ℝ))).restrict
      (Set.univ.pi s)) = _
    rw [Measure.restrict_pi_pi]
    exact integral_fintype_prod_eq_prod (fun i x => f i x)
  rw [hint, ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (hf0 i))]
  apply Finset.prod_congr rfl
  intro i _
  exact (realDensityMeasure_apply volume (f i) (hf i) (hf0 i) (hs i)).symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CorrelationDerivative
namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H]

theorem gowersMoment_im_zero (j : ℕ) (f : H → ℂ) :
    (gowersMoment (j + 1) f).im = 0 := by
  induction j generalizing f with
  | zero =>
    rw [gowersMoment_one]
    change ((𝔼 x, f x) * starRingEnd ℂ (𝔼 x, f x)).im = 0
    rw [Complex.mul_conj, Complex.ofReal_im]
  | succ j ih =>
    rw [gowersMoment, expect_im]
    exact Finset.expect_eq_zero (fun h _ ↦ ih (multiplicativeDerivative f h))

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H]

variable [Fintype H]

theorem gowersMoment_eq_cubeAverage (j : ℕ) (f : H → ℂ) :
    gowersMoment j f = cubeAverage j (fun hs ↦ 𝔼 x, cubeProduct f hs x) := by
  induction j generalizing f with
  | zero => simp [gowersMoment, cubeAverage]
  | succ j ih =>
    simp only [gowersMoment, cubeAverage, ih, cubeProduct_cons_eq_derivative]

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H]

omit [Fintype H] in
theorem cubeProduct_crossDerivative (f g : H → ℂ) (h : H) (hs : List H) (x : H) :
    cubeProduct (crossDerivative f g h) hs x =
      cubeProduct f hs x * star (cubeProduct g hs (x + h)) := by
  induction hs generalizing x with
  | nil => simp [crossDerivative]
  | cons k hs ih =>
    simp only [cubeProduct_cons, ih, star_mul, star_star]
    rw [show x + k + h = x + h + k by abel]
    ring

theorem expect_gowersMoment_crossDerivative (j : ℕ) (f g : H → ℂ) :
    (𝔼 h, gowersMoment j (crossDerivative f g h)) =
      cubeAverage j (fun hs ↦ (𝔼 x, cubeProduct f hs x) * star (𝔼 x, cubeProduct g hs x)) := by
  simp only [gowersMoment_eq_cubeAverage]
  rw [← cubeAverage_comm_expect]
  simp_rw [cubeProduct_crossDerivative]
  have hpoint : ∀ hs : List H,
      (𝔼 h, 𝔼 x, cubeProduct f hs x * star (cubeProduct g hs (x + h))) =
        (𝔼 x, cubeProduct f hs x) * star (𝔼 x, cubeProduct g hs x) := by
    intro hs
    exact expect_crossDerivative (cubeProduct f hs) (cubeProduct g hs)
  simp_rw [hpoint]

theorem gowersMoment_eq_average_square (j : ℕ) (f : H → ℂ) :
    (gowersMoment (j + 1) f).re =
      cubeAverage j (fun hs ↦ ‖𝔼 x, cubeProduct f hs x‖ ^ 2) := by
  have h := congrArg Complex.re (expect_gowersMoment_crossDerivative j f f)
  change (𝔼 h, gowersMoment j (multiplicativeDerivative f h)).re = _
  simpa only [crossDerivative_self, cubeAverage_re,
    mul_star_re_eq_norm_sq] using h

theorem norm_expect_gowersMoment_crossDerivative_sq_le (j : ℕ) (f g : H → ℂ) :
    ‖𝔼 h, gowersMoment j (crossDerivative f g h)‖ ^ 2 ≤
      (gowersMoment (j + 1) f).re * (gowersMoment (j + 1) g).re := by
  rw [expect_gowersMoment_crossDerivative,
    gowersMoment_eq_average_square, gowersMoment_eq_average_square]
  exact cubeAverage_norm_inner_sq_le j _ _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.DiagonalImageDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem realDensityMeasure_real_univ {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (hf : Integrable f μ) (hf0 : ∀ x, 0 ≤ f x) :
    (realDensityMeasure μ f).real Set.univ = ∫ x, f x ∂μ := by
  change (realDensityMeasure μ f Set.univ).toReal = _
  rw [realDensityMeasure_apply μ f hf hf0 MeasurableSet.univ, Measure.restrict_univ,
    ENNReal.toReal_ofReal (integral_nonneg hf0)]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

theorem boundedDensity_mass {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) {B : ℝ} (hB : ∀ x, f x ≤ B)
    [IsProbabilityMeasure (realDensityMeasure μ f)] : Integrable f μ ∧ (∫ x, f x ∂μ) = 1 := by
  have hi : Integrable f μ := (integrable_const B).mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hf0 x)]
      exact hB x))
  refine ⟨hi, ?_⟩
  have he := realDensityMeasure_real_univ μ f hi hf0
  change ((realDensityMeasure μ f) Set.univ).toReal = _ at he
  rw [measure_univ, ENNReal.toReal_one] at he
  exact he.symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BooleanCubeProduct
namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H]

theorem mixedGowersMoment_one (F : (Fin 1 → Bool) → H → ℂ) :
    mixedGowersMoment 1 F =
      (𝔼 x, F (Fin.cons false default) x) * star (𝔼 x, F (Fin.cons true default) x) :=
  expect_crossDerivative _ _

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H]

theorem mixedCubeProduct_crossDerivative {j : ℕ} (F G : (Fin j → Bool) → H → ℂ)
    (h : H) (hs : Fin j → H) (x : H) :
    mixedCubeProduct (fun ω ↦ crossDerivative (F ω) (G ω) h) hs x =
      mixedCubeProduct F hs x * star (mixedCubeProduct G hs (x + h)) := by
  simp only [mixedCubeProduct, crossDerivative, map_mul, conjugationPower_star,
    Finset.prod_mul_distrib]
  change _ = _ * (starRingEnd ℂ) _
  rw [map_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro ω hω
  congr 3
  abel

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

omit [Fintype H] in
theorem mixedCubeProduct_indicator (j : ℕ) (Q : Finset H) (hs : Fin j → H) (x : H) :
    mixedCubeProduct (fun _ ↦ restrictTo Q (fun _ ↦ 1)) hs x =
      if ∀ ω : Fin j → Bool, x + cubeShift hs ω ∈ Q then 1 else 0 := by
  have hv (ω : Fin j → Bool) :
      conjugationPower (booleanWeight ω) (restrictTo Q (fun _ ↦ 1) (x + cubeShift hs ω)) =
        if x + cubeShift hs ω ∈ Q then 1 else 0 := by
    by_cases hω : x + cubeShift hs ω ∈ Q <;> simp [restrictTo, hω]
  simp only [mixedCubeProduct, hv]
  by_cases hall : ∀ ω : Fin j → Bool, x + cubeShift hs ω ∈ Q
  · simp [hall]
  · rw [if_neg hall]
    obtain ⟨ω, hω⟩ := not_forall.mp hall
    exact Finset.prod_eq_zero (Finset.mem_univ ω) (if_neg hω)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem derivative_correlations_force_additive_quadruples
    (f : G → ℂ) (g : G → G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    (𝔼 h, ‖𝔼 x, multiplicativeDerivative f h x * star (g h x)‖) ^ 4 ≤
      𝔼 a, 𝔼 h, 𝔼 k, additiveQuadrupleCorrelation g a h k := by
  let C (a : G) := 𝔼 h, ‖𝔼 x, multiplicativeDerivative f a x *
    (star (g h x) * g (h - a) (x + a))‖
  have hfirst : (𝔼 h, ‖𝔼 x, multiplicativeDerivative f h x * star (g h x)‖) ^ 2 ≤
      𝔼 a, C a := by
    have hcs := shifted_test_cauchy_schwarz f (fun x => star (f x))
      (fun h x => star (g h x)) (M := 1) (by simpa only [norm_star] using hf)
    have hreindex : (𝔼 h, 𝔼 k, ‖𝔼 x, f x * star (f (x + h - k)) *
        star (g h x) * g k (x + h - k)‖) = 𝔼 a, C a := by
      calc
        _ = 𝔼 h, 𝔼 a, ‖𝔼 x, multiplicativeDerivative f a x *
            (star (g h x) * g (h - a) (x + a))‖ := by
          apply Finset.expect_congr rfl
          intro h _
          apply Fintype.expect_equiv (Equiv.subLeft h)
          intro k
          simp only [Equiv.subLeft_apply, sub_sub_cancel, multiplicativeDerivative,
            ← add_sub_assoc, mul_assoc]
        _ = _ := Finset.expect_comm _ _ _
    rw [← hreindex]
    simpa only [one_pow, one_mul, star_star, multiplicativeDerivative, mul_assoc] using hcs
  have hsecond (a : G) : C a ^ 2 ≤
      𝔼 h, 𝔼 k, additiveQuadrupleCorrelation g a h k := by
    have hcs := finite_absolute_cauchy_schwarz (multiplicativeDerivative f a)
      (fun h x => star (g h x) * g (h - a) (x + a))
      (multiplicativeDerivative_norm_le_one f hf a)
    simpa only [one_pow, one_mul, C, additiveQuadrupleCorrelation, star_mul,
      star_star, mul_assoc, mul_comm, mul_left_comm] using hcs
  calc
    _ = ((𝔼 h, ‖𝔼 x, multiplicativeDerivative f h x * star (g h x)‖) ^ 2) ^ 2 := by ring
    _ ≤ (𝔼 a, C a) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) hfirst 2
    _ ≤ 𝔼 a, C a ^ 2 := expect_square_le C
    _ ≤ _ := Finset.expect_le_expect (fun a _ => hsecond a)

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

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

noncomputable def supportedCubeEquiv {φ : A →+ B} {Q : Set A}
    (hφ : ReflectsPairSums φ Q) (j : ℕ) : SupportedCube j Q ≃ SupportedCube j (φ '' Q) :=
  Equiv.ofBijective (SupportedCube.map φ) ⟨SupportedCube.map_injective hφ.injOn j,
    SupportedCube.map_surjective hφ j⟩

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {A : Type*} [AddCommGroup A]

section FiniteAmbient

variable [Fintype A] [DecidableEq A]

theorem supportedCubeSum_eq_sum (j : ℕ) (Q : Finset A) (F : (Fin j → Bool) → A → ℂ) :
    supportedCubeSum j (Q : Set A) F =
      ∑ p ∈ groupCubeSet j Q, mixedCubeProduct F p.1 p.2 := by
  exact (Finset.sum_subtype (groupCubeSet j Q) (fun p ↦ by simp [groupCubeSet])
    (fun p ↦ mixedCubeProduct F p.1 p.2)).symm

omit [Fintype A] in
theorem mixedCubeProduct_restrictTo {j : ℕ} (Q : Finset A)
    (F : (Fin j → Bool) → A → ℂ) (hs : Fin j → A) (x : A) :
    mixedCubeProduct (fun ω ↦ restrictTo Q (F ω)) hs x =
      if ∀ ω : Fin j → Bool, x + cubeShift hs ω ∈ Q then mixedCubeProduct F hs x else 0 := by
  classical
  by_cases hall : ∀ ω : Fin j → Bool, x + cubeShift hs ω ∈ Q
  · rw [if_pos hall]
    unfold mixedCubeProduct
    apply Finset.prod_congr rfl
    intro ω hω
    simp only [restrictTo, if_pos (hall ω)]
  · rw [if_neg hall]
    obtain ⟨ω, hω⟩ := not_forall.mp hall
    unfold mixedCubeProduct
    apply Finset.prod_eq_zero (Finset.mem_univ ω)
    simp only [restrictTo, if_neg hω, map_zero]

end FiniteAmbient

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

theorem mixedCubeProduct_imageExtension {φ : A →+ B} {Q : Finset A}
    (hi : Set.InjOn φ (Q : Set A)) {j : ℕ} (F : (Fin j → Bool) → A → ℂ)
    (p : SupportedCube j (Q : Set A)) :
    mixedCubeProduct (fun ω ↦ imageExtension φ Q (F ω))
      (fun i ↦ φ (p.val.1 i)) (φ p.val.2) = mixedCubeProduct F p.val.1 p.val.2 := by
  unfold mixedCubeProduct
  apply Finset.prod_congr rfl
  intro ω hω
  rw [← map_cubeShift, ← map_add]
  exact congrArg (conjugationPower (booleanWeight ω))
    (imageExtension_apply hi (F ω) (p.property ω))

variable [Fintype B] [DecidableEq B]

omit [Fintype B] [DecidableEq B] in
theorem supportedCubeSum_imageExtension {φ : A →+ B} {Q : Finset A}
    (hφ : ReflectsPairSums φ (Q : Set A)) (j : ℕ) (F : (Fin j → Bool) → A → ℂ) :
    supportedCubeSum j (φ '' (Q : Set A)) (fun ω ↦ imageExtension φ Q (F ω)) =
      supportedCubeSum j (Q : Set A) F := by
  classical
  symm
  apply Fintype.sum_equiv (supportedCubeEquiv hφ j)
  intro p
  exact (mixedCubeProduct_imageExtension hφ.injOn F p).symm

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

variable [Fintype B] [DecidableEq B]

theorem card_supportedCube_image {φ : A →+ B} {Q : Finset A}
    (hφ : ReflectsPairSums φ (Q : Set A)) (j : ℕ) :
    Nat.card (SupportedCube j (Q : Set A)) = groupCubeCount j (Q.image φ) := by
  classical
  rw [Nat.card_congr (supportedCubeEquiv hφ j)]
  simpa only [Finset.coe_image] using card_supportedCube j (Q.image φ)

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

noncomputable def integerBoxGowersNorm (T : ι → ℕ) (j : ℕ) (f : (ι → ℤ) → ℂ) : ℝ :=
  finiteSupportGowersNorm j (integerBox T) f

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductCutoffLipschitz
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff BigOperators

noncomputable def scalarCubeCutoffWeight {α : Type*} [Fintype α] [DecidableEq α]
    (b : (Option α → ℝ) → ℝ) (a : Option α → ℝ) : ℝ := scalarCubeDomainDensity α * b a

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.DensityMixtureAELaw
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem realDensityMeasure_pi {D : Type*} [Fintype D] {E : D → Type*}
    [∀ d, MeasurableSpace (E d)] (μ : ∀ d, Measure (E d)) [∀ d, SigmaFinite (μ d)]
    (f : ∀ d, E d → ℝ) (hf : ∀ d, Integrable (f d) (μ d)) (hf0 : ∀ d x, 0 ≤ f d x) :
    Measure.pi (fun d => realDensityMeasure (μ d) (f d)) =
      realDensityMeasure (Measure.pi μ) (tensorCutoffWeight f) := by
  let : ∀ d, IsFiniteMeasure (realDensityMeasure (μ d) (f d)) :=
    fun d => realDensityMeasure_finite (μ d) (f d) (hf d) (hf0 d)
  apply Measure.pi_eq
  intro s hs
  have hfi : Integrable (tensorCutoffWeight f) (Measure.pi μ) := Integrable.fintype_prod_dep hf
  rw [realDensityMeasure_apply _ (tensorCutoffWeight f) hfi
    (tensorCutoffWeight_nonneg f hf0) (MeasurableSet.univ_pi hs)]
  have hi : (∫ x in Set.univ.pi s, tensorCutoffWeight f x ∂Measure.pi μ) =
      ∏ d, ∫ y in s d, f d y ∂μ d := by
    rw [Measure.restrict_pi_pi]
    exact integral_fintype_prod_eq_prod f
  rw [hi, ENNReal.ofReal_prod_of_nonneg (fun d _ => integral_nonneg (hf0 d))]
  apply Finset.prod_congr rfl
  intro d _
  exact (realDensityMeasure_apply (μ d) (f d) (hf d) (hf0 d) (hs d)).symm

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem independentIntegerLaw_density {J : Type*} [Fintype J] (p : J → PMF ℤ) :
    Measure.pi (fun j => (p j).toMeasure) =
      realDensityMeasure (Measure.pi (fun _ : J => (Measure.count : Measure ℤ)))
        (fun z => ∏ j, (p j (z j)).toReal) := by
  simp_rw [pmf_realDensity_count]
  exact realDensityMeasure_pi (fun _ => Measure.count) (fun j z => (p j z).toReal)
    (fun j => pmf_real_integrable (p j)) (fun _ _ => ENNReal.toReal_nonneg)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Function _root_.Set

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem embeddingDensity_measurable (e : X → Y) (he : MeasurableEmbedding e)
    (c : ℝ) (f : X → ℝ) (hf : Measurable f) : Measurable (embeddingDensity e c f) :=
  measurable_const.mul (he.measurable_extend hf measurable_const)

omit [MeasurableSpace X] [MeasurableSpace Y] in
theorem embeddingDensity_bound (e : X → Y) (he : Function.Injective e)
    {c B : ℝ} (hB : 0 ≤ B) (f : X → ℝ) (hf : ∀ x, c * f x ≤ B) (y : Y) :
    embeddingDensity e c f y ≤ B := by
  by_cases hy : y ∈ Set.range e
  · obtain ⟨x, rfl⟩ := hy
    rw [embeddingDensity_apply e he]
    exact hf x
  · rw [embeddingDensity_zero e c f y hy]
    exact hB

theorem embeddingDensity_law (e : X → Y) (he : MeasurableEmbedding e)
    (μ : Measure X) (ν : Measure Y) {c : ℝ} (hc : 0 ≤ c)
    (hmap : Measure.map e μ = ENNReal.ofReal c • ν.restrict (Set.range e)) (f : X → ℝ) :
    Measure.map e (realDensityMeasure μ f) = realDensityMeasure ν (embeddingDensity e c f) := by
  rw [realDensityMeasure_map_embedding e he, hmap, realDensityMeasure_smul_real _ _ hc]
  apply realDensityMeasure_restrict_support ν _ he.measurableSet_range
  exact embeddingDensity_zero e c f

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

theorem productDensity_pushforward {J : Type*} [Fintype J] {X Y : J → Type*}
    [∀ j, MeasurableSpace (X j)] [∀ j, MeasurableSpace (Y j)]
    (μ : ∀ j, Measure (X j)) (ν : ∀ j, Measure (Y j)) [∀ j, SigmaFinite (ν j)]
    (q : ∀ j, X j → Y j) (hq : ∀ j, Measurable (q j)) (f : ∀ j, Y j → ℝ)
    (hfi : ∀ j, Integrable (f j) (ν j)) (hf0 : ∀ j y, 0 ≤ f j y)
    (hlaw : ∀ j, Measure.map (q j) (μ j) = realDensityMeasure (ν j) (f j)) :
    Measure.map (fun x j => q j (x j)) (Measure.pi μ) =
      realDensityMeasure (Measure.pi ν) (tensorCutoffWeight f) := by
  have houtput : ∀ j, SigmaFinite (Measure.map (q j) (μ j)) := by
    intro j
    rw [hlaw j]
    let : IsFiniteMeasure (realDensityMeasure (ν j) (f j)) :=
      realDensityMeasure_finite (ν j) (f j) (hfi j) (hf0 j)
    exact IsFiniteMeasure.toSigmaFinite _
  rw [Measure.pi_map_pi (μ := μ) (f := q) (hμ := houtput) (fun j => (hq j).aemeasurable)]
  simp_rw [hlaw]
  exact realDensityMeasure_pi ν f hfi hf0

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.RestrictedComplexChartDensityComparison
namespace OAI

section

namespace Erdos3

open MeasureTheory _root_.Set

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

omit [MeasurableSpace X] [MeasurableSpace Y] in
theorem restrictedChartDensity_apply (q : X → Y) (S : Set X) (c : ℝ) (f : X → ℝ)
    (hinj : Set.InjOn q S) {x : X} (hx : x ∈ S) :
    restrictedChartDensity q S c f (q x) = c * f x :=
  embeddingDensity_apply _ (fun a b h => Subtype.ext (hinj a.property b.property h)) c _ ⟨x,hx⟩

omit [MeasurableSpace X] [MeasurableSpace Y] in
theorem restrictedChartDensity_zero (q : X → Y) (S : Set X) (c : ℝ) (f : X → ℝ)
    {y : Y} (hy : y ∉ q '' S) : restrictedChartDensity q S c f y = 0 := by
  apply embeddingDensity_zero
  rintro ⟨x, rfl⟩
  exact hy ⟨x.val, x.property, rfl⟩

theorem subtype_density_map (μ : Measure X) {S : Set X} (hS : MeasurableSet S)
    (f : X → ℝ) (hf : ∀ x ∉ S, f x = 0) :
    Measure.map ((↑) : S → X)
      (realDensityMeasure (Measure.comap ((↑) : S → X) μ) (fun x => f x.val)) =
      realDensityMeasure μ f := by
  have hmap : Measure.map ((↑) : S → X) (Measure.comap ((↑) : S → X) μ) =
      ENNReal.ofReal (1 : ℝ) • μ.restrict (Set.range ((↑) : S → X)) := by
    simpa only [ENNReal.ofReal_one, one_smul, Subtype.range_coe] using map_comap_subtype_coe hS μ
  have h := embeddingDensity_law ((↑) : S → X) (MeasurableEmbedding.subtype_coe hS)
    (Measure.comap ((↑) : S → X) μ) μ zero_le_one hmap (fun x => f x.val)
  have he : embeddingDensity ((↑) : S → X) 1 (fun x => f x.val) = f := by
    funext x
    by_cases hx : x ∈ S
    · have hi := embeddingDensity_apply ((↑) : S → X) Subtype.coe_injective 1 (fun x => f x.val) ⟨x,hx⟩
      simpa only [one_mul] using hi
    · rw [embeddingDensity_zero _ _ _ x (by simpa only [Subtype.range_coe] using hx), hf x hx]
  rwa [he] at h

theorem restrictedChartDensity_law (q : X → Y) (hq : Measurable q)
    {S : Set X} (hS : MeasurableSet S)
    (he : MeasurableEmbedding (fun x : S => q x.val))
    (μ : Measure X) (ν : Measure Y) {c : ℝ} (hc : 0 ≤ c)
    (hmap : Measure.map q (μ.restrict S) = ENNReal.ofReal c • ν.restrict (q '' S))
    (f : X → ℝ) (hf : ∀ x ∉ S, f x = 0) :
    Measure.map q (realDensityMeasure μ f) = realDensityMeasure ν (restrictedChartDensity q S c f) := by
  let μS := Measure.comap ((↑) : S → X) μ
  have hrange : Set.range (fun x : S => q x.val) = q '' S := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.val, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x,hx⟩, rfl⟩
  have hm : Measure.map (fun x : S => q x.val) μS =
      ENNReal.ofReal c • ν.restrict (Set.range (fun x : S => q x.val)) := by
    rw [hrange]
    change Measure.map (q ∘ ((↑) : S → X)) μS = _
    rw [← Measure.map_map hq measurable_subtype_coe]
    change Measure.map q (Measure.map ((↑) : S → X) (Measure.comap ((↑) : S → X) μ)) = _
    rw [map_comap_subtype_coe hS μ, hmap]
  rw [← subtype_density_map μ hS f hf, Measure.map_map hq measurable_subtype_coe]
  exact embeddingDensity_law _ he μS ν hc hm _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineCoefficientLaw
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff

theorem affineProbabilityProfile_le (c : ℝ) {w : ℝ} (hw : 0 < w) (x : ℝ) :
    affineProbabilityProfile c w x ≤ w⁻¹ := by
  exact (mul_le_mul_of_nonneg_left (smoothProbabilityProfile_range _).2
    (inv_nonneg.mpr hw.le)).trans_eq (mul_one _)

theorem affineProbabilityProfile_integral (c : ℝ) {w : ℝ} (hw : 0 < w) :
    (∫ x, affineProbabilityProfile c w x) = 1 := by
  change (∫ x, w⁻¹ * smoothProbabilityProfile ((x-c)/w)) = 1
  rw [integral_const_mul,
    integral_sub_right_eq_self (fun x => smoothProbabilityProfile (x/w)) c,
    Measure.integral_comp_div, smoothProbabilityProfile_integral, smul_eq_mul,
    mul_one, abs_of_pos hw, inv_mul_cancel₀ hw.ne']

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.InactiveShortLogBounds
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem mixedInterpolation_constants_exp_bounds {I : Type*} [Fintype I] (n : ℕ)
    {δ B L : ℝ≥0} {P W Q : ℝ} (hP : 0 ≤ P) (hW : 0 ≤ W) (hQ : 0 ≤ Q)
    (hI : (Fintype.card I : ℝ) ≤ P) (hn : (n : ℝ) ≤ P)
    (hδ : ((δ⁻¹ : ℝ≥0) : ℝ) ≤ Real.exp W)
    (hB : (B : ℝ) ≤ Real.exp Q) (hL : (L : ℝ) ≤ Real.exp Q)
    (hA : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) :
    ((δ⁻¹^Fintype.card I * B^n : ℝ≥0) : ℝ) ≤ Real.exp (P*(W+Q)) ∧
      ((δ⁻¹^Fintype.card I * (n*L*B^n) + B^n*affineProductProfileLip I δ : ℝ≥0) : ℝ) ≤
        Real.exp ((2*P+1)*(W+Q)+3*P+1) := by
  have hδ0 : 0 ≤ ((δ⁻¹ : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
  have hd := pow_le_exp_mul_of_le_exp hδ0 hδ hW (Fintype.card I) hI
  have hb := pow_le_exp_mul_of_le_exp B.coe_nonneg hB hQ n hn
  have hd1 := pow_le_exp_mul_of_le_exp hδ0 hδ hW (Fintype.card I + 1)
    (by push_cast; linarith : ((Fintype.card I + 1 : ℕ) : ℝ) ≤ P+1)
  have hIE : (Fintype.card I : ℝ) ≤ Real.exp P := hI.trans (by linarith [Real.add_one_le_exp P])
  have hnE : (n : ℝ) ≤ Real.exp P := hn.trans (by linarith [Real.add_one_le_exp P])
  constructor
  · simp only [NNReal.coe_mul, NNReal.coe_pow]
    calc
      _ ≤ Real.exp (P*W) * Real.exp (P*Q) := by gcongr
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  · simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_natCast,
      affineProductProfileLip]
    have hfirst : (((δ⁻¹ : ℝ≥0) : ℝ)^Fintype.card I) * ((n : ℝ)*L*(B : ℝ)^n) ≤
        Real.exp (P*W+P+Q+P*Q) := by
      calc
        _ ≤ Real.exp (P*W) * (Real.exp P * Real.exp Q * Real.exp (P*Q)) := by gcongr
        _ = _ := by rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have hsecond : (B : ℝ)^n * ((Fintype.card I : ℝ)*probabilityProfileLipschitz*
        ((δ⁻¹ : ℝ≥0) : ℝ)^(Fintype.card I+1)) ≤ Real.exp (P*Q+2*P+(P+1)*W) := by
      calc
        _ ≤ Real.exp (P*Q) * (Real.exp P * Real.exp P * Real.exp ((P+1)*W)) := by gcongr
        _ = _ := by rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have hsum := add_le_exp_add_one (by positivity) (by positivity) hfirst hsecond
    exact hsum.trans_eq (congrArg Real.exp (by ring))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerRowInterpolationMixture
namespace OAI

section

namespace Erdos3

open scoped ContDiff

theorem normalizedIntegerInterpolation_range (K c δ : ℝ) (hK : 0 < K) (hδ : 0 < δ)
    (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ δ * K) (u : ℝ) :
    0 ≤ normalizedIntegerInterpolation K c δ u ∧
      normalizedIntegerInterpolation K c δ u ≤ 2 / δ := by
  have hZ := shiftedSmoothSampleSum_pos (c * K) hlarge
  have hlo := (shiftedSmoothSampleSum_bounds (c * K) hlarge).1
  constructor
  · exact div_nonneg (mul_nonneg hK.le (smoothProbabilityProfile_range _).1) hZ.le
  · calc
      _ ≤ K / shiftedSmoothSampleSum (c * K) (δ * K) :=
        div_le_div_of_nonneg_right
          (by simpa using mul_le_mul_of_nonneg_left (smoothProbabilityProfile_range ((u-c)/δ)).2 hK.le)
          hZ.le
      _ ≤ 2 / δ := (div_le_div_iff₀ hZ hδ).mpr (by nlinarith)

end Erdos3

end

section

namespace Erdos3

theorem normalizedIntegerInterpolation_difference (K c δ : ℝ) (hK : 0 < K) (hδ : 0 < δ)
    (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ δ * K) (x y : ℝ) :
    |normalizedIntegerInterpolation K c δ x - normalizedIntegerInterpolation K c δ y| ≤
      (2 * (probabilityProfileLipschitz : ℝ) / δ ^ 2) * |x - y| := by
  have hZ := shiftedSmoothSampleSum_pos (c * K) hlarge
  have hlo := (shiftedSmoothSampleSum_bounds (c * K) hlarge).1
  have hratio : K / shiftedSmoothSampleSum (c * K) (δ * K) ≤ 2 / δ :=
    (div_le_div_iff₀ hZ hδ).mpr (by nlinarith)
  have hprof := smoothProbabilityProfile_lipschitz.dist_le_mul ((x-c)/δ) ((y-c)/δ)
  rw [Real.dist_eq, Real.dist_eq, ← sub_div, sub_sub_sub_cancel_right, abs_div, abs_of_pos hδ] at hprof
  have he : normalizedIntegerInterpolation K c δ x - normalizedIntegerInterpolation K c δ y =
      (K / shiftedSmoothSampleSum (c*K) (δ*K)) *
        (smoothProbabilityProfile ((x-c)/δ) - smoothProbabilityProfile ((y-c)/δ)) := by
    unfold normalizedIntegerInterpolation
    ring
  rw [he, abs_mul, abs_of_pos (div_pos hK hZ)]
  calc
    _ ≤ (K / shiftedSmoothSampleSum (c*K) (δ*K)) *
        ((probabilityProfileLipschitz : ℝ) * (|x-y| / δ)) :=
      mul_le_mul_of_nonneg_left hprof (div_nonneg hK.le hZ.le)
    _ ≤ (2 / δ) * ((probabilityProfileLipschitz : ℝ) * (|x-y| / δ)) :=
      mul_le_mul_of_nonneg_right hratio (by positivity)
    _ = _ := by ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.EuclideanCoefficientTorus
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

variable {K : Type*} {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

instance euclideanCoefficientLayers_borel [Fintype K] :
    BorelSpace (EuclideanCoefficientLayers (K := K) U) := by
  let : ∀ j, BorelSpace (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup) :=
    fun _ => QuotientAddGroup.borelSpace
  let : ∀ j, BorelSpace (BoundedCoefficientExponent K (j.val + 1) → euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup) :=
    fun _ => Pi.borelSpace
  exact Pi.borelSpace

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.MixedDensityInterpolation
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

noncomputable def mixedCoefficientLaw {I J : Type*} [Fintype I] [Fintype J]
    (c w : I → ℝ) (p : J → PMF ℤ) : Measure ((I → ℝ) × (J → ℤ)) :=
  (Measure.pi (fun i => affineCoefficientMeasure (c i) (w i))).prod
    (Measure.pi (fun j => (p j).toMeasure))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def constantCoefficientDensity {I J : Type*} [Fintype I] [Fintype J]
    (w : I → ℝ) (K δ : J → ℝ) (hK : ∀ j, 0 < K j) (hδ : ∀ j, 0 < δ j) :
    ((I → ℝ) × (J → ℤ)) → ℝ :=
  mixedCoefficientDensity (fun _ => 0) w (fun j => constantIntegerPMF (K j) (δ j) (hK j) (hδ j))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MixedCoefficientSmallSupport
namespace OAI

section

namespace Erdos3

open Module Submodule _root_.Set

variable {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}

theorem basisAxisScale_cast_pos {E J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (b : Basis J ℝ E) (j : J) : (0 : ℝ) < basisAxisScale b j :=
  Nat.cast_pos.mpr (basisAxisScale_pos b j)

noncomputable def latticeConstantMass (W : Submodule ℝ (EuclideanSpace ℝ D))
    (b : Basis (Fin n) ℝ Wᗮ) (δ : Fin n → ℝ) (hδ : ∀ j, 0 < δ j) : Fin n → PMF ℤ :=
  fun j => constantIntegerPMF (basisAxisScale b j) (δ j) (basisAxisScale_cast_pos b j) (hδ j)

end Erdos3

end

section

namespace Erdos3

open Module Submodule
open scoped BigOperators

theorem normalizedMixedPoint_small {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}
    (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ) (o : OrthonormalBasis I ℝ W)
    {C R : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hchart : ∀ p, ‖(normalizedOrthogonalChart W b).symm p‖ ≤ C * ‖p‖)
    (hsmall : C * ((Fintype.card I : ℝ) + 1) * R ≤ 1 / 4)
    (x : (I → ℝ) × (Fin n → ℤ))
    (hu : ∀ i, |x.1 i| ≤ R) (hz : ∀ i, |(x.2 i : ℝ) / basisAxisScale b i| ≤ R) :
    normalizedLatticePoint W b (orthonormalMixedChart o x) ∈ standardLatticeSmallBox D := by
  have hu' : ‖x.1‖ ≤ R := (pi_norm_le_iff_of_nonneg hR).mpr (by simpa only [Real.norm_eq_abs] using hu)
  have hz' : ‖fun i => (x.2 i : ℝ) / basisAxisScale b i‖ ≤ R :=
    (pi_norm_le_iff_of_nonneg hR).mpr (by simpa only [Real.norm_eq_abs] using hz)
  have ho : ‖orthonormalChart o x.1‖ ≤ (Fintype.card I : ℝ) * R :=
    (orthonormalChart_norm_le o x.1).trans (mul_le_mul_of_nonneg_left hu' (Nat.cast_nonneg _))
  have hp : ‖(orthonormalChart o x.1, fun i => (x.2 i : ℝ) / basisAxisScale b i)‖ ≤
      ((Fintype.card I : ℝ) + 1) * R := by
    rw [Prod.norm_def]
    apply max_le <;> nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card I)]
  have hn : ‖normalizedLatticePoint W b (orthonormalMixedChart o x)‖ ≤ 1 / 4 := by
    apply (hchart _).trans
    exact (mul_le_mul_of_nonneg_left hp hC).trans (by simpa only [mul_assoc] using hsmall)
  intro d
  have hd := PiLp.norm_apply_le (normalizedLatticePoint W b (orthonormalMixedChart o x)) d
  rw [Real.norm_eq_abs] at hd
  exact (hd.trans hn).trans_lt (by norm_num)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ScaledArrayLaw
namespace OAI

section

namespace Erdos3

open Module Submodule _root_.Set

theorem restrictedChartDensity_recover {X Y : Type*} (q : X → Y) (S : Set X)
    (c : ℝ) (f : X → ℝ) (hinj : Set.InjOn q S) {y : Y}
    (hy : restrictedChartDensity q S c f y ≠ 0) :
    ∃ x, x ∈ S ∧ q x = y ∧ f x ≠ 0 := by
  have hm : y ∈ q '' S := by
    by_contra hn
    exact hy (restrictedChartDensity_zero q S c f hn)
  obtain ⟨x, hx, rfl⟩ := hm
  refine ⟨x, hx, rfl, ?_⟩
  rw [restrictedChartDensity_apply q S c f hinj hx] at hy
  exact (mul_ne_zero_iff.mp hy).2

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedShortAxis
namespace OAI

section

namespace Erdos3

theorem allocatedArrayWidths_floor {I J V : Type*} [Fintype J]
    (e : J → V →₀ ℕ) (T : V → ℝ) (hT : ∀ v, 0 < T v)
    (Pc : I → Finset J) (j₀ : J) {R σ : ℝ} (hR : 0 < R) (hσ : 0 < σ)
    {L s : ℕ} (hL : 0 < L) (hTL : ∀ v, T v ≤ L)
    (he : ∀ j, (e j).sum (fun _ n => n) ≤ s) (i : I) (j : J) :
    allocatedWidthFloor R σ L s (Fintype.card J) ≤ allocatedArrayWidths e T Pc j₀ R σ i j := by
  classical
  let a := min (R / 4)
    (min (principalProfileSize R (Fintype.card J) / 2) (tailProfileSize R σ (Fintype.card J)))
  have ha : 0 ≤ a := le_of_lt (lt_min (by positivity)
    (lt_min (div_pos (principalProfileSize_pos hR _) (by norm_num)) (tailProfileSize_pos hR hσ _)))
  have hprincipal : principalProfileSize R (Fintype.card J) ≤ principalProfileSize R (Pc i).card := by
    unfold principalProfileSize
    apply div_le_div_of_nonneg_left hR.le (by positivity)
    gcongr
    exact_mod_cast (Pc i).card_le_univ
  have haWidth : a ≤ coefficientProfileWidth (Pc i) j₀ (R / 4)
      (principalProfileSize R (Pc i).card) (tailProfileSize R σ (Fintype.card J)) j := by
    unfold coefficientProfileWidth
    split_ifs
    · exact min_le_left _ _
    · exact ((min_le_right _ _).trans (min_le_left _ _)).trans
        (div_le_div_of_nonneg_right hprincipal (by norm_num))
    · exact (min_le_right _ _).trans (min_le_right _ _)
  have hmono := monomialScale_le_uniform_pow T (fun v => (hT v).le)
    (by exact_mod_cast hL) hTL (e j) (he j)
  have hscale := monomialScale_pos T hT (e j)
  change a / (L : ℝ)^s ≤ coefficientProfileWidth (Pc i) j₀ (R / 4)
    (principalProfileSize R (Pc i).card) (tailProfileSize R σ (Fintype.card J)) j / monomialScale T (e j)
  exact (div_le_div_of_nonneg_left ha hscale hmono).trans
    (div_le_div_of_nonneg_right haWidth hscale.le)

end Erdos3

end

section

namespace Erdos3

theorem allocatedProfile_inverse_power_bounds (a : ℕ) {R σ X : ℝ}
    (hR : 0 < R) (hσ : 0 < σ) (hX : 8 ≤ X)
    (hRX : R⁻¹ ≤ X) (hσX : σ⁻¹ ≤ X) (haX : (a : ℝ) + 1 ≤ X) :
    (R / 4)⁻¹ ≤ X^2 ∧ (principalProfileSize R a)⁻¹ ≤ X^3 ∧
      (principalProfileSize R a / 2)⁻¹ ≤ X^4 ∧ (tailProfileSize R σ a)⁻¹ ≤ X^4 := by
  have hX0 : 0 ≤ X := by linarith
  have h2 : (2 : ℝ) ≤ X := by linarith
  have h4 : (4 : ℝ) ≤ X := by linarith
  have hp0 : 0 ≤ (principalProfileSize R a)⁻¹ := inv_nonneg.mpr (principalProfileSize_pos hR a).le
  have hprincipal : (principalProfileSize R a)⁻¹ ≤ X^3 := by
    unfold principalProfileSize
    rw [inv_div, div_eq_mul_inv]
    calc
      _ ≤ X * X * X := by gcongr
      _ = _ := by ring
  refine ⟨?_, hprincipal, ?_, ?_⟩
  · rw [inv_div, div_eq_mul_inv]
    calc
      _ ≤ X * X := by gcongr
      _ = _ := by ring
  · rw [inv_div, div_eq_mul_inv]
    calc
      _ ≤ X * X^3 := by gcongr
      _ = _ := by ring
  · unfold tailProfileSize
    rw [inv_div, div_eq_mul_inv, mul_inv_rev]
    calc
      _ ≤ X * X * (X * X) := by gcongr
      _ = _ := by ring

theorem allocatedWidthFloor_inverse_power_bound (L s m a : ℕ) (hs : s ≤ m)
    {R σ X : ℝ} (hR : 0 < R) (hσ : 0 < σ) (hX : 8 ≤ X)
    (hRX : R⁻¹ ≤ X) (hσX : σ⁻¹ ≤ X) (haX : (a : ℝ) + 1 ≤ X) (hLX : (L : ℝ) ≤ X) :
    (allocatedWidthFloor R σ L s a)⁻¹ ≤ X^(m+4) := by
  have hX1 : 1 ≤ X := by linarith
  have hX0 : 0 ≤ X := by linarith
  obtain ⟨hρ, _, hγ, hε⟩ := allocatedProfile_inverse_power_bounds a hR hσ hX hRX hσX haX
  have hmin : (min (R/4) (min (principalProfileSize R a / 2) (tailProfileSize R σ a)))⁻¹ ≤ X^4 :=
    inv_min_le_of_inv_le (hρ.trans (pow_le_pow_right₀ hX1 (by norm_num)))
      (inv_min_le_of_inv_le hγ hε)
  have hLs : (L : ℝ)^s ≤ X^m :=
    (pow_le_pow_left₀ (Nat.cast_nonneg _) hLX s).trans (pow_le_pow_right₀ hX1 hs)
  have hγ0 := (principalProfileSize_pos hR a).le
  have hε0 := (tailProfileSize_pos hR hσ a).le
  have hmin0 : 0 ≤ (min (R/4) (min (principalProfileSize R a / 2) (tailProfileSize R σ a)))⁻¹ := by
    positivity
  rw [allocatedWidthFloor, inv_div, div_eq_mul_inv]
  calc
    _ ≤ X^m * X^4 := by gcongr
    _ = _ := (pow_add _ _ _).symm

end Erdos3

end

section

namespace Erdos3

theorem allocatedProfile_inverse_exp_bounds (a : ℕ) {R σ P : ℝ}
    (hP : 0 ≤ P) (hR : 0 < R) (hσ : 0 < σ)
    (hRP : R⁻¹ ≤ Real.exp P) (hσP : σ⁻¹ ≤ Real.exp P) (haP : (a : ℝ) ≤ P) :
    (R / 4)⁻¹ ≤ Real.exp (4 * (P + 8)) ∧
      (principalProfileSize R a)⁻¹ ≤ Real.exp (4 * (P + 8)) ∧
      (principalProfileSize R a / 2)⁻¹ ≤ Real.exp (4 * (P + 8)) ∧
      (tailProfileSize R σ a)⁻¹ ≤ Real.exp (4 * (P + 8)) := by
  let X := Real.exp (P + 8)
  have hPX : Real.exp P ≤ X := Real.exp_le_exp.mpr (by linarith)
  have hX : 8 ≤ X := by dsimp [X]; linarith [Real.add_one_le_exp (P+8)]
  have hX1 : 1 ≤ X := by linarith
  have haX : (a : ℝ) + 1 ≤ X :=
    (by linarith [Real.add_one_le_exp P] : (a : ℝ) + 1 ≤ Real.exp P).trans hPX
  obtain ⟨hρ, hγ, hγ2, hε⟩ := allocatedProfile_inverse_power_bounds a hR hσ hX
    (hRP.trans hPX) (hσP.trans hPX) haX
  have he : X^4 = Real.exp (4*(P+8)) := by simp only [X, ← Real.exp_nat_mul, Nat.cast_ofNat]
  rw [← he]
  exact ⟨hρ.trans (pow_le_pow_right₀ hX1 (by norm_num)),
    hγ.trans (pow_le_pow_right₀ hX1 (by norm_num)), hγ2, hε⟩

theorem allocatedWidthFloor_inverse_exp_bound (L s m a : ℕ) (hs : s ≤ m)
    {R σ P : ℝ} (hP : 0 ≤ P) (hR : 0 < R) (hσ : 0 < σ)
    (hRP : R⁻¹ ≤ Real.exp P) (hσP : σ⁻¹ ≤ Real.exp P)
    (haP : (a : ℝ) ≤ P) (hLP : (L : ℝ) ≤ Real.exp P) :
    (allocatedWidthFloor R σ L s a)⁻¹ ≤ Real.exp (((m : ℝ)+4)*(P+8)) := by
  let X := Real.exp (P+8)
  have hPX : Real.exp P ≤ X := Real.exp_le_exp.mpr (by linarith)
  have hX : 8 ≤ X := by dsimp [X]; linarith [Real.add_one_le_exp (P+8)]
  have haX : (a : ℝ)+1 ≤ X :=
    (by linarith [Real.add_one_le_exp P] : (a : ℝ)+1 ≤ Real.exp P).trans hPX
  have h := allocatedWidthFloor_inverse_power_bound L s m a hs hR hσ hX
    (hRP.trans hPX) (hσP.trans hPX) haX (hLP.trans hPX)
  simpa only [X, ← Real.exp_nat_mul, Nat.cast_add, Nat.cast_ofNat] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PrincipalIntegerInterpolation
namespace OAI

section

namespace Erdos3

theorem principalIntegerInterpolation_range (K T γ : ℝ) (hK : 0 < K) (hT : 0 < T)
    (hγ : 0 < γ) (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ (γ / 2) * (K / T)) (x : ℝ) :
    0 ≤ principalIntegerInterpolation K T γ x ∧ principalIntegerInterpolation K T γ x ≤ 4*T/γ := by
  have h := normalizedIntegerInterpolation_range (K/T) (3*γ/2) (γ/2)
    (div_pos hK hT) (by positivity) hlarge (T*x)
  refine ⟨mul_nonneg hT.le h.1, ?_⟩
  exact (mul_le_mul_of_nonneg_left h.2 hT.le).trans_eq (by ring)

theorem principalIntegerInterpolation_difference (K T γ : ℝ) (hK : 0 < K) (hT : 0 < T)
    (hγ : 0 < γ) (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ (γ / 2) * (K / T)) (x y : ℝ) :
    |principalIntegerInterpolation K T γ x - principalIntegerInterpolation K T γ y| ≤
      (8 * (probabilityProfileLipschitz : ℝ) * T^2 / γ^2) * |x-y| := by
  have h := normalizedIntegerInterpolation_difference (K/T) (3*γ/2) (γ/2)
    (div_pos hK hT) (by positivity) hlarge (T*x) (T*y)
  rw [← mul_sub, abs_mul, abs_of_pos hT] at h
  unfold principalIntegerInterpolation
  rw [← mul_sub, abs_mul, abs_of_pos hT]
  exact (mul_le_mul_of_nonneg_left h hT.le).trans_eq (by ring)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerInterpolationExpBounds
namespace OAI

section

namespace Erdos3

theorem constantIntegerInterpolation_power_bounds {X ρ : ℝ}
    (hX : 8 ≤ X) (hA : (probabilityProfileLipschitz : ℝ) ≤ X)
    (hρ : 0 < ρ) (hρX : ρ⁻¹ ≤ X) :
    constantIntegerInterpolationCap ρ ≤ X^3 ∧ constantIntegerInterpolationLip ρ ≤ X^7 := by
  have hX0 : 0 ≤ X := by linarith
  have hX1 : 1 ≤ X := by linarith
  have h2 : (2 : ℝ) ≤ X := by linarith
  have hc : constantIntegerInterpolationCap ρ ≤ X^3 := by
    unfold constantIntegerInterpolationCap
    rw [div_eq_mul_inv]
    calc
      _ ≤ X * X * X := by gcongr
      _ = _ := by ring
  refine ⟨hc, ?_⟩
  unfold constantIntegerInterpolationLip
  apply max_le
  · have ht : 2 * (probabilityProfileLipschitz : ℝ) / ρ^2 ≤ X^4 := by
      rw [div_eq_mul_inv, ← inv_pow]
      calc
        _ ≤ X * X * X^2 := by gcongr
        _ = _ := by ring
    exact ht.trans (pow_le_pow_right₀ hX1 (by norm_num))
  · have hc0 : 0 ≤ constantIntegerInterpolationCap ρ := by
      unfold constantIntegerInterpolationCap
      positivity
    calc
      _ ≤ X * (X^3)^2 := by gcongr
      _ = _ := by ring

theorem principalAxisInterpolation_power_bounds (h L : ℕ) {X γ : ℝ}
    (hX : 8 ≤ X) (hA : (probabilityProfileLipschitz : ℝ) ≤ X)
    (hγ : 0 < γ) (hγX : γ⁻¹ ≤ X) (hL : (L : ℝ)^h ≤ X) :
    principalAxisInterpolationCap h L γ ≤ X^3 ∧ principalAxisInterpolationLip h L γ ≤ X^7 := by
  have hX0 : 0 ≤ X := by linarith
  have hX1 : 1 ≤ X := by linarith
  have h2 : (2 : ℝ) ≤ X := by linarith
  have h4 : (4 : ℝ) ≤ X := by linarith
  have hX3 : X ≤ X^3 := by simpa only [pow_one] using (pow_le_pow_right₀ hX1 (show 1 ≤ 3 by norm_num))
  constructor
  · unfold principalAxisInterpolationCap
    apply max_le
    · rw [div_eq_mul_inv]
      calc
        _ ≤ X * X * X := by gcongr
        _ = _ := by ring
    · exact hL.trans hX3
  · unfold principalAxisInterpolationLip
    apply max_le
    · have ht : 8 * (probabilityProfileLipschitz : ℝ) * ((L : ℝ)^h)^2 / γ^2 ≤ X^6 := by
        rw [div_eq_mul_inv, ← inv_pow]
        calc
          _ ≤ X * X * X^2 * X^2 := by gcongr
          _ = _ := by ring
      exact ht.trans (pow_le_pow_right₀ hX1 (by norm_num))
    · have ht : 2 * ((L : ℝ)^h)^2 ≤ X^3 := by
        calc
          _ ≤ X * X^2 := by gcongr
          _ = _ := by ring
      exact ht.trans (pow_le_pow_right₀ hX1 (by norm_num))

theorem tailAxisInterpolation_power_bounds (L s : ℕ) {X ε : ℝ}
    (hX : 8 ≤ X) (hA : (probabilityProfileLipschitz : ℝ) ≤ X)
    (hε : 0 < ε) (hεX : ε⁻¹ ≤ X) (hL : (L : ℝ)^s ≤ X) (hL1 : (L : ℝ)^(s+1) ≤ X) :
    tailAxisInterpolationCap L s ε ≤ X^3 ∧ tailAxisInterpolationLip L s ε ≤ X^7 := by
  have hX0 : 0 ≤ X := by linarith
  have hX1 : 1 ≤ X := by linarith
  have h2 : (2 : ℝ) ≤ X := by linarith
  have hX3 : X ≤ X^3 := by simpa only [pow_one] using (pow_le_pow_right₀ hX1 (show 1 ≤ 3 by norm_num))
  constructor
  · unfold tailAxisInterpolationCap
    apply max_le
    · rw [div_eq_mul_inv]
      calc
        _ ≤ X * X * X := by gcongr
        _ = _ := by ring
    · exact hL1.trans hX3
  · unfold tailAxisInterpolationLip
    apply max_le
    · have ht : 2 * (probabilityProfileLipschitz : ℝ) * ((L : ℝ)^s)^2 / ε^2 ≤ X^6 := by
        rw [div_eq_mul_inv, ← inv_pow]
        calc
          _ ≤ X * X * X^2 * X^2 := by gcongr
          _ = _ := by ring
      exact ht.trans (pow_le_pow_right₀ hX1 (by norm_num))
    · have ht : 2 * ((L : ℝ)^(s+1))^2 ≤ X^3 := by
        calc
          _ ≤ X * X^2 := by gcongr
          _ = _ := by ring
      exact ht.trans (pow_le_pow_right₀ hX1 (by norm_num))

theorem integerPolynomialInterpolation_power_bounds (h L s : ℕ) {X ρ γ ε : ℝ}
    (hX : 8 ≤ X) (hA : (probabilityProfileLipschitz : ℝ) ≤ X)
    (hρ : 0 < ρ) (hγ : 0 < γ) (hε : 0 < ε)
    (hρX : ρ⁻¹ ≤ X) (hγX : γ⁻¹ ≤ X) (hεX : ε⁻¹ ≤ X)
    (hLh : (L : ℝ)^h ≤ X) (hLs : (L : ℝ)^s ≤ X) (hLs1 : (L : ℝ)^(s+1) ≤ X) :
    integerPolynomialInterpolationCap h L s ρ γ ε ≤ X^3 ∧
      integerPolynomialInterpolationLip h L s ρ γ ε ≤ X^7 := by
  obtain ⟨hc, hl⟩ := constantIntegerInterpolation_power_bounds hX hA hρ hρX
  obtain ⟨pc, pl⟩ := principalAxisInterpolation_power_bounds h L hX hA hγ hγX hLh
  obtain ⟨tc, tl⟩ := tailAxisInterpolation_power_bounds L s hX hA hε hεX hLs hLs1
  exact ⟨max_le hc (max_le pc tc), max_le hl (max_le pl tl)⟩

end Erdos3

end

section

namespace Erdos3

theorem integerPolynomialInterpolation_exp_bounds (m h L s : ℕ)
    (hh : h ≤ m) (hs : s ≤ m) {P ρ γ ε : ℝ} (hP : 0 ≤ P)
    (hA : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) (hL : (L : ℝ) ≤ Real.exp P)
    (hρ : 0 < ρ) (hγ : 0 < γ) (hε : 0 < ε)
    (hρP : ρ⁻¹ ≤ Real.exp P) (hγP : γ⁻¹ ≤ Real.exp P) (hεP : ε⁻¹ ≤ Real.exp P) :
    integerPolynomialInterpolationCap h L s ρ γ ε ≤
        Real.exp (3 * integerInterpolationLogEnvelope m P) ∧
      integerPolynomialInterpolationLip h L s ρ γ ε ≤
        Real.exp (7 * integerInterpolationLogEnvelope m P) := by
  let Q := integerInterpolationLogEnvelope m P
  let X := Real.exp Q
  have hm0 := Nat.cast_nonneg (α := ℝ) m
  have hPQ : P ≤ Q := by dsimp [Q, integerInterpolationLogEnvelope]; nlinarith
  have hQ8 : 8 ≤ Q := by dsimp [Q, integerInterpolationLogEnvelope]; nlinarith
  have hX : 8 ≤ X := by dsimp [X]; linarith [Real.add_one_le_exp Q]
  have hPX : Real.exp P ≤ X := Real.exp_le_exp.mpr hPQ
  have hp (k : ℕ) (hk : k ≤ m + 1) : (L : ℝ)^k ≤ X := by
    calc
      _ ≤ (Real.exp P)^k := pow_le_pow_left₀ (Nat.cast_nonneg _) hL _
      _ = Real.exp ((k : ℝ) * P) := (Real.exp_nat_mul P k).symm
      _ ≤ X := by
        apply Real.exp_le_exp.mpr
        have hkr : (k : ℝ) ≤ (m : ℝ) + 1 := by exact_mod_cast hk
        have hmul := mul_le_mul_of_nonneg_right hkr hP
        dsimp [Q, integerInterpolationLogEnvelope]
        linarith
  have h := integerPolynomialInterpolation_power_bounds h L s hX (hA.trans hPX) hρ hγ hε
    (hρP.trans hPX) (hγP.trans hPX) (hεP.trans hPX) (hp h (by omega)) (hp s (by omega)) (hp (s+1) (by omega))
  simpa only [X, ← Real.exp_nat_mul, Nat.cast_ofNat, Q] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedScalarLogBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)

theorem allocatedLayerCenters_constant (j : Fin m) (i : I j) :
    allocatedLayerCenters B U b S j i (constantCoefficientSlot _ _) = 0 := by
  classical
  simp only [allocatedLayerCenters, allocatedArrayCenters, coefficientProfileCenter,
    if_neg (layerContinuousPrincipalSlots_not_constant B j i), zero_div]

theorem allocatedLayerWidths_constant (j : Fin m) (i : I j) :
    allocatedLayerWidths B U b S j i (constantCoefficientSlot _ _) = R j / 4 := by
  classical
  simp [allocatedLayerWidths, allocatedArrayWidths, coefficientProfileWidth,
    constantCoefficientSlot, monomialScale]

theorem allocatedLayerIntegerPMFs_constant (j : Fin m) (i : Fin (n j)) :
    allocatedLayerIntegerPMFs B U b hR hσ S j i (constantCoefficientSlot _ _) =
      latticeConstantMass (euclideanSubspace (U j)) (b j) (fun _ => R j / 4)
        (fun _ => div_pos (hR j) (by norm_num)) i := by
  classical
  simp only [allocatedLayerIntegerPMFs, allocatedProjectionPMFs,
    allocatedIntegerPolynomialCoordinatePMF, integerPolynomialCoordinatePMF,
    ite_true, latticeConstantMass]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

theorem allocatedLayerCommonCap_one_le (R σ : Fin m → ℝ) (L : ℕ) (j : Fin m) :
    1 ≤ allocatedLayerCommonCap (G := G) B R σ L j := le_add_of_nonneg_right (by positivity)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped BigOperators NNReal

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

theorem allocatedLayerIntegerInterpolation_exp_bounds (R σ : Fin m → ℝ) (L : ℕ) (j : Fin m)
    {P : ℝ} (hP : 0 ≤ P) (hR : 0 < R j) (hσ : 0 < σ j)
    (hRP : (R j)⁻¹ ≤ Real.exp P) (hσP : (σ j)⁻¹ ≤ Real.exp P)
    (hcount : (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ) ≤ P)
    (hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) (hLP : (L : ℝ) ≤ Real.exp P)
    (i : Fin (n j)) :
    allocatedLayerIntegerInterpolationCap (G := G) B R σ L j i ≤ Real.exp (allocatedScalarLog m P) ∧
      allocatedLayerIntegerInterpolationLip (G := G) B R σ L j i ≤ Real.exp (allocatedScalarLog m P) := by
  have hprincipalCount : ((layerIntegerPrincipalSlots (G := G) B j i).card : ℝ) ≤ P :=
    (Nat.cast_le.mpr (layerIntegerPrincipalSlots (G := G) B j i).card_le_univ).trans hcount
  have hp := allocatedProfile_inverse_exp_bounds _ hP hR hσ hRP hσP hprincipalCount
  have ht := allocatedProfile_inverse_exp_bounds _ hP hR hσ hRP hσP hcount
  have hQ : 0 ≤ 4*(P+8) := by positivity
  have hPQ : P ≤ 4*(P+8) := by linarith
  have he := Real.exp_le_exp.mpr hPQ
  have h := integerPolynomialInterpolation_exp_bounds (layerTailDegree m) (j.val+1) L (layerTailDegree m)
    (layerDegree_le_tailDegree j) le_rfl hQ (hAP.trans he) (hLP.trans he)
    (div_pos hR (by norm_num)) (principalProfileSize_pos hR _) (tailProfileSize_pos hR hσ _)
    hp.1 hp.2.1 ht.2.2.2
  have henv : 0 ≤ integerInterpolationLogEnvelope (layerTailDegree m) (4*(P+8)) := by
    unfold integerInterpolationLogEnvelope
    positivity
  refine ⟨h.1.trans (Real.exp_le_exp.mpr ?_), h.2⟩
  change 3 * integerInterpolationLogEnvelope (layerTailDegree m) (4*(P+8)) ≤
    7 * integerInterpolationLogEnvelope (layerTailDegree m) (4*(P+8))
  linarith

theorem allocatedLayerCommonInterpolation_exp_bounds (R σ : Fin m → ℝ) (L : ℕ) (j : Fin m)
    {P : ℝ} (hP : 0 ≤ P) (hR : 0 < R j) (hσ : 0 < σ j)
    (hRP : (R j)⁻¹ ≤ Real.exp P) (hσP : (σ j)⁻¹ ≤ Real.exp P)
    (hcount : (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ) ≤ P)
    (hn : (n j : ℝ) ≤ P) (hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (hLP : (L : ℝ) ≤ Real.exp P) :
    (allocatedLayerCommonCap (G := G) B R σ L j : ℝ) ≤ Real.exp (allocatedCommonLog m P) ∧
      (allocatedLayerCommonLip (G := G) B R σ L j : ℝ) ≤ Real.exp (allocatedCommonLog m P) := by
  have h := allocatedLayerIntegerInterpolation_exp_bounds B R σ L j hP hR hσ hRP hσP hcount hAP hLP
  have hcard : (Fintype.card (Fin (n j)) : ℝ) ≤ P := by simpa only [Fintype.card_fin] using hn
  have hc := sum_le_exp_of_card_and_uniform_bound
    (fun i => (Real.toNNReal (allocatedLayerIntegerInterpolationCap (G := G) B R σ L j i) : ℝ))
    (allocatedScalarLog_nonneg m hP) hcard (fun i => coe_toNNReal_le_exp (h i).1)
  have hl := sum_le_exp_of_card_and_uniform_bound
    (fun i => (Real.toNNReal (allocatedLayerIntegerInterpolationLip (G := G) B R σ L j i) : ℝ))
    (allocatedScalarLog_nonneg m hP) hcard (fun i => coe_toNNReal_le_exp (h i).2)
  constructor
  · simp only [allocatedLayerCommonCap, NNReal.coe_add, NNReal.coe_one, NNReal.coe_sum]
    exact one_add_le_exp_succ (by have h := allocatedScalarLog_nonneg m hP; positivity) hc
  · simp only [allocatedLayerCommonLip, NNReal.coe_sum]
    exact hl.trans (Real.exp_le_exp.mpr (by unfold allocatedCommonLog; linarith))

end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.EmptyLayerDetectionGeometry
namespace OAI

section

namespace Erdos3

open Module Submodule MeasureTheory
open scoped BigOperators NNReal

variable {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}

theorem euclideanFromCoordinates_lipschitz :
    LipschitzWith (Fintype.card D) (EuclideanSpace.equiv D ℝ).symm := by
  have hn (x : D → ℝ) : ‖(EuclideanSpace.equiv D ℝ).symm x‖ ≤ (Fintype.card D : ℝ) * ‖x‖ := by
    calc
      _ ≤ ∑ i, |x i| := euclidean_norm_le_sum_abs _
      _ ≤ ∑ _i : D, ‖x‖ := Finset.sum_le_sum (fun i _ => by
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i)
      _ = _ := by simp
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, ← map_sub, dist_eq_norm]
  exact hn (x - y)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoefficientAmbientCoordinates
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

variable {K : Type*} {m : ℕ} {J : Fin m → Type*}

def coefficientAmbientSlice (s : CoefficientSlot K m)
    (v : CoefficientAmbientIndex K J → UnitAddCircle) : J s.1 → UnitAddCircle :=
  fun i => v ⟨s, i⟩

variable [Fintype K] [∀ j, Fintype (J j)]

theorem coefficientAmbientSlice_lipschitz (s : CoefficientSlot K m) :
    LipschitzWith 1 (coefficientAmbientSlice (J := J) s) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul]
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro i
  exact dist_le_pi_dist x y ⟨s, i⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.JointPivotProfileBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem affineProfileLogBound_nonneg (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ affineProfileLogBound n t := by
  unfold affineProfileLogBound
  positivity

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.CanonicalConstantDensityBound
namespace OAI

section

namespace Erdos3

open MeasureTheory Module Submodule
open scoped BigOperators

theorem earlyConstantDensityCap_nonneg (a n : ℕ) {R V : ℝ} (hR : 0 < R) (hV : 0 ≤ V) :
    0 ≤ earlyConstantDensityCap a n R V := by
  unfold earlyConstantDensityCap
  positivity

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.CoefficientEvaluationTorus
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem constantCoefficientTorusMap_nonconstant {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (y : CoefficientTorus (K := Empty) U)
    (s : CoefficientSlot K m) (hs : s.2.val ≠ 0) :
    coefficientCoordinateTorus U (constantCoefficientTorusMap U y) s = 0 := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective (coefficientIntegerLattice U) y
  rw [constantCoefficientTorusMap_mk, coefficientCoordinateTorus_mk]
  have hzero : (fun _ : Unit => constantCoefficientArray (K := K) U x s) = 0 := by
    funext u
    simp [constantCoefficientArray, hs]
  rw [hzero, map_zero]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.CoefficientProductLaw
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

noncomputable def coefficientProductDensity {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    (f : ∀ s : CoefficientSlot K m, SubspaceArrayTorus Unit (U s.1) → ℝ)
    (x : CoefficientTorus (K := K) U) : ℝ := ∏ s, f s (coefficientCoordinateTorus U x s)

theorem coefficientProductDensity_nonneg {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    (f : ∀ s : CoefficientSlot K m, SubspaceArrayTorus Unit (U s.1) → ℝ)
    (hf : ∀ s x, 0 ≤ f s x) (x : CoefficientTorus (K := K) U) :
    0 ≤ coefficientProductDensity U f x := Finset.prod_nonneg (fun s _ => hf s _)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedFiberCap
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

noncomputable def nonconstantCoefficientFactor {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (f : ∀ s : CoefficientSlot K m, SubspaceArrayTorus Unit (U s.1) → ℝ)
    (s : CoefficientSlot K m) (x : SubspaceArrayTorus Unit (U s.1)) : ℝ :=
  if s.2.val = 0 then 1 else f s x

theorem constantCoefficientCap_product {K : Type*} [Fintype K] {m : ℕ} (C : Fin m → ℝ) :
    (∏ s : CoefficientSlot K m, if s.2.val = 0 then C s.1 else 1) = ∏ j, C j := by
  rw [Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro j _
  rw [Finset.prod_eq_single (zeroCoefficientExponent K (j.val + 1))]
  · simp [zeroCoefficientExponent]
  · intro d _ hd
    have hd0 : d.val ≠ 0 := fun he => hd (Subtype.ext he)
    simp [hd0]
  · simp

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.UnconditionedSpatialWidthBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem spatialTrimMargin_error_bound {I : Type*} [Fintype I] {τ : ℝ}
    (N : I → ℕ) (hN : ∀ i, 0 < N i) (hsize : ∀ i, 4 ≤ τ * (N i : ℝ)) :
    2 * (∑ i, 2 * (spatialTrimMargin τ N i : ℝ) / N i) ≤ 2 * (Fintype.card I : ℝ) * τ := by
  have hi (i : I) : 2 * (spatialTrimMargin τ N i : ℝ) / N i ≤ τ := by
    apply (div_le_iff₀ (show (0 : ℝ) < N i by exact_mod_cast hN i)).mpr
    linarith [spatialTrimMargin_bound N hsize i]
  calc
    _ ≤ 2 * ∑ _i : I, τ := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hi i)) (by norm_num)
    _ = _ := by simp [mul_assoc]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeSelectedCorrelators
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem exists_many_correlated_additive_quadruples
    (f : G → ℂ) (g : G → G → ℂ) (H : Finset G)
    (hf : ∀ x, ‖f x‖ ≤ 1) (hg : ∀ h x, ‖g h x‖ ≤ 1)
    (hzero : ∀ h, h ∉ H → ∀ x, g h x = 0)
    {alpha delta : ℝ} (halpha : 0 < alpha) (hdelta : 0 < delta)
    (hdense : alpha * Fintype.card G ≤ (H.card : ℝ))
    (hcorr : ∀ h ∈ H, delta ≤ ‖𝔼 x, multiplicativeDerivative f h x * star (g h x)‖) :
    ∃ Q : Finset (G × G × G), Q.Nonempty ∧
      (alpha * delta) ^ 4 / 2 * (Fintype.card G : ℝ) ^ 3 ≤ (Q.card : ℝ) ∧
      ∀ t ∈ Q, t.2.1 ∈ H ∧ t.2.1 - t.1 ∈ H ∧
        t.2.2 ∈ H ∧ t.2.2 - t.1 ∈ H ∧
        (alpha * delta) ^ 4 / 2 ≤ additiveQuadrupleCorrelation g t.1 t.2.1 t.2.2 := by
  classical
  have hcardG : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hindicator : (𝔼 h : G, if h ∈ H then delta else 0) =
      (H.card : ℝ) * delta / Fintype.card G := by
    rw [Fintype.expect_eq_sum_div_card]
    simp
  have hmean : alpha * delta ≤
      𝔼 h, ‖𝔼 x, multiplicativeDerivative f h x * star (g h x)‖ := by
    calc
      _ ≤ (H.card : ℝ) * delta / Fintype.card G := by
        apply (le_div_iff₀ hcardG).mpr
        nlinarith [mul_le_mul_of_nonneg_right hdense hdelta.le]
      _ = _ := hindicator.symm
      _ ≤ _ := by
        apply Finset.expect_le_expect
        intro h _
        split_ifs with hh
        · exact hcorr h hh
        · exact norm_nonneg _
  have hsplit : (𝔼 t : G × G × G, additiveQuadrupleCorrelation g t.1 t.2.1 t.2.2) =
      𝔼 a, 𝔼 h, 𝔼 k, additiveQuadrupleCorrelation g a h k := by
    simp only [← Finset.univ_product_univ, Finset.expect_product]
  have hquad : (alpha * delta) ^ 4 ≤
      𝔼 t : G × G × G, additiveQuadrupleCorrelation g t.1 t.2.1 t.2.2 := by
    rw [hsplit]
    exact (pow_le_pow_left₀ (mul_pos halpha hdelta).le hmean 4).trans
      (derivative_correlations_force_additive_quadruples f g hf)
  obtain ⟨Q, hQcard, hQ⟩ := exists_dense_level_set
    (fun t : G × G × G => additiveQuadrupleCorrelation g t.1 t.2.1 t.2.2)
    (by positivity : 0 ≤ (alpha * delta) ^ 4)
    (fun t => additiveQuadrupleCorrelation_le_one g hg t.1 t.2.1 t.2.2) hquad
  have hcards : (Fintype.card (G × G × G) : ℝ) = (Fintype.card G : ℝ) ^ 3 := by
    simp only [Fintype.card_prod, Nat.cast_mul]
    ring
  rw [hcards] at hQcard
  have hQnonempty : Q.Nonempty := by
    apply Finset.card_pos.mp
    have : (0 : ℝ) < (Q.card : ℝ) := lt_of_lt_of_le (by positivity) hQcard
    exact_mod_cast this
  refine ⟨Q, hQnonempty, hQcard, fun t ht => ?_⟩
  obtain ⟨h₁, h₂, h₃, h₄⟩ := additiveQuadrupleCorrelation_support g H hzero
    (lt_of_lt_of_le (by positivity) (hQ t ht))
  exact ⟨h₁, h₂, h₃, h₄, hQ t ht⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ActiveAveragedProfileComparison
namespace OAI

section

namespace Erdos3

open scoped NNReal

noncomputable def idealSiteLogBudget (m q : ℕ) (P : ℝ) : ℝ :=
  q+(m : ℝ)*P+affineProfileLogBound m P+P+1

theorem idealSiteLogBudget_bounds (m q : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ idealSiteLogBudget m q P ∧ P ≤ idealSiteLogBudget m q P ∧
    (m : ℝ)*P ≤ idealSiteLogBudget m q P ∧
    affineProfileLogBound m P+q ≤ idealSiteLogBudget m q P := by
  have hf := affineProfileLogBound_nonneg m hP
  have hm : 0 ≤ (m : ℝ)*P := by positivity
  unfold idealSiteLogBudget
  constructor
  · positivity
  constructor
  · linarith [Nat.cast_nonneg (α := ℝ) q]
  constructor <;> linarith [Nat.cast_nonneg (α := ℝ) q]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AnisotropicSpatialCapBudget
namespace OAI

section

namespace Erdos3

open BooleanCubeKernel

theorem anisotropicSpatialDensityCap_exp_bound {α G : Type*} [Fintype α] [Fintype G]
    (selection : α ↪ G) {M : ℕ} {P : ℝ} (hP : 0 ≤ P) (hM : 0 < M)
    (hMP : (M : ℝ) ≤ Real.exp P)
    (hα : (Fintype.card (Unit ⊕ α) : ℝ) ≤ P) (hG : (Fintype.card G : ℝ) ≤ P) :
    anisotropicSpatialDensityCap selection (1 / (M : ℝ)) ≤ Real.exp (anisotropicSpatialCapLog P) := by
  let j := Fintype.card (Unit ⊕ α)
  have hj2 : (j : ℝ) ^ 2 ≤ P ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hα 2
  have hκ : 0 < 1 / (M : ℝ) := one_div_pos.mpr (Nat.cast_pos.mpr hM)
  have hU : physicalSpatialInverseBound α (1 / (M : ℝ)) ≤ Real.exp (P ^ 2 + 2 * P) :=
    (physicalSpatialInverseBound_le_exp α hκ (by simpa only [one_div, inv_inv] using hMP)).trans
      (Real.exp_le_exp.mpr (by change (j : ℝ) ^ 2 + j + P ≤ _; linarith))
  have hU0 : 0 ≤ physicalSpatialInverseBound α (1 / (M : ℝ)) := by
    unfold physicalSpatialInverseBound
    positivity
  have hpower := pow_le_exp_mul_of_le_exp hU0 hU (by positivity) j hα
  have hfact := (factorial_le_exp_sq j).trans (Real.exp_le_exp.mpr hj2)
  have hfree : (Fintype.card (UnselectedColumn selection) : ℝ) ≤ P := by
    have hc := selectedColumn_card selection
    exact (Nat.cast_le.mpr (by omega)).trans hG
  have htwo : (2 : ℝ) ^ Fintype.card (UnselectedColumn selection) ≤ Real.exp (2 * P) := by
    simpa only [mul_comm P 2] using pow_le_exp_mul_of_le_exp (by norm_num : (0 : ℝ) ≤ 2)
      (by linarith [Real.add_one_le_exp (2 : ℝ)]) (by norm_num : (0 : ℝ) ≤ 2) _ hfree
  unfold anisotropicSpatialDensityCap
  calc
    _ ≤ Real.exp (P ^ 2) * Real.exp (P * (P ^ 2 + 2 * P)) * Real.exp (2 * P) := by gcongr
    _ = _ := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      unfold anisotropicSpatialCapLog
      ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.QuadraticFrequencyCoordinates
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem exists_many_derivative_character_relations
    (f : G → ℂ) (H : Finset G) (χ : G → AddChar G ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) {α δ : ℝ} (hα : 0 < α) (hδ : 0 < δ)
    (hdense : α * Fintype.card G ≤ (H.card : ℝ))
    (hcorr : ∀ h ∈ H, δ ≤ ‖finiteFourierCoeff (multiplicativeDerivative f h) (χ h)‖) :
    ∃ Q : Finset (G × G × G), Q.Nonempty ∧
      (α * δ) ^ 4 / 2 * (Fintype.card G : ℝ) ^ 3 ≤ (Q.card : ℝ) ∧
      ∀ t ∈ Q, t.2.1 ∈ H ∧ t.2.1 - t.1 ∈ H ∧ t.2.2 ∈ H ∧ t.2.2 - t.1 ∈ H ∧
        χ (t.2.1 - t.1) + χ t.2.2 = χ t.2.1 + χ (t.2.2 - t.1) := by
  classical
  let g (h x : G) : ℂ := if h ∈ H then χ h x else 0
  have hg (h x : G) : ‖g h x‖ ≤ 1 := by
    dsimp [g]
    split_ifs
    · exact (AddChar.norm_apply _ _).le
    · simp
  have hzero (h : G) (hh : h ∉ H) (x : G) : g h x = 0 := by simp [g, hh]
  have hcorr' (h : G) (hh : h ∈ H) :
      δ ≤ ‖𝔼 x, multiplicativeDerivative f h x * star (g h x)‖ := by
    simpa only [g, if_pos hh, finiteFourierCoeff] using hcorr h hh
  obtain ⟨Q, hQ, hcard, hrelations⟩ :=
    exists_many_correlated_additive_quadruples f g H hf hg hzero hα hδ hdense hcorr'
  refine ⟨Q, hQ, hcard, ?_⟩
  intro t ht
  obtain ⟨h₁, h₂, h₃, h₄, hlarge⟩ := hrelations t ht
  refine ⟨h₁, h₂, h₃, h₄, character_relation_of_quadruple_pos χ t.1 t.2.1 t.2.2 ?_⟩
  have heq : additiveQuadrupleCorrelation g t.1 t.2.1 t.2.2 =
      additiveQuadrupleCorrelation (fun h x => χ h x) t.1 t.2.1 t.2.2 := by
    simp only [additiveQuadrupleCorrelation, g, if_pos h₁, if_pos h₂, if_pos h₃, if_pos h₄]
  rw [heq] at hlarge
  exact lt_of_lt_of_le (by positivity) hlarge

theorem derivative_character_graph_energy [DecidableEq G]
    (f : G → ℂ) (H : Finset G) (χ : G → AddChar G ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) {α δ : ℝ} (hα : 0 < α) (hδ : 0 < δ)
    (hdense : α * Fintype.card G ≤ (H.card : ℝ))
    (hcorr : ∀ h ∈ H, δ ≤ ‖finiteFourierCoeff (multiplicativeDerivative f h) (χ h)‖) :
    (α * δ) ^ 4 / 2 * (Fintype.card G : ℝ) ^ 3 ≤
      (Finset.addEnergy (additiveGraph H χ) (additiveGraph H χ) : ℝ) := by
  classical
  obtain ⟨Q, _, hcard, hrelations⟩ :=
    exists_many_derivative_character_relations f H χ hf hα hδ hdense hcorr
  have henergy := graph_energy_of_few_quadruple_differences H Q χ {0}
    (fun t ht => let h := hrelations t ht; ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩)
    (by
      intro t ht
      simp only [Finset.mem_singleton]
      rw [(hrelations t ht).2.2.2.2]
      abel)
  have henergy' : Q.card ≤ Finset.addEnergy (additiveGraph H χ) (additiveGraph H χ) := by
    simpa only [Finset.card_singleton, one_mul] using henergy
  exact hcard.trans (by exact_mod_cast henergy')

end Erdos3

end

section

namespace Erdos3

open scoped Pointwise

theorem additiveGraph_difference_card_hom
    {G K L : Type*} [AddCommGroup G] [AddCommGroup K] [AddCommGroup L]
    [DecidableEq G] [DecidableEq K] [DecidableEq L]
    (H : Finset G) (b : G → K) (e : K →+ L) (he : Function.Injective e) :
    (additiveGraph H (fun h => e (b h)) - additiveGraph H (fun h => e (b h))).card =
      (additiveGraph H b - additiveGraph H b).card := by
  let F : G × K →+ G × L := {
    toFun := fun x => (x.1, e x.2)
    map_zero' := by simp
    map_add' := by intro x y; simp }
  have hF : Function.Injective F := by
    intro x y h
    exact Prod.ext (congrArg (fun z : G × L => z.1) h)
      (he (congrArg (fun z : G × L => z.2) h))
  have hgraph : additiveGraph H (fun h => e (b h)) = (additiveGraph H b).image F := by
    unfold additiveGraph
    rw [Finset.image_image]
    rfl
  rw [hgraph]
  apply FreimanModel.card_difference_image_of_freiman
  exact FreimanModel.isAddFreimanIso_of_injOn_iterated_sums F (additiveGraph H b) 2
    hF.injOn hF.injOn

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.MixedCyclicErrorBudget
namespace OAI

section

namespace Erdos3

def mixedCyclicErrorSlope (s : ℕ) : ℕ := mixedRootTensorExponent s + mixedRootCornerExponent s

def mixedCyclicErrorBuffer (s : ℕ) : ℕ := 2 * mixedRootCornerCoefficient s + 14

theorem mixed_cyclic_error_bound (s : ℕ) {d u e N : ℝ} (hd : 0 ≤ d) (hu : 0 ≤ u)
    (hdu : d ≤ Real.exp u) (hN : Real.exp (e + mixedCyclicErrorBuffer s) ≤ N) :
    (d ^ mixedRootTensorExponent s + 1) *
        ((mixedRootCornerCoefficient s : ℝ) * d ^ mixedRootCornerExponent s *
          Real.exp (-(e + (mixedCyclicErrorSlope s : ℝ) * u + mixedCyclicErrorBuffer s))) +
      12 * Real.exp (-(e + mixedCyclicErrorBuffer s)) + 2 / N ≤ Real.exp (-e) := by
  have hp (n : ℕ) : d ^ n ≤ Real.exp ((n : ℝ) * u) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ hd hdu n
  have hn : d ^ mixedRootTensorExponent s + 1 ≤
      2 * Real.exp ((mixedRootTensorExponent s : ℝ) * u) := by
    have h := hp (mixedRootTensorExponent s)
    linarith [Real.one_le_exp (show 0 ≤ (mixedRootTensorExponent s : ℝ) * u by positivity)]
  have hcoef : (d ^ mixedRootTensorExponent s + 1) *
      ((mixedRootCornerCoefficient s : ℝ) * d ^ mixedRootCornerExponent s) ≤
      (2 * mixedRootCornerCoefficient s : ℝ) * Real.exp ((mixedCyclicErrorSlope s : ℝ) * u) := by
    calc
      _ ≤ (2 * Real.exp ((mixedRootTensorExponent s : ℝ) * u)) *
          ((mixedRootCornerCoefficient s : ℝ) * Real.exp ((mixedRootCornerExponent s : ℝ) * u)) :=
        mul_le_mul hn (mul_le_mul_of_nonneg_left (hp (mixedRootCornerExponent s)) (Nat.cast_nonneg _))
          (by positivity) (by positivity)
      _ = (2 * mixedRootCornerCoefficient s : ℝ) *
          Real.exp ((mixedRootTensorExponent s : ℝ) * u + (mixedRootCornerExponent s : ℝ) * u) := by
        rw [Real.exp_add]
        ring
      _ = _ := by simp only [mixedCyclicErrorSlope, Nat.cast_add, add_mul]
  have hfirst : (d ^ mixedRootTensorExponent s + 1) *
      ((mixedRootCornerCoefficient s : ℝ) * d ^ mixedRootCornerExponent s *
        Real.exp (-(e + (mixedCyclicErrorSlope s : ℝ) * u + mixedCyclicErrorBuffer s))) ≤
      (2 * mixedRootCornerCoefficient s : ℝ) * Real.exp (-(e + mixedCyclicErrorBuffer s)) := by
    calc
      _ = ((d ^ mixedRootTensorExponent s + 1) *
          ((mixedRootCornerCoefficient s : ℝ) * d ^ mixedRootCornerExponent s)) *
            Real.exp (-(e + (mixedCyclicErrorSlope s : ℝ) * u + mixedCyclicErrorBuffer s)) := by ring
      _ ≤ ((2 * mixedRootCornerCoefficient s : ℝ) * Real.exp ((mixedCyclicErrorSlope s : ℝ) * u)) *
          Real.exp (-(e + (mixedCyclicErrorSlope s : ℝ) * u + mixedCyclicErrorBuffer s)) :=
        mul_le_mul_of_nonneg_right hcoef (Real.exp_nonneg _)
      _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  have hrecip : 1 / N ≤ Real.exp (-(e + mixedCyclicErrorBuffer s)) := by
    have h := one_div_le_one_div_of_le (Real.exp_pos _) hN
    simpa only [one_div, ← Real.exp_neg] using h
  have hthird : 2 / N ≤ 2 * Real.exp (-(e + mixedCyclicErrorBuffer s)) := by
    calc
      _ = 2 * (1 / N) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hrecip (by norm_num)
  calc
    _ ≤ (mixedCyclicErrorBuffer s : ℝ) * Real.exp (-(e + mixedCyclicErrorBuffer s)) := by
      have h := add_le_add (add_le_add hfirst (le_refl (12 * Real.exp (-(e + mixedCyclicErrorBuffer s))))) hthird
      apply h.trans_eq
      have hB : (mixedCyclicErrorBuffer s : ℝ) = 2 * mixedRootCornerCoefficient s + 14 := by
        simp only [mixedCyclicErrorBuffer, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      rw [hB]
      ring
    _ ≤ Real.exp (mixedCyclicErrorBuffer s : ℝ) * Real.exp (-(e + mixedCyclicErrorBuffer s)) :=
      mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (mixedCyclicErrorBuffer s : ℝ)])
        (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SharedFreeComparisonBasis
namespace OAI

section

namespace Erdos3

theorem exists_sharedFreeComparisonBasisBudget_bound :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ q p : ℝ, 0 ≤ q → q ≤ p → 0 ≤ p →
      sharedFreeComparisonBasisBudget q p ≤ (p + C) ^ C := by
  let R (X : Polynomial ℕ) := ((X + 1 + (X + 3) ^ 7 + 2) ^ 9 + X + 4) ^ 4
  let H (X : Polynomial ℕ) := X + R X + 2
  let G (X : Polynomial ℕ) := X + X * ((X + 2) ^ 7 + X)
  let V (X : Polynomial ℕ) := G (X + (X + (X + 3) ^ 7 + 2) ^ 4 + 1)
  let F (X : Polynomial ℕ) := X + V (4 * X)
  let A : Polynomial ℕ := Polynomial.X + F (Polynomial.X + H Polynomial.X)
  let T : Polynomial ℕ := A + V (4 * A)
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget T
  refine ⟨C, hC, ?_⟩
  intro q p hq hqp hp
  have hheight : 0 ≤ coefficientFourHeightBudget p := coefficientFourHeightBudget_nonneg hp
  have hupper : sharedFreeComparisonBasisBudget q p ≤ sharedFreeComparisonBasisBudget p p := by
    have hA := add_le_add hqp (fourRefinementBasisBudget_mono (add_nonneg hq hheight)
      (add_le_add hqp (le_refl (coefficientFourHeightBudget p))))
    have hA0 : 0 ≤ q + fourRefinementBasisBudget (q + coefficientFourHeightBudget p) :=
      add_nonneg hq (fourRefinementBasisBudget_nonneg (add_nonneg hq hheight))
    dsimp only [sharedFreeComparisonBasisBudget]
    exact add_le_add hA (preimageBasisBudget_mono (mul_nonneg (by norm_num) hA0)
      (mul_le_mul_of_nonneg_left hA (by norm_num)))
  apply hupper.trans
  simpa [T, A, F, V, G, H, R, sharedFreeComparisonBasisBudget, coefficientFourHeightBudget,
    refiltrationCoordinateBudget, fourRefinementBasisBudget, preimageBasisBudget,
    sparseGeneratorBudget, Polynomial.eval₂_pow] using hbound p hp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedPairFrozenEquivalence
namespace OAI

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

theorem exists_mixed_frozen_equivalence_budget (a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p q r u : ℝ, 0 ≤ p → 0 ≤ q → 0 ≤ r → 0 ≤ u →
      ∃ t : ℝ, 0 ≤ t ∧ r ≤ t ∧ u ≤ t ∧ p ≤ t ∧
        productNiltestBudget (mixedPairBudget p q) ≤ t ∧
        t + (t + a) ^ a ≤ (p + q + r + u + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let B := 4 * (X + 1) + (X + (X + 2) ^ 2 + 3) + 6
  let T := (B + 2) ^ 2 + B + (B + (B ^ 2 + B + 3) ^ 2) + B ^ 2 + 4 + X + 3
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (T + (T + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro p q r u hp hq hr hu
  let v := p + q + r + u
  let b := 4 * (v + 1) + raisedNiltestBudget v + 6
  let t := productNiltestBudget b + v + 3
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hpqv : p + q ≤ v := by dsimp [v]; linarith
  have hb : 0 ≤ b := by dsimp [b, raisedNiltestBudget]; positivity
  have hprod : 0 ≤ productNiltestBudget b := by
    unfold productNiltestBudget productObservableLipBudget
    positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hrt : r ≤ t := by dsimp [t, v]; linarith
  have hut : u ≤ t := by dsimp [t, v]; linarith
  have hpt : p ≤ t := by dsimp [t, v]; linarith
  have hBt : mixedPairBudget p q ≤ b := by
    dsimp [mixedPairBudget, b, raisedNiltestBudget]
    gcongr
  have hB0 : 0 ≤ mixedPairBudget p q := by
    unfold mixedPairBudget raisedNiltestBudget
    positivity
  have hprodmono : productNiltestBudget (mixedPairBudget p q) ≤ productNiltestBudget b :=
    productNiltestBudget_mono hB0 hBt
  have htest : productNiltestBudget (mixedPairBudget p q) ≤ t :=
    hprodmono.trans (by dsimp [t]; linarith)
  have hsum : t + (t + a) ^ a ≤ (p + q + r + u + C) ^ C := by
    simpa [X, B, T, t, b, v, raisedNiltestBudget, productNiltestBudget,
      productObservableLipBudget, Polynomial.eval₂_pow] using hbudget v hv
  exact ⟨t, ht, hrt, hut, hpt, htest, hsum⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedSpatialProxyCap
namespace OAI

section

namespace Erdos3

open BooleanCubeKernel

theorem narrowTrimmedSpatialWidths_lower {G J X : Type*}
    {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ1 : ξ ≤ 1)
    (N : X → ℕ) (hN : ∀ x, 0 < N x) (z : Option (G ⊕ J) × X) :
    trimmedSpatialWidths W (ξ * τ) N z ≤ narrowTrimmedSpatialWidths W τ ξ N z := by
  have he : trimmedSpatialWidths W (ξ * τ) N z = ξ * trimmedSpatialWidths W τ N z := by
    unfold trimmedSpatialWidths
    ring
  rw [he]
  rcases z with ⟨_ | (g | j), x⟩
  · exact mul_le_of_le_one_left (trimmedSpatialWidths_pos hW hτ N hN _).le hξ1
  · exact mul_le_of_le_one_left (trimmedSpatialWidths_pos hW hτ N hN _).le hξ1
  · exact le_rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SupportedCubeUnitBounds
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem normalizedSupportedCubeSum_norm_le_one {A : Type*} [AddCommGroup A]
    (j : ℕ) (Q : Finset A) (F : (Fin j → Bool) → A → ℂ)
    (hF : ∀ ω x, x ∈ Q → ‖F ω x‖ ≤ 1) :
    ‖normalizedSupportedCubeSum j Q F‖ ≤ 1 := by
  have hprod (c : SupportedCube j (Q : Set A)) :
      ‖mixedCubeProduct F c.val.1 c.val.2‖ ≤ 1 := by
    simp only [mixedCubeProduct, norm_prod, conjugationPower_norm]
    exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun ω _ => hF ω _ (c.property ω))
  have hsum : ‖supportedCubeSum j (Q : Set A) F‖ ≤
      (Nat.card (SupportedCube j (Q : Set A)) : ℝ) := by
    apply (norm_sum_le _ _).trans
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      Nat.card_eq_fintype_card] using Finset.sum_le_sum (fun c (_ : c ∈ Finset.univ) => hprod c)
  rw [normalizedSupportedCubeSum, norm_div, Complex.norm_natCast]
  by_cases hc : Nat.card (SupportedCube j (Q : Set A)) = 0
  · simp only [hc, Nat.cast_zero, div_zero, zero_le_one]
  · have hpos : (0 : ℝ) < Nat.card (SupportedCube j (Q : Set A)) := by
      exact_mod_cast Nat.pos_of_ne_zero hc
    exact (div_le_iff₀ hpos).mpr (by simpa only [one_mul] using hsum)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BoxCyclicEncoding
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem boxCode_density {n : ℕ} (T : Fin n → ℕ) [∀ i, NeZero (T i)] :
    ((integerBox T).card : ℝ) / (boxCodeModulus T : ℝ) = ((4 : ℝ) ^ n)⁻¹ := by
  have hprod : ((∏ i, T i : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (T i)))
  rw [card_integerBox, boxCodeModulus_eq, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  field_simp [hprod]

theorem boxCode_density_lower {n : ℕ} (T : Fin n → ℕ) [∀ i, NeZero (T i)] :
    Real.exp (-(4 * (n : ℝ))) ≤ ((integerBox T).card : ℝ) / (boxCodeModulus T : ℝ) := by
  have h4 : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hpow : (4 : ℝ) ^ n ≤ Real.exp (4 * (n : ℝ)) := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) h4 n
    rw [← Real.exp_nat_mul] at h
    simpa only [mul_comm] using h
  rw [boxCode_density, ← one_div]
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 4 ^ n)).mpr
  calc
    _ ≤ Real.exp (-(4 * (n : ℝ))) * Real.exp (4 * (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hpow (Real.exp_nonneg _)
    _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SpatialTupleErrorBudget
namespace OAI

section

namespace Erdos3

theorem spatialTupleEarlyWidth_inv_bound (n : ℕ) {G V B ε P : ℝ}
    (hG : 0 ≤ G) (hV : 0 ≤ V) (hB : 0 ≤ B) (hε : 0 < ε) (hP : 0 ≤ P)
    (hn : (n : ℝ) ≤ P) (hGP : G ≤ Real.exp P) (hVP : V ≤ Real.exp P)
    (hBP : B ≤ Real.exp P) (hεP : ε⁻¹ ≤ Real.exp P) :
    (twoTermErrorWidth B (spatialTupleTolerance n G V ε))⁻¹ ≤
      Real.exp (2 * (P + spatialTupleToleranceLog P) + 4) := by
  let R := P + spatialTupleToleranceLog P
  have hT := spatialTupleToleranceLog_nonneg hP
  have hR : 0 ≤ R := add_nonneg hP hT
  have hPR : P ≤ R := le_add_of_nonneg_right hT
  have hTR : spatialTupleToleranceLog P ≤ R := le_add_of_nonneg_left hP
  have ht := (spatialTupleTolerance_spec n hG hV hε).1
  have hit := (spatialTupleTolerance_inv_bound n hG hV hε hP hn hGP hVP hεP).trans
    (Real.exp_le_exp.mpr hTR)
  exact (twoTermErrorChoices_log_bounds (A := 0) (T := 0) (by norm_num) hB ht hR
    (Real.exp_nonneg R) (Real.exp_nonneg R) (hBP.trans (Real.exp_le_exp.mpr hPR)) hit).2

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

theorem anisotropicSpatialDensityLip_le_exp {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) {M : ℕ} {p : ℝ} (hp : 0 ≤ p) (hM : 0 < M)
    (hMp : (M : ℝ) ≤ Real.exp p)
    (hI : (Fintype.card (Unit ⊕ I) : ℝ) ≤ p) (hJ : (Fintype.card J : ℝ) ≤ p) :
    anisotropicSpatialDensityLip s (1 / (M : ℝ)) ≤
      Real.exp (anisotropicSpatialCapLog p +
        2 * spatialProfileLog (Fintype.card (Unit ⊕ I)) (Fintype.card (UnselectedColumn s)) p) := by
  let P := spatialProfileLog (Fintype.card (Unit ⊕ I)) (Fintype.card (UnselectedColumn s)) p
  have hdata := spatialProfileLog_bounds Empty s hp hMp
  have hinv : physicalSpatialInverseBound I (1 / (M : ℝ)) ≤ Real.exp P := by
    rw [physicalSpatialInverseBound_eq_scalar]
    simpa only [P, Fintype.card_sum, Fintype.card_empty, add_zero] using hdata.2.1
  have hK : ((Fintype.card (UnselectedColumn s) + Fintype.card (Unit ⊕ I) : ℝ) *
      probabilityProfileLipschitz) ≤ Real.exp P := by
    simpa only [P, Fintype.card_sum, Fintype.card_empty, add_zero] using hdata.2.2.2
  have hcap := anisotropicSpatialDensityCap_exp_bound s hp hM hMp hI hJ
  have hcap0 := anisotropicSpatialDensityCap_nonneg s
    (show 0 ≤ 1 / (M : ℝ) by positivity)
  have hinv0 : 0 ≤ physicalSpatialInverseBound I (1 / (M : ℝ)) := by
    unfold physicalSpatialInverseBound
    positivity
  unfold anisotropicSpatialDensityLip
  calc
    _ ≤ Real.exp (anisotropicSpatialCapLog p) * Real.exp P * Real.exp P := by gcongr
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoarseSpatialPartitionBudget
namespace OAI

section

namespace Erdos3

theorem spatialTupleCoarseMesh_inv_bound (d : ℕ) {G V K ε P : ℝ}
    (hG : 0 ≤ G) (hV : 0 ≤ V) (hK : 0 ≤ K) (hε : 0 < ε) (hP : 0 ≤ P)
    (hd : (d : ℝ) ≤ P) (hGP : G ≤ Real.exp P) (hVP : V ≤ Real.exp P)
    (hKP : K ≤ Real.exp P) (hεP : ε⁻¹ ≤ Real.exp P) :
    (spatialTupleCoarseMesh d G V K ε)⁻¹ ≤ Real.exp (coarseSpatialReciprocalLog P) := by
  have hwidth := spatialTupleEarlyWidth_inv_bound d hG hV hK hε hP hd hGP hVP hKP hεP
  have ht := (spatialTupleTolerance_spec d hG hV hε).1
  have hw := (twoTermErrorWidth_spec hK ht).1
  have hfour : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  unfold spatialTupleCoarseMesh
  rw [inv_div, div_eq_mul_inv]
  calc
    _ ≤ Real.exp 4 * Real.exp (2 * (P + spatialTupleToleranceLog P) + 4) :=
      mul_le_mul hfour hwidth (inv_nonneg.mpr hw.le) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; unfold coarseSpatialReciprocalLog; ring

theorem spatialTupleCoarseMesh_partition_budget (d n : ℕ) {G V K ε μ C P : ℝ}
    (hG : 0 ≤ G) (hV : 0 ≤ V) (hK : 0 ≤ K) (hμ : 0 ≤ μ) (hC : 0 ≤ C)
    (hε : 0 < ε) (hP : 0 ≤ P) (hd : (d : ℝ) ≤ P) (hn : (n : ℝ) ≤ P)
    (hGP : G ≤ Real.exp P) (hVP : V ≤ Real.exp P) (hKP : K ≤ Real.exp P)
    (hεP : ε⁻¹ ≤ Real.exp P) (hμP : μ ≤ Real.exp P)
    (hΓP : μ ^ n ≤ Real.exp P) (hCP : C ≤ Real.exp P) :
    let r := spatialTupleCoarseMesh d G V K ε
    r⁻¹ ≤ Real.exp (coarseSpatialReciprocalLog P) ∧
      (μ ^ n * (intervalSiteCount 4 r : ℝ) ^ n * (μ ^ n * C)) ^ d ≤
        Real.exp (coarseSpatialPartitionLog P) := by
  intro r
  have hri := spatialTupleCoarseMesh_inv_bound d hG hV hK hε hP hd hGP hVP hKP hεP
  refine ⟨hri, ?_⟩
  have hr : 0 < r := (spatialTupleCoarseMesh_spec d hG hV hK hε).1
  have hL := (coarseSpatialLogs_nonneg hP).1
  let R := P + coarseSpatialReciprocalLog P + 4
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hPR : P ≤ R := by dsimp [R]; linarith
  have hLR : coarseSpatialReciprocalLog P ≤ R := by dsimp [R]; linarith
  have hfour : (4 : ℝ) ≤ Real.exp R := by
    have hR4 : 4 ≤ R := by dsimp [R]; linarith
    linarith [Real.add_one_le_exp R]
  have hcount := intervalSiteCount_le_exp (by norm_num : (0 : ℝ) ≤ 4) hr hR hfour
    (by simpa only [one_div] using hri.trans (Real.exp_le_exp.mpr hLR))
  have he := Real.exp_le_exp.mpr hPR
  have hbase := siteCoefficientAllowance_le_exp n hμ (Nat.cast_nonneg _) (pow_nonneg hμ _) hC
    (hμP.trans he) hcount (hΓP.trans he) (hCP.trans he)
  have hpower := vectorSiteAllowance_le_exp d (by positivity) hbase
  apply hpower.trans
  apply Real.exp_le_exp.mpr
  change (d : ℝ) * ((3 * R + 4) * n + 2 * R) ≤ R * ((3 * R + 4) * R + 2 * R)
  gcongr
  · exact hd.trans hPR
  · exact hn.trans hPR

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedSlicedCoarseSource
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem exists_allocatedEarlyCoarseLog_bound (m dim : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ {s : ℝ}, 0 ≤ s →
      coarseSpatialReciprocalLog (allocatedEarlyCoarseInput m dim s) ≤ (s + a) ^ a ∧
      coarseSpatialPartitionLog (allocatedEarlyCoarseInput m dim s) ≤ (s + a) ^ a := by
  let poly : Polynomial ℕ :=
    coarseSpatialReciprocalLog (allocatedEarlyCoarseInput m dim Polynomial.X) +
      coarseSpatialPartitionLog (allocatedEarlyCoarseInput m dim Polynomial.X)
  obtain ⟨a, ha, hpoly⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨a, ha, ?_⟩
  intro s hs
  have hsum : coarseSpatialReciprocalLog (allocatedEarlyCoarseInput m dim s) +
      coarseSpatialPartitionLog (allocatedEarlyCoarseInput m dim s) ≤ (s + a) ^ a := by
    simpa [poly, allocatedEarlyCoarseInput, coarseSpatialReciprocalLog, coarseSpatialPartitionLog,
      spatialTupleToleranceLog, spatialLipschitzEnvelope, spatialFixedProfileEnvelope,
      anisotropicSpatialCapLog, coefficientErrorVolumeLog, Polynomial.eval₂_pow] using hpoly s hs
  obtain ⟨hinv, hpartition⟩ := coarseSpatialLogs_nonneg (allocatedEarlyCoarseInput_bounds m dim hs).1
  exact ⟨(le_add_of_nonneg_right hpartition).trans hsum,
    (le_add_of_nonneg_left hinv).trans hsum⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedFiniteIdealMaskBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical NNReal

theorem idealSiteLogBudget_le_finite_profile {outputs dim : ℕ} {D p : ℝ}
    (hp : 0 ≤ p) (hout : (outputs : ℝ) ≤ D) (hdim : (dim : ℝ) ≤ D)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ D) :
    idealSiteLogBudget outputs dim p ≤ allocatedFiniteIdealProfileLog D p := by
  have hm := mul_le_mul_of_nonneg_right hout hp
  dsimp only [idealSiteLogBudget, affineProfileLogBound, allocatedFiniteIdealProfileLog]
  nlinarith only [hout, hdim, hprofile, hm]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.NormalizedNativeUniformBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem exists_normalizedNative_uniform_budget (m Anorm Anative : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {B P E analytic gain mass spatial volume coverLog : ℝ} {nX : ℕ},
      0 ≤ B → P ∈ Set.Icc 0 B → E ∈ Set.Icc 0 B → analytic ∈ Set.Icc 0 B →
      gain ∈ Set.Icc 0 B → mass ∈ Set.Icc 0 B → spatial ∈ Set.Icc 0 B →
      volume ∈ Set.Icc 0 B → coverLog ≤ B → (nX : ℝ) ≤ B →
      let budget := (B + A) ^ A
      (((m + 1 : ℕ) : ℝ) * P + nX * P ≤ budget) ∧
      coverLog ≤ budget ∧
      (P + E + analytic + Anorm) ^ Anorm ≤ budget ∧
      (gain + 8 + mass + spatial + volume + 2) ^ Anative ≤ budget := by
  let X : Polynomial ℕ := Polynomial.X
  let poly : Polynomial ℕ := (m + 1 : ℕ) * X + X ^ 2 + X +
    (3 * X + Polynomial.C Anorm) ^ Anorm + (4 * X + 10) ^ Anative
  obtain ⟨A, hA, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨A, hA, ?_⟩
  intro B P E analytic gain mass spatial volume coverLog nX hB hP hE ha hg hm hs hv hc hn budget
  have hsum : ((m + 1 : ℕ) : ℝ) * B + B ^ 2 + B +
      (3 * B + Anorm) ^ Anorm + (4 * B + 10) ^ Anative ≤ budget := by
    simpa [poly, X, Polynomial.eval₂_pow] using hbound B hB
  have hnorm0 : 0 ≤ (3 * B + Anorm) ^ Anorm := by positivity
  have hnative0 : 0 ≤ (4 * B + 10) ^ Anative := by positivity
  have hperiod0 : 0 ≤ ((m + 1 : ℕ) : ℝ) * B := by positivity
  have hperiod : ((m + 1 : ℕ) : ℝ) * P + nX * P ≤ ((m + 1 : ℕ) : ℝ) * B + B ^ 2 := by
    rw [pow_two]
    exact add_le_add (mul_le_mul_of_nonneg_left hP.2 (Nat.cast_nonneg _))
      (mul_le_mul hn hP.2 hP.1 hB)
  have hnorm : (P + E + analytic + Anorm) ^ Anorm ≤ (3 * B + Anorm) ^ Anorm := by
    apply pow_le_pow_left₀ (add_nonneg (add_nonneg (add_nonneg hP.1 hE.1) ha.1) (Nat.cast_nonneg _))
    linarith only [hP.2, hE.2, ha.2]
  have hnative : (gain + 8 + mass + spatial + volume + 2) ^ Anative ≤ (4 * B + 10) ^ Anative := by
    apply pow_le_pow_left₀ (add_nonneg
      (add_nonneg (add_nonneg (add_nonneg (add_nonneg hg.1 (by norm_num)) hm.1) hs.1) hv.1) (by norm_num))
    linarith only [hg.2, hm.2, hs.2, hv.2]
  refine ⟨?_, ?_, ?_, ?_⟩
  · linarith only [hsum, hperiod, hB, hnorm0, hnative0]
  · linarith only [hsum, hc, hperiod0, sq_nonneg B, hnorm0, hnative0]
  · linarith only [hsum, hnorm, hperiod0, sq_nonneg B, hB, hnative0]
  · linarith only [hsum, hnative, hperiod0, sq_nonneg B, hB, hnorm0]

end Erdos3.VectorPolynomial

end

end OAI
end


