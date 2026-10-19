-- Prove2me | Definitions.Def_OAIE3v2B032
-- name    : OAIE3v2B032
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T09:59:37.929401+00:00
-- url     : https://prove2.me/theorems/a360058a-4ddd-4cb9-a6cd-6bee28fcb724
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 33 of 311
-- statement:
--   Definitions bundle 33 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports no other bundle of this split.
--
--   Modules: `Dynamics/AllocatedActiveBudgetedSite.lean`, `Dynamics/AllocatedFiniteIdealMaskBudget.lean`, `Dynamics/CanonicalDetectedScaleInputBudget.lean`, `Dynamics/ModeThresholdLogBudget.lean`, `Dynamics/NormalizedTwistNativeApproximationBudget.lean`, `Dynamics/PreparedModularGeneralNativeBudget.lean`, `Dynamics/VectorSiteBudget.lean`, `Estimates/AllocatedCanonicalPeriodPrimitiveBounds.lean`, `Estimates/AllocatedPrimitiveFrontInitialLong.lean`, `Estimates/AllocatedScalarLogBounds.lean`, `Estimates/AllocatedShortAxis.lean`, `Estimates/AllocatedTrimmedVectorSite.lean`, `Estimates/BooleanCubeProduct.lean`, `Estimates/CanonicalEmptyLayerGeometry.lean`, `Estimates/CorrelationDerivative.lean`, `Estimates/DenseProgressionInnerFamily.lean`, `Estimates/DiagonalRowTransfer.lean`, `Estimates/FiniteCommonStrideFamily.lean`, `Estimates/FiniteInnerProgressionFamily.lean`, `Estimates/ImageExtensionInverseBounds.lean`, `Estimates/InactiveShortLogBounds.lean`, `Estimates/OverlapCubeWeights.lean`, `Estimates/PreparedFiniteNestedSourceRelativeInitializerBounds.lean`, `Estimates/PreparedFiniteScheduleLocalScalarConstruction.lean`, `Estimates/PrincipalAxisInterpolation.lean`, `Estimates/QuotientTranslatePartition.lean`, `Estimates/RectangularDetExpansion.lean`, `Estimates/ResidualErrorAllocation.lean`, `Estimates/RowRestrictedDeckSiteMask.lean`, `Estimates/UniformProductAccuracyLogBounds.lean`, `Fourier/UniformSpectrumLogBounds.lean`, `Geometry/AllocatedInactiveSupportBudget.lean`, `Geometry/AnisotropicSpatialCapBudget.lean`, `Geometry/BoxCyclicEncoding.lean`, `Geometry/BoxDetectionExponents.lean`, `Geometry/BoxDifferenceHom.lean`, `Geometry/CoarseSpatialPartitionBudget.lean`, `Geometry/CoefficientSquareSpatialBudget.lean`, `Geometry/FiniteRowChartRadiusBudget.lean`, `Geometry/SampledCommonBox.lean`, `Geometry/SmoothSpatialCostBudget.lean`, `Geometry/SpatialNumericEnvelopeFunctoriality.lean`, `Geometry/SpatialTupleErrorBudget.lean`, `Geometry/SupportedCubeEquivTransport.lean`, `Geometry/UnconditionedSpatialWidthBudget.lean`, `Lattices/AffineAmbientPrimitiveBudget.lean`, `Lattices/IntegerInterpolationExpBounds.lean`, `Lattices/IntegerRadixCoding.lean`, `Lattices/LatticeSheetHaar.lean`, `Lattices/PhysicalSubboxResidueSlice.lean`, `Lattices/PositiveIntegerPeriodization.lean`, `Lattices/ResidueRefinedPeriod.lean`, `Linear/AllocatedKernelPrimitiveBudget.lean`, `Linear/KernelCoefficientLogBudget.lean`, `Linear/PreparedUniformShortSourceRankBudget.lean`, `Polynomial/CandidateNestedDegreeNetSchedule.lean`, `Polynomial/ForecastSlicedEarlyUnrestrictedPolynomialBudget.lean`, `Polynomial/IntegerPolynomialActiveProfileSupport.lean`, `Polynomial/PreparedFiniteNestedForwardAllDegreePaddedSource.lean`, `Probability/DensityMixtureAELaw.lean`, `Probability/FiniteArrayMeasure.lean`, `Probability/SampledWeightCellLaw.lean`, `Probability/ScaledArrayLaw.lean`, `Probability/SmoothSpatialProbability.lean`, `Sampling/AllocatedSlicedGridGeometryBudget.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueRefinedPeriod
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def residueRefinedPeriod {X : Type*} [Fintype X] (m : ℕ) (q : X → ℕ) : ℕ :=
  m * ∏ d, q d

theorem residueRefinedPeriod_pos {X : Type*} [Fintype X]
    {m : ℕ} (hm : 0 < m) (q : X → ℕ) (hq : ∀ d, 0 < q d) :
    0 < residueRefinedPeriod m q :=
  Nat.mul_pos hm (Finset.prod_pos (fun d _ => hq d))

theorem stride_mul_dvd_residueRefinedPeriod {X : Type*} [Fintype X]
    (m : ℕ) (q : X → ℕ) (d : X) : q d * m ∣ residueRefinedPeriod m q := by
  classical
  obtain ⟨a, ha⟩ := Finset.dvd_prod_of_mem q (Finset.mem_univ d)
  refine ⟨a, ?_⟩
  unfold residueRefinedPeriod
  rw [ha]
  ring

theorem residueRefinedPeriod_exp_bound {X : Type*} [Fintype X]
    (m : ℕ) (q : X → ℕ) {P R : ℝ}
    (hm : (m : ℝ) ≤ Real.exp P) (hq : ∀ d, (q d : ℝ) ≤ Real.exp R) :
    (residueRefinedPeriod m q : ℝ) ≤ Real.exp (P + Fintype.card X * R) := by
  have hprod : (∏ d, (q d : ℝ)) ≤ Real.exp R ^ Fintype.card X := by
    calc
      _ ≤ ∏ _d : X, Real.exp R :=
        Finset.prod_le_prod (fun direction _ => Nat.cast_nonneg (q direction))
          (fun direction _ => hq direction)
      _ = _ := by simp only [Finset.prod_const, Finset.card_univ]
  have h := mul_le_mul hm hprod (Finset.prod_nonneg (fun d _ => Nat.cast_nonneg (q d))) (Real.exp_pos P).le
  simpa only [residueRefinedPeriod, Nat.cast_mul, Nat.cast_prod, Real.exp_add, Real.exp_nat_mul] using h

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

omit [AddCommGroup H] in
theorem expect_im (f : H → ℂ) : (𝔼 x, f x).im = 𝔼 x, (f x).im := by
  simp [Fintype.expect_eq_sum_div_card]

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H]

variable [Fintype H]

noncomputable def cubeAverage {M : Type*} [AddCommMonoid M] [Module ℚ≥0 M] :
    ℕ → (List H → M) → M
  | 0, F => F []
  | j + 1, F => 𝔼 h, cubeAverage j (fun hs ↦ F (h :: hs))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.SampledWeightCellLaw
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

variable {ι : Type*} [Fintype ι]

noncomputable def independentCoordinateDensity (f : ι → ℝ → ℝ) (x : ι → ℝ) : ℝ :=
  ∏ i, f i (x i)

theorem independentCoordinateDensity_integrable (f : ι → ℝ → ℝ) (hf : ∀ i, Integrable (f i)) :
    Integrable (independentCoordinateDensity f) := Integrable.fintype_prod hf

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BoxDetectionExponents
namespace OAI

section

namespace Erdos3

theorem exp_neg_nat_mul_le_inverse_pow (N d : ℕ) (hN : 0 < N) {p : ℝ} (hd : (d : ℝ) ≤ p) :
    Real.exp (-(N : ℝ) * p) ≤ ((1 : ℝ) / N) ^ d := by
  have hbase : (N : ℝ) ≤ Real.exp N := by linarith [Real.add_one_le_exp (N : ℝ)]
  have hpow : (N : ℝ) ^ d ≤ Real.exp ((N : ℝ) * p) := by
    calc
      _ ≤ (Real.exp N) ^ d := pow_le_pow_left₀ (Nat.cast_nonneg N) hbase d
      _ = Real.exp ((d : ℝ) * N) := (Real.exp_nat_mul _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [show (0 : ℝ) ≤ N from Nat.cast_nonneg N])
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hi := one_div_le_one_div_of_le (pow_pos hn d) hpow
  simpa only [div_pow, one_pow, neg_mul, Real.exp_neg, one_div, inv_pow] using hi

theorem exp_neg_le_of_pow {x P : ℝ} {n : ℕ} (hx : 0 ≤ x) (hP : 0 ≤ P) (hn : n ≠ 0)
    (h : Real.exp (-P) ≤ x ^ n) : Real.exp (-P) ≤ x := by
  have ht : Real.exp (-P) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hp : ∀ k : ℕ, Real.exp (-P) ^ (k + 1) ≤ Real.exp (-P) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ]
      exact (mul_le_mul ih ht (Real.exp_nonneg _) (Real.exp_nonneg _)).trans_eq (mul_one _)
  cases n with
  | zero => exact False.elim (hn rfl)
  | succ k => exact le_of_pow_le_pow_left₀ (Nat.succ_ne_zero k) hx ((hp k).trans h)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BooleanCubeProduct
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G]

variable [Fintype G]

def derivativeInverseBudget (s : ℕ) (p : ℝ) : ℝ := (2 ^ (s + 2) : ℕ) * p + 2

theorem derivativeInverseBudget_ge_two (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    2 ≤ derivativeInverseBudget s p := by
  unfold derivativeInverseBudget
  exact le_add_of_nonneg_left (mul_nonneg (Nat.cast_nonneg _) hp)

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

noncomputable def imageExtension (φ : A →+ B) (Q : Finset A) (f : A → ℂ) : B → ℂ := by
  classical
  exact fun y ↦ ∑ a ∈ Q, if φ a = y then f a else 0

theorem imageExtension_apply {φ : A →+ B} {Q : Finset A} (hi : Set.InjOn φ (Q : Set A))
    (f : A → ℂ) {a : A} (ha : a ∈ Q) : imageExtension φ Q f (φ a) = f a := by
  classical
  unfold imageExtension
  rw [Finset.sum_eq_single a]
  · simp
  · intro b hb hba
    exact if_neg (fun he ↦ hba (hi hb ha he))
  · intro hna
    exact (hna ha).elim

theorem imageExtension_eq_zero {φ : A →+ B} {Q : Finset A} (f : A → ℂ) {y : B}
    (hy : y ∉ φ '' (Q : Set A)) : imageExtension φ Q f y = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro a ha
  exact if_neg (fun he ↦ hy ⟨a, ha, he⟩)

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

def smallCubeSide (T : ι → ℕ) (j : ℕ) (i : ι) : ℕ := (T i - 1) / (j + 1) + 1

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BoxDifferenceHom
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def finiteBoxCorrelation {X Y : Type*} [Fintype X] [Fintype Y]
    (F : X → Y → ℂ) : ℂ :=
  𝔼 x, 𝔼 x', 𝔼 y, 𝔼 y',
    F x y * star (F x' y) * star (F x y') * F x' y'

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def boxSlice {X : Type*} (a z : Fin 2 → X) : Fin 4 → X := ![z 0, a 0, z 1, a 1]

noncomputable def boxKernel {X : Type*} (K : X → X → ℂ) (x : Fin 4 → X) : ℂ :=
  K (x 0) (x 2) * star (K (x 1) (x 2)) * star (K (x 0) (x 3)) * K (x 1) (x 3)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ResidualErrorAllocation
namespace OAI

section

namespace Erdos3

noncomputable def twoTermErrorResolution (T A ε : ℝ) : ℝ := 1+T+2*A/ε

noncomputable def twoTermErrorWidth (B ε : ℝ) : ℝ := min 1 (ε/(2*(1+B)))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.FiniteArrayMeasure
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem finiteArray_uncurry_measurePreserving {I J X : Type*} [Fintype I] [Fintype J]
    [MeasurableSpace X] (μ : I → J → Measure X) [∀ i j, SigmaFinite (μ i j)] :
    MeasurePreserving (MeasurableEquiv.curry I J X).symm
      (Measure.pi (fun i => Measure.pi (μ i))) (Measure.pi (fun ij : I × J => μ ij.1 ij.2)) := by
  refine ⟨(MeasurableEquiv.curry I J X).symm.measurable, ?_⟩
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply (MeasurableEquiv.curry I J X).symm.measurable (MeasurableSet.univ_pi hs)]
  have he : (MeasurableEquiv.curry I J X).symm ⁻¹' Set.univ.pi s =
      Set.univ.pi (fun i => Set.univ.pi (fun j => s (i, j))) := by
    ext x
    constructor
    · intro hx i _ j _
      exact hx (i, j) (Set.mem_univ _)
    · intro hx ij _
      exact hx ij.1 (Set.mem_univ _) ij.2 (Set.mem_univ _)
  rw [he, Measure.pi_pi]
  simp only [Measure.pi_pi, Fintype.prod_prod_type]

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

theorem pmf_real_integrable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (p : PMF X) : Integrable (fun x => (p x).toReal) Measure.count := by
  apply integrable_count_iff.mpr
  simpa only [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg] using
    ENNReal.summable_toReal p.tsum_coe_ne_top

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RectangularDetExpansion
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem rectangular_det_expansion {I J R : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [CommRing R] (A : Matrix I J R) (B : Matrix J I R) :
    (A*B).det = ∑ p : I → J, (A.submatrix id p).det * ∏ i, B (p i) i := by
  simp only [Matrix.det_apply', Matrix.mul_apply, Finset.prod_univ_sum, Finset.mul_sum,
    Fintype.piFinset_univ, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro σ _
  simp only [Finset.prod_mul_distrib, Matrix.submatrix_apply, id_eq]
  ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedKernelPrimitiveBudget
namespace OAI


namespace Erdos3


noncomputable def scalarKernelCutoffLogBudget (I J : Type*) [Fintype I] [Fintype J] (P : ℝ) : ℝ :=
  2 * ((4 + 3 * ((Fintype.card (J × Option I) * Fintype.card I : ℕ) : ℝ)) * (P + 2)) + 8


noncomputable def scalarKernelInputBudget (I J : Type*) [Fintype I] [Fintype J] (R : ℝ) : ℝ :=
  16 * (10 + (Fintype.card I : ℝ) + Fintype.card J + Fintype.card (J × Option I) + R)^3


noncomputable def scalarKernelLogarithmicBudget (I J : Type*) [Fintype I] [Fintype J] (R : ℝ) : ℝ :=
  scalarKernelCutoffLogBudget I J (scalarKernelInputBudget I J R)

theorem scalarKernelLogarithmicBudget_eq (I J : Type*) [Fintype I] [Fintype J] (R : ℝ) :
    scalarKernelLogarithmicBudget I J R =
      2 * ((4 + 3 * ((Fintype.card J : ℝ) * (Fintype.card I + 1) * Fintype.card I)) *
        (16 * (10 + (Fintype.card I : ℝ) + Fintype.card J + Fintype.card J * (Fintype.card I + 1) + R)^3 + 2)) + 8 := by
  simp only [scalarKernelLogarithmicBudget, scalarKernelCutoffLogBudget, scalarKernelInputBudget,
    Fintype.card_prod, Fintype.card_option, Nat.cast_mul, Nat.cast_add, Nat.cast_one]

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ModeThresholdLogBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem coe_toNNReal_le_exp {x P : ℝ} (hx : x ≤ Real.exp P) :
    (Real.toNNReal x : ℝ) ≤ Real.exp P := by
  rw [Real.coe_toNNReal']
  exact max_le hx (Real.exp_nonneg _)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteInnerProgressionFamily
namespace OAI

section

namespace Erdos3

open scoped Classical

noncomputable def finiteSitePreimage {T X : Type*} [Fintype T] [DecidableEq T] [DecidableEq X]
    (e : T → X) (A : Finset X) : Finset T := Finset.univ.filter (fun t => e t ∈ A)

theorem image_finiteSitePreimage {T X : Type*} [Fintype T] [DecidableEq T] [DecidableEq X]
    (e : T → X) (A : Finset X) (hA : A ⊆ Finset.univ.image e) :
    (finiteSitePreimage e A).image e = A := by
  ext x
  simp only [Finset.mem_image, finiteSitePreimage, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ht
  · intro hx
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp (hA hx)
    exact ⟨t, hx, rfl⟩

theorem finiteSitePreimage_card {T X : Type*} [Fintype T] [DecidableEq T] [DecidableEq X]
    (e : T → X) (he : Function.Injective e) (A : Finset X)
    (hA : A ⊆ Finset.univ.image e) : (finiteSitePreimage e A).card = A.card := by
  have h := congrArg Finset.card (image_finiteSitePreimage e A hA)
  simpa only [Finset.card_image_of_injective _ he] using h

theorem finiteSitePreimage_subset {T X : Type*} [Fintype T] [DecidableEq T] [DecidableEq X]
    (e : T → X) (he : Function.Injective e) (A : Finset X) (S : Finset T)
    (hA : A ⊆ S.image e) : finiteSitePreimage e A ⊆ S := by
  intro t ht
  have het : e t ∈ A := (Finset.mem_filter.mp ht).2
  obtain ⟨s, hs, hst⟩ := Finset.mem_image.mp (hA het)
  exact he hst ▸ hs

noncomputable def finiteSiteInnerFamily {T X : Type*} [Fintype T] [DecidableEq T] [DecidableEq X]
    (e : T → X) (D : Finset (Finset X)) : Finset (Finset T) :=
  (D.filter (fun A => A ⊆ Finset.univ.image e)).image (finiteSitePreimage e)

theorem finiteSiteInnerFamily_card {T X : Type*} [Fintype T] [DecidableEq T] [DecidableEq X]
    (e : T → X) (D : Finset (Finset X)) : (finiteSiteInnerFamily e D).card ≤ D.card :=
  Finset.card_image_le.trans (Finset.card_filter_le _ _)

theorem mem_finiteSiteInnerFamily {T X : Type*} [Fintype T] [DecidableEq T] [DecidableEq X]
    (e : T → X) (D : Finset (Finset X)) {A : Finset X}
    (hAD : A ∈ D) (hA : A ⊆ Finset.univ.image e) :
    finiteSitePreimage e A ∈ finiteSiteInnerFamily e D :=
  Finset.mem_image.mpr ⟨A, Finset.mem_filter.mpr ⟨hAD, hA⟩, rfl⟩

theorem finiteSiteInnerFamily_image_mem {T X : Type*} [Fintype T] [DecidableEq T] [DecidableEq X]
    (e : T → X) (D : Finset (Finset X)) {A : Finset T}
    (hA : A ∈ finiteSiteInnerFamily e D) : A.image e ∈ D := by
  obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hA
  rw [image_finiteSitePreimage e B (Finset.mem_filter.mp hB).2]
  exact (Finset.mem_filter.mp hB).1

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DenseProgressionInnerFamily
namespace OAI

section

namespace Erdos3

theorem progression_endpoint_bounds {L m H : ℕ} {c δ : ℝ}
    (hL : 0 < L) (hm : 0 < m) (hH : 2 ≤ H) (hδ : 0 < δ)
    (hc : 0 ≤ c) (hlast : c + (m : ℝ) * ((H : ℝ) - 1) < L)
    (hdense : δ * L ≤ H) :
    δ * L ≤ (m * H : ℕ) ∧ ((m * H : ℕ) : ℝ) < 2 * L ∧
      m ≤ ⌈2 / δ⌉₊ ∧ |c| ≤ δ⁻¹ * (m * H : ℕ) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hH2 : (2 : ℝ) ≤ H := by exact_mod_cast hH
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have hmlast : (m : ℝ) * ((H : ℝ) - 1) < L := by linarith
  have hmL : (m : ℝ) < L := by nlinarith
  have hwidth : (m : ℝ) * H < 2 * L := by nlinarith
  have hlower : δ * L ≤ (m : ℝ) * H := hdense.trans (by nlinarith [Nat.cast_nonneg (α := ℝ) H])
  have hprod : ((m : ℝ) * δ) * L < 2 * L := by
    have he := mul_le_mul_of_nonneg_left hdense (Nat.cast_nonneg (α := ℝ) m)
    nlinarith only [he, hwidth]
  have hstride : (m : ℝ) < 2 / δ :=
    (lt_div_iff₀ hδ).mpr ((mul_lt_mul_iff_left₀ hL0).mp hprod)
  have hcL : c ≤ L := by nlinarith
  have hLwidth : (L : ℝ) ≤ ((m : ℝ) * H) / δ := (le_div_iff₀ hδ).mpr (by nlinarith only [hlower])
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [Nat.cast_mul] using hlower
  · simpa only [Nat.cast_mul] using hwidth
  · exact_mod_cast hstride.le.trans (Nat.le_ceil (2 / δ))
  · rw [abs_of_nonneg hc]
    simpa only [Nat.cast_mul, div_eq_mul_inv, mul_comm] using hcL.trans hLwidth

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ImageExtensionInverseBounds
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B] [Fintype B] [DecidableEq B]

omit [Fintype B] in
theorem imageExtension_norm_le_one (φ : A →+ B) (Q : Finset A) (f : A → ℂ)
    (hφ : Set.InjOn φ (Q : Set A)) (hf : ∀ x ∈ Q, ‖f x‖ ≤ 1) (y : B) :
    ‖imageExtension φ Q f y‖ ≤ 1 := by
  classical
  by_cases hy : y ∈ Q.image φ
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    rw [imageExtension_apply hφ f hx]
    exact hf x hx
  · rw [imageExtension_eq_zero f (by
      rintro ⟨x, hx, hxy⟩
      exact hy (Finset.mem_image.mpr ⟨x, hx, hxy⟩))]
    simp

theorem sum_imageExtension_mul (φ : A →+ B) (Q : Finset A) (f : A → ℂ) (g : B → ℂ) :
    (∑ y : B, imageExtension φ Q f y * g y) = ∑ x ∈ Q, f x * g (φ x) := by
  classical
  simp only [imageExtension, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp

theorem expect_imageExtension_mul (φ : A →+ B) (Q : Finset A) (hQ : Q.Nonempty)
    (f : A → ℂ) (g : B → ℂ) :
    (𝔼 y : B, imageExtension φ Q f y * g y) =
      ((Q.card : ℂ) / Fintype.card B) * (𝔼 x ∈ Q, f x * g (φ x)) := by
  classical
  rw [Fintype.expect_eq_sum_div_card, sum_imageExtension_mul, Finset.expect_eq_sum_div_card]
  have hq : (Q.card : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hQ.card_pos.ne'
  field_simp

theorem norm_expect_imageExtension_mul_le (φ : A →+ B) (Q : Finset A) (hQ : Q.Nonempty)
    (hφ : Set.InjOn φ (Q : Set A)) (f : A → ℂ) (g : B → ℂ) :
    ‖𝔼 y : B, imageExtension φ Q f y * g y‖ ≤ ‖𝔼 x ∈ Q, f x * g (φ x)‖ := by
  classical
  rw [expect_imageExtension_mul φ Q hQ, norm_mul, norm_div, Complex.norm_natCast, Complex.norm_natCast]
  have hc : Q.card ≤ Fintype.card B := by
    have h := (Q.image φ).card_le_univ
    rwa [Finset.card_image_of_injOn hφ] at h
  have hratio : (Q.card : ℝ) / Fintype.card B ≤ 1 :=
    (div_le_one (by exact_mod_cast Fintype.card_pos : (0 : ℝ) < Fintype.card B)).mpr (by exact_mod_cast hc)
  exact mul_le_of_le_one_left (norm_nonneg _) hratio

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

noncomputable def finiteCommonStrideFamily {I : Type*} [Fintype I] [DecidableEq I]
    (M : ℕ) (C : I → Finset (Finset ℤ)) : Finset (Finset (I → ℤ)) :=
  (Finset.univ : Finset (Fin M × (I → Fin M))).biUnion (fun q =>
    (Fintype.piFinset C).image (fun S => Fintype.piFinset (fun i =>
      (S i).image (fun x => ((q.2 i).val : ℤ) + (q.1.val + 1 : ℕ) * x))))

theorem finiteCommonStrideFamily_card {I : Type*} [Fintype I] [DecidableEq I]
    (M : ℕ) (C : I → Finset (Finset ℤ)) :
    (finiteCommonStrideFamily M C).card ≤ M ^ (Fintype.card I + 1) * ∏ i, (C i).card := by
  apply Finset.card_biUnion_le.trans
  calc
    _ ≤ ∑ _q : Fin M × (I → Fin M), (Fintype.piFinset C).card :=
      Finset.sum_le_sum (fun _ _ => Finset.card_image_le)
    _ = _ := by simp [Fintype.card_piFinset, pow_succ, mul_assoc, mul_comm]

theorem mem_finiteCommonStrideFamily {I : Type*} [Fintype I] [DecidableEq I]
    (M : ℕ) (C : I → Finset (Finset ℤ)) {m : ℕ} (hm : 0 < m) (hmM : m ≤ M)
    (r : I → ℕ) (hr : ∀ i, r i < M) (S : I → Finset ℤ) (hS : ∀ i, S i ∈ C i) :
    Fintype.piFinset (fun i => (S i).image (fun x => (r i : ℤ) + m * x)) ∈
      finiteCommonStrideFamily M C := by
  apply Finset.mem_biUnion.mpr
  refine ⟨(⟨m - 1, by omega⟩, fun i => ⟨r i, hr i⟩), Finset.mem_univ _, ?_⟩
  apply Finset.mem_image.mpr
  exact ⟨S, Fintype.mem_piFinset.mpr hS, by simp only [Nat.sub_add_cancel hm]⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.QuotientTranslatePartition
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem additiveFundamentalDomain_op {E : Type*} [AddCommGroup E] [MeasurableSpace E]
    (Γ : AddSubgroup E) {F : Set E} {μ : Measure E}
    (hF : IsAddFundamentalDomain Γ F μ) : IsAddFundamentalDomain Γ.op F μ := by
  have h := hF.preimage_of_equiv (MeasurePreserving.id μ).quasiMeasurePreserving
    (Γ.equivOp.bijective) (fun g x => ?_)
  · exact h
  · change x + (g : E) = (g : E) + x
    exact add_comm _ _

end Erdos3

end

section

namespace Erdos3

open MeasureTheory _root_.Set
open scoped Pointwise

theorem quotient_preimage_image_vadd {E : Type*} [AddCommGroup E]
    (Γ : AddSubgroup E) (A : Set E) :
    (QuotientAddGroup.mk : E → E ⧸ Γ) ⁻¹'
      ((QuotientAddGroup.mk : E → E ⧸ Γ) '' A) = ⋃ g : Γ, g +ᵥ A := by
  rw [QuotientAddGroup.preimage_image_mk_eq_iUnion_image]
  congr 1
  funext g
  change (fun x : E => x + g.val) '' A = (fun x : E => g.val + x) '' A
  simp only [add_comm]

theorem quotient_injective_translates_disjoint {E : Type*} [AddCommGroup E]
    (Γ : AddSubgroup E) {A : Set E}
    (hA : InjOn (QuotientAddGroup.mk : E → E ⧸ Γ) A) :
    Pairwise (fun g h : Γ => Disjoint (g +ᵥ A) (h +ᵥ A)) := by
  intro g h hgh
  apply Set.disjoint_left.mpr
  rintro x ⟨a, ha, hga⟩ ⟨b, hb, hhb⟩
  change g.val + a = x at hga
  change h.val + b = x at hhb
  have hg0 : QuotientAddGroup.mk' Γ g.val = 0 :=
    (QuotientAddGroup.eq_zero_iff _).mpr g.property
  have hh0 : QuotientAddGroup.mk' Γ h.val = 0 :=
    (QuotientAddGroup.eq_zero_iff _).mpr h.property
  have hab : a = b := hA ha hb (by
    have he := congrArg (QuotientAddGroup.mk' Γ) (hga.trans hhb.symm)
    simpa only [map_add, hg0, hh0, zero_add, QuotientAddGroup.mk'_apply] using he)
  subst b
  exact hgh (Subtype.ext (add_right_cancel (hga.trans hhb.symm)))

theorem quotient_injective_lift_measure {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] (Γ : AddSubgroup E) [Countable Γ]
    (ν : Measure E) [ν.IsAddLeftInvariant]
    {F A : Set E} (hF : IsAddFundamentalDomain Γ F ν) (hFm : MeasurableSet F)
    (hAm : MeasurableSet A) (hA : InjOn (QuotientAddGroup.mk : E → E ⧸ Γ) A) :
    ν (((QuotientAddGroup.mk : E → E ⧸ Γ) ⁻¹'
      ((QuotientAddGroup.mk : E → E ⧸ Γ) '' A)) ∩ F) = ν A := by
  rw [quotient_preimage_image_vadd, Set.iUnion_inter]
  rw [measure_iUnion]
  · exact (hF.measure_eq_tsum A).symm
  · intro g h hgh
    exact (quotient_injective_translates_disjoint Γ hA hgh).mono inter_subset_left inter_subset_left
  · intro g
    exact (hAm.const_vadd g).inter hFm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LatticeSheetHaar
namespace OAI

section

namespace Erdos3

open MeasureTheory Module

variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype I]

theorem lattice_fundamentalDomain_volume (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (b : Basis I ℤ Λ) :
    volume (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ Λ)) =
      ENNReal.ofReal (ZLattice.covolume Λ) := by
  rw [ZLattice.covolume_eq_measure_fundamentalDomain Λ volume
    (ZLattice.isAddFundamentalDomain b volume), measureReal_def,
    ENNReal.ofReal_toReal (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.InactiveShortLogBounds
namespace OAI

section

namespace Erdos3

open scoped NNReal BigOperators

theorem normalizedCoefficientCoordinates_lipschitz {I : Type*} [Fintype I]
    (c w : I → ℝ) {δ : ℝ≥0} (hδ : 0 < δ) (hw : ∀ i, (δ : ℝ) ≤ w i) :
    LipschitzWith δ⁻¹ (fun x : I → ℝ => fun i => (x i - c i) / w i) := by
  have hδr : (0 : ℝ) < δ := hδ
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm]
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  change ‖(x i-c i)/w i - (y i-c i)/w i‖ ≤ _
  rw [Real.norm_eq_abs, ← sub_div, sub_sub_sub_cancel_right, abs_div,
    abs_of_pos (hδr.trans_le (hw i))]
  calc
    _ ≤ ‖x-y‖ / w i := div_le_div_of_nonneg_right
      (norm_le_pi_norm (x-y) i) (hδr.le.trans (hw i))
    _ ≤ ‖x-y‖ / (δ : ℝ) := div_le_div_of_nonneg_left (norm_nonneg _) hδr (hw i)
    _ = _ := by simp only [NNReal.coe_inv, dist_eq_norm, div_eq_mul_inv]; ring

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem pow_le_exp_mul_of_le_exp {x Q P : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ Real.exp Q)
    (hQ : 0 ≤ Q) (n : ℕ) (hn : (n : ℝ) ≤ P) : x^n ≤ Real.exp (P*Q) := by
  calc
    _ ≤ (Real.exp Q)^n := pow_le_pow_left₀ hx0 hx _
    _ = Real.exp ((n : ℝ)*Q) := (Real.exp_nat_mul Q n).symm
    _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hn hQ)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.IntegerPolynomialActiveProfileSupport
namespace OAI

section

namespace Erdos3

theorem small_coordinate_lift_unique {D : Type*} (f y z : D → ℝ)
    (hy : ∀ d, |y d| < 1 / 2) (hz : ∀ d, |z d| < 1 / 2)
    (hfy : ∀ d, ∃ a : ℤ, f d - y d = a) (hfz : ∀ d, ∃ a : ℤ, f d - z d = a) : y = z := by
  funext d
  obtain ⟨a, ha⟩ := hfy d
  obtain ⟨b, hb⟩ := hfz d
  have hlo : (-1 : ℝ) < (b - a : ℤ) := by
    rw [Int.cast_sub]
    linarith [(abs_lt.mp (hy d)).1, (abs_lt.mp (hz d)).2]
  have hhi : ((b - a : ℤ) : ℝ) < 1 := by
    rw [Int.cast_sub]
    linarith [(abs_lt.mp (hy d)).2, (abs_lt.mp (hz d)).1]
  have hlo' : (-1 : ℤ) < b - a := by exact_mod_cast hlo
  have hhi' : b - a < (1 : ℤ) := by exact_mod_cast hhi
  have he : b = a := by omega
  rw [he] at hb
  linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ScaledArrayLaw
namespace OAI

section

namespace Erdos3

open MeasureTheory Module Submodule

theorem scaledProfile_div_bound {c w S R : ℝ} (hw : 0 ≤ w) (hS : 1 ≤ S) (hb : |c| + w ≤ R) :
    |c / S| + w / S ≤ R := by
  have hS0 : 0 < S := lt_of_lt_of_le zero_lt_one hS
  rw [abs_div, abs_of_pos hS0, ← add_div]
  apply (div_le_self (add_nonneg (abs_nonneg _) hw) hS).trans hb

theorem scaledAbs_le_of_bound {a S R : ℝ} (hS : 1 ≤ S) (hb : |a| * S ≤ R) : |a| ≤ R := by
  calc
    |a| = |a| * 1 := (mul_one _).symm
    _ ≤ |a| * S := mul_le_mul_of_nonneg_left hS (abs_nonneg a)
    _ ≤ R := hb

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedShortAxis
namespace OAI

section

namespace Erdos3

noncomputable def tailAxisInterpolationCap (L s : ℕ) (ε : ℝ) : ℝ :=
  max (2 * (L : ℝ)^s / ε) ((L : ℝ)^(s+1))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PrincipalAxisInterpolation
namespace OAI

section

namespace Erdos3

noncomputable def principalAxisInterpolationCap (h L : ℕ) (γ : ℝ) : ℝ :=
  max (4 * (L : ℝ)^h / γ) ((L : ℝ)^h)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerInterpolationExpBounds
namespace OAI

section

namespace Erdos3

def integerInterpolationLogEnvelope (m : ℕ) (P : ℝ) : ℝ := ((m : ℝ) + 1) * P + 8

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedScalarLogBounds
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

def allocatedWidthLog (m : ℕ) (P : ℝ) : ℝ := ((m : ℝ)+4)*(P+8)

theorem allocatedWidthLog_nonneg (m : ℕ) {P : ℝ} (hP : 0 ≤ P) : 0 ≤ allocatedWidthLog m P := by
  unfold allocatedWidthLog
  positivity

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PositiveIntegerPeriodization
namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {D : Type*} [Fintype D]

noncomputable def positiveIntegerPeriodization (H : (D → ℝ) → ℝ) (x : D → ℝ) : ℝ :=
  ∑' n : D → ℤ, H (fun i => x i + (n i : ℝ))

omit [Fintype D] in
theorem integer_shifts_small_box_injective (x : D → ℝ) (n m : D → ℤ)
    (hn : ∀ i, |x i + (n i : ℝ)| < 1/2) (hm : ∀ i, |x i + (m i : ℝ)| < 1/2) : n = m := by
  have he := small_coordinate_lift_unique x (fun i => x i + (n i : ℝ))
    (fun i => x i + (m i : ℝ)) hn hm
    (fun i => ⟨-n i, by push_cast; ring⟩) (fun i => ⟨-m i, by push_cast; ring⟩)
  funext i
  apply Int.cast_injective (α := ℝ)
  have hi := congrFun he i
  linarith

omit [Fintype D] in
theorem positiveIntegerPeriodization_periodic (H : (D → ℝ) → ℝ) (x : D → ℝ) (m : D → ℤ) :
    positiveIntegerPeriodization H (fun i => x i + (m i : ℝ)) = positiveIntegerPeriodization H x := by
  unfold positiveIntegerPeriodization
  have h := (Equiv.addRight m).tsum_eq (fun n : D → ℤ => H (fun i => x i + (n i : ℝ)))
  convert h using 1
  apply tsum_congr
  intro n
  congr 1
  funext i
  change x i + (m i : ℝ) + (n i : ℝ) = x i + ((n i + m i : ℤ) : ℝ)
  push_cast
  ring

omit [Fintype D] in
theorem positiveIntegerPeriodization_local (H : (D → ℝ) → ℝ)
    (hs : ∀ x, H x ≠ 0 → ∀ i, |x i| < 1/2) (x : D → ℝ) (hx : ∀ i, |x i| < 1/2) :
    positiveIntegerPeriodization H x = H x := by
  unfold positiveIntegerPeriodization
  rw [tsum_eq_single (0 : D → ℤ)]
  · simp
  · intro n hn
    by_contra hnonzero
    apply hn
    exact integer_shifts_small_box_injective x n 0 (hs _ hnonzero) (by simpa using hx)

omit [Fintype D] in
theorem positiveIntegerPeriodization_range (H : (D → ℝ) → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hH : ∀ x, 0 ≤ H x ∧ H x ≤ B)
    (hs : ∀ x, H x ≠ 0 → ∀ i, |x i| < 1/2) (x : D → ℝ) :
    0 ≤ positiveIntegerPeriodization H x ∧ positiveIntegerPeriodization H x ≤ B := by
  refine ⟨tsum_nonneg (fun n => (hH _).1), ?_⟩
  by_cases hx : ∃ n : D → ℤ, H (fun i => x i + (n i : ℝ)) ≠ 0
  · obtain ⟨n, hn⟩ := hx
    have he : positiveIntegerPeriodization H x = H (fun i => x i + (n i : ℝ)) := by
      apply tsum_eq_single n
      intro m hm
      by_contra hnonzero
      exact hm (integer_shifts_small_box_injective x m n (hs _ hnonzero) (hs _ hn))
    rw [he]
    exact (hH _).2
  · have hz : ∀ n : D → ℤ, H (fun i => x i + (n i : ℝ)) = 0 :=
      fun n => not_ne_iff.mp (fun hn => hx ⟨n, hn⟩)
    simp only [positiveIntegerPeriodization, hz, tsum_zero]
    exact hB

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.UnconditionedSpatialWidthBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def spatialWidthFraction (P τ : ℝ) : ℝ := τ/(8*(1+Real.exp (2*P)))

theorem spatialWidthFraction_pos (P : ℝ) {τ : ℝ} (hτ : 0 < τ) :
    0 < spatialWidthFraction P τ := by
  unfold spatialWidthFraction
  positivity

theorem spatial_threshold_large {P : ℝ} (hP : 0 ≤ P) {A : ℕ} (hA : 256 ≤ A) :
    Real.exp (5*P+128) ≤ Real.exp ((P+A)^A) := by
  have hAr : (256 : ℝ) ≤ A := by exact_mod_cast hA
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ (P+(A : ℝ))^2 := by nlinarith [sq_nonneg (P+(A : ℝ)-3)]
    _ ≤ _ := pow_le_pow_right₀ (by linarith) (by omega)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem spatialTrimMargin_size_of_exp_size {P τ H : ℝ} (hP : 0 ≤ P) (hτ : 0 < τ)
    (hτP : τ⁻¹ ≤ Real.exp P) (hH : Real.exp (5*P+128) ≤ H) : 4 ≤ τ*H := by
  have h4 : (4 : ℝ) ≤ Real.exp 128 := by linarith [Real.add_one_le_exp (128 : ℝ)]
  have h : 4/τ ≤ H := calc
    _ = 4*τ⁻¹ := div_eq_mul_inv _ _
    _ ≤ 4*Real.exp P := mul_le_mul_of_nonneg_left hτP (by norm_num)
    _ ≤ Real.exp 128 * Real.exp P := mul_le_mul_of_nonneg_right h4 (by positivity)
    _ = Real.exp (128+P) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (5*P+128) := Real.exp_le_exp.mpr (by linarith)
    _ ≤ H := hH
  simpa only [mul_comm H τ] using (div_le_iff₀ hτ).mp h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SampledCommonBox
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem commonStrideCount_exp_bound {p : ℝ} (hp : 0 ≤ p) :
    (⌈2 / Real.exp (-p)⌉₊ : ℝ) ≤ Real.exp (p + 2) := by
  rw [Real.exp_neg, div_inv_eq_mul]
  have hceil := (Nat.ceil_lt_add_one (show 0 ≤ 2 * Real.exp p by positivity)).le
  have h1 := Real.one_le_exp hp
  have h3 : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  calc
    _ ≤ 3 * Real.exp p := by linarith
    _ ≤ Real.exp 2 * Real.exp p := mul_le_mul_of_nonneg_right h3 (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add, add_comm]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.VectorSiteBudget
namespace OAI

section

namespace Erdos3

theorem siteCoefficientAllowance_le_exp (n : ℕ) {m M G C P : ℝ}
    (hm0 : 0 ≤ m) (hM0 : 0 ≤ M) (hG0 : 0 ≤ G) (hC0 : 0 ≤ C)
    (hm : m ≤ Real.exp P) (hM : M ≤ Real.exp (2 * P + 4))
    (hG : G ≤ Real.exp P) (hC : C ≤ Real.exp P) :
    m^n * M^n * (G * C) ≤ Real.exp ((3 * P + 4) * n + 2 * P) := by
  calc
    _ ≤ (Real.exp P)^n * (Real.exp (2 * P + 4))^n * (Real.exp P * Real.exp P) := by gcongr
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

end Erdos3

end

section

namespace Erdos3

theorem vectorSiteAllowance_le_exp (d : ℕ) {A P : ℝ} (hA : 0 ≤ A) (hAP : A ≤ Real.exp P) :
    A^d ≤ Real.exp (d * P) := by
  simpa only [Real.exp_nat_mul] using pow_le_pow_left₀ hA hAP d

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.SmoothSpatialProbability
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

noncomputable def scalarSpatialIndexAllowance (I : Type*) [Fintype I] (B : ℕ) : ℝ :=
  (B : ℝ)^(Fintype.card I + 1)

noncomputable def scalarSpatialInverseAllowance (I : Type*) [Fintype I] (B : ℕ) : ℝ :=
  (Fintype.card I + 1 : ℝ) * ((Fintype.card I + 1).factorial : ℝ) * B

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SmoothSpatialCostBudget
namespace OAI

section

namespace Erdos3

theorem scalarSpatialIndexAllowance_le_exp (I : Type*) [Fintype I] {B : ℕ} {R : ℝ}
    (hB : (B : ℝ) ≤ Real.exp R) :
    scalarSpatialIndexAllowance I B ≤ Real.exp ((Fintype.card I + 1 : ℝ) * R) := by
  unfold scalarSpatialIndexAllowance
  calc
    _ ≤ (Real.exp R)^(Fintype.card I + 1) := pow_le_pow_left₀ (Nat.cast_nonneg _) hB _
    _ = _ := by rw [← Real.exp_nat_mul]; push_cast; rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RowRestrictedDeckSiteMask
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical Matrix

noncomputable def coefficientDeckPeriodCap {m : ℕ} (O B : Fin m → Type*)
    [∀ j, Fintype (O j)] [∀ j, Fintype (B j)] (period : ℕ) : ℝ :=
  ∏ j, ∏ _i : B j, (period : ℝ) ^ Fintype.card (O j)

theorem coefficientDeckPeriodCap_nonneg {m : ℕ} (O B : Fin m → Type*)
    [∀ j, Fintype (O j)] [∀ j, Fintype (B j)] (period : ℕ) :
    0 ≤ coefficientDeckPeriodCap O B period := by
  unfold coefficientDeckPeriodCap
  positivity

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AnisotropicSpatialCapBudget
namespace OAI

section

namespace Erdos3

def anisotropicSpatialCapLog {A : Type*} [Semiring A] (P : A) : A :=
  P ^ 3 + 3 * P ^ 2 + 2 * P

theorem anisotropicSpatialCapLog_nonneg {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ anisotropicSpatialCapLog P := by
  unfold anisotropicSpatialCapLog
  positivity

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedTrimmedVectorSite
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

noncomputable def allocatedPrimitiveRootRatio (p : ℝ) : ℝ≥0 := Real.toNNReal (p + 1)

theorem allocatedPrimitiveRootRatio_bounds {p : ℝ} (hp : 0 ≤ p) :
    (allocatedPrimitiveRootRatio p : ℝ) = p + 1 ∧
      1 ≤ allocatedPrimitiveRootRatio p ∧
      (allocatedPrimitiveRootRatio p : ℝ) ≤ Real.exp (p + 1) := by
  have heq : (allocatedPrimitiveRootRatio p : ℝ) = p + 1 :=
    Real.coe_toNNReal _ (by linarith)
  refine ⟨heq, ?_, ?_⟩
  · exact_mod_cast (show (1 : ℝ) ≤ allocatedPrimitiveRootRatio p by rw [heq]; linarith)
  · rw [heq]
    linarith [Real.add_one_le_exp (p + 1)]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelCoefficientLogBudget
namespace OAI

section

namespace Erdos3

def kernelPeriodCandidate {B : ℕ} (degree : ℕ) (a : Fin B) : ℕ :=
  (a.val + 1) ^ degree

theorem kernelPeriodCandidate_pos {B : ℕ} (degree : ℕ) (a : Fin B) :
    0 < kernelPeriodCandidate degree a :=
  pow_pos (Nat.succ_pos _) _

theorem kernelPeriodCandidate_le {B : ℕ} (degree : ℕ) (a : Fin B) :
    kernelPeriodCandidate degree a ≤ B ^ degree :=
  Nat.pow_le_pow_left (Nat.succ_le_of_lt a.isLt) _

theorem kernelPeriodCandidate_le_exp {B : ℕ} {p : ℝ}
    (hB : (B : ℝ) ≤ Real.exp p) (degree : ℕ) (a : Fin B) :
    (kernelPeriodCandidate degree a : ℝ) ≤ Real.exp (degree * p) := by
  calc
    _ ≤ (B : ℝ) ^ degree := by exact_mod_cast kernelPeriodCandidate_le degree a
    _ ≤ (Real.exp p) ^ degree := pow_le_pow_left₀ (Nat.cast_nonneg _) hB _
    _ = _ := (Real.exp_nat_mul p degree).symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.NormalizedTwistNativeApproximationBudget
namespace OAI

section

namespace Erdos3

noncomputable def allocatedModelTestLog (u p : ℝ) : ℝ := 2 * u + 5 * p + 12

noncomputable def allocatedModelUnitThreshold (u p K C : ℝ) : ℝ :=
  (Real.exp (-(u + 3)) / Real.exp p ^ 2) /
    max 1 (K * (2 * C) / Real.exp (-(u + 3)))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CanonicalDetectedScaleInputBudget
namespace OAI

section

namespace Erdos3

noncomputable def slicedDetectionGainLog (s C count : ℕ) (p q a : ℝ) : ℝ :=
  (5 * p + 20) * count + p + 2 + a + 1 + (2 ^ (s + 1) : ℕ) * (q + C) ^ C

theorem slicedDetectionGainLog_nonneg (s C count : ℕ) {p q a : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (ha : 0 ≤ a) :
    0 ≤ slicedDetectionGainLog s C count p q a := by
  unfold slicedDetectionGainLog
  positivity

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.FiniteRowChartRadiusBudget
namespace OAI

section

namespace Erdos3

noncomputable def finiteRowChartRadius (rows dim : ℕ) (C T : ℝ) : ℝ :=
  1 / (4 * ((rows : ℝ) + 1) * (C + 1) * ((dim : ℝ) + 1) * (T + 1))

theorem finiteRowChartRadius_pos (rows dim : ℕ) {C T : ℝ} (hC : 0 ≤ C) (hT : 0 ≤ T) :
    0 < finiteRowChartRadius rows dim C T := by
  unfold finiteRowChartRadius
  positivity

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.OverlapCubeWeights
namespace OAI

section

namespace Erdos3

theorem overlap_weight_comparison (j : ℕ) {q r C D c δ : ℝ}
    (hq : 0 < q) (hr : 0 ≤ r) (hc : 0 ≤ c) (hδ : 0 ≤ δ)
    (hD : 0 < D) (hDq : D ≤ q ^ (j + 3))
    (hC : c * r ^ (j + 2) ≤ C) (hδr : δ * q ≤ r) :
    c * δ ^ (j + 1) * (r / q ^ 2) ≤ C / D := by
  have hδq : δ ≤ r / q := (le_div_iff₀ hq).mpr hδr
  have hC0 : 0 ≤ C := (mul_nonneg hc (pow_nonneg hr _)).trans hC
  calc
    _ ≤ c * (r / q) ^ (j + 1) * (r / q ^ 2) := by gcongr
    _ = (c * r ^ (j + 2)) / q ^ (j + 3) := by
      simp only [div_pow, pow_succ]
      field_simp
    _ ≤ C / q ^ (j + 3) := div_le_div_of_nonneg_right hC (by positivity)
    _ ≤ C / D := div_le_div_of_nonneg_left hC0 hD hDq

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DiagonalRowTransfer
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem quadratic_original_error_bound {d u e N : ℝ} (hd : 0 ≤ d) (hu : 0 ≤ u)
    (hdu : d ≤ Real.exp u) (hN : Real.exp (e + 4 * u + 40) ≤ N) :
    d ^ 4 * ((d ^ 2 + 1) * (d ^ 2 * ((1 + d ^ 2) *
      (4 * d ^ 2 * Real.exp (-(e + 12 * u + 40))))) +
        12 * Real.exp (-(e + 4 * u + 40)) + 2 / N) ≤ Real.exp (-e) := by
  have hp (n : ℕ) : d ^ n ≤ Real.exp ((n : ℝ) * u) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ hd hdu n
  have h2 : d ^ 2 + 1 ≤ 2 * Real.exp (2 * u) := by
    have hh := hp 2
    norm_num only [Nat.cast_ofNat] at hh
    linarith [Real.one_le_exp (show 0 ≤ 2 * u by positivity)]
  have hplus : (d ^ 2 + 1) ^ 2 ≤ 4 * Real.exp (4 * u) := by
    calc
      _ ≤ (2 * Real.exp (2 * u)) ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
      _ = 4 * Real.exp (4 * u) := by
        rw [mul_pow, ← Real.exp_nat_mul]
        norm_num
        ring_nf
  have hcoef : 4 * d ^ 8 * (d ^ 2 + 1) ^ 2 ≤ 16 * Real.exp (12 * u) := by
    calc
      _ ≤ 4 * Real.exp (8 * u) * (4 * Real.exp (4 * u)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (by simpa only [Nat.cast_ofNat] using hp 8)
          (by norm_num)) hplus (by positivity) (by positivity)
      _ = _ := by rw [show 4 * Real.exp (8 * u) * (4 * Real.exp (4 * u)) =
        16 * (Real.exp (8 * u) * Real.exp (4 * u)) by ring, ← Real.exp_add]; congr 2; ring
  have hfirst : d ^ 4 * ((d ^ 2 + 1) * (d ^ 2 * ((1 + d ^ 2) *
      (4 * d ^ 2 * Real.exp (-(e + 12 * u + 40)))))) ≤ 16 * Real.exp (-(e + 40)) := by
    calc
      _ = (4 * d ^ 8 * (d ^ 2 + 1) ^ 2) * Real.exp (-(e + 12 * u + 40)) := by ring
      _ ≤ (16 * Real.exp (12 * u)) * Real.exp (-(e + 12 * u + 40)) :=
        mul_le_mul_of_nonneg_right hcoef (Real.exp_nonneg _)
      _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  have hfour : d ^ 4 ≤ Real.exp (4 * u) := by simpa only [Nat.cast_ofNat] using hp 4
  have hscaled : d ^ 4 * Real.exp (-(e + 4 * u + 40)) ≤ Real.exp (-(e + 40)) := by
    calc
      _ ≤ Real.exp (4 * u) * Real.exp (-(e + 4 * u + 40)) :=
        mul_le_mul_of_nonneg_right hfour (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hrecip : 1 / N ≤ Real.exp (-(e + 4 * u + 40)) := by
    have hh := one_div_le_one_div_of_le (Real.exp_pos _) hN
    simpa only [one_div, ← Real.exp_neg] using hh
  have hthird : d ^ 4 * (2 / N) ≤ 2 * Real.exp (-(e + 40)) := by
    have hh := (mul_le_mul_of_nonneg_left hrecip (pow_nonneg hd 4)).trans hscaled
    calc
      _ = 2 * (d ^ 4 * (1 / N)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hh (by norm_num)
  have hsum : d ^ 4 * ((d ^ 2 + 1) * (d ^ 2 * ((1 + d ^ 2) *
      (4 * d ^ 2 * Real.exp (-(e + 12 * u + 40))))) +
        12 * Real.exp (-(e + 4 * u + 40)) + 2 / N) ≤ 30 * Real.exp (-(e + 40)) := by
    nlinarith
  apply hsum.trans
  calc
    _ ≤ Real.exp 40 * Real.exp (-(e + 40)) :=
      mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (40 : ℝ)]) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoefficientSquareSpatialBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def coefficientErrorVolumeLog {A : Type*} [Semiring A] (P : A) : A := P ^ 2 * (P + 61)

def coefficientErrorSpatialLog {A : Type*} [Semiring A] (P : A) : A :=
  P * (P ^ 3 + anisotropicSpatialCapLog P) + coefficientErrorVolumeLog P

theorem coefficientErrorSpatialLog_nonneg {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ coefficientErrorSpatialLog P := by
  have h := anisotropicSpatialCapLog_nonneg hP
  unfold coefficientErrorSpatialLog coefficientErrorVolumeLog
  positivity

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerRadixCoding
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def integerRadixValue : {n : ℕ} → (Fin n → ℕ) → (Fin n → ℤ) → ℤ
  | 0, _, _ => 0
  | n + 1, R, x => x 0 + (R 0 : ℤ) * integerRadixValue (fun i : Fin n => R i.succ) (fun i => x i.succ)

theorem integerRadixValue_zero {n : ℕ} (R : Fin n → ℕ) :
    integerRadixValue R 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (0 : ℤ) + (R 0 : ℤ) * integerRadixValue (fun i : Fin n => R i.succ) 0 = 0
      rw [ih, mul_zero, add_zero]

theorem integerRadixValue_add {n : ℕ} (R : Fin n → ℕ) (x y : Fin n → ℤ) :
    integerRadixValue R (x + y) = integerRadixValue R x + integerRadixValue R y := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [integerRadixValue, Pi.add_apply]
      rw [show (fun i : Fin n => x i.succ + y i.succ) =
        (fun i => x i.succ) + (fun i => y i.succ) from rfl, ih]
      ring

def integerRadixHom {n : ℕ} (R : Fin n → ℕ) : (Fin n → ℤ) →+ ℤ where
  toFun := integerRadixValue R
  map_zero' := integerRadixValue_zero R
  map_add' := integerRadixValue_add R

theorem integerRadixValue_bounds {n : ℕ} (R : Fin n → ℕ) (x : Fin n → ℤ)
    (hx : ∀ i, 0 ≤ x i ∧ x i < (R i : ℤ)) :
    0 ≤ integerRadixValue R x ∧ integerRadixValue R x < ((∏ i, R i : ℕ) : ℤ) := by
  induction n with
  | zero => simp [integerRadixValue]
  | succ n ih =>
      have h0 := hx 0
      have ht := ih (fun i => R i.succ) (fun i => x i.succ) (fun i => hx i.succ)
      have hm := mul_le_mul_of_nonneg_left
        (show integerRadixValue (fun i : Fin n => R i.succ) (fun i => x i.succ) ≤
          ((∏ i : Fin n, R i.succ : ℕ) : ℤ) - 1 by omega)
        (Nat.cast_nonneg (R 0) : (0 : ℤ) ≤ R 0)
      rw [integerRadixValue, Fin.prod_univ_succ, Nat.cast_mul]
      constructor
      · exact add_nonneg h0.1 (mul_nonneg (Nat.cast_nonneg _) ht.1)
      · nlinarith

theorem integerRadixValue_injective_on_digits {n : ℕ} (R : Fin n → ℕ)
    (x y : Fin n → ℤ) (hx : ∀ i, 0 ≤ x i ∧ x i < (R i : ℤ))
    (hy : ∀ i, 0 ≤ y i ∧ y i < (R i : ℤ))
    (he : integerRadixValue R x = integerRadixValue R y) : x = y := by
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
      have hx0 := hx 0
      have hy0 := hy 0
      have hR : (R 0 : ℤ) ≠ 0 := ne_of_gt (lt_of_le_of_lt hx0.1 hx0.2)
      have h0 : x 0 = y 0 := by
        have h := congrArg (fun z : ℤ => z % (R 0 : ℤ)) he
        simpa only [integerRadixValue, Int.add_emod, Int.mul_emod, Int.emod_self,
          zero_mul, Int.zero_emod, add_zero, Int.emod_eq_of_lt hx0.1 hx0.2,
          Int.emod_eq_of_lt hy0.1 hy0.2] using h
      have ht : integerRadixValue (fun i : Fin n => R i.succ) (fun i => x i.succ) =
          integerRadixValue (fun i : Fin n => R i.succ) (fun i => y i.succ) := by
        apply mul_left_cancel₀ hR
        simpa only [integerRadixValue, h0, add_left_cancel_iff] using he
      have hh := ih (fun i => R i.succ) (fun i => x i.succ) (fun i => y i.succ)
        (fun i => hx i.succ) (fun i => hy i.succ) ht
      funext i
      exact Fin.cases h0 (fun j => congrFun hh j) i

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

def boxCodeModulus {n : ℕ} (T : Fin n → ℕ) : ℕ := ∏ i, 4 * T i

def boxIntegerCode {n : ℕ} (T : Fin n → ℕ) : (Fin n → ℤ) →+ ℤ :=
  integerRadixHom (fun i => 4 * T i)

def boxCyclicCode {n : ℕ} (T : Fin n → ℕ) : (Fin n → ℤ) →+ ZMod (boxCodeModulus T) :=
  (Int.castAddHom (ZMod (boxCodeModulus T))).comp (boxIntegerCode T)

theorem boxCodeModulus_pos {n : ℕ} (T : Fin n → ℕ) [∀ i, NeZero (T i)] :
    0 < boxCodeModulus T :=
  Finset.prod_pos (fun i _ => Nat.mul_pos (by norm_num) (NeZero.pos (T i)))

instance boxCodeModulus_neZero {n : ℕ} (T : Fin n → ℕ) [∀ i, NeZero (T i)] :
    NeZero (boxCodeModulus T) := ⟨(boxCodeModulus_pos T).ne'⟩

theorem boxCodeModulus_eq {n : ℕ} (T : Fin n → ℕ) :
    boxCodeModulus T = 4 ^ n * ∏ i, T i := by
  simp [boxCodeModulus, Finset.prod_mul_distrib]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CanonicalEmptyLayerGeometry
namespace OAI

section

namespace Erdos3.VectorPolynomial.CanonicalEmptyLayerGeometry

open Module Submodule

abbrev Q (q : ℕ) (_ : Fin q) : Type := PEmpty

end Erdos3.VectorPolynomial.CanonicalEmptyLayerGeometry

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SpatialTupleErrorBudget
namespace OAI

section

namespace Erdos3

theorem twoTermErrorWidth_spec {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) :
    0 < twoTermErrorWidth B ε ∧ twoTermErrorWidth B ε ≤ 1 ∧
      B * twoTermErrorWidth B ε ≤ ε / 2 := by
  have hden : 0 < 2 * (1 + B) := by positivity
  refine ⟨lt_min zero_lt_one (div_pos hε hden), min_le_left _ _, ?_⟩
  calc
    _ ≤ B * (ε / (2 * (1 + B))) := mul_le_mul_of_nonneg_left (min_le_right _ _) hB
    _ ≤ ε / 2 := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hden).mpr
      nlinarith

noncomputable def spatialTupleTolerance (n : ℕ) (G V ε : ℝ) : ℝ :=
  min (1 / 4) (ε / (2 * (n + 1) * (2 + G) ^ n * (1 + V)))

theorem spatialTupleTolerance_spec (n : ℕ) {G V ε : ℝ}
    (hG : 0 ≤ G) (hV : 0 ≤ V) (hε : 0 < ε) :
    0 < spatialTupleTolerance n G V ε ∧ spatialTupleTolerance n G V ε ≤ 1 / 4 ∧
      spatialTupleTolerance n G V ε * (2 * (n + 1) * (2 + G) ^ n * (1 + V)) ≤ ε := by
  have hden : 0 < 2 * (n + 1 : ℝ) * (2 + G) ^ n * (1 + V) := by positivity
  refine ⟨lt_min (by norm_num) (div_pos hε hden), min_le_left _ _, ?_⟩
  exact (le_div_iff₀ hden).mp (min_le_right _ _)

end Erdos3

end

section

namespace Erdos3

def spatialTupleToleranceLog {A : Type*} [Semiring A] (P : A) : A := P ^ 2 + 5 * P + 6

theorem spatialTupleToleranceLog_nonneg {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ spatialTupleToleranceLog P := by unfold spatialTupleToleranceLog; positivity

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SpatialNumericEnvelopeFunctoriality
namespace OAI

section

namespace Erdos3

open VectorPolynomial

noncomputable def spatialTupleCoarseMesh (n : ℕ) (G V K ε : ℝ) : ℝ :=
  twoTermErrorWidth K (spatialTupleTolerance n G V ε) / 4

theorem spatialTupleCoarseMesh_spec (n : ℕ) {G V K ε : ℝ}
    (hG : 0 ≤ G) (hV : 0 ≤ V) (hK : 0 ≤ K) (hε : 0 < ε) :
    0 < spatialTupleCoarseMesh n G V K ε ∧ spatialTupleCoarseMesh n G V K ε ≤ 1 / 4 ∧
      ∀ {g k v : ℝ}, 0 ≤ g → g ≤ G → 0 ≤ k → k ≤ K → 0 ≤ v → v ≤ V →
        n * (8 * k * spatialTupleCoarseMesh n G V K ε) * (1 + g)^n * v ≤ ε := by
  let t := spatialTupleTolerance n G V ε
  let δ := twoTermErrorWidth K t
  have ht := spatialTupleTolerance_spec n hG hV hε
  have hδ := twoTermErrorWidth_spec hK ht.1
  have ht0 : 0 < t := ht.1
  have hδ0 : 0 < δ := hδ.1
  have hr : 0 < spatialTupleCoarseMesh n G V K ε := div_pos hδ.1 (by norm_num)
  refine ⟨hr, div_le_div_of_nonneg_right hδ.2.1 (by norm_num), ?_⟩
  intro g k v hg hgG hk hkK hv hvV
  have hinner : 8 * k * spatialTupleCoarseMesh n G V K ε ≤ t := by
    have hkδ : k * δ ≤ K * δ := mul_le_mul_of_nonneg_right hkK hδ0.le
    change 8 * k * (δ / 4) ≤ t
    linarith [hδ.2.2]
  have hp : (1 + g)^n ≤ (2 + G)^n :=
    pow_le_pow_left₀ (by positivity) (by linarith) n
  calc
    _ ≤ n * t * (2 + G)^n * V := by gcongr
    _ = t * (2 + G)^n * (n * V) := by ring
    _ ≤ t * (2 + G)^n * (2 * (n + 1) * (1 + V)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    _ = t * (2 * (n + 1) * (2 + G)^n * (1 + V)) := by ring
    _ ≤ ε := ht.2.2

end Erdos3

end

section

namespace Erdos3

section Maps

variable {α β : Type*} [Semiring α] [Semiring β] (f : α →+* β)

@[simp] theorem map_coefficientErrorSpatialLog (p : α) :
    f (coefficientErrorSpatialLog p) = coefficientErrorSpatialLog (f p) := by
  simp [coefficientErrorSpatialLog, coefficientErrorVolumeLog, anisotropicSpatialCapLog,
    map_ofNat]

@[simp] theorem map_spatialTupleToleranceLog (p : α) :
    f (spatialTupleToleranceLog p) = spatialTupleToleranceLog (f p) := by
  simp [spatialTupleToleranceLog, map_ofNat]

end Maps

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoarseSpatialPartitionBudget
namespace OAI

section

namespace Erdos3

def coarseSpatialReciprocalLog {A : Type*} [Semiring A] (P : A) : A :=
  2 * (P + spatialTupleToleranceLog P) + 8

def coarseSpatialPartitionLog {A : Type*} [Semiring A] (P : A) : A :=
  let R := P + coarseSpatialReciprocalLog P + 4
  R * ((3 * R + 4) * R + 2 * R)

theorem coarseSpatialLogs_nonneg {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ coarseSpatialReciprocalLog P ∧ 0 ≤ coarseSpatialPartitionLog P := by
  have ht := spatialTupleToleranceLog_nonneg hP
  have hL : 0 ≤ coarseSpatialReciprocalLog P := by unfold coarseSpatialReciprocalLog; positivity
  exact ⟨hL, by unfold coarseSpatialPartitionLog; positivity⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedInactiveSupportBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace VectorPolynomial

def allocatedNaturalSupportLog {A : Type*} [Semiring A] (D : A) : A := D ^ 2 + 3 * D + 7

def allocatedNaturalSiteLog {A : Type*} [Semiring A] (D : A) : A := D ^ 2 + 4 * D + 8

theorem allocatedNaturalSupportLog_nonneg {D : ℝ} (hD : 0 ≤ D) :
    0 ≤ allocatedNaturalSupportLog D := by unfold allocatedNaturalSupportLog; positivity

end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedSlicedGridGeometryBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical

def slicedGridGeometryLog {A : Type*} [Semiring A] (D v w t : A) : A :=
  (D + 1) * (D ^ 2 + 2 * D + v + 8 + (D + v + 8 + D + 1) + D * w) +
    (2 * D * t + D + 2 * (D + v + 8) + 5) + (D ^ 2 + 2 * D + 2 * v + 1)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformProductAccuracyLogBounds
namespace OAI

section

namespace Erdos3

def uniformProductAccuracyLog {A : Type*} [Semiring A] (D T E : A) : A :=
  D + D * (T + 4) + E

theorem uniformProductAccuracyLog_nonneg {D T E : ℝ}
    (hD : 0 ≤ D) (hT : 0 ≤ T) (hE : 0 ≤ E) :
    0 ≤ uniformProductAccuracyLog D T E := by unfold uniformProductAccuracyLog; positivity

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.UniformSpectrumLogBounds
namespace OAI

section

namespace Erdos3

def majorArcLocalizationLog {A : Type*} [Semiring A] (n : ℕ) (p : A) : A :=
  256 + 6 * p + ((n + 1) * 2 : ℕ) * (1 + 2 * p)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedActiveBudgetedSite
namespace OAI

section

namespace Erdos3

def siteExponentialOutputLog {A : Type*} [Semiring A] (s : ℕ) (Q : A) : A :=
  s * (4 * Q + 8) + 8 * Q + 18

theorem siteExponentialOutputLog_nonneg (s : ℕ) {Q : ℝ} (hQ : 0 ≤ Q) :
    0 ≤ siteExponentialOutputLog s Q := by unfold siteExponentialOutputLog; positivity

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineAmbientPrimitiveBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped NNReal

def affineAmbientMassLog {A : Type*} [Semiring A] (P : A) : A :=
  4 * P ^ 3 + 9 * P ^ 2 + 5 * P

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped NNReal

noncomputable def affineAmbientPrimitiveBudget {A : Type*} [Semiring A] (base Q : A) : A :=
  let P₂ := 9 * (9 * (base + Q) + 13) + 5
  2 * affineAmbientMassLog P₂ + 7 * P₂ + 1

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

def allocatedFiniteIdealProfileLog {A : Type*} [Semiring A] (D p : A) : A :=
  3 * D + (2 * D + 2) * p + 1

def allocatedFiniteIdealCoefficientLog {A : Type*} [Semiring A]
    (m : ℕ) (D p : A) : A :=
  (2 ^ (m + 1) : ℕ) * D * (4 * allocatedFiniteIdealProfileLog D p + 8) +
    allocatedFiniteIdealProfileLog D p

def allocatedFiniteIdealLipschitzLog {A : Type*} [Semiring A] (D p c : A) : A :=
  D + 6 * allocatedFiniteIdealProfileLog D p + c + 14

theorem allocatedFiniteIdeal_budget_nonneg (m : ℕ) {D p c : ℝ}
    (hD : 0 ≤ D) (hp : 0 ≤ p) (hc : 0 ≤ c) :
    0 ≤ allocatedFiniteIdealProfileLog D p ∧
      0 ≤ allocatedFiniteIdealCoefficientLog m D p ∧
      0 ≤ allocatedFiniteIdealLipschitzLog D p c := by
  dsimp only [allocatedFiniteIdealProfileLog, allocatedFiniteIdealCoefficientLog,
    allocatedFiniteIdealLipschitzLog]
  refine ⟨?_, ?_, ?_⟩ <;> positivity

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedCanonicalPeriodPrimitiveBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

theorem canonicalCoefficientDeckPeriodCap_le_exp {m : ℕ} (O Q : Fin m → Type*)
    [∀ j, Fintype (O j)] [∀ j, Fintype (Q j)] {period : ℕ} {L : ℝ}
    (hperiod : (period : ℝ) ≤ Real.exp L) :
    coefficientDeckPeriodCap O Q period ≤
      Real.exp (∑ j, (Fintype.card (Q j) : ℝ) * (Fintype.card (O j) * L)) := by
  unfold coefficientDeckPeriodCap
  calc
    _ ≤ ∏ j, ∏ _i : Q j, Real.exp ((Fintype.card (O j) : ℝ) * L) := by
      apply Finset.prod_le_prod (fun _ _ => by positivity)
      intro j _
      apply Finset.prod_le_prod (fun _ _ => by positivity)
      intro i _
      rw [Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) hperiod _
    _ = _ := by
      simp only [← Real.exp_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem periodFunctionLabelCard_le_exp {m : ℕ} (Q : Fin m → Type*)
    [∀ j, Fintype (Q j)] {period : ℕ} [NeZero period] {L : ℝ}
    (hperiod : (period : ℝ) ≤ Real.exp L) :
    (Fintype.card (∀ j, Q j → ZMod period) : ℝ) ≤
      Real.exp (∑ j, (Fintype.card (Q j) : ℝ) * L) := by
  simp only [Fintype.card_pi, ZMod.card, Finset.prod_const, Finset.card_univ,
    Nat.cast_prod, Nat.cast_pow]
  calc
    _ ≤ ∏ j, Real.exp ((Fintype.card (Q j) : ℝ) * L) := by
      apply Finset.prod_le_prod (fun _ _ => by positivity)
      intro j _
      rw [Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) hperiod _
    _ = _ := (Real.exp_sum _ _).symm

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ForecastSlicedEarlyUnrestrictedPolynomialBudget
namespace OAI

section

namespace Erdos3
open scoped BigOperators

@[gcongr] theorem majorArcLocalizationLog_mono_budget (n : ℕ) {p p₂ : ℝ}
    (hp : p ≤ p₂) :
    majorArcLocalizationLog n p ≤ majorArcLocalizationLog n p₂ := by
  unfold majorArcLocalizationLog
  gcongr

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedModularGeneralNativeBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical

def allocatedAmbientNormalizationLog {A : Type*} [Semiring A]
    (dim : ℕ) (D V Q E : A) : A :=
  (dim + 1 : ℕ) * D * (8 + Q + E) + (dim : ℕ) * D * (V + 1)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedFiniteNestedSourceRelativeInitializerBounds
namespace OAI

section

namespace Erdos3

theorem twice_chartCoefficient_le_exp {C Pchart Bstruct : ℝ}
    (hC : C ≤ Real.exp Pchart) (hallow : Pchart + 1 ≤ Bstruct) :
    2 * C ≤ Real.exp Bstruct := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    linarith only [Real.add_one_le_exp (1 : ℝ)]
  calc
    2 * C ≤ 2 * Real.exp Pchart := mul_le_mul_of_nonneg_left hC (by norm_num)
    _ ≤ Real.exp 1 * Real.exp Pchart :=
      mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
    _ = Real.exp (Pchart + 1) := by rw [← Real.exp_add, add_comm]
    _ ≤ Real.exp Bstruct := Real.exp_le_exp.mpr hallow

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedFiniteScheduleLocalScalarConstruction
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

noncomputable def preparedFiniteScheduleLocalMaster
    (Pchart D pRadius Qstride Pphysical u pModel Prho target gainLog : ℝ) : ℝ :=
  Pchart + D + pRadius + Qstride + Pphysical +
    (u + pModel + allocatedModelTestLog u pModel + Prho + target + gainLog + 32)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.PreparedUniformShortSourceRankBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

structure PreparedSourceScalarData where
  D : ℝ
  pRadius : ℝ
  Ptail : ℝ
  Prho : ℝ
  Pk : ℝ
  target : ℝ
  F : ℝ
  Tmod : ℝ
  Ppert : ℝ
  Epert : ℝ
  Bstruct : ℝ
  Pmin : ℝ
  Elog : ℝ
  Vlog : ℝ
  master : ℝ
  Pphysical : ℝ
  lateTarget : ℝ
  Eforecast : ℝ
  gainLog : ℝ

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CandidateNestedDegreeNetSchedule
namespace OAI

section

namespace Erdos3.VectorPolynomial

def candidateDegreeReturnBudget (degree : ℕ) (q : ℝ) : ℝ :=
  (3 : ℝ) ^ degree * (q + 1) - 1

@[simp] theorem candidateDegreeReturnBudget_zero (q : ℝ) :
    candidateDegreeReturnBudget 0 q = q := by
  simp [candidateDegreeReturnBudget]

theorem candidateDegreeReturnBudget_succ (degree : ℕ) (q : ℝ) :
    candidateDegreeReturnBudget (degree + 1) q =
      3 * candidateDegreeReturnBudget degree q + 2 := by
  simp only [candidateDegreeReturnBudget, pow_succ]
  ring

theorem candidateDegreeReturnBudget_nonneg (degree : ℕ) {q : ℝ} (hq : 0 ≤ q) :
    0 ≤ candidateDegreeReturnBudget degree q := by
  induction degree with
  | zero => simpa using hq
  | succ degree ih =>
    rw [candidateDegreeReturnBudget_succ]
    positivity

theorem candidateDegreeReturnBudget_monotone_degree {q : ℝ} (hq : 0 ≤ q) :
    Monotone (fun degree => candidateDegreeReturnBudget degree q) := by
  apply monotone_nat_of_le_succ
  intro degree
  rw [candidateDegreeReturnBudget_succ]
  have h := candidateDegreeReturnBudget_nonneg degree hq
  linarith only [h]

theorem le_candidateDegreeReturnBudget (degree : ℕ) {q : ℝ} (hq : 0 ≤ q) :
    q ≤ candidateDegreeReturnBudget degree q := by
  simpa only [candidateDegreeReturnBudget_zero] using
    candidateDegreeReturnBudget_monotone_degree hq (Nat.zero_le degree)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PreparedFiniteNestedForwardAllDegreePaddedSource
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule
open scoped Classical BigOperators NNReal TensorProduct

abbrev PreparedFiniteNestedForwardAllDegreeSlot (outerDepth innerDepth cutoff : ℕ) :=
  Fin (outerDepth + 1) × Fin (innerDepth + 1) × Fin (cutoff + 1) × Bool

def preparedFiniteNestedForwardAllDegreeOuter {outerDepth innerDepth cutoff : ℕ}
    (k : PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff) :
    Fin (outerDepth + 1) := k.1

def preparedFiniteNestedForwardAllDegreeStage {outerDepth innerDepth cutoff : ℕ}
    (k : PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff) :
    Fin (innerDepth + 1) := k.2.1

def preparedFiniteNestedForwardAllDegreeIsDirect {outerDepth innerDepth cutoff : ℕ}
    (k : PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff) : Bool :=
  k.2.2.2

def preparedFiniteNestedForwardAllDegreeDegree {outerDepth innerDepth cutoff : ℕ}
    (k : PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff) : ℕ :=
  k.2.2.1.val

def preparedFiniteNestedForwardAllDegreeAnchor (outerDepth innerDepth cutoff : ℕ) :
    PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff :=
  (⟨outerDepth, Nat.lt_succ_self outerDepth⟩,
    ⟨innerDepth, Nat.lt_succ_self innerDepth⟩, 0, false)

@[simp] theorem preparedFiniteNestedForwardAllDegreeOuter_slot {outerDepth innerDepth cutoff : ℕ}
    (outer : Fin (outerDepth + 1)) (inner : Fin (innerDepth + 1))
    (degree : Fin (cutoff + 1)) (direct : Bool) :
    preparedFiniteNestedForwardAllDegreeOuter (outer, inner, degree, direct) = outer := rfl

@[simp] theorem preparedFiniteNestedForwardAllDegreeStage_slot {outerDepth innerDepth cutoff : ℕ}
    (outer : Fin (outerDepth + 1)) (inner : Fin (innerDepth + 1))
    (degree : Fin (cutoff + 1)) (direct : Bool) :
    preparedFiniteNestedForwardAllDegreeStage (outer, inner, degree, direct) = inner := rfl

@[simp] theorem preparedFiniteNestedForwardAllDegreeIsDirect_slot {outerDepth innerDepth cutoff : ℕ}
    (outer : Fin (outerDepth + 1)) (inner : Fin (innerDepth + 1))
    (degree : Fin (cutoff + 1)) (direct : Bool) :
    preparedFiniteNestedForwardAllDegreeIsDirect (outer, inner, degree, direct) = direct := rfl

@[simp] theorem preparedFiniteNestedForwardAllDegreeDegree_slot {outerDepth innerDepth cutoff : ℕ}
    (outer : Fin (outerDepth + 1)) (inner : Fin (innerDepth + 1))
    (degree : Fin (cutoff + 1)) (direct : Bool) :
    preparedFiniteNestedForwardAllDegreeDegree (outer, inner, degree, direct) = degree.val := rfl

@[simp] theorem preparedFiniteNestedForwardAllDegreeAnchor_outer
    (outerDepth innerDepth cutoff : ℕ) :
    preparedFiniteNestedForwardAllDegreeOuter
      (preparedFiniteNestedForwardAllDegreeAnchor outerDepth innerDepth cutoff) =
      ⟨outerDepth, Nat.lt_succ_self outerDepth⟩ := rfl

@[simp] theorem preparedFiniteNestedForwardAllDegreeAnchor_stage
    (outerDepth innerDepth cutoff : ℕ) :
    preparedFiniteNestedForwardAllDegreeStage
      (preparedFiniteNestedForwardAllDegreeAnchor outerDepth innerDepth cutoff) =
      ⟨innerDepth, Nat.lt_succ_self innerDepth⟩ := rfl

@[simp] theorem preparedFiniteNestedForwardAllDegreeAnchor_model
    (outerDepth innerDepth cutoff : ℕ) :
    preparedFiniteNestedForwardAllDegreeIsDirect
      (preparedFiniteNestedForwardAllDegreeAnchor outerDepth innerDepth cutoff) = false := rfl

@[simp] theorem preparedFiniteNestedForwardAllDegreeAnchor_degree
    (outerDepth innerDepth cutoff : ℕ) :
    preparedFiniteNestedForwardAllDegreeDegree
      (preparedFiniteNestedForwardAllDegreeAnchor outerDepth innerDepth cutoff) = 0 := rfl

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedPrimitiveFrontInitialLong
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule
open scoped BigOperators Classical TensorProduct NNReal

theorem allocatedCandidate_retainedMass_pos {massLog retainedLoss massH : ℝ}
    (hmass : Real.exp (-massLog) ≤ massH) :
    0 < Real.exp (-retainedLoss) * massH :=
  mul_pos (Real.exp_pos _) ((Real.exp_pos _).trans_le hmass)

end Erdos3.VectorPolynomial

end

end OAI
end


