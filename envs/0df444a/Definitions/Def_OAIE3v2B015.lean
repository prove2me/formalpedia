-- Prove2me | Definitions.Def_OAIE3v2B015
-- name    : OAIE3v2B015
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T09:58:06.556976+00:00
-- url     : https://prove2.me/theorems/77fa2f51-15b8-45e1-92a0-f11d235457ff
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 16 of 311
-- statement:
--   Definitions bundle 16 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports no other bundle of this split.
--
--   Modules: `Estimates/ActiveProfileNoise.lean`, `Estimates/BooleanCubeProduct.lean`, `Estimates/CanonicalEmptyLayerGeometry.lean`, `Estimates/CanonicalScalarSourceEnvelope.lean`, `Estimates/ComplexFiniteMeans.lean`, `Estimates/CoveredInducedCorrelationFamily.lean`, `Estimates/CyclicCutNeighborhood.lean`, `Estimates/CyclicShortShiftSet.lean`, `Estimates/FixedPartnerPower.lean`, `Estimates/NormalizedIntervalWindow.lean`, `Estimates/PaddedBooleanFeatures.lean`, `Estimates/PreparedScalarStructuralBasePower.lean`, `Estimates/ProductiveFrozenLocalMajorFamily.lean`, `Estimates/RationalTaggedConstraintHistory.lean`, `Estimates/ScalarCubeDomain.lean`, `Estimates/SlicedPairAmplitude.lean`, `Estimates/SmoothSublevelCutoff.lean`, `Estimates/UniformProductAccuracy.lean`, `Fourier/IntegerSupportTorus.lean`, `Fourier/UniformScaledRetainedCharacters.lean`, `Fourier/WeightedBlockTorus.lean`, `Geometry/BoxDetectionExponents.lean`, `Geometry/BoxWindowAveraging.lean`, `Geometry/CertifiedFullChartFrozenTerminal.lean`, `Geometry/CoordinateCopySum.lean`, `Geometry/CubeSignalCoordinates.lean`, `Geometry/DenseRealBoxCell.lean`, `Geometry/FixedSpatialEmptyCoordinates.lean`, `Geometry/LowTaggedCoordinateRestriction.lean`, `Geometry/MissingCoordinateProducts.lean`, `Geometry/MixedCoveredChart.lean`, `Geometry/MixedProfileCoordinates.lean`, `Geometry/ProductEuclideanCoordinates.lean`, `Geometry/SigmaAxisCoordinates.lean`, `Geometry/TwoBoxSmoothingComplex.lean`, `Geometry/UnconditionedSpatialWidthBudget.lean`, `Geometry/UnitBoxAmplitude.lean`, `Geometry/VariableRoundedGraphCoordinates.lean`, `Geometry/WeightedBlockSupportScale.lean`, `Lattices/AffineBoxTest.lean`, `Lattices/AffineWindowGoodKernelBound.lean`, `Lattices/CommonIntegerIntervalCorrelation.lean`, `Lattices/CubeResidueSupport.lean`, `Lattices/IntegerFrozenChart.lean`, `Lattices/LargestBadPrimeProduct.lean`, `Lattices/NormalizedLatticeSheet.lean`, `Lattices/PhysicalSubboxResidueSlice.lean`, `Lattices/RandomAffinePair.lean`, `Lattices/RelativeSliceAffineThreeFactorLaw.lean`, `Lattices/ResidueCutoffLengthBudget.lean`, `Lattices/ScalarResidueInteriorCell.lean`, `Lattices/SmoothBadPrimeProduct.lean`, `Lattices/SmoothIntegerTranslation.lean`, `Linear/AllocatedModularRankCongruenceOutput.lean`, `Linear/BalancedDualBounds.lean`, `Linear/ContainedKernelPhysicalDisplacement.lean`, `Linear/LowTaggedCoordinateProjection.lean`, `Linear/MahlerBasis.lean`, `Linear/ProperCyclicKernelBasis.lean`, `Linear/SpatialMatrixBlockWideProbability.lean`, `Nilpotent/LocalMajorDenseSliceNiltest.lean`, `Polynomial/BufferedSampledCurrentGradePhase.lean`, `Polynomial/CRTPolynomialChargeBound.lean`, `Polynomial/CRTPolynomialImage.lean`, `Polynomial/CRTPolynomialInputAffineLaw.lean`, `Polynomial/LowTaggedPolynomialCoordinates.lean`, `Polynomial/NormalizedRealPolynomialChart.lean`, `Polynomial/PolynomialParameterContinuity.lean`, `Polynomial/RationalPolynomialForecastBoxError.lean`, `Polynomial/TranslationPolynomialSymbolLiftHom.lean`, `Polynomial/VectorPolynomialReconstruction.lean`, `Probability/AllocatedPhysicalCoveredDensity.lean`, `Probability/AnisotropicSmoothPairLaw.lean`, `Probability/BinaryDensity.lean`, `Probability/DensityMixtureAELaw.lean`, `Probability/DiagonalDensityTransport.lean`, `Probability/LargeCokernelProbability.lean`, `Probability/PairedProductDensity.lean`, `Probability/RestrictedComplexChartDensityComparison.lean`, `Probability/SlicedRemainderDensityFamily.lean`, `Sampling/ActualFixedSpatialSlicedForecastSourceLaw.lean`, `Sampling/AllocatedDenseFiberSliceForecastGeometry.lean`, `Sampling/AllocatedExternalLocalGoodForecastPath.lean`, `Sampling/FixedPathSlicedGridMeshBudget.lean`, `Sampling/ForecastModularCutoff.lean`, `Sampling/ForecastOriginalSampleUniformBudget.lean`, `Sampling/SamplingRankProjectedContainment.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedIntervalWindow
namespace OAI

section

namespace Erdos3

open MeasureTheory _root_.Set

noncomputable def intervalWindow (a b : ℝ) : ℝ → ℝ :=
  (Ioc a b).indicator (fun _ => 1)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

noncomputable def normalizedIntervalWindow (ℓ x t : ℝ) : ℝ :=
  intervalWindow x (x + ℓ) t / ℓ

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ComplexFiniteMeans
namespace OAI

section

open scoped BigOperators

namespace Erdos3

theorem prod_bool_tuple_succ {M : Type*} [CommMonoid M] {n : ℕ}
    (F : (Fin (n + 1) → Bool) → M) :
    (∏ ω, F ω) =
      (∏ ω : Fin n → Bool, F (Fin.cons false ω)) *
        (∏ ω : Fin n → Bool, F (Fin.cons true ω)) := by
  calc
    (∏ ω, F ω) = ∏ q : Bool × (Fin n → Bool), F (Fin.cons q.1 q.2) := by
      apply Fintype.prod_equiv (Fin.consEquiv (fun _ : Fin (n + 1) ↦ Bool)).symm
      intro ω
      simp
    _ = _ := by rw [Fintype.prod_prod_type]; simp [mul_comm]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.BinaryDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

noncomputable def binaryDensity {X Y : Type*} (f : X → ℝ) (g : Y → ℝ) (p : X × Y) : ℝ :=
  f p.1 * g p.2

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BoxWindowAveraging
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

variable {ι : Type*} [Fintype ι]

noncomputable def boxProbabilityWindow (ℓ x t : ι → ℝ) : ℝ :=
  ∏ i, normalizedIntervalWindow (ℓ i) (x i) (t i)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineBoxTest
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

variable {ι : Type*} [Fintype ι]

noncomputable def affineBoxAverage (ℓ : ι → ℝ) (A : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (g : (ι → ℝ) → ℝ) (x : ι → ℝ) : ℝ :=
  ∫ u, boxProbabilityWindow ℓ 0 u * g (x + A u)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ProductEuclideanCoordinates
namespace OAI

section

namespace Erdos3

theorem euclidean_norm_le_sum_abs {ι : Type*} [Fintype ι] (x : EuclideanSpace ℝ ι) :
    ‖x‖ ≤ ∑ i, |x i| := by
  have hsq := Finset.sum_sq_le_sq_sum_of_nonneg
    (s := Finset.univ) (f := fun i => ‖x i‖) (fun i _ => norm_nonneg (x i))
  have he := PiLp.norm_sq_eq_of_L2 (fun _ : ι => ℝ) x
  have hn := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => norm_nonneg (x i))
  have h : ‖x‖ ≤ ∑ i, ‖x i‖ := by nlinarith [norm_nonneg x]
  simpa only [Real.norm_eq_abs] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.LargeCokernelProbability
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

def sampledColumnMatrix {I J : Type*} {Ω : J → Type*}
    (column : ∀ j, Ω j → I → ℤ) (x : ∀ j, Ω j) : Matrix I J ℤ :=
  fun i j => column j (x j) i

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.DiagonalDensityTransport
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {ι : Type*}

noncomputable def inverseJacobian (A : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) : ℝ :=
  |LinearMap.det A.symm.toLinearEquiv.toLinearMap|

variable [Fintype ι]

noncomputable def linearDensityPullback (A : (ι → ℝ) ≃L[ℝ] (ι → ℝ))
    (f : (ι → ℝ) → ℝ) (x : ι → ℝ) : ℝ := inverseJacobian A * f (A.symm x)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

variable {ι : Type*} [Fintype ι]

noncomputable def linearBoxDensity (ℓ : ι → ℝ) (A : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) :
    (ι → ℝ) → ℝ := linearDensityPullback A (boxProbabilityWindow ℓ 0)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.TwoBoxSmoothingComplex
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

variable {ι : Type*} [Fintype ι]

noncomputable def twoBoxDifferenceDensity (ℓ r : ι → ℝ)
    (A B : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) : (ι → ℝ) → ℝ :=
  affineBoxAverage ℓ A.toContinuousLinearMap (linearBoxDensity r B)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.UnitBoxAmplitude
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

def positiveUnitBox (ι : Type*) := Set.univ.pi (fun _ : ι => Set.Ioc (0 : ℝ) 1)

noncomputable def unitBoxMeasure (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  volume.restrict (positiveUnitBox ι)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.PairedProductDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory

noncomputable def unitScalarMeasure : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SmoothSublevelCutoff
namespace OAI

section

namespace Erdos3

open scoped ContDiff NNReal

theorem exists_smooth_scalar_cutoff :
    ∃ A : ℝ≥0, 1 ≤ A ∧ ∃ χ : ℝ → ℝ,
      ContDiff ℝ ∞ χ ∧ (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
      (∀ x, |x| ≤ 1 / 2 → χ x = 1) ∧
      (∀ x, 3 / 4 ≤ |x| → χ x = 0) ∧ LipschitzWith A χ := by
  let f : ContDiffBump (0 : ℝ) := ⟨1 / 2, 3 / 4, by norm_num, by norm_num⟩
  have hsmooth : ContDiff ℝ 1 f := f.contDiff
  obtain ⟨A, hA⟩ := ContDiff.lipschitzWith_of_hasCompactSupport f.hasCompactSupport hsmooth one_ne_zero
  refine ⟨A + 1, by simp, f, f.contDiff, fun x => ⟨f.nonneg, f.le_one⟩, ?_, ?_, ?_⟩
  · intro x hx
    apply f.one_of_mem_closedBall
    simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero] using hx
  · intro x hx
    apply f.zero_of_le_dist
    simpa only [Real.dist_eq, sub_zero] using hx
  · exact hA.weaken (by simp)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformProductAccuracy
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def uniformProductAccuracy (N : ℕ) (C δ : ℝ) : ℝ :=
  min 1 (δ / (((N : ℝ) + 1) * (C + 2) ^ N))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SigmaAxisCoordinates
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {D : Type*} [Fintype D] (I : D → Type*) [∀ d, Fintype (I d)]

noncomputable def sigmaAxisCoordinates : ((Σ d, I d) → ℝ) ≃L[ℝ] (∀ d, I d → ℝ) where
  toLinearEquiv :=
    { toFun := fun x d i => x ⟨d, i⟩
      invFun := fun x s => x s.1 s.2
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CyclicShortShiftSet
namespace OAI

section

namespace Erdos3

theorem exists_exponential_constant_fiber {α β : Type*}
    (S : Finset α) (hS : S.Nonempty) (f : α → β) (A : Set β) (hA : A.Finite)
    (hf : ∀ x ∈ S, f x ∈ A) {C : ℝ} (hcount : (A.ncard : ℝ) ≤ Real.exp C) :
    ∃ y ∈ A, ∃ T : Finset α, T ⊆ S ∧ T.Nonempty ∧ (∀ x ∈ T, f x = y) ∧
      Real.exp (-C) * S.card ≤ (T.card : ℝ) := by
  classical
  have hf' : ∀ x ∈ S, f x ∈ hA.toFinset := fun x hx => hA.mem_toFinset.mpr (hf x hx)
  have hAne : hA.toFinset.Nonempty := by
    obtain ⟨x, hx⟩ := hS
    exact ⟨f x, hf' x hx⟩
  have hn : hA.toFinset.card • (Real.exp (-C) * S.card) ≤ (S.card : ℝ) := by
    rw [nsmul_eq_mul, ← Set.ncard_eq_toFinset_card A hA]
    calc
      (A.ncard : ℝ) * (Real.exp (-C) * S.card) ≤
          Real.exp C * (Real.exp (-C) * S.card) :=
        mul_le_mul_of_nonneg_right hcount (by positivity)
      _ = (S.card : ℝ) := by rw [← mul_assoc, ← Real.exp_add]; simp
  obtain ⟨y, hy, hlarge⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    (s := S) (t := hA.toFinset) (f := f) hf' hAne hn
  have hpos : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hS
  have htpos : 0 < (S.filter (fun x => f x = y)).card := by
    exact_mod_cast (mul_pos (Real.exp_pos (-C)) hpos).trans_le hlarge
  exact ⟨y, hA.mem_toFinset.mp hy, S.filter (fun x => f x = y), Finset.filter_subset _ _,
    Finset.card_pos.mp htpos, fun x hx => (Finset.mem_filter.mp hx).2, hlarge⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BoxDetectionExponents
namespace OAI

section

namespace Erdos3

theorem exp_sub_one_le_half_exp (x : ℝ) : Real.exp (x - 1) ≤ Real.exp x / 2 := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  calc
    _ ≤ Real.exp (x - 1) * Real.exp 1 := mul_le_mul_of_nonneg_left htwo (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem two_pow_le_exp_of_le (d : ℕ) {p : ℝ} (hd : (d : ℝ) ≤ p) :
    (2 : ℝ) ^ d ≤ Real.exp p := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  calc
    _ ≤ (Real.exp 1) ^ d := pow_le_pow_left₀ (by norm_num) htwo d
    _ = Real.exp d := by rw [← Real.exp_nat_mul, mul_one]
    _ ≤ _ := Real.exp_le_exp.mpr hd

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FixedPartnerPower
namespace OAI

section

namespace Erdos3

theorem exists_large_fixed_choices {G K P : Type*} [Fintype K] [Fintype P]
    (H : Finset G) (hH : H.Nonempty) (rel : G → K → P → Prop)
    (hchoice : ∀ h ∈ H, ∀ k, ∃ p, rel h k p) {R : ℝ}
    (hcount : (Fintype.card P : ℝ) ≤ Real.exp R) :
    ∃ (q : K → P) (S : Finset G), S ⊆ H ∧ S.Nonempty ∧
      Real.exp (-R * Fintype.card K) * H.card ≤ (S.card : ℝ) ∧
      ∀ h ∈ S, ∀ k, rel h k (q k) := by
  classical
  choose choices hchoices using hchoice
  obtain ⟨h0, hh0⟩ := hH
  have hH : H.Nonempty := ⟨h0, hh0⟩
  let code : G → (K → P) := fun h => if hh : h ∈ H then choices h hh else choices h0 hh0
  have hcode (h : G) (hh : h ∈ H) (k : K) : rel h k (code h k) := by
    simpa [code, hh] using hchoices h hh k
  have hcodeCount : (((Set.univ : Set (K → P)).ncard : ℕ) : ℝ) ≤
      Real.exp (R * Fintype.card K) := by
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fun, Nat.cast_pow]
    calc
      _ ≤ (Real.exp R) ^ Fintype.card K := pow_le_pow_left₀ (Nat.cast_nonneg _) hcount _
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  obtain ⟨q, _, S, hsub, hSn, hconst, hsize⟩ := exists_exponential_constant_fiber
    H hH code Set.univ Set.finite_univ (fun _ _ => Set.mem_univ _) hcodeCount
  refine ⟨q, S, hsub, hSn, ?_, ?_⟩
  · simpa only [neg_mul] using hsize
  · intro h hh k
    rw [← hconst h hh]
    exact hcode h (hsub hh) k

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.BalancedDualBounds
namespace OAI

section

namespace Erdos3

theorem exists_complex_unit_phase (z : ℂ) :
    ∃ a : ℂ, ‖a‖ = 1 ∧ a * z = (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · subst z
    exact ⟨1, by simp, by simp⟩
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  refine ⟨star z / (‖z‖ : ℂ), ?_, ?_⟩
  · simp [hn]
  · calc
      _ = (star z * z) / (‖z‖ : ℂ) := by ring
      _ = ((‖z‖ ^ 2 : ℝ) : ℂ) / (‖z‖ : ℂ) := by
        rw [mul_comm (star z) z]
        change z * (starRingEnd ℂ) z / (‖z‖ : ℂ) = _
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      _ = _ := by
        rw [Complex.ofReal_pow]
        field_simp

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

variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

def restrictTo (Q : Finset H) (f : H → ℂ) : H → ℂ :=
  fun x ↦ if x ∈ Q then f x else 0

omit [AddCommGroup H] [Fintype H] in
@[simp] theorem restrictTo_empty (f : H → ℂ) :
    restrictTo ∅ f = (fun _ ↦ 0) := by
  funext x
  simp [restrictTo]

omit [AddCommGroup H] in
theorem expect_restrictTo (Q : Finset H) (f : H → ℂ) :
    (𝔼 x, restrictTo Q f x) = (∑ x ∈ Q, f x) / Fintype.card H := by
  simp [restrictTo, Fintype.expect_eq_sum_div_card]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CyclicCutNeighborhood
namespace OAI

section

open scoped BigOperators symmDiff

namespace Erdos3

variable {N : ℕ}

def cyclicInterval (a : ZMod N) (L : ℕ) : Finset (ZMod N) :=
  (Finset.range L).image (fun k : ℕ => a + (k : ZMod N))

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {N : ℕ} [NeZero N]

omit [NeZero N] in
theorem cyclicInterval_card (a : ZMod N) {L : ℕ} (hL : L ≤ N) :
    (cyclicInterval a L).card = L := by
  unfold cyclicInterval
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro i hi j hj he
  have hiN : i < N := (Finset.mem_range.mp hi).trans_le hL
  have hjN : j < N := (Finset.mem_range.mp hj).trans_le hL
  have hc : (i : ZMod N) = (j : ZMod N) := add_left_cancel he
  have hv := congrArg ZMod.val hc
  simpa only [ZMod.val_natCast_of_lt hiN, ZMod.val_natCast_of_lt hjN] using hv

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.VectorPolynomialReconstruction
namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {σ ι R S V : Type*} [CommRing R] [CommRing S] [AddCommGroup V] [Module R V]

theorem scalar_weightedDegree_le_iff (w : σ → ℕ) (d : ℕ) (p : MvPolynomial σ S) :
    p.weightedTotalDegree w ≤ d ↔
      ∀ α, d < Finsupp.weight w α → p.coeff α = 0 := by
  classical
  simp only [MvPolynomial.weightedTotalDegree, Finset.sup_le_iff,
    MvPolynomial.mem_support_iff]
  exact ⟨fun h α hd => Classical.byContradiction (fun hα => (not_le_of_gt hd) (h α hα)),
    fun h α hα => le_of_not_gt (fun hd => hα (h α hd))⟩

end Erdos3.VectorPolynomial

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

omit [Fintype ι] [DecidableEq ι] in
theorem int_eq_of_zmod_eq_of_bounds {m : ℕ} {a b : ℤ}
    (ha : 0 ≤ a ∧ a < m) (hb : 0 ≤ b ∧ b < m) (he : (a : ZMod m) = (b : ZMod m)) :
    a = b := by
  have hm := (ZMod.intCast_eq_intCast_iff' a b m).mp he
  simpa only [Int.emod_eq_of_lt ha.1 ha.2, Int.emod_eq_of_lt hb.1 hb.2] using hm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PaddedBooleanFeatures
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def booleanFeature {α R : Type*} [DecidableEq α] [Zero R] [One R]
    (a : Option α) (t : Finset α) : R :=
  match a with
  | none => 1
  | some i => if i ∈ t then 1 else 0

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ScalarCubeDomain
namespace OAI

section

namespace Erdos3

open scoped BigOperators ContDiff

noncomputable def scalarCubeValue {α : Type*} [Fintype α] [DecidableEq α]
    (a : Option α → ℝ) (t : Finset α) : ℝ :=
  ∑ r : Option α, (booleanFeature r t : ℝ) * a r

def scalarCubeDomain (α : Type*) [Fintype α] [DecidableEq α] : Set (Option α → ℝ) :=
  {a | ∀ t : Finset α, scalarCubeValue a t ∈ Set.Ioo (0 : ℝ) 1}

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialParameterContinuity
namespace OAI

section

namespace Erdos3

open scoped ContDiff

abbrev PolynomialParameter (Z I : Type*) := Option (Z ⊕ I)

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
open scoped NNReal

noncomputable def scalarDensityConvolution (f g : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ t, f (x - t) * g t

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.RestrictedComplexChartDensityComparison
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {X Y : Type*}

noncomputable def restrictedComplexChartDensity (q : X → Y) (S : Set X) (c : ℝ)
    (f : X → ℂ) : Y → ℂ :=
  fun y => (c : ℂ) * Function.extend (fun x : S => q x.val) (fun x => f x.val) (fun _ => 0) y

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SlicedPairAmplitude
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

structure SlicedProductBlock (ι : Type*) where
  coefficient : ℝ
  lower : ι → ℝ
  width : ι → ℝ
  lastLower : ℝ
  lastWidth : ℝ

namespace SlicedProductBlock

variable {ι : Type*} [Fintype ι]

noncomputable def prefixProduct (B : SlicedProductBlock ι) (x : ι → ℝ) : ℝ :=
  ∏ i, (B.lower i + B.width i * x i)

noncomputable def slope (B : SlicedProductBlock ι) (x : ι → ℝ) : ℝ :=
  B.coefficient * B.lastWidth * B.prefixProduct x

noncomputable def base (B : SlicedProductBlock ι) (x : ι → ℝ) : ℝ :=
  B.coefficient * B.lastLower * B.prefixProduct x

end SlicedProductBlock

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RandomAffinePair
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {T : Type*} [MeasurableSpace T]

noncomputable def affinePairWidth (a b : T → ℝ) (p : T × ℝ) : ℝ := max |a p.1| |b p.1|

noncomputable def affinePairShift (a b c : T → ℝ) (p : T × ℝ) : ℝ :=
  c p.1 + min 0 (a p.1) + min 0 (b p.1) + min |a p.1| |b p.1| * p.2

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.SlicedRemainderDensityFamily
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {B F : Type*} [Fintype B] [Fintype F] [DecidableEq B] [DecidableEq F]

noncomputable def principalSliceValue (c : B → ℝ) (lower width : B × F → ℝ)
    (x : B × F → ℝ) : ℝ :=
  ∑ b, c b * ∏ k, (lower (b, k) + width (b, k) * x (b, k))

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {B ι : Type*} [Fintype B] [Fintype ι] [DecidableEq B] [DecidableEq ι]

def principalSliceBlock (c : B → ℝ) (lower width : B × Option ι → ℝ) (b : B) :
    SlicedProductBlock ι where
  coefficient := c b
  lower i := lower (b, some i)
  width i := width (b, some i)
  lastLower := lower (b, none)
  lastWidth := width (b, none)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

noncomputable def fourBlockDecomposition (B : Type*) [Fintype B] (hB : 4 ≤ Fintype.card B) :
    Fin 4 ⊕ Fin (Fintype.card B - 4) ≃ B :=
  Fintype.equivOfCardEq (by simp only [Fintype.card_sum, Fintype.card_fin]; omega)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LargestBadPrimeProduct
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

noncomputable def largestTestedBadDepth {Ω : Type*} (A : ℕ → ℕ)
    (bad : ℕ → ℕ → Ω → Prop) (p : ℕ) (x : Ω) : ℕ :=
  ((Finset.Icc 1 (A p)).filter (fun a => bad p a x)).sup id

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CRTPolynomialImage
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {L Tag V : Type*} [Fintype L]

noncomputable def crtInput (q : L → ℕ)
    (hq : Pairwise (fun l k => (q l).Coprime (q k)))
    (x : ∀ l : L, V → ZMod (q l)) (v : V) : ZMod (∏ l, q l) :=
  (ZMod.prodEquivPi q hq).symm (fun l => x l v)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CubeResidueSupport
namespace OAI


namespace Erdos3

open scoped BigOperators

def integerScalarCubeValue {I : Type*} [Fintype I] (x : Option I → ℤ) (t : Finset I) : ℤ :=
  x none + ∑ i ∈ t, x (some i)

def IntegerScalarCube {I : Type*} [Fintype I] (L : ℕ) (x : Option I → ℤ) : Prop :=
  ∀ t : Finset I, 0 ≤ integerScalarCubeValue x t ∧ integerScalarCubeValue x t < L

theorem integerScalarCube_small_positive {I : Type*} [Fintype I] {L H : ℕ}
    (hH : 0 < H) (hHL : (Fintype.card I + 1) * H ≤ L) (x : Option I → Fin H) :
    IntegerScalarCube L (fun i => ((x i).val : ℤ)) := by
  intro t
  have ht : t.card ≤ Fintype.card I := Finset.card_le_univ t
  have hx (i : Option I) : (0 : ℤ) ≤ (x i).val ∧ ((x i).val : ℤ) ≤ (H : ℤ) - 1 := by
    exact ⟨Nat.cast_nonneg _, by have := (x i).isLt; omega⟩
  have hsum0 : (0 : ℤ) ≤ ∑ i ∈ t, ((x (some i)).val : ℤ) :=
    Finset.sum_nonneg (fun i _ => (hx (some i)).1)
  have hsum : (∑ i ∈ t, ((x (some i)).val : ℤ)) ≤ (t.card : ℤ) * ((H : ℤ) - 1) := by
    simpa only [Finset.sum_const, nsmul_eq_mul] using
      (Finset.sum_le_sum (fun i (_ : i ∈ t) => (hx (some i)).2))
  have hHL' : ((Fintype.card I : ℤ) + 1) * H ≤ L := by exact_mod_cast hHL
  have ht' : (t.card : ℤ) ≤ Fintype.card I := by exact_mod_cast ht
  have hH' : (1 : ℤ) ≤ H := by exact_mod_cast hH
  dsimp [integerScalarCubeValue]
  constructor
  · exact add_nonneg (hx none).1 hsum0
  · have h0 := (hx none).2
    have hmul := mul_le_mul_of_nonneg_right ht' (sub_nonneg.mpr hH')
    nlinarith [show (0 : ℤ) ≤ Fintype.card I from Nat.cast_nonneg _]

end Erdos3


namespace Erdos3

theorem nat_div_half_lower {L n : ℕ} (hn : 0 < n) (hL : n ≤ L) :
    L ≤ 2 * n * (L / n) := by
  have hd : 0 < L / n := Nat.div_pos hL hn
  have hm := Nat.mod_lt L hn
  have he := Nat.div_add_mod L n
  nlinarith


theorem scalarResiduePoint_bound (m H : ℕ) (hm : 0 < m) (r : ZMod m) (x : Fin H) :
    r.val + m * x.val < m * H := by
  let : NeZero m := ⟨hm.ne'⟩
  have hr := ZMod.val_lt r
  have hx := x.isLt
  nlinarith

theorem scalarResiduePoint_cast (m : ℕ) (hm : 0 < m) (r : ZMod m) (x : ℕ) :
    ((r.val + m * x : ℕ) : ZMod m) = r := by
  let : NeZero m := ⟨hm.ne'⟩
  simp


open scoped BigOperators Classical

end Erdos3


namespace Erdos3

noncomputable def scalarCubeResidueDensityCap (I : Type*) [Fintype I] (M : ℕ) : ℝ :=
  (4 * (Fintype.card I + 1 : ℕ) * (M : ℝ)) ^ (Fintype.card I + 1)

theorem scalarCubeResidueDensityCap_pos (I : Type*) [Fintype I] (M : ℕ) (hM : 0 < M) :
    0 < scalarCubeResidueDensityCap I M := by
  unfold scalarCubeResidueDensityCap
  positivity


open scoped BigOperators

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CRTPolynomialChargeBound
namespace OAI


namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

def modularRankChargeFactor (s : ℕ) : ℕ := 4 * s * (2 ^ s * s.factorial)

end Erdos3


namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

theorem totalDegree_map_le {V R S : Type*} [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) (F : MvPolynomial V R) : (map φ F).totalDegree ≤ F.totalDegree := by
  unfold totalDegree
  apply Finset.sup_le
  intro m hm
  exact le_totalDegree (support_map_subset φ F hm)

end Erdos3


namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

theorem primePower_crt_coprime {L : Type*} (p A : L → ℕ)
    (hp : ∀ l, (p l).Prime) (hinj : Function.Injective p) :
    Pairwise (fun l k => (p l ^ A l).Coprime (p k ^ A k)) := by
  intro l k hlk
  exact Nat.coprime_pow_primes (A l) (A k) (hp l) (hp k) (hinj.ne hlk)

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.UniformScaledRetainedCharacters
namespace OAI

section

namespace Erdos3

noncomputable def majorArcLocalizationConstant (n : ℕ) (U : ℝ) : ℝ :=
  256 * U ^ 6 * (2 * U ^ 2) ^ ((n + 1) * 2)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CommonIntegerIntervalCorrelation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def integerGridStart (a L : ℕ) : ℕ := L * (a / L + 1)

theorem integerGridStart_bounds (a : ℕ) {L : ℕ} (hL : 0 < L) :
    a ≤ integerGridStart a L ∧ integerGridStart a L ≤ a + L := by
  constructor
  · exact (Nat.lt_mul_div_succ a hL).le
  · dsimp [integerGridStart]
    rw [Nat.mul_add, Nat.mul_one]
    exact Nat.add_le_add_right (by simpa only [Nat.mul_comm] using Nat.div_mul_le_self a L) L

theorem norm_sum_subset_card_loss {α : Type*} [DecidableEq α]
    {S T : Finset α} (hTS : T ⊆ S) (f : α → ℂ) (hf : ∀ x ∈ S, ‖f x‖ ≤ 1) :
    ‖∑ x ∈ S, f x‖ ≤ ‖∑ x ∈ T, f x‖ + (S.card : ℝ) - (T.card : ℝ) := by
  have hsum := Finset.sum_sdiff (f := f) hTS
  have hb : ‖∑ x ∈ S \ T, f x‖ ≤ ((S \ T).card : ℝ) := by
    apply (norm_sum_le _ _).trans
    simpa using Finset.sum_le_sum (fun x hx => hf x (Finset.mem_sdiff.mp hx).1)
  have hc : ((S \ T).card : ℝ) + (T.card : ℝ) = (S.card : ℝ) := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hTS
  have hn := norm_add_le (∑ x ∈ S \ T, f x) (∑ x ∈ T, f x)
  rw [hsum] at hn
  linarith only [hb, hc, hn]

end Erdos3

end

section

namespace Erdos3

theorem exists_exp_integer_grid_scale {p : ℝ} (hp : 0 ≤ p) {N : ℕ}
    (hN : Real.exp (2 * p + 8) ≤ (N : ℝ)) :
    ∃ L : ℕ, 0 < L ∧ 4 * (L : ℝ) ≤ Real.exp (-(2 * p)) * N ∧
      ((N / L + 2 : ℕ) : ℝ) ≤ Real.exp (2 * p + 5) := by
  let x := Real.exp (-(2 * p)) * N / 8
  let L := ⌊x⌋₊
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have h16 : (16 : ℝ) ≤ Real.exp 8 :=
    (by norm_num : (16 : ℝ) ≤ 2 ^ 8).trans (two_pow_le_exp_of_le 8 le_rfl)
  have hscaled : Real.exp 8 ≤ Real.exp (-(2 * p)) * N := by
    calc
      _ = Real.exp (-(2 * p)) * Real.exp (2 * p + 8) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hN (Real.exp_nonneg _)
  have hx2 : 2 ≤ x := by dsimp [x]; linarith only [h16, hscaled]
  have hfloor : (L : ℝ) ≤ x := Nat.floor_le hx0
  have hlt : x < (L : ℝ) + 1 := Nat.lt_floor_add_one x
  have hL : 0 < L := by
    have : (0 : ℝ) < L := by linarith only [hx2, hlt]
    exact_mod_cast this
  have hhalf : x ≤ 2 * (L : ℝ) := by linarith only [hx2, hlt]
  have hupper : 4 * (L : ℝ) ≤ Real.exp (-(2 * p)) * N := by
    dsimp [x] at hfloor hx0
    linarith only [hfloor, hx0]
  have hlower : Real.exp (-(2 * p)) * N ≤ 16 * (L : ℝ) := by
    dsimp [x] at hhalf
    linarith only [hhalf]
  have hNL : (N : ℝ) ≤ 16 * Real.exp (2 * p) * L := by
    calc
      _ = Real.exp (2 * p) * (Real.exp (-(2 * p)) * N) := by
        rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
      _ ≤ Real.exp (2 * p) * (16 * L) :=
        mul_le_mul_of_nonneg_left hlower (Real.exp_nonneg _)
      _ = _ := by ring
  have hdiv : ((N / L : ℕ) : ℝ) ≤ 16 * Real.exp (2 * p) :=
    Nat.cast_div_le.trans ((div_le_iff₀ (by exact_mod_cast hL : (0 : ℝ) < L)).mpr hNL)
  have h18 : (18 : ℝ) ≤ Real.exp 5 :=
    (by norm_num : (18 : ℝ) ≤ 2 ^ 5).trans (two_pow_le_exp_of_le 5 le_rfl)
  refine ⟨L, hL, hupper, ?_⟩
  calc
    _ = ((N / L : ℕ) : ℝ) + 2 := by norm_cast
    _ ≤ 18 * Real.exp (2 * p) := by
      have h1 := Real.one_le_exp (show 0 ≤ 2 * p by positivity)
      linarith only [hdiv, h1]
    _ ≤ Real.exp 5 * Real.exp (2 * p) := mul_le_mul_of_nonneg_right h18 (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineWindowGoodKernelBound
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def integerStrideHom (m : ℤ) : ℤ →+ ℤ where
  toFun x := m * x
  map_zero' := mul_zero m
  map_add' := mul_add m

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SmoothIntegerTranslation
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

def smoothAffineSample {K I : Type*} [Fintype K] (t : K → ℤ)
    (z : Option K × I → ℤ) : I → ℤ :=
  fun i => z (none, i) + ∑ k, t k * z (some k, i)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.NormalizedRealPolynomialChart
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {U B : Type*}

noncomputable def normalizedRealPolynomialChart (H : U → ℝ)
    (A : B → MvPolynomial U ℝ) : U ⊕ B → MvPolynomial (U ⊕ B) ℝ :=
  Sum.elim (fun i => C ((H i)⁻¹) * X (Sum.inl i))
    (fun j => X (Sum.inr j) - rename Sum.inl (A j))

@[simp] theorem normalizedRealPolynomialChart_inl (H : U → ℝ)
    (A : B → MvPolynomial U ℝ) (i : U) :
    normalizedRealPolynomialChart H A (Sum.inl i) = C ((H i)⁻¹) * X (Sum.inl i) :=
  rfl

@[simp] theorem normalizedRealPolynomialChart_inr (H : U → ℝ)
    (A : B → MvPolynomial U ℝ) (j : B) :
    normalizedRealPolynomialChart H A (Sum.inr j) =
      X (Sum.inr j) - rename Sum.inl (A j) :=
  rfl

@[simp] theorem normalizedRealPolynomialChart_eval (H : U → ℝ)
    (A : B → MvPolynomial U ℝ) (u : U → ℝ) (b : B → ℝ) (j : U ⊕ B) :
    eval (Sum.elim u b) (normalizedRealPolynomialChart H A j) =
      Sum.elim (fun i => u i / H i) (fun i => b i - eval u (A i)) j := by
  cases j <;>
    simp [normalizedRealPolynomialChart, eval_rename, Function.comp_def,
      div_eq_mul_inv, mul_comm]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.SamplingRankProjectedContainment
namespace OAI

section

namespace Erdos3

open scoped Matrix BigOperators

namespace VectorPolynomial

def jointRationalSpace {ι κ ρ : Type*} [Fintype ι] [Fintype κ]
    (B : Matrix ι κ ℚ) (A : Matrix ρ ι ℚ) : Submodule ℝ (ι → ℝ) :=
  LinearMap.range (Matrix.of (fun i j => (B i j : ℝ))).mulVecLin ⊓
    LinearMap.ker (Matrix.of (fun i j => (A i j : ℝ))).mulVecLin

open scoped TensorProduct

end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RationalPolynomialForecastBoxError
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

noncomputable def integerLongPolynomialOutput {A I J : Type*} (poly : J → MvPolynomial (A ⊕ I) ℤ)
    (inactive : I → ℤ) (N : ℕ) (t : A → ZMod N) : J → ℤ :=
  fun j => MvPolynomial.eval (Sum.elim (fun a => ((t a).val : ℤ)) inactive) (poly j)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastModularCutoff
namespace OAI

section

namespace Erdos3

def modularForecastRankConstant (s D : ℕ) : ℕ :=
  (D + 2) * (2 ^ s * s.factorial) * 2 ^ s

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.FixedPathSlicedGridMeshBudget
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

noncomputable def scalarCubeGridBoundaryConstant (I : Type*) [Fintype I] : ℝ :=
  Fintype.card (Bool × Finset I) * (4 : ℝ)^Fintype.card I * 2 * (Fintype.card I + 1)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ScalarResidueInteriorCell
namespace OAI

section

namespace Erdos3

noncomputable def paddedResidueDensityCap (I : Type*) [Fintype I] (M : ℕ) : ℝ :=
  2 ^ (Fintype.card I + 1) * scalarCubeResidueDensityCap I M

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueCutoffLengthBudget
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

noncomputable def scalarCubeCutoffDerivativeNumerator (I : Type*) [Fintype I]
    (A : ℝ≥0) : ℝ :=
  (2 * 2 ^ Fintype.card I : ℕ) * ((A : ℝ) * ((Fintype.card I : ℝ) + 1))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.IntegerSupportTorus
namespace OAI

section

namespace Erdos3

noncomputable def integerSupportTorusFactor (H : ℝ) : ℕ := 2 * ⌈H⌉₊ + 1

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.WeightedBlockSupportScale
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def blockJetScaleBound (q h b : ℕ) (A : ℝ) : ℝ :=
  b * 2 ^ h * ((q + 1 : ℕ) : ℝ) ^ h * A

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.WeightedBlockTorus
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def blockTorusFactor (q h b : ℕ) (A : ℝ) : ℕ :=
  integerSupportTorusFactor (blockJetScaleBound q h b A)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NormalizedLatticeSheet
namespace OAI

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

noncomputable def latticeSheetPoint (W : Submodule ℝ E) (z : Wᗮ) (u : W) : E :=
  u.val + z.val

theorem latticeSheetPoint_projection (W : Submodule ℝ E) (z : Wᗮ) (u : W) :
    W.orthogonalProjectionOnto (latticeSheetPoint W z u) = u := by
  change W.orthogonalProjectionOnto (u.val + z.val) = u
  rw [map_add, W.orthogonalProjectionOnto_apply_of_mem_orthogonal z.property, add_zero]
  exact Subtype.ext (W.starProjection_eq_self_iff.mpr u.property)

theorem latticeSheetPoint_projection_orthogonal (W : Submodule ℝ E) (z : Wᗮ) (u : W) :
    Wᗮ.orthogonalProjectionOnto (latticeSheetPoint W z u) = z := by
  change Wᗮ.orthogonalProjectionOnto (u.val + z.val) = z
  rw [map_add, W.orthogonalProjectionOnto_orthogonal_apply_eq_zero u.property, zero_add]
  exact Subtype.ext (Wᗮ.starProjection_eq_self_iff.mpr z.property)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CanonicalScalarSourceEnvelope
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

noncomputable def scalarCubePrimitiveEnvelope (I : Type*) [Fintype I]
    (A B T : ℝ≥0) (M : ℕ) : ℝ :=
  let q := (Fintype.card I : ℝ) + 1
  let V := (2 * q) ^ (Fintype.card I + 1)
  1 + q + M + B + T + 4 * V * ((2 : ℝ) ^ Fintype.card I) ^ 2 +
    2 * scalarCubeGridBoundaryConstant I * V + scalarCubeCutoffDerivativeNumerator I A +
      paddedResidueDensityCap I M

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.DenseRealBoxCell
namespace OAI

section

namespace Erdos3.FreimanModel

open scoped Pointwise

theorem exists_nonempty_large_fiber {α β : Type*} [Fintype β] [Nonempty β] [DecidableEq β]
    (A : Finset α) (hA : A.Nonempty) (f : α → β) :
    ∃ b : β, (A.filter fun x => f x = b).Nonempty ∧
      A.card ≤ Fintype.card β * (A.filter fun x => f x = b).card := by
  classical
  let k := Fintype.card β
  have hk : 0 < k := Fintype.card_pos
  let n := (A.card - 1) / k
  have hApos := hA.card_pos
  have hkn : k * n < A.card := by
    have hle : k * n ≤ A.card - 1 := Nat.mul_div_le (A.card - 1) k
    omega
  obtain ⟨b, _, hcard⟩ :=
    Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (s := A) (t := Finset.univ) (f := f) (fun _ _ => Finset.mem_univ _)
      (by simpa only [Finset.card_univ] using hkn)
  refine ⟨b, Finset.card_pos.mp ((Nat.zero_le n).trans_lt hcard), ?_⟩
  have hceil : A.card - 1 < k * (n + 1) := Nat.lt_mul_div_succ (A.card - 1) hk
  have hmul : k * (n + 1) ≤ k * (A.filter fun x => f x = b).card :=
    Nat.mul_le_mul_left k (by omega)
  change A.card ≤ k * (A.filter fun x => f x = b).card
  omega

end Erdos3.FreimanModel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.MahlerBasis
namespace OAI

section

namespace Erdos3.IntegerBasisReduction.Mahler

open scoped BigOperators
open Module

abbrev IntegralPoint (n : ℕ) := Fin n → ℤ

def integralEmbed {n : ℕ} (x : IntegralPoint n) : Fin n → ℝ :=
  fun i ↦ (x i : ℝ)

@[simp]
theorem integralEmbed_zero {n : ℕ} :
    integralEmbed (0 : IntegralPoint n) = 0 := by
  ext i
  simp [integralEmbed]

end Erdos3.IntegerBasisReduction.Mahler

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ProperCyclicKernelBasis
namespace OAI

section

namespace Erdos3.IntegerBasisReduction.Mahler

open scoped BigOperators
open Module

def prefixIndex {n : ℕ} (i : Fin n) (j : Fin i.val) : Fin n :=
  ⟨j.val, lt_trans j.isLt i.isLt⟩

def extendPrefix {n : ℕ} (i : Fin n) (t : Fin i.val → ℤ) : Fin n → ℤ :=
  fun j ↦ if h : j < i then t ⟨j.val, h⟩ else 0

end Erdos3.IntegerBasisReduction.Mahler

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.UnconditionedSpatialWidthBudget
namespace OAI

section

namespace Erdos3
open scoped BigOperators

noncomputable def unconditionedSpatialTrimFraction (d : ℕ) (σ : ℝ) : ℝ :=
  σ / (32 * (d + 1))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.LocalMajorDenseSliceNiltest
namespace OAI

section

namespace Erdos3.OrdinaryPolynomialPhase

open _root_.MvPolynomial
open scoped TensorProduct NNReal

def weight : Fin 0 → ℕ := fun _ => 1

theorem weight_pos : ∀ i, 0 < weight i := fun i => Fin.elim0 i

end Erdos3.OrdinaryPolynomialPhase

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ActiveProfileNoise
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {D : Type*} [Fintype D] (B : D → Type*) [∀ d, Fintype (B d)]

noncomputable def unitProfilePrincipalLowerBound : ℝ :=
  1 / (8 * (((∑ d, Fintype.card (B d) : ℕ) : ℝ) + 1))

theorem unitProfilePrincipalLowerBound_pos : 0 < unitProfilePrincipalLowerBound B := by
  unfold unitProfilePrincipalLowerBound
  positivity

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MixedCoveredChart
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped Classical

abbrev MixedCoveredJetSource {m : ℕ} (I O E : Fin m → Type*) (n : Fin m → ℕ) (d : ℕ) :=
  (∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ)) × (∀ j, O j → E j → ZMod d)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.VariableRoundedGraphCoordinates
namespace OAI

section

namespace Erdos3.FreimanModel

def variableRoundedGraphModuli {I : Type*} (N : ℕ) (M : I → ℕ) : Option I → ℕ
  | none => N
  | some i => M i

def variableRoundedGraphCoordinateEquiv {I : Type*} (N : ℕ) (M : I → ℕ) :
    (ZMod N × (∀ i, ZMod (M i))) ≃+ (∀ i : Option I, ZMod (variableRoundedGraphModuli N M i)) where
  toFun x i := match i with
    | none => x.1
    | some j => x.2 j
  invFun x := (x none, fun i => x (some i))
  left_inv x := rfl
  right_inv x := by funext i; cases i <;> rfl
  map_add' x y := by funext i; cases i <;> rfl

theorem variableRoundedGraphModuli_neZero {I : Type*} (N : ℕ) (M : I → ℕ) [NeZero N] [∀ i, NeZero (M i)] :
    ∀ i : Option I, NeZero (variableRoundedGraphModuli N M i) := by
  intro i
  cases i <;> dsimp [variableRoundedGraphModuli] <;> infer_instance

end Erdos3.FreimanModel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MissingCoordinateProducts
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def missingCoordinateProduct {I K α : Type*} [Fintype I]
    (coordinate : I → K) (f : I → (K → α) → ℂ) (k : K) (x : K → α) : ℂ := by
  classical
  exact ∏ i ∈ Finset.univ with coordinate i = k, f i x

theorem missingCoordinateProduct_prod {I K α : Type*} [Fintype I] [Fintype K]
    (coordinate : I → K) (f : I → (K → α) → ℂ) (x : K → α) :
    (∏ k, missingCoordinateProduct coordinate f k x) = ∏ i, f i x := by
  classical
  exact Finset.prod_fiberwise Finset.univ coordinate (fun i => f i x)

theorem missingCoordinateProduct_norm {I K α : Type*} [Fintype I]
    (coordinate : I → K) (f : I → (K → α) → ℂ) (hf : ∀ i x, ‖f i x‖ ≤ 1)
    (k : K) (x : K → α) : ‖missingCoordinateProduct coordinate f k x‖ ≤ 1 := by
  classical
  unfold missingCoordinateProduct
  rw [norm_prod]
  exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun i _ => hf i x)

theorem missingCoordinateProduct_independent {I K α : Type*} [Fintype I]
    (coordinate : I → K) (f : I → (K → α) → ℂ)
    (hf : ∀ i x y, (∀ k, k ≠ coordinate i → x k = y k) → f i x = f i y)
    (k : K) (x y : K → α) (hxy : ∀ l, l ≠ k → x l = y l) :
    missingCoordinateProduct coordinate f k x = missingCoordinateProduct coordinate f k y := by
  classical
  apply Finset.prod_congr rfl
  intro i hi
  have heq : coordinate i = k := (Finset.mem_filter.mp hi).2
  apply hf i x y
  simpa only [heq] using hxy

theorem exists_missing_coordinate_product_factors {I K α : Type*} [Fintype I] [Fintype K]
    (f : I → (K → α) → ℂ) (hf : ∀ i x, ‖f i x‖ ≤ 1)
    (hind : ∀ i, ∃ k, ∀ x y, (∀ l, l ≠ k → x l = y l) → f i x = f i y) :
    ∃ A : K → (K → α) → ℂ,
      (∀ k x, ‖A k x‖ ≤ 1) ∧
      (∀ k x y, (∀ l, l ≠ k → x l = y l) → A k x = A k y) ∧
      ∀ x, (∏ k, A k x) = ∏ i, f i x := by
  classical
  choose coordinate homit using hind
  exact ⟨missingCoordinateProduct coordinate f, missingCoordinateProduct_norm coordinate f hf,
    missingCoordinateProduct_independent coordinate f homit, missingCoordinateProduct_prod coordinate f⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoveredInducedCorrelationFamily
namespace OAI

section

namespace Erdos3.QuadraticMarked

open Module
open scoped TensorProduct NNReal

def weights : Fin 1 → ℕ := fun _ => 1

def marked : Fin 1 → Bool := fun _ => true

theorem weight_pos (i : Fin 1) : 0 < weights i := by
  change 0 < (1 : ℕ)
  omega

end Erdos3.QuadraticMarked

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CubeSignalCoordinates
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_false_of_ne_true {d : ℕ} {ω : Fin d → Bool}
    (h : ω ≠ fun _ => true) : ∃ j, ω j = false := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp h
  refine ⟨j, ?_⟩
  cases he : ω j <;> simp_all

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MixedProfileCoordinates
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem mixedProfile_card (d N : ℕ) [NeZero N] :
    Fintype.card ((Fin (d + 1) → ZMod N) × ZMod N) = N ^ (d + 2) := by
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, ZMod.card, pow_succ]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedPhysicalCoveredDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory Module Submodule
open scoped Classical

def standardLatticeClosedQuarterBox (J : Type*) [Fintype J] : Set (EuclideanSpace ℝ J) :=
  {x | ∀ i, |x i| ≤ 1 / 4}

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RelativeSliceAffineThreeFactorLaw
namespace OAI

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators

variable {X : Type*} [Fintype X] [DecidableEq X]
variable {keep : X → Prop} [DecidablePred keep] {N : X → ℕ} {q : ℕ}

def fiberParameterStride (i : X) : ℕ := if keep i then q else 0

end Erdos3.ResidueBoxSlice

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CanonicalEmptyLayerGeometry
namespace OAI

section

namespace Erdos3.VectorPolynomial.CanonicalEmptyLayerGeometry

open Module Submodule

abbrev I (q : ℕ) (_ : Fin q) : Type := PEmpty
abbrev J (q : ℕ) (_ : Fin q) : Type := PEmpty

noncomputable def U (q : ℕ) (j : Fin q) : Submodule ℝ (J q j → ℝ) := ⊥

end Erdos3.VectorPolynomial.CanonicalEmptyLayerGeometry

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedScalarStructuralBasePower
namespace OAI

section

namespace Erdos3

open scoped NNReal ContDiff

noncomputable def normalizedSiteCutoffBound : ℝ≥0 :=
  Classical.choose exists_smooth_scalar_cutoff

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.LowTaggedPolynomialCoordinates
namespace OAI

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial
open scoped BigOperators

variable {m : ℕ} (J : Fin m → Type*) [∀ j, Fintype (J j)]

abbrev LowTaggedIndex (d : ℕ) := {i : Σ j, J j // i.1.val + 1 ≤ d}

noncomputable def lowTaggedIndex (d : ℕ) (i : Fin (Fintype.card (LowTaggedIndex J d))) :
    Σ j, J j := ((Fintype.equivFin (LowTaggedIndex J d)).symm i).val

noncomputable def lowTaggedWeight (d : ℕ) : Fin (Fintype.card (LowTaggedIndex J d)) → ℕ :=
  fun i => (lowTaggedIndex J d i).1.val + 1

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.TranslationPolynomialSymbolLiftHom
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

def lieHomSubalgebra {A B : Type*} [LieRing A] [LieAlgebra ℚ A]
    [LieRing B] [LieAlgebra ℚ B] (f : A →ₗ⁅ℚ⁆ B) (K : LieSubalgebra ℚ B)
    (hf : ∀ x, f x ∈ K) : A →ₗ⁅ℚ⁆ K where
  toLinearMap := f.toLinearMap.codRestrict K.toSubmodule hf
  map_lie' {x y} := Subtype.ext (f.map_lie x y)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.LowTaggedCoordinateRestriction
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {m : ℕ} (J : Fin m → Type*) [∀ j, Fintype (J j)]

noncomputable def lowTaggedSlot (d : ℕ) (j : Fin m) (hj : j.val + 1 ≤ d)
    (k : J j) : Fin (Fintype.card (LowTaggedIndex J d)) :=
  Fintype.equivFin (LowTaggedIndex J d) ⟨⟨j, k⟩, hj⟩

@[simp] theorem lowTaggedIndex_slot (d : ℕ) (j : Fin m) (hj : j.val + 1 ≤ d)
    (k : J j) : lowTaggedIndex J d (lowTaggedSlot J d j hj k) = ⟨j, k⟩ := by
  simp [lowTaggedIndex, lowTaggedSlot]

theorem lowTaggedSlot_injective (d : ℕ) (j : Fin m) (hj : j.val + 1 ≤ d) :
    Function.Injective (lowTaggedSlot J d j hj) := by
  intro k l h
  have he := congrArg (lowTaggedIndex J d) h
  simpa using he

noncomputable def lowTaggedEmbedding (d : ℕ) (j : Fin m) (hj : j.val + 1 ≤ d) :
    (J j → ℝ) →ₗ[ℝ] (Fin (Fintype.card (LowTaggedIndex J d)) → ℝ) := by
  classical
  exact ∑ k : J j,
    (LinearMap.single ℝ (fun _ : Fin (Fintype.card (LowTaggedIndex J d)) => ℝ)
      (lowTaggedSlot J d j hj k)).comp (LinearMap.proj k)

theorem lowTaggedEmbedding_apply (d : ℕ) (j : Fin m) (hj : j.val + 1 ≤ d)
    (v : J j → ℝ) (i : Fin (Fintype.card (LowTaggedIndex J d))) :
    lowTaggedEmbedding J d j hj v i =
      ∑ k : J j, (Pi.single (lowTaggedSlot J d j hj k) (v k) :
        Fin (Fintype.card (LowTaggedIndex J d)) → ℝ) i := by
  classical
  simp [lowTaggedEmbedding, LinearMap.sum_apply, Finset.sum_apply]

@[simp] theorem lowTaggedEmbedding_apply_slot (d : ℕ) (j : Fin m)
    (hj : j.val + 1 ≤ d) (v : J j → ℝ) (k : J j) :
    lowTaggedEmbedding J d j hj v (lowTaggedSlot J d j hj k) = v k := by
  classical
  rw [lowTaggedEmbedding_apply]
  rw [Finset.sum_eq_single k]
  · simp
  · intro l _ hl
    exact Pi.single_eq_of_ne (fun he => hl
      ((lowTaggedSlot_injective J d j hj) he.symm)) _
  · simp

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} (J : Fin m → Type*) [∀ j, Fintype (J j)]

noncomputable def lowTaggedRestriction (d : ℕ) (j : Fin m) (hj : j.val + 1 ≤ d) :
    (Fin (Fintype.card (LowTaggedIndex J d)) → ℝ) →ₗ[ℝ] (J j → ℝ) :=
  LinearMap.pi fun k => LinearMap.proj (lowTaggedSlot J d j hj k)

@[simp] theorem lowTaggedRestriction_apply (d : ℕ) (j : Fin m)
    (hj : j.val + 1 ≤ d) (z : Fin (Fintype.card (LowTaggedIndex J d)) → ℝ)
    (k : J j) :
    lowTaggedRestriction J d j hj z k = z (lowTaggedSlot J d j hj k) := rfl

@[simp] theorem lowTaggedRestriction_embedding (d : ℕ) (j : Fin m)
    (hj : j.val + 1 ≤ d) (v : J j → ℝ) :
    lowTaggedRestriction J d j hj (lowTaggedEmbedding J d j hj v) = v := by
  funext k
  exact lowTaggedEmbedding_apply_slot J d j hj v k

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.LowTaggedCoordinateProjection
namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} (J : Fin m → Type*) [∀ j, Fintype (J j)]

noncomputable def lowTaggedCoordinates (d : ℕ) (x : ∀ j, J j → ℝ) :
    Fin (Fintype.card (LowTaggedIndex J d)) → ℝ :=
  fun i => x (lowTaggedIndex J d i).1 (lowTaggedIndex J d i).2

@[simp] theorem lowTaggedCoordinates_apply_slot (d : ℕ) (x : ∀ j, J j → ℝ)
    (j : Fin m) (hj : j.val + 1 ≤ d) (k : J j) :
    lowTaggedCoordinates J d x (lowTaggedSlot J d j hj k) = x j k := by
  unfold lowTaggedCoordinates
  rw [lowTaggedIndex_slot]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalTaggedConstraintHistory
namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} (J : Fin m → Type*) [∀ j, Fintype (J j)]

theorem lowTaggedIndex_injective (d : ℕ) :
    Function.Injective (lowTaggedIndex J d) := by
  intro i k h
  apply (Fintype.equivFin (LowTaggedIndex J d)).symm.injective
  apply Subtype.ext
  exact h

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} (J : Fin m → Type*) [∀ j, Fintype (J j)] {X : Type*}

abbrev fullTaggedVariableWeight : X ⊕ (Σ j, J j) → ℕ :=
  Sum.elim (fun _ => 1) (fun i => i.1.val + 1)

noncomputable abbrev lowTaggedVariableWeight (d : ℕ) :
    X ⊕ Fin (Fintype.card (LowTaggedIndex J d)) → ℕ :=
  Sum.elim (fun _ => 1) (lowTaggedWeight J d)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.BufferedSampledCurrentGradePhase
namespace OAI

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial

noncomputable def integerSampledRealChart {σ τ : Type*}
    (β : σ → MvPolynomial τ ℤ) : σ → MvPolynomial τ ℝ :=
  fun i => MvPolynomial.map (Int.castRingHom ℝ) (β i)

theorem integerSampledRealChart_eval {σ τ : Type*}
    (β : σ → MvPolynomial τ ℤ) (u : τ → ℤ) (i : σ) :
    MvPolynomial.eval (fun x => (u x : ℝ)) (integerSampledRealChart β i) =
      (MvPolynomial.eval u (β i) : ℝ) :=
  (MvPolynomial.map_eval (Int.castRingHom ℝ) u (β i)).symm

noncomputable def integerSampledSpatial {m : ℕ} {X τ : Type*} {J : Fin m → Type*}
    (β : X ⊕ (Σ j, J j) → MvPolynomial τ ℤ) (u : τ → ℤ) : X → ℤ :=
  fun x => MvPolynomial.eval u (β (Sum.inl x))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerFrozenChart
namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial
open scoped Classical

variable {I R : Type*} [CommRing R]

noncomputable def frozenCoordinate (keep : I → Prop) (fixed : {i // ¬keep i} → R)
    (i : I) : MvPolynomial {i // keep i} R :=
  if hi : keep i then X ⟨i, hi⟩ else C (fixed ⟨i, hi⟩)

noncomputable def freezePolynomial (keep : I → Prop) (fixed : {i // ¬keep i} → R) :
    MvPolynomial I R →ₐ[R] MvPolynomial {i // keep i} R :=
  aeval (frozenCoordinate keep fixed)

theorem freezePolynomial_map {S : Type*} [CommRing S] (φ : R →+* S)
    (keep : I → Prop) (fixed : {i // ¬keep i} → R) (P : MvPolynomial I R) :
    MvPolynomial.map φ (freezePolynomial keep fixed P) =
      freezePolynomial keep (fun i => φ (fixed i)) (MvPolynomial.map φ P) := by
  change MvPolynomial.map φ (eval₂ C (frozenCoordinate keep fixed) P) =
    eval₂ C (frozenCoordinate keep (fun i => φ (fixed i))) (MvPolynomial.map φ P)
  rw [map_eval₂]
  apply congrArg (fun f => eval₂ C f (MvPolynomial.map φ P))
  funext i
  by_cases hi : keep i <;> simp [frozenCoordinate, hi]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductiveFrozenLocalMajorFamily
namespace OAI

section

namespace Erdos3

open scoped BigOperators TensorProduct

variable {V : Type*} (Long : V → Prop) [DecidablePred Long]

def longCoordinateProjection (i : {i // Long i}) : (V → ℤ) →+ ℤ where
  toFun x := x i.val
  map_zero' := rfl
  map_add' _ _ := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SmoothBadPrimeProduct
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

def smoothResiduePrimeBad {J : Type*} (P : Finset ℕ)
    (E : ∀ p : P, ∀ a : ℕ, (J → ZMod (p.val ^ a)) → Prop)
    (p a : ℕ) (x : J → ℤ) : Prop :=
  ∃ hp : p ∈ P, E ⟨p, hp⟩ a (fun j => (x j : ZMod (p ^ a)))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CRTPolynomialInputAffineLaw
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {L V : Type*} [Fintype L] [Fintype V]

noncomputable def prescribedCRTPolynomialInput
    (p A e : L → ℕ)
    (hq : Pairwise (fun l k => (p l ^ A l).Coprime (p k ^ A k)))
    (origin : ∀ l, V → ZMod (p l ^ A l))
    (x : ∀ l, V → ZMod (p l ^ A l)) : V → ZMod (∏ l, p l ^ A l) :=
  crtInput (fun l => p l ^ A l) hq
    (fun l v => origin l v + (p l : ZMod (p l ^ A l)) ^ e l * x l v)

local instance crtInputModulusNeZero (p A : L → ℕ) [∀ l, NeZero (p l)] :
    NeZero (∏ l, p l ^ A l) :=
  ⟨Finset.prod_ne_zero_iff.mpr (fun l _ => pow_ne_zero _ (NeZero.ne (p l)))⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoordinateCopySum
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def coordinateCopySum {C J R : Type*} [Fintype C]
    [DecidableEq J] [CommRing R] (label : C → J) : (C → R) →ₗ[R] (J → R) where
  toFun x j := ∑ c, if label c = j then x c else 0
  map_add' x y := by
    ext j
    simp only [Pi.add_apply, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro c _
    split_ifs <;> simp
  map_smul' r x := by
    ext j
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    split_ifs <;> simp

@[simp] theorem coordinateCopySum_apply {C J R : Type*} [Fintype C]
    [DecidableEq J] [CommRing R] (label : C → J) (x : C → R) (j : J) :
    coordinateCopySum label x j = ∑ c, if label c = j then x c else 0 := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedModularRankCongruenceOutput
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ}
  {G X : Type*}
  {I E : Fin m → Type*}
  {n : Fin m → ℕ}

abbrev SpatialDegreeOutput (X : Type*) (j : Fin m) := {_x : X // j.val = 0}

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SpatialMatrixBlockWideProbability
namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial
open scoped BigOperators Classical

noncomputable def spatialRankExponent {K : Type*} : Option K → K →₀ ℕ
  | none => 0
  | some k => Finsupp.single k 1

noncomputable def spatialRankPolynomial {K R : Type*} [Fintype K] [CommRing R]
    (c : Option K → R) : MvPolynomial K R :=
  ∑ e, monomial (spatialRankExponent e) (c e)

def spatialKernelRankSlot {G P A : Type*} (e : A ↪ G) (a : A) : Option (G ⊕ P) :=
  some (.inl (e a))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CertifiedFullChartFrozenTerminal
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule _root_.MvPolynomial
open scoped BigOperators Classical

theorem integerSampledRealChart_freeze {A V : Type*}
    (β : A → MvPolynomial V ℤ) (keep : V → Prop)
    (fixed : {i // ¬keep i} → ℤ) (i : A) :
    integerSampledRealChart (fun z => freezePolynomial keep fixed (β z)) i =
      freezePolynomial keep (fun i => (fixed i : ℝ)) (integerSampledRealChart β i) :=
  freezePolynomial_map (Int.castRingHom ℝ) keep fixed (β i)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.FixedSpatialEmptyCoordinates
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

variable {X : Type*}

variable [Fintype X]

noncomputable def fixedSpatialEmptyCoordinates :
    (X → ℝ) ≃ₗᵢ[ℝ] ((Σ _ : X, Unit ⊕ Empty) → ℝ) where
  toFun u a := u a.1
  invFun v x := v ⟨x, .inl ()⟩
  left_inv _ := rfl
  right_inv v := by
    funext a
    rcases a with ⟨x, u | e⟩
    · cases u
      rfl
    · exact isEmptyElim e
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' u := by
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg (norm_nonneg u)).mpr
      intro a
      exact norm_le_pi_norm u a.1
    · apply (pi_norm_le_iff_of_nonneg (norm_nonneg (fun a : Σ _ : X, Unit ⊕ Empty => u a.1))).mpr
      intro x
      exact norm_le_pi_norm (fun a : Σ _ : X, Unit ⊕ Empty => u a.1) ⟨x, .inl ()⟩

noncomputable def fixedSpatialEmptyDensity (f : (X → ℝ) → ℝ)
    (v : (Σ _ : X, Unit ⊕ Empty) → ℝ) : ℝ :=
  f (fixedSpatialEmptyCoordinates.symm v)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ContainedKernelPhysicalDisplacement
namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical
variable {G X T : Type*} [Fintype G] [Fintype X] [Fintype T]

noncomputable def fixedSpatialKernelBlock (e : G ≃ X ⊕ (X ⊕ T))
    (W L : ℝ) (z : Option G × X → ℝ) (second : Bool) : Matrix X X ℝ :=
  fun x i => (L / (1 + W)) * z (some (e.symm (if second then Sum.inr (Sum.inl i) else Sum.inl i)), x)

noncomputable def fixedSpatialKernelRest (e : G ≃ X ⊕ (X ⊕ T))
    (W L : ℝ) (z : Option G × X → ℝ) (t : T → ℝ) : X → ℝ :=
  fun x => (L / (1 + W)) * ∑ j, z (some (e.symm (Sum.inr (Sum.inr j))), x) * t j

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {G X : Type*} [Fintype G]

noncomputable def fixedSpatialKernelSliceFrame (W L : ℝ)
    (z : Option G × X → ℝ) (lower width : G → ℝ) : Option G × X → ℝ :=
  fun a => match a.1 with
    | none => z (none, a.2) + (L / (1 + W)) * ∑ g, z (some g, a.2) * lower g
    | some g => width g * z (some g, a.2)

@[simp] theorem fixedSpatialKernelSliceFrame_none (W L : ℝ)
    (z : Option G × X → ℝ) (lower width : G → ℝ) (x : X) :
    fixedSpatialKernelSliceFrame W L z lower width (none, x) =
      z (none, x) + (L / (1 + W)) * ∑ g, z (some g, x) * lower g := rfl

@[simp] theorem fixedSpatialKernelSliceFrame_some (W L : ℝ)
    (z : Option G × X → ℝ) (lower width : G → ℝ) (g : G) (x : X) :
    fixedSpatialKernelSliceFrame W L z lower width (some g, x) =
      width g * z (some g, x) := rfl

variable {T : Type*} [Fintype X]

theorem fixedSpatialKernelBlock_slice_det (e : G ≃ X ⊕ (X ⊕ T)) (W L : ℝ)
    (z : Option G × X → ℝ) (lower width : G → ℝ) (second : Bool) :
    (fixedSpatialKernelBlock e W L
      (fixedSpatialKernelSliceFrame W L z lower width) second).det =
      (fixedSpatialKernelBlock e W L z second).det *
        ∏ i, width (e.symm (if second then Sum.inr (Sum.inl i) else Sum.inl i)) := by
  have hmatrix : fixedSpatialKernelBlock e W L
      (fixedSpatialKernelSliceFrame W L z lower width) second =
      fixedSpatialKernelBlock e W L z second * Matrix.diagonal
        (fun i => width (e.symm (if second then Sum.inr (Sum.inl i) else Sum.inl i))) := by
    ext x i
    simp only [Matrix.mul_diagonal, fixedSpatialKernelBlock, fixedSpatialKernelSliceFrame_some]
    ring
  rw [hmatrix, Matrix.det_mul, Matrix.det_diagonal]

theorem fixedSpatialKernelBlock_slice_det_ne_zero
    (e : G ≃ X ⊕ (X ⊕ T)) (W L : ℝ)
    (z : Option G × X → ℝ) (lower width : G → ℝ) (second : Bool)
    (hdet : (fixedSpatialKernelBlock e W L z second).det ≠ 0)
    (hwidth : ∀ g, width g ≠ 0) :
    (fixedSpatialKernelBlock e W L
      (fixedSpatialKernelSliceFrame W L z lower width) second).det ≠ 0 := by
  rw [fixedSpatialKernelBlock_slice_det]
  exact mul_ne_zero hdet (Finset.prod_ne_zero_iff.mpr (fun _ _ => hwidth _))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AnisotropicSmoothPairLaw
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

noncomputable def smoothPairCoefficientScale {J : Type*} (H L : ℝ) : Option J → ℝ :=
  fun c => match c with | none => H | some _ => H / L

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastOriginalSampleUniformBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

def forecastOriginalSmoothBudget (m : ℕ) (P : ℝ) : ℝ :=
  (10 * (m : ℝ) + 30) * (P + 1) ^ 2

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedExternalLocalGoodForecastPath
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal Matrix

theorem actualForecastPrimeNeZero (Pr : Finset ℕ) (hPr : ∀ p ∈ Pr, p.Prime) :
    ∀ p : Pr, NeZero p.val :=
  fun p => ⟨(hPr p.val p.property).ne_zero⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ActualFixedSpatialSlicedForecastSourceLaw
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {R σ : Fin m → ℝ}
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (Dmod : ℕ) {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G)
variable (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable {Tsp : Type} [Fintype Tsp]
variable (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)) (Wsp Lsp : ℝ)
variable (physicalN : X → ℕ) (τ δslice P Pbad Ppres : ℝ)

namespace ActualFixedSpatialSlicedForecastPath
variable {B U b S hR hσ Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres}

theorem det_ne_zero_change_decidable {Y : Type} [Fintype Y]
    (d₀ d₁ : DecidableEq Y) (A : Matrix Y Y ℝ) :
    (letI := d₀; A.det ≠ 0) → (letI := d₁; A.det ≠ 0) := by
  cases Subsingleton.elim d₀ d₁
  exact id

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedDenseFiberSliceForecastGeometry
namespace OAI

section

namespace Erdos3.ResidueBoxSlice

theorem fiberParameterStride_le {X : Type*} {keep : X → Prop}
    [DecidablePred keep] {q : ℕ} (i : X) :
    fiberParameterStride (keep := keep) (q := q) i ≤ q := by
  unfold fiberParameterStride
  split <;> omega

end Erdos3.ResidueBoxSlice

end

end OAI
end


