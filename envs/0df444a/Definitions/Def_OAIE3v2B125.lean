-- Prove2me | Definitions.Def_OAIE3v2B125
-- name    : OAIE3v2B125
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:58:24.991362+00:00
-- url     : https://prove2.me/theorems/7bd6d745-fabc-4453-885d-876cc2db79be
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 127 of 311
-- statement:
--   Definitions bundle 127 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B101`, `OAIE3v2B103`, `OAIE3v2B104`, `OAIE3v2B105`, `OAIE3v2B109`, `OAIE3v2B110`, `OAIE3v2B111`, `OAIE3v2B112` of this split.
--
--   Modules: `Dynamics/AdaptedMapGeometryBudget.lean`, `Dynamics/PositiveComparisonDataBudget.lean`, `Dynamics/QuotientDetectorHeightBudget.lean`, `Estimates/AllocatedCoveredFixedTest.lean`, `Estimates/AllocatedEnormousProfiles.lean`, `Estimates/AllocatedFiberCap.lean`, `Estimates/AllocatedOriginalSampleFullSliceLipschitz.lean`, `Estimates/AllocatedOriginalSampleQuadratureUniformBounds.lean`, `Estimates/AllocatedPhysicalLongIdealCap.lean`, `Estimates/AllocatedProfileDimensions.lean`, `Estimates/AllocatedRelativeChildSliceGeometry.lean`, `Estimates/CoefficientJetScalar.lean`, `Estimates/CoefficientSliceEmbedding.lean`, `Estimates/EmptyLayerDetectionGeometry.lean`, `Estimates/ExternalPivotMaskSelection.lean`, `Fourier/AllocatedMaskedCoefficientFourier.lean`, `Fourier/CanonicalDensityFourier.lean`, `Fourier/CoefficientAmbientFourier.lean`, `Geometry/AllocatedProjectedSpatialComparison.lean`, `Lattices/AllocatedIntegerKernelComparison.lean`, `Lattices/IntegerRowInterpolationMixture.lean`, `Linear/CanonicalAmbientKernel.lean`, `Polynomial/AllocatedSpatialLogPolynomial.lean`, `Polynomial/PolynomialPatchShearOrbit.lean`, `Polynomial/PolynomialShearAffineExponential.lean`, `Probability/AllocatedLongJetMixture.lean`, `Probability/CoefficientAmbientDensity.lean`, `Probability/MassBoundedShearBudget.lean`, `Probability/RelativeFullSliceLaw.lean`, `Probability/RelativeSliceFiniteLaw.lean`, `Sampling/FixedSpatialKernelProgressionForecastIntegral.lean`, `Sampling/FullTaggedRationalChartGrid.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B101
import Definitions.Def_OAIE3v2B103
import Definitions.Def_OAIE3v2B104
import Definitions.Def_OAIE3v2B105
import Definitions.Def_OAIE3v2B109
import Definitions.Def_OAIE3v2B110
import Definitions.Def_OAIE3v2B111
import Definitions.Def_OAIE3v2B112

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialShearAffineExponential
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial Module

variable {σ R : Type*} [CommRing R]

theorem polynomialShear_finrank_le {K : Type*} [Field K] [Fintype σ]
    (w : σ → ℕ) (hwpos : ∀ i, 0 < w i) (s : ℕ) (hw : ∀ i, w i ≤ s) :
    finrank K (PolynomialShearLieAlgebra w K) ≤ Fintype.card σ * (Fintype.card σ + 1) ^ s := by
  let : Module.Finite K (weightedSupportLE (R := K) w s) := weightedSupportLE_moduleFinite w hwpos s
  calc
    _ ≤ finrank K (σ → weightedSupportLE (R := K) w s) :=
      LinearMap.finrank_le_finrank_of_injective
        (polynomialShearBoundedCoordinates_injective (R := K) w s hw)
    _ = ∑ _i : σ, finrank K (weightedSupportLE (R := K) w s) := Module.finrank_pi_fintype K
    _ = Fintype.card σ * finrank K (weightedSupportLE (R := K) w s) := by simp
    _ ≤ Fintype.card σ * (Fintype.card σ + 1) ^ s :=
      Nat.mul_le_mul_left _ (weightedSupportLE_finrank_le (K := K) w hwpos s)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialPatchShearOrbit
namespace OAI

section

namespace Erdos3

open Module

variable {σ : Type*} [Fintype σ] (w : σ → ℕ) [Fintype (PolynomialShearIndex w)]

theorem polynomialShearIndex_card_le (s : ℕ) (hpos : ∀ i, 0 < w i) (hw : ∀ i, w i ≤ s) :
    Fintype.card (PolynomialShearIndex w) ≤ Fintype.card σ * (Fintype.card σ + 1) ^ s := by
  rw [← finrank_eq_card_basis (polynomialShearBasis (R := ℚ) w)]
  exact polynomialShear_finrank_le w hpos s hw

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AdaptedMapGeometryBudget
namespace OAI

section

namespace Erdos3

theorem exists_adaptedMapGeometryBudget_fixed_power :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      adaptedMapGeometryBudget p + 1 ≤ (p + 2) ^ C := by
  let P : Polynomial ℕ :=
    (Polynomial.X + 3) ^ 11 + (Polynomial.X + 4) ^ 11 +
      ((Polynomial.X + 1) + ((Polynomial.X + 1) + 4) ^ 5 +
        ((Polynomial.X + 1) + 2) ^ 4 + 2) ^ 4 + Polynomial.X + 2 + 1
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_fixed_power_budget P
  refine ⟨C, hC, fun p hp => ?_⟩
  simpa [P, adaptedMapGeometryBudget, adaptedMarkedMapHeightBudget, Polynomial.eval₂_pow]
    using hbound p hp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerRowInterpolationMixture
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem affineProductProfile_sample_sum {I : Type*} [Fintype I]
    (c w S : I → ℝ) (hw : ∀ i, 0 < w i) (hS : ∀ i, 0 < S i) :
    coefficientWeightSum (affineProductProfile c w) S =
      profileWidthFactor w * ∏ i, shiftedSmoothSampleSum (c i * S i) (w i * S i) := by
  unfold coefficientWeightSum
  simp_rw [affineProductProfile_sample c w S hw hS]
  rw [tsum_mul_left, shiftedSmoothProductSamples_sum _ _ (fun i => mul_pos (hw i) (hS i))]

theorem affineProductProfile_sample_sum_pos {I : Type*} [Fintype I]
    (c w S : I → ℝ) (hw : ∀ i, 0 < w i) (hS : ∀ i, 0 < S i)
    (hlarge : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ w i * S i) :
    0 < coefficientWeightSum (affineProductProfile c w) S := by
  rw [affineProductProfile_sample_sum c w S hw hS]
  exact mul_pos (profileWidthFactor_pos w hw)
    (Finset.prod_pos (fun i _ => shiftedSmoothSampleSum_pos _ (hlarge i)))

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

variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (o : OrthonormalBasis I ℝ W)

theorem mixedAmbientInterpolation_grid (c w : I → ℝ) (f : Fin n → ℝ → ℝ)
    (p : Fin n → PMF ℤ)
    (hf : ∀ i (k : ℤ), f i ((k : ℝ) / basisAxisScale b i) = basisAxisScale b i * (p i k).toReal)
    (u : I → ℝ) (z : Fin n → ℤ) :
    mixedAmbientInterpolation W b o c w f
      ((EuclideanSpace.equiv D ℝ) (normalizedLatticePoint W b (orthonormalMixedChart o (u, z)))) =
      ZLattice.covolume (latticeSection (standardEuclideanLattice D) W) *
        mixedCoefficientDensity c w p (u, z) := by
  have hK : (∏ i, (basisAxisScale b i : ℝ)) ≠ 0 :=
    ne_of_gt (Finset.prod_pos (fun i _ => Nat.cast_pos.mpr (basisAxisScale_pos b i)))
  rw [mixedAmbientInterpolation, ContinuousLinearEquiv.symm_apply_apply,
    mixedRealCoordinates_integer, mixedDensityInterpolation_grid c w f _ p hf,
    mixedDensityCovolumeRatio]
  field_simp [hK]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.RelativeFullSliceLaw
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical
namespace ResidueBoxSlice
variable {X : Type*} [Fintype X] [DecidableEq X] {N : X → ℕ} {q s d : ℕ}

noncomputable def fullSliceReinsertPatch (S : ResidueBoxSlice N q)
    (Q : PolynomialPatch X s d) : PolynomialPatch X s d :=
  Q.reparam S.fullSliceInverseParameters S.fullSliceInverseParameters_degree

end ResidueBoxSlice

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientSliceEmbedding
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

namespace ScalarCubeLocalizationData

variable {I : Type*} [Fintype I] [DecidableEq I] (d : ScalarCubeLocalizationData I)

noncomputable def baseLaw : FiniteProbabilityWeights (IntegerScalarCubeBox I d.length) :=
  scalarCubeResidueWeights I d.length d.modulusBound d.length_pos d.modulus d.residue
    d.modulus_pos d.modulus_le d.size

noncomputable def source : FiniteProbabilityWeights (IntegerScalarCubeBox I d.length) :=
  d.baseLaw.reweight (fun z => d.weight (d.point z)) (fun z => (d.weight_range (d.point z)).1) d.normalized

end ScalarCubeLocalizationData

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.CanonicalAmbientKernel
namespace OAI

section

namespace Erdos3

open Module Submodule MeasureTheory
open scoped NNReal

variable {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W) (o : OrthonormalBasis I ℝ W)

theorem canonicalAmbientKernel_eq_of_lift (c w : I → ℝ) (f : Fin n → ℝ → ℝ)
    (p : Fin n → PMF ℤ)
    (hf : ∀ i (k : ℤ), f i ((k : ℝ) / basisAxisScale b i) = basisAxisScale b i * (p i k).toReal)
    (hs : ∀ x, mixedCoefficientDensity c w p x ≠ 0 → ∀ d,
      |normalizedLatticePoint W b (orthonormalMixedChart o x) d| ≤ 1/4)
    (u : W) (v : D → ℝ)
    (hv : u.val - (EuclideanSpace.equiv D ℝ).symm v ∈ standardEuclideanLattice D)
    (hsmall : ∀ d, |v d| < 1/2) :
    canonicalAmbientKernel W b o c w f v = canonicalMixedDensity W b hb o c w p
      (QuotientAddGroup.mk' (latticeSection (standardEuclideanLattice D) W).toAddSubgroup u) := by
  obtain ⟨y, hy, hq⟩ := exists_normalized_chart_lift W b hb u _ hv
  let x := (orthonormalMixedChart o).symm y
  have hx : normalizedLatticePoint W b (orthonormalMixedChart o x) =
      (EuclideanSpace.equiv D ℝ).symm v := by
    simpa only [x, MeasurableEquiv.apply_symm_apply] using hy
  have hqx : normalizedLatticeQuotient W b hb (orthonormalMixedChart o x) =
      QuotientAddGroup.mk' (latticeSection (standardEuclideanLattice D) W).toAddSubgroup u := by
    simpa only [x, MeasurableEquiv.apply_symm_apply] using hq
  have hgrid : mixedAmbientInterpolation W b o c w f v =
      ZLattice.covolume (latticeSection (standardEuclideanLattice D) W) *
        mixedCoefficientDensity c w p x := by
    simpa only [Prod.mk.eta, hx, ContinuousLinearEquiv.apply_symm_apply] using
      mixedAmbientInterpolation_grid W b o c w f p hf x.1 x.2
  have hd : canonicalMixedDensity W b hb o c w p
      (QuotientAddGroup.mk' (latticeSection (standardEuclideanLattice D) W).toAddSubgroup u) =
      ZLattice.covolume (latticeSection (standardEuclideanLattice D) W) *
        mixedCoefficientDensity c w p x := by
    rw [← hqx]
    apply canonicalMixedDensity_apply W b hb o
    rw [hx]
    exact hsmall
  rw [canonicalAmbientKernel, hgrid, hd]
  by_cases hzero : mixedCoefficientDensity c w p x = 0
  · rw [hzero, mul_zero, mul_zero]
  · have hquarter : ∀ d, |v d| ≤ 1/4 := by
      have hh := hs x hzero
      rw [hx] at hh
      exact hh
    rw [smallBoxCutoff_one v hquarter, one_mul]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.CanonicalDensityFourier
namespace OAI

section

namespace Erdos3

open Module Submodule MeasureTheory
open scoped NNReal

variable {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}

variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W) (o : OrthonormalBasis I ℝ W)

theorem canonicalAmbientTorusDensity_eq (c w : I → ℝ) (f : Fin n → ℝ → ℝ)
    (p : Fin n → PMF ℤ)
    (hf : ∀ i (k : ℤ), f i ((k : ℝ) / basisAxisScale b i) = basisAxisScale b i * (p i k).toReal)
    (hs : ∀ x, mixedCoefficientDensity c w p x ≠ 0 → ∀ d,
      |normalizedLatticePoint W b (orthonormalMixedChart o x) d| ≤ 1/4)
    (u : W) :
    canonicalAmbientTorusDensity W b o c w f (fun i => (u.val i : UnitAddCircle)) =
      canonicalMixedDensity W b hb o c w p
        (QuotientAddGroup.mk' (latticeSection (standardEuclideanLattice D) W).toAddSubgroup u) := by
  let H := canonicalAmbientKernel W b o c w f
  let d := canonicalMixedDensity W b hb o c w p
    (QuotientAddGroup.mk' (latticeSection (standardEuclideanLattice D) W).toAddSubgroup u)
  have hsupport : ∀ v, H v ≠ 0 → ∀ i, |v i| < 1/2 :=
    canonicalAmbientKernel_support W b o c w f
  have hlocal (v : D → ℝ)
      (hv : u.val - (EuclideanSpace.equiv D ℝ).symm v ∈ standardEuclideanLattice D)
      (hvsmall : ∀ i, |v i| < 1/2) : H v = d :=
    canonicalAmbientKernel_eq_of_lift W b hb o c w f p hf hs u v hv hvsmall
  change realPeriodicTorusLift (positiveIntegerPeriodization H)
    (fun i => (u.val i : UnitAddCircle)) = d
  rw [realPeriodicTorusLift_coe _ (positiveIntegerPeriodization_periodic H)]
  by_cases hd : d = 0
  · rw [hd]
    have hz : ∀ z : D → ℤ, H (fun i => u.val i + (z i : ℝ)) = 0 := by
      intro z
      by_cases hz : H (fun i => u.val i + (z i : ℝ)) = 0
      · exact hz
      · exact (hlocal _ (coordinate_integer_translate_sub_mem u.val z) (hsupport _ hz)).trans hd
    simp only [positiveIntegerPeriodization, hz, tsum_zero]
  · obtain ⟨x, hxsmall, hq, _⟩ := canonicalMixedDensity_recover W b hb o c w p hd
    let v := normalizedLatticePoint W b (orthonormalMixedChart o x)
    have hv : u.val - v ∈ standardEuclideanLattice D :=
      normalizedLatticePoint_sub_mem_of_mk_eq W b hb u _ hq.symm
    obtain ⟨z, hz⟩ := exists_coordinate_integer_translate u.val v hv
    calc
      positiveIntegerPeriodization H (fun i => u.val i) =
          positiveIntegerPeriodization H (fun i => v i) := by
        rw [hz]
        exact (positiveIntegerPeriodization_periodic H _ z).symm
      _ = H (fun i => v i) := positiveIntegerPeriodization_local H hsupport _ hxsmall
      _ = d := hlocal _ hv hxsmall

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.CoefficientAmbientDensity
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators NNReal

variable {K : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (c w : ∀ j : Fin m, I j → BoundedCoefficientExponent K (j.val + 1) → ℝ)
variable (f : ∀ j : Fin m, Fin (n j) → BoundedCoefficientExponent K (j.val + 1) → ℝ → ℝ)

variable (p : ∀ j : Fin m, Fin (n j) → BoundedCoefficientExponent K (j.val + 1) → PMF ℤ)
variable (hf : ∀ j i d (k : ℤ), f j i d ((k : ℝ) / basisAxisScale (b j) i) =
  basisAxisScale (b j) i * (p j i d k).toReal)
variable (hs : ∀ j d x, mixedCoefficientDensity (fun i => c j i d) (fun i => w j i d)
  (fun i => p j i d) x ≠ 0 → ∀ a,
    |normalizedLatticePoint (euclideanSubspace (U j)) (b j) (orthonormalMixedChart (o j) x) a| ≤ 1/4)

include hf hs in
omit [Fintype K] in
theorem coefficientAmbientFactor_eq (s : CoefficientSlot K m) (x : CoefficientTorus (K := K) U) :
    coefficientAmbientFactor U b o c w f s (coefficientAmbientSlice s (coefficientAmbientTorus U x)) =
      canonicalMixedDensity (euclideanSubspace (U s.1)) (b s.1) (hb s.1) (o s.1)
        (fun i => c s.1 i s.2) (fun i => w s.1 i s.2) (fun i => p s.1 i s.2)
        (euclideanCoefficientEquiv U x s.1 s.2) := by
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk'_surjective (coefficientIntegerLattice U) x
  rw [euclideanCoefficientEquiv_mk]
  exact canonicalAmbientTorusDensity_eq (euclideanSubspace (U s.1)) (b s.1) (hb s.1) (o s.1)
    _ _ _ _ (fun i k => hf s.1 i s.2 k) (hs s.1 s.2)
    ((euclideanSubspaceArrayEquiv (U s.1)).symm (fun _ => v s))

include hf hs in
theorem coefficientAmbientDensity_eq (x : CoefficientTorus (K := K) U) :
    coefficientAmbientDensity U b o c w f (coefficientAmbientTorus U x) =
      canonicalCoefficientDensity U b hb o c w p x := by
  unfold coefficientAmbientDensity canonicalCoefficientDensity canonicalArrayDensity
  rw [Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro j _
  apply Finset.prod_congr rfl
  intro d _
  exact coefficientAmbientFactor_eq U b hb o c w f p hf hs ⟨j, d⟩ x

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.CoefficientAmbientFourier
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators NNReal

variable {K : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

theorem exists_coefficient_ambient_fourier_approximation
    (c w : ∀ j : Fin m, I j → BoundedCoefficientExponent K (j.val + 1) → ℝ)
    (f : ∀ j : Fin m, Fin (n j) → BoundedCoefficientExponent K (j.val + 1) → ℝ → ℝ)
    (p : ∀ j : Fin m, Fin (n j) → BoundedCoefficientExponent K (j.val + 1) → PMF ℤ)
    (hf : ∀ j i d (k : ℤ), f j i d ((k : ℝ) / basisAxisScale (b j) i) =
      basisAxisScale (b j) i * (p j i d k).toReal)
    (hs : ∀ j d x, mixedCoefficientDensity (fun i => c j i d) (fun i => w j i d)
      (fun i => p j i d) x ≠ 0 → ∀ a,
        |normalizedLatticePoint (euclideanSubspace (U j)) (b j) (orthonormalMixedChart (o j) x) a| ≤ 1/4)
    {B L : ℝ≥0} (hB : 1 ≤ B)
    (hcap : ∀ s x, 0 ≤ coefficientAmbientFactor U b o c w f s x ∧
      coefficientAmbientFactor U b o c w f s x ≤ B)
    (hlip : ∀ s, LipschitzWith L (coefficientAmbientFactor U b o c w f s))
    {δ P : ℝ} (hδ : 0 < δ) (hP : 0 ≤ P)
    (hdim : (Fintype.card (CoefficientAmbientIndex K J) : ℝ) ≤ P)
    (hLP : ((Fintype.card (CoefficientSlot K m) * L * B^Fintype.card (CoefficientSlot K m) : ℝ≥0) : ℝ)
      ≤ Real.exp P) (hδP : δ⁻¹ ≤ Real.exp P) :
    ∃ (F : Type) (inst : Fintype F), letI := inst
    ∃ (frequency : F → ∀ j : Fin m, (K →₀ ℕ) → J j → ℤ) (a : F → ℂ),
      (Fintype.card F : ℝ) ≤ Real.exp (2 * P * (2 * P + 2) ^ 4) ∧
      (∀ t j d, d.degree ≤ j.val + 1 → ∀ i,
        |(frequency t j d i : ℝ)| ≤ Real.exp ((2 * P + 2) ^ 4)) ∧
      (∑ t, ‖a t‖) ≤ Real.exp (2 * P * (2 * P + 2) ^ 4) * (B : ℝ)^Fintype.card (CoefficientSlot K m) ∧
      ∀ x, ‖(canonicalCoefficientDensity U b hb o c w p x : ℂ) -
        coefficientTorusFourierSum U frequency a x‖ ≤ δ := by
  obtain ⟨hbound, hLip⟩ := coefficientAmbientDensity_bounds U b o c w f hB hcap hlip
  have hc : LipschitzWith
      (Fintype.card (CoefficientSlot K m) * L * B^Fintype.card (CoefficientSlot K m))
      (fun x => (coefficientAmbientDensity U b o c w f x : ℂ)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Complex.isometry_ofReal.dist_eq]
    exact hLip.dist_le_mul x y
  have hbnd (x) : ‖(coefficientAmbientDensity U b o c w f x : ℂ)‖ ≤
      (B^Fintype.card (CoefficientSlot K m) : ℝ≥0) := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hbound x).1, NNReal.coe_pow]
      using (hbound x).2
  obtain ⟨F, inst, frequency, a, hcard, hfreq, hsum, herr⟩ :=
    exists_ambient_torus_fourier_approximation _ _ _ hc hbnd hδ hP hdim hLP hδP
  let _ := inst
  refine ⟨F, inst, fun t => coefficientSlotFrequency (fun s i => frequency t ⟨s, i⟩), a,
    hcard, ?_, hsum, ?_⟩
  · intro t
    exact coefficientSlotFrequency_bound (fun s i => frequency t ⟨s, i⟩) (fun s i => hfreq t ⟨s, i⟩)
  · intro x
    simpa only [coefficientAmbientDensity_eq U b hb o c w f p hf hs x,
      coefficientAmbientTorus_character, coefficientTorusFourierSum] using
      herr (coefficientAmbientTorus U x)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.AllocatedMaskedCoefficientFourier
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)

include hC hV in
theorem exists_allocated_coefficient_fourier_approximation
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (hσ1 : ∀ j, σ j ≤ 1)
    (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cinv j * ‖x‖)
    (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1/4)
    {δ P : ℝ} (hδ : 0 < δ) (hP : 0 ≤ P)
    (hdim : (Fintype.card (CoefficientAmbientIndex (LayerSamplerVariables G I n B) J) : ℝ) ≤ P)
    (hLP : let A := allocatedAmbientFactorCap (G := G) B R σ S.value V
      let L := allocatedAmbientFactorLip (G := G) B R σ S.value (fun j => Fintype.card (J j)) C V
      let N := Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m)
      ((N * L * A^N : ℝ≥0) : ℝ) ≤ Real.exp P)
    (hδP : δ⁻¹ ≤ Real.exp P) :
    ∃ (F : Type) (inst : Fintype F), letI := inst
    ∃ (frequency : F → ∀ j : Fin m, (LayerSamplerVariables G I n B →₀ ℕ) → J j → ℤ) (a : F → ℂ),
      (Fintype.card F : ℝ) ≤ Real.exp (2 * P * (2 * P + 2) ^ 4) ∧
      (∀ t j d, d.degree ≤ j.val + 1 → ∀ i,
        |(frequency t j d i : ℝ)| ≤ Real.exp ((2 * P + 2) ^ 4)) ∧
      (∑ t, ‖a t‖) ≤ Real.exp (2 * P * (2 * P + 2) ^ 4) *
        (allocatedAmbientFactorCap (G := G) B R σ S.value V : ℝ)^
          Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m) ∧
      ∀ x, ‖(allocatedCoefficientDensity B U b hb o hR hσ S x : ℂ) -
        coefficientTorusFourierSum U frequency a x‖ ≤ δ := by
  have h := allocatedAmbientFactor_bounds B U b S o C V hC hV hR hσ
  exact exists_coefficient_ambient_fourier_approximation U b hb o _ _ _ _
    (fun j i d => (allocatedLayerIntegerInterpolation_spec B U b S hR hσ j i d).1)
    (allocatedLayerColumns_quarter_support B U b hR hσ S o hσ1 Cinv hCinv hchart hsmall)
    (allocatedAmbientFactorCap_one_le (G := G) B R σ S.value V)
    (fun s x => (h s).1 x) (fun s => (h s).2) hδ hP hdim hLP hδP

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)

include hC hV in
theorem exists_allocated_coefficient_uniform_fourier
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (hσ1 : ∀ j, σ j ≤ 1)
    (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cinv j * ‖x‖)
    (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1/4)
    {P δ : ℝ} (hP : 0 ≤ P) (hm : (m : ℝ) ≤ P)
    (hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ) ≤ P)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (hn : ∀ j, (n j : ℝ) ≤ P)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (hLP : (S.value : ℝ) ≤ Real.exp P)
    (hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (hδ : 0 < δ) (hδP : δ⁻¹ ≤ Real.exp P) :
    let Q := allocatedFourierLogBudget m P
    ∃ (F : Type) (inst : Fintype F), letI := inst
    ∃ (frequency : F → ∀ j : Fin m, (LayerSamplerVariables G I n B →₀ ℕ) → J j → ℤ) (a : F → ℂ),
      (Fintype.card F : ℝ) ≤ Real.exp (2*Q*(2*Q+2)^4) ∧
      (∀ t j d, d.degree ≤ j.val+1 → ∀ i, |(frequency t j d i : ℝ)| ≤ Real.exp ((2*Q+2)^4)) ∧
      (∑ t, ‖a t‖) ≤ Real.exp (2*Q*(2*Q+2)^4+Q) ∧
      ∀ x, ‖(allocatedCoefficientDensity B U b hb o hR hσ S x : ℂ) -
        coefficientTorusFourierSum U frequency a x‖ ≤ δ := by
  have hbudget := allocatedCoefficient_fourier_input_budget B (J := J) R σ S.value S.positive C V
    hP hm hK hR hσ hRP hσP hcount hI hn hJ hAP hLP hCP hVP
  have hLip :
      ((Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m) *
        allocatedAmbientFactorLip (G := G) B R σ S.value (fun j => Fintype.card (J j)) C V *
        (allocatedAmbientFactorCap (G := G) B R σ S.value V)^
          Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m) : ℝ≥0) : ℝ) ≤
      Real.exp (allocatedFourierLogBudget m P) := by
    simpa only [NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_natCast] using hbudget.2.2.2
  obtain ⟨F, inst, frequency, a, hcard, hfreq, hsum, herr⟩ :=
    exists_allocated_coefficient_fourier_approximation B U b hb o S C V hC hV
      hR hσ hσ1 Cinv hCinv hchart hsmall hδ (allocatedFourierLogBudget_nonneg m hP)
      hbudget.2.1 hLip (hδP.trans (Real.exp_le_exp.mpr hbudget.1))
  let _ := inst
  refine ⟨F, inst, frequency, a, hcard, hfreq, ?_, herr⟩
  exact hsum.trans ((mul_le_mul_of_nonneg_left hbudget.2.2.1 (Real.exp_nonneg _)).trans_eq
    (Real.exp_add _ _).symm)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedFiberCap
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped BigOperators

variable {K : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (c w : ∀ j : Fin m, I j → BoundedCoefficientExponent K (j.val + 1) → ℝ)
variable (p : ∀ j : Fin m, Fin (n j) → BoundedCoefficientExponent K (j.val + 1) → PMF ℤ)

variable [∀ j, MeasurableSpace (SubspaceArrayTorus Unit (U j))]
variable [∀ j, BorelSpace (SubspaceArrayTorus Unit (U j))]

omit [Fintype K] in
theorem canonicalCoefficientFactor_measurable (s : CoefficientSlot K m) :
    Measurable (canonicalCoefficientFactor U b hb o c w p s) :=
  (canonicalMixedDensity_measurable _ (b s.1) (hb s.1) (o s.1) _ _ _).comp
    (euclideanSubspaceTorusMeasurableEquiv (U s.1)).symm.measurable

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ExternalPivotMaskSelection
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem exists_simultaneous_external_pivot_masks
    {Ω J K X Y I : Type*} [Fintype Ω] [Fintype J] [Fintype K]
    [Fintype I] [Nonempty I]
    (F : K → X → Y → ℂ) (centers : K → I → Y → ℂ)
    {B ε δ : ℝ} (hnet : ∀ k x, ∃ i, ∀ y, ‖F k x y - centers k i y‖ ≤ ε)
    (outer : FiniteProbabilityWeights Ω) (H : Finset Ω) (hH : 0 < outer.mass H)
    (localLaw : Ω → K → FiniteProbabilityWeights J)
    (physical : Ω → J → X) (point : Ω → K → J → Y) (w : X → ℂ)
    (hB : 0 ≤ B) (hδ : 0 < δ) (herror : B * ε ≤ δ / 2)
    (hw : ∀ x, ‖w x‖ ≤ B)
    (hscore : ∀ a ∈ H, ∀ k, δ ≤ ‖(localLaw a k).complexMean
      (fun j => w (physical a j) * F k (physical a j) (point a k j))‖) :
    ∃ (chosen : K → I) (masked : K → X → ℂ) (H' : Finset Ω),
      (∀ k x, masked k x =
        if externalNetIndex (F k) (centers k) (hnet k) x = chosen k then w x else 0) ∧
      (∀ k x, ‖masked k x‖ ≤ B) ∧
      H' ⊆ H ∧ 0 < outer.mass H' ∧
      outer.mass H / (Fintype.card I : ℝ) ^ Fintype.card K ≤ outer.mass H' ∧
      ∀ a ∈ H', ∀ k, δ / (2 * Fintype.card I) ≤
        ‖(localLaw a k).complexMean (fun j => masked k (physical a j) *
          centers k (chosen k) (point a k j))‖ := by
  have hex (a : Ω) (ha : a ∈ H) (k : K) :=
    exists_externalNet_large_masked_complex_score (localLaw a k) (F k) (centers k)
      (hnet k) (physical a) (point a k) w hB hδ herror
      (fun j => hw _) (hscore a ha k)
  let code : Ω → K → I := fun a k =>
    if ha : a ∈ H then Classical.choose (hex a ha k) else Classical.choice inferInstance
  obtain ⟨chosen, hmass⟩ := outer.exists_code_fiber_mass H code
  let H' := H.filter (fun a => code a = chosen)
  have hsub : H' ⊆ H := Finset.filter_subset _ _
  have hmass' : outer.mass H / (Fintype.card I : ℝ) ^ Fintype.card K ≤ outer.mass H' := by
    rw [Fintype.card_fun, Nat.cast_pow] at hmass
    convert hmass using 1
    congr 1
    ext a
    simp only [H', Finset.mem_filter]
  have hpos : 0 < outer.mass H' :=
    (div_pos hH (pow_pos (Nat.cast_pos.mpr Fintype.card_pos) _)).trans_le hmass'
  let masked := fun k x =>
    if externalNetIndex (F k) (centers k) (hnet k) x = chosen k then w x else 0
  refine ⟨chosen, masked, H', fun _ _ => rfl, ?_, hsub, hpos, hmass', ?_⟩
  · intro k x
    dsimp only [masked]
    split_ifs
    · exact hw x
    · simpa only [norm_zero] using hB
  · intro a ha k
    have hcode : code a = chosen := (Finset.mem_filter.mp ha).2
    have he := Classical.choose_spec (hex a (hsub ha) k)
    have hc : code a k = Classical.choose (hex a (hsub ha) k) := by
      simp only [code, dif_pos (hsub ha)]
    rw [← hc, hcode] at he
    exact he

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PositiveComparisonDataBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem exists_positiveComparisonDataBudget_bound (m q : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ p : ℝ, 0 ≤ p → positiveComparisonDataBudget m q p ≤ (p + a) ^ a := by
  obtain ⟨b, _, hb⟩ := exists_allocatedFourierOutputBudget_bound m
  obtain ⟨a, ha, haBound⟩ := exists_natPolynomial_eval_budget
    ((2 * Polynomial.X + 4) + 2 * (2 * Polynomial.X + 4 + Polynomial.C b) ^ b +
      3 * Polynomial.X + Polynomial.C (q + 1) * (4 * Polynomial.X + 5) + 4)
  refine ⟨a, ha, ?_⟩
  intro p hp
  have hP : 0 ≤ 2 * p + 4 := by linarith
  have hB := allocatedFourierLogBudget_nonneg m hP
  have hBF : allocatedFourierLogBudget m (2 * p + 4) ≤ allocatedFourierOutputBudget m (2 * p + 4) := by
    have h := (allocatedFourierOutputBudget_dominates m hP).2.2
    have hnonneg : 0 ≤ 2 * allocatedFourierLogBudget m (2 * p + 4) *
        (2 * allocatedFourierLogBudget m (2 * p + 4) + 2) ^ 4 := by positivity
    linarith
  have hpoly : (2 * p + 4) + 2 * (2 * p + 4 + b) ^ b + 3 * p +
      (q + 1 : ℕ) * (4 * p + 5) + 4 ≤ (p + a) ^ a := by
    simpa [Polynomial.eval₂_pow] using haBound p hp
  apply le_trans _ hpoly
  unfold positiveComparisonDataBudget
  have hF := hb (2 * p + 4) hP
  push_cast
  linarith

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.QuotientDetectorHeightBudget
namespace OAI

section

namespace Erdos3

theorem rationalHeightLE_ceil_exp_of_entries {q : ℚ} {r : ℝ}
    (hq : (q.num.natAbs : ℝ) ≤ Real.exp r ∧ (q.den : ℝ) ≤ Real.exp r) :
    RationalHeightLE q ⌈Real.exp r⌉₊ :=
  ⟨Nat.cast_le.mp (hq.1.trans (Nat.le_ceil _)),
    Nat.cast_le.mp (hq.2.trans (Nat.le_ceil _))⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientJetScalar
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Matrix

variable {m : ℕ} {I : Fin m → Type*} {n : Fin m → ℕ}

noncomputable def coefficientJetAxisReference (O : Fin m → Type*) [∀ j, Fintype (O j)] :
    ∀ a : LayerSamplerAxis I n, Measure (CoefficientJetAxisRow O a)
  | ⟨j, .inl _⟩ => (volume : Measure (O j → ℝ))
  | ⟨j, .inr _⟩ => (Measure.count : Measure (O j → ℤ))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedEnormousProfiles
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

noncomputable def allocatedLongCoefficientSource : Measure (AllocatedLongCoefficients B U basis S) :=
  Measure.pi (fun a => allocatedCoefficientAxisLaw B U basis hR hσ S a.val)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

theorem allocatedIntegerProfileScales_pos (j : Fin m) (i : Fin (n j)) (d) :
    0 < allocatedIntegerProfileScales B U basis S j i d :=
  div_pos (by exact_mod_cast basisAxisScale_pos (basis j) i)
    (monomialScale_pos _ (fun v => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U basis S v)) d.val)

include hR hσ in
theorem allocatedIntegerProfileWidths_pos (j : Fin m) (i : Fin (n j)) (d) :
    0 < allocatedIntegerProfileWidths (G := G) B R σ j i d :=
  coefficientProfileWidth_pos _ _ (div_pos (hR j) (by norm_num)) (principalProfileSize_pos (hR j) _)
    (tailProfileSize_pos (hR j) (hσ j) _) d

variable (j : Fin m) (i : Fin (n j)) (hσ1 : σ j ≤ 1)
variable (henormous : S.value^(layerTailDegree m+1) < basisAxisScale (basis j) i)

include hR hσ hσ1 in
theorem allocatedIntegerProfile_support :
    ∀ x, R j < ‖x‖ → affineProductProfile (allocatedIntegerProfileCenters (G := G) B R j i)
      (allocatedIntegerProfileWidths B R σ j i) x = 0 := by
  apply affineProductProfile_zero_outside _ _ (allocatedIntegerProfileWidths_pos B hR hσ j i) (hR j).le
  intro d
  exact (allocatedProfile_term_bound (layerIntegerPrincipalSlots B j i) (constantCoefficientSlot _ _)
    (layerIntegerPrincipalSlots_not_constant B j i) (hR j) (hσ j) hσ1 d).trans (by linarith [hR j])

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedIntegerKernelComparison
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (j : Fin m) (i : Fin (n j))

local notation "centers" => allocatedIntegerProfileCenters (G := G) B R j i
local notation "widths" => allocatedIntegerProfileWidths (G := G) B R σ j i
local notation "reindex" => allocatedKernelCoefficientEquiv (G := G) B j
local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S

variable {α O : Type*} [Fintype α] [DecidableEq α] [Fintype O] [DecidableEq O]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable (rows : O → Finset α) (s : O ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ((scalarKernelIntegerJet x (j.val+1) rows).submatrix id s).det ≠ 0)

local notation "input" => partitionedPrincipalInput grid (fun g a => (g, a))
local notation "fixedReal" => Sum.elim
  (fun ga : G × Option α => ((x (Prod.fst ga) (Prod.snd ga) : ℤ) : ℝ) / (S.value : ℝ))
  (principalTupleNormalized (principalAxisLength grid sides) u)
local notation "height" => (basisAxisScale (basis j) i : ℝ)
local notation "heightPos" => Nat.cast_pos.mpr (basisAxisScale_pos (basis j) i)
local notation "kernelScale" => kernelJetCoefficientScale G (j.val+1) (S.value : ℝ) height
local notation "pivot" => normalizedPivotEquiv (Matrix.submatrix (scalarKernelIntegerJet x (j.val+1) rows) id s) hA
  (fun o => kernelScale (s o)) (fun _ => height)
  (fun o => kernelJetCoefficientScale_pos G (j.val+1)
    (Nat.cast_pos.mpr (LayerSamplerScale.positive S)) heightPos (s o))
  (fun _ => heightPos)
local notation "free" => matrixSupCLM (normalizedIntegerColumns
  (remainingMatrixColumns (scalarKernelIntegerJet x (j.val+1) rows) s)
  (fun d => kernelScale (Subtype.val d)) (fun _ => height))

noncomputable def allocatedIntegerKernelDensity
    (y : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) (fun a => ¬grid a) → ℝ) :
    (O → ℝ) → ℝ :=
  affineSelectedJetDensity s pivot free (allocatedNonkernelExponent B j) input fixedReal rows
    (centers ∘ reindex) (widths ∘ reindex) y

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedLongJetMixture
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)

noncomputable def allocatedLongJetReference (O : Fin m → Type*) [∀ j, Fintype (O j)] :
    Measure (AllocatedLongJetRows B U basis S O) :=
  Measure.pi (fun a : {a // ¬grid a} => coefficientJetAxisReference O a.val)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedCoveredFixedTest
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v w : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "axis" => coefficientJetAxisEquiv O I n
local notation "join" => MeasurableEquiv.piEquivPiSubtypeProd (CoefficientJetAxisRow O) grid

noncomputable def allocatedMixedJetReconstruct
    (a₀ : AllocatedFrozenCoefficients B U b S) (z : AllocatedLongJetRows B U b S O) :
    ∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ) :=
  (axis).symm ((join).symm (allocatedFrozenJetMap B U b S x u w rows a₀, z))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)] (d : ℕ) [NeZero d]

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "root" v => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v)
local notation "dirs" v => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)
local notation "deck" => PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)

variable (φ : (AllocatedFrozenCoefficients B U b S ×
  (∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ))) × (∀ j, O j → Q j → ZMod d) → ℂ)

noncomputable def allocatedDeckMixedTest (a₀ : AllocatedFrozenCoefficients B U b S)
    (t : ∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ)) : ℂ :=
  ∫ r, φ ((a₀, t), coefficientDeckJetMap (root v₀) (dirs v₀) rows d r) ∂(deck).toMeasure

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (F : AllocatedFrozenCoefficients B U b S × EuclideanJetLayers U O → ℂ)

local notation "pullback" => (fun p : (AllocatedFrozenCoefficients B U b S ×
  (∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ))) × (∀ j, O j → Q j → ZMod d) =>
  F (Prod.fst (Prod.fst p), coveredJetChart U b hb bW d
    (mixedCoveredJetCoordinates U o d (Prod.snd (Prod.fst p), Prod.snd p))))

noncomputable def allocatedCoveredFixedTest
    (a₀ : AllocatedFrozenCoefficients B U b S) (z : AllocatedLongJetRows B U b S O) : ℂ :=
  allocatedDeckMixedTest B U b S x u v₀ rows Q d pullback a₀
    (allocatedMixedJetReconstruct B U b S x u v₀ rows a₀ z)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.RelativeSliceFiniteLaw
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

namespace ResidueBoxSlice

variable {X : Type*} [Fintype X] [DecidableEq X]
variable {keep : X → Prop} [DecidablePred keep] {N : X → ℕ} {q : ℕ}

noncomputable def fiberSliceLaw
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
    (hlen : ∀ k, 0 < S.length k) (fixed : {x // ¬keep x} → ℤ)
    (hfixed : ∀ k, 0 ≤ fixed k ∧ fixed k < (N k.val : ℤ)) :
    FiniteProbabilityWeights (integerBox N) := by
  letI : ∀ k, Nonempty (Fin (S.length k)) := fun k => ⟨⟨0, hlen k⟩⟩
  exact (FiniteProbabilityWeights.uniform (∀ k, Fin (S.length k))).finitePushforward
    (S.fiberPointInBox fixed hfixed)

theorem fiberSliceLaw_mean
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
    (hlen : ∀ k, 0 < S.length k) (fixed : {x // ¬keep x} → ℤ)
    (hfixed : ∀ k, 0 ≤ fixed k ∧ fixed k < (N k.val : ℤ))
    (test : integerBox N → ℝ) :
    (S.fiberSliceLaw hlen fixed hfixed).mean test =
      𝔼 u, test (S.fiberPointInBox fixed hfixed u) := by
  let : ∀ k, Nonempty (Fin (S.length k)) := fun k => ⟨⟨0, hlen k⟩⟩
  exact FiniteProbabilityWeights.uniform_finitePushforward_mean _ _

end ResidueBoxSlice

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.MassBoundedShearBudget
namespace OAI

section

namespace Erdos3

theorem exists_mass_bounded_shear_parameter_budget (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (d D : ℕ) (M p : ℝ),
      0 ≤ p → 0 ≤ M → M ≤ p → (d : ℝ) ≤ p → D ≤ d * (d + 1) ^ s →
      ∃ t : ℝ, 0 ≤ t ∧
        (D + s.factorial + 2 * s + 1 : ℕ) ≤ t ∧
        t + shearKernelLogBudget s d M p + shearActionLogBudget s d M + (t + a) ^ a + 4 ≤
          (p + 2) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let Q := 1 + X + Polynomial.C (s.factorial + 2 * s + 1) + X * (X + 1) ^ s
  let K := Q + Q + Q + Polynomial.C s +
    (Polynomial.C s * Q * Q + 1) * (Polynomial.C s * (Q + 1))
  let T := Polynomial.C s + Polynomial.C s *
    (Q * (Polynomial.C (s + 1) * (Q + 1) ^ s) * Polynomial.C s) +
    Polynomial.C s * (Polynomial.C s * Q * Q)
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_fixed_power_budget
    (Q + K + T + (Q + Polynomial.C a) ^ a + 4)
  refine ⟨C, hC, ?_⟩
  intro d D M p hp hM hMp hd hD
  let t : ℝ := 1 + p + (s.factorial + 2 * s + 1 : ℕ) + p * (p + 1) ^ s
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hpt : p ≤ t := by
    have hprod : 0 ≤ p * (p + 1) ^ s := by positivity
    dsimp [t]
    linarith [Nat.cast_nonneg (α := ℝ) (s.factorial + 2 * s + 1)]
  have hdt := hd.trans hpt
  have hMt := hMp.trans hpt
  have hDb : (D : ℝ) ≤ p * (p + 1) ^ s := by
    apply (Nat.cast_le.mpr hD).trans
    push_cast
    gcongr
  have hgeo : ((D + s.factorial + 2 * s + 1 : ℕ) : ℝ) ≤ t := by
    dsimp [t]
    push_cast at *
    linarith
  have hK : shearKernelLogBudget s d M p ≤
      t + t + t + s + ((s : ℝ) * t * t + 1) * ((s : ℝ) * (t + 1)) := by
    unfold shearKernelLogBudget
    push_cast
    gcongr
  have hT : shearActionLogBudget s d M ≤
      s + (s : ℝ) * (t * (((s : ℝ) + 1) * (t + 1) ^ s) * s) +
        s * ((s : ℝ) * t * t) := by
    unfold shearActionLogBudget
    push_cast
    gcongr
  have htotal : t +
      (t + t + t + s + ((s : ℝ) * t * t + 1) * ((s : ℝ) * (t + 1))) +
      (s + (s : ℝ) * (t * (((s : ℝ) + 1) * (t + 1) ^ s) * s) +
        s * ((s : ℝ) * t * t)) + (t + a) ^ a + 4 ≤ (p + 2) ^ C := by
    simpa [X, Q, K, T, t, Polynomial.eval₂_pow, Nat.cast_add, Nat.cast_mul] using hbound p hp
  refine ⟨t, ht, hgeo, ?_⟩
  linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedRelativeChildSliceGeometry
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "degree" => layerSamplerDegree I n

theorem allocatedPrincipalSides_long_of_not_short (a : LayerSamplerAxis I n)
    (ha : ¬allocatedShortAxis (I := I) U basis S.value a) (b : B a) (v : Fin (degree a)) :
    allocatedPrincipalSides B U basis S ⟨a, b, v⟩ = S.value := by
  rcases a with ⟨j, i⟩
  cases i with
  | inl i => rfl
  | inr i =>
    have hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i := Nat.lt_of_not_ge ha
    simp only [allocatedPrincipalSides, layerSamplerSides, heterogeneousSamplerSides,
      layerSamplerDenominators, Sum.elim_inr, layerSamplerDegree,
      integerAxisSideLength, hactive, ↓reduceIte]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedOriginalSampleQuadratureUniformBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (degree (Subtype.val a)))

noncomputable def allocatedOriginalSampleLiftLip : ℝ≥0 := Fintype.card Input * m

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (L : ℕ)

def allocatedShortIntegerAxisEquiv :
    AllocatedShortIntegerAxis U b L ≃
      {a : LayerSamplerAxis I n // allocatedShortAxis U b L a} where
  toFun a := ⟨⟨a.val.1, Sum.inr a.val.2⟩, a.property⟩
  invFun a := by
    rcases a with ⟨⟨j, i⟩, ha⟩
    cases i with
    | inl i => exact False.elim ha
    | inr i => exact ⟨⟨j, i⟩, ha⟩
  left_inv a := by cases a; rfl
  right_inv a := by
    rcases a with ⟨⟨j, i⟩, ha⟩
    cases i with
    | inl i => exact False.elim ha
    | inr i => rfl

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedOriginalSampleFullSliceLipschitz
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

noncomputable def allocatedOriginalSampleFullSliceLip (t : ℝ) : ℝ≥0 :=
  (1 + Real.toNNReal |t|) * allocatedOriginalSampleLiftLip B U basis S

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedProfileDimensions
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

theorem allocatedKernelVariables_card_le_variables :
    Fintype.card G ≤ Fintype.card (LayerSamplerVariables G I n B) := by
  change _ ≤ Fintype.card (G ⊕ PrincipalTupleIndex B (layerSamplerDegree I n))
  rw [Fintype.card_sum]
  omega

theorem allocatedJointParameter_card (α : Type*) [Fintype α] :
    Fintype.card (JointBlockParameter B (layerSamplerDegree I n) α) =
      Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n))*(Fintype.card α+1) := by
  simp only [JointBlockParameter, BlockParameter, PrincipalTupleIndex, Fintype.card_sigma,
    Fintype.card_prod, Fintype.card_fin, Fintype.card_option]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  ring

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedPhysicalLongIdealCap
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] (rowSets : Fin m → Finset (Finset α))

noncomputable def allocatedIdealCoverSupport (j : Fin m) : ℝ :=
  (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
    ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)) +
  (partitionedIdealRadius α m + 1) +
  ∑ i : Fin (n j), (allocatedSiteCoefficientRadius (G := G) B rowSets ⟨j, i⟩ + 1)

theorem allocatedIdealCoverSupport_nonneg (j : Fin m) :
    0 ≤ allocatedIdealCoverSupport (G := G) B rowSets j := by
  have hi := partitionedIdealRadius_nonneg α m
  have hw : 0 ≤ ∑ i : Fin (n j), (allocatedSiteCoefficientRadius (G := G) B rowSets ⟨j, i⟩ + 1) :=
    Finset.sum_nonneg (fun i _ => by linarith [allocatedSiteCoefficientRadius_nonneg (G := G) B rowSets ⟨j, i⟩])
  unfold allocatedIdealCoverSupport
  positivity

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedProjectedSpatialComparison
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

noncomputable def allocatedSpatialLateLog (P Q : ℝ) : ℝ :=
  2 * Q + 3 + Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m) * allocatedAmbientLog m P

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.AllocatedSpatialLogPolynomial
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem allocatedSpatialLateLog_nonneg {m : ℕ} {G : Type*} [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) :
    0 ≤ allocatedSpatialLateLog (G := G) B P Q := by
  have := allocatedAmbientLog_nonneg m hP
  unfold allocatedSpatialLateLog
  positivity

theorem exists_allocatedSpatialLateLog_bound (m : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ {G : Type*} [Fintype G]
      {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
      (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] {P Q T : ℝ},
      0 ≤ P → 0 ≤ Q → P ≤ T → Q ≤ T →
      (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ T →
      allocatedSpatialLateLog (G := G) B P Q ≤ (T + a) ^ a := by
  let scalar : Polynomial ℕ := 7 * (Polynomial.C (layerTailDegree m + 1) * (4 * (Polynomial.X + 8)) + 8)
  let common : Polynomial ℕ := Polynomial.X + Polynomial.X * scalar + 1
  let width : Polynomial ℕ := Polynomial.C (m + 4) * (Polynomial.X + 8)
  let mixed : Polynomial ℕ := (2 * Polynomial.X + 1) * (width + common) + 3 * Polynomial.X + 1
  let ambient : Polynomial ℕ := Polynomial.X + Polynomial.X * (2 * mixed + 4 * Polynomial.X + 9) + 1
  let poly : Polynomial ℕ := 2 * Polynomial.X + 3 +
    Polynomial.C (m * (m + 1)) * (Polynomial.X + 1) ^ m * ambient
  obtain ⟨a, ha, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨a, ha, ?_⟩
  intro G _ I _ n B _ P Q T hP hQ hPT hQT hvars
  have hT : 0 ≤ T := hP.trans hPT
  have hslots : (Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m) : ℝ) ≤
      (m : ℝ) * (m + 1) * (T + 1) ^ m := by
    have h : (Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m) : ℝ) ≤
        (m : ℝ) * (m + 1) * ((Fintype.card (LayerSamplerVariables G I n B) : ℝ) + 1) ^ m := by
      exact_mod_cast coefficientSlot_card_le (K := LayerSamplerVariables G I n B) m
    apply h.trans
    gcongr
  have hambient : allocatedAmbientLog m P ≤ allocatedAmbientLog m T := by
    dsimp only [allocatedAmbientLog, allocatedMixedLog, allocatedWidthLog, allocatedCommonLog,
      allocatedScalarLog, integerInterpolationLogEnvelope]
    gcongr
  have hA0 := allocatedAmbientLog_nonneg m hP
  calc
    allocatedSpatialLateLog (G := G) B P Q ≤
        2 * T + 3 + ((m : ℝ) * (m + 1) * (T + 1) ^ m) * allocatedAmbientLog m T := by
      unfold allocatedSpatialLateLog
      gcongr
    _ ≤ _ := by
      simpa [poly, ambient, mixed, width, common, scalar, allocatedAmbientLog, allocatedMixedLog,
        allocatedWidthLog, allocatedCommonLog, allocatedScalarLog, integerInterpolationLogEnvelope,
        Polynomial.eval₂_pow] using hbound T hT

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.FixedSpatialKernelProgressionForecastIntegral
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X T : Type*} [Fintype G] [Fintype X] [DecidableEq X]
  [MeasurableSpace T]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

variable (μ : Measure T) [IsProbabilityMeasure μ] (center : X → ℝ) {rest : T → X → ℝ}
variable (hrest : Measurable rest) (A₁ A₂ : (X → ℝ) ≃L[ℝ] (X → ℝ))
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    4 ≤ Fintype.card (B a.val))
  (lower width : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

noncomputable def fixedSpatialOriginalForecastCap {δ : ℝ} (hδ : 0 < δ) : ℝ≥0 :=
  fixedSpatialBlockDensityCap A₂ * allocatedForecastAllAxisLiftCap B hδ

noncomputable def fixedSpatialOriginalForecastLip {δ : ℝ} (hδ : 0 < δ) : ℝ≥0 :=
  allocatedForecastAllAxisLiftCap B hδ * fixedSpatialBlockDensityLipschitz A₁ A₂ +
    fixedSpatialBlockDensityCap A₂ * allocatedForecastAllAxisLiftLip B hδ

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.FullTaggedRationalChartGrid
namespace OAI

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators Classical Matrix

variable {m : ℕ} {X : Type*} (J : Fin m → Type*) [∀ j, Fintype (J j)]

theorem fullTaggedLinearMapChart_coefficientGrid
    (P : ∀ j, (J j → ℝ) →ₗ[ℝ] (J j → ℝ)) (D : ℕ)
    (hP : ∀ j i a, ∃ z : ℤ, (D : ℝ) * P j (Pi.single a 1) i = (z : ℝ))
    (v : X ⊕ (Σ j, J j)) :
    realPolynomialCoefficientGrid D (fullTaggedLinearMapChart J P v) := by
  cases v with
  | inl x => exact realPolynomialCoefficientGrid_X D _
  | inr v =>
    apply (realPolynomialCoefficientGrid_iff D _).mpr
    change C (D : ℝ) * (∑ a : J v.1, P v.1 (Pi.single a 1) v.2 •
      MvPolynomial.X (Sum.inr ⟨v.1, a⟩ : X ⊕ (Σ j, J j))) ∈
        integralRealPolynomialSubring (X ⊕ (Σ j, J j))
    simp only [smul_eq_C_mul, Finset.mul_sum]
    apply (integralRealPolynomialSubring _).sum_mem
    intro a _
    obtain ⟨z, hz⟩ := hP v.1 v.2 a
    rw [← mul_assoc, ← map_mul, hz]
    exact (integralRealPolynomialSubring _).mul_mem
      (C_int_mem_integralRealPolynomialSubring z) (X_mem_integralRealPolynomialSubring _)

end Erdos3.VectorPolynomial

end

end OAI
end


