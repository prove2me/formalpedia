-- Prove2me | Definitions.Def_OAIE3v2B098
-- name    : OAIE3v2B098
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:26:55.443276+00:00
-- url     : https://prove2.me/theorems/87fa93e0-a4cb-43c8-9846-c7eacb7df117
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 100 of 311
-- statement:
--   Definitions bundle 100 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B069`, `OAIE3v2B070`, `OAIE3v2B071`, `OAIE3v2B072`, `OAIE3v2B074`, `OAIE3v2B081`, `OAIE3v2B082`, `OAIE3v2B083` of this split.
--
--   Modules: `Estimates/AllocatedAmbientLogBounds.lean`, `Estimates/AllocatedScalarLogBounds.lean`, `Estimates/AllocatedShortAxis.lean`, `Estimates/BooleanCubeProduct.lean`, `Estimates/EmptyLayerDetectionGeometry.lean`, `Estimates/InactiveShortLogBounds.lean`, `Estimates/MixedRealPoint.lean`, `Estimates/PrincipalAxisInterpolation.lean`, `Fourier/AllocatedMaskedCoefficientFourier.lean`, `Fourier/CanonicalDensityFourier.lean`, `Fourier/EuclideanCoefficientTorus.lean`, `Geometry/EmptyLayerChartBounds.lean`, `Geometry/MixedCoefficientSmallSupport.lean`, `Geometry/MixedRealCoordinates.lean`, `Geometry/NormalizedChartLift.lean`, `Lattices/AffineCoefficientLaw.lean`, `Lattices/IntegerRowInterpolationMixture.lean`, `Lattices/PrincipalIntegerInterpolation.lean`, `Linear/CanonicalAmbientKernel.lean`, `Polynomial/IntegerPolynomialInterpolation.lean`, `Probability/CoefficientAmbientDensity.lean`, `Probability/MixedDensityInterpolation.lean`, `Probability/ScaledArrayLaw.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B069
import Definitions.Def_OAIE3v2B070
import Definitions.Def_OAIE3v2B071
import Definitions.Def_OAIE3v2B072
import Definitions.Def_OAIE3v2B074
import Definitions.Def_OAIE3v2B081
import Definitions.Def_OAIE3v2B082
import Definitions.Def_OAIE3v2B083

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BooleanCubeProduct
namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H]

theorem norm_gowersMoment (j : ℕ) (f : H → ℂ) :
    ‖gowersMoment (j + 1) f‖ = (gowersMoment (j + 1) f).re := by
  have he : gowersMoment (j + 1) f = ((gowersMoment (j + 1) f).re : ℂ) := by
    apply Complex.ext
    · rfl
    · simp only [gowersMoment_im_zero, Complex.ofReal_im]
  conv_lhs => rw [he]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (gowersMoment_re_nonneg j f)]

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H]

theorem gowersNorm_pow_le_mean_norm (j : ℕ) (f : H → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    gowersNorm (j + 1) f ^ (2 ^ (j + 1)) ≤ 𝔼 x, ‖f x‖ := by
  rw [gowersNorm_pow, ← norm_gowersMoment]
  exact norm_gowersMoment_le_mean_norm (j + 1) f hf

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
open scoped BigOperators ContDiff

theorem affineProductProfile_norm_le {I : Type*} [Fintype I] (c w : I → ℝ)
    (hw : ∀ i, 0 < w i) (x : I → ℝ) : ‖affineProductProfile c w x‖ ≤ profileWidthFactor w := by
  rw [Real.norm_eq_abs, abs_of_nonneg (affineProductProfile_nonneg c w hw x)]
  exact Finset.prod_le_prod (fun i _ => affineProbabilityProfile_nonneg (c i) (hw i) (x i))
    (fun i _ => affineProbabilityProfile_le (c i) (hw i) (x i))

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

theorem affineProductProfile_lipschitz {I : Type*} [Fintype I]
    (c w : I → ℝ) {δ : ℝ≥0} (hδ : 0 < δ) (hw : ∀ i, (δ : ℝ) ≤ w i) :
    LipschitzWith (affineProductProfileLip I δ) (affineProductProfile c w) := by
  have hδr : (0 : ℝ) < δ := hδ
  have hwp := profileWidthFactor_pos w (fun i => hδr.trans_le (hw i))
  have hl := (smoothProductProfile_lipschitz I).comp
    (normalizedCoefficientCoordinates_lipschitz c w hδ hw)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hb := hl.dist_le_mul x y
  rw [Real.dist_eq] at hb ⊢
  rw [affineProductProfile_eq, affineProductProfile_eq, ← mul_sub, abs_mul, abs_of_pos hwp]
  calc
    _ ≤ profileWidthFactor w *
        (((Fintype.card I * probabilityProfileLipschitz * δ⁻¹ : ℝ≥0) : ℝ) * dist x y) :=
      mul_le_mul_of_nonneg_left hb hwp.le
    _ ≤ (δ : ℝ)⁻¹ ^ Fintype.card I *
        (((Fintype.card I * probabilityProfileLipschitz * δ⁻¹ : ℝ≥0) : ℝ) * dist x y) :=
      mul_le_mul_of_nonneg_right (profileWidthFactor_le w hδr hw) (by positivity)
    _ = _ := by
      simp only [affineProductProfileLip, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_pow,
        NNReal.coe_inv, pow_succ]
      ring

theorem affineProductProfile_cap {I : Type*} [Fintype I]
    (c w : I → ℝ) {δ : ℝ} (hδ : 0 < δ) (hw : ∀ i, δ ≤ w i) :
    ∀ x, ‖affineProductProfile c w x‖ ≤ δ⁻¹ ^ Fintype.card I :=
  fun x => (affineProductProfile_norm_le c w (fun i => hδ.trans_le (hw i)) x).trans
    (profileWidthFactor_le w hδ hw)

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

theorem normalizedIntegerPMF_apply (K c δ : ℝ) (hK : 0 < K) (hδ : 0 < δ)
    (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ δ * K) (k : ℤ) :
    (normalizedIntegerPMF K c δ hK hδ hlarge k).toReal =
      smoothProbabilityProfile (((k : ℝ) - c * K) / (δ * K)) /
        shiftedSmoothSampleSum (c * K) (δ * K) :=
  shiftedSmoothCoefficientPMF_apply _ _ _ _ _

theorem normalizedIntegerInterpolation_grid (K c δ : ℝ) (hK : 0 < K) (hδ : 0 < δ)
    (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ δ * K) (k : ℤ) :
    normalizedIntegerInterpolation K c δ ((k : ℝ) / K) =
      K * (normalizedIntegerPMF K c δ hK hδ hlarge k).toReal := by
  rw [normalizedIntegerInterpolation, affineProfile_sample_coordinate c (k : ℝ) hδ hK,
    normalizedIntegerPMF_apply, mul_div_assoc]

end Erdos3

end

section

namespace Erdos3

theorem normalizedIntegerInterpolation_spec (K c δ : ℝ) (hK : 0 < K) (hδ : 0 < δ)
    (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ δ * K) :
    IsIntegerMassInterpolation K (normalizedIntegerPMF K c δ hK hδ hlarge)
      (2 / δ) (2 * (probabilityProfileLipschitz : ℝ) / δ ^ 2) (normalizedIntegerInterpolation K c δ) :=
  ⟨normalizedIntegerInterpolation_grid K c δ hK hδ hlarge,
    normalizedIntegerInterpolation_range K c δ hK hδ hlarge,
    normalizedIntegerInterpolation_difference K c δ hK hδ hlarge⟩

end Erdos3

end

section

namespace Erdos3

theorem constantIntegerInterpolation_spec (K δ : ℝ) (hK : 0 < K) (hδ : 0 < δ) :
    IsIntegerMassInterpolation K (constantIntegerPMF K δ hK hδ)
      (constantIntegerInterpolationCap δ) (constantIntegerInterpolationLip δ)
      (constantIntegerInterpolation K δ) := by
  by_cases hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ δ * K
  · rw [constantIntegerPMF_large K δ hK hδ hlarge]
    simp only [constantIntegerInterpolation, hlarge, ↓reduceIte]
    apply (normalizedIntegerInterpolation_spec K 0 δ hK hδ hlarge).mono
    · apply div_le_div_of_nonneg_right _ hδ.le
      have hA : (1 : ℝ) ≤ probabilityProfileLipschitz := probabilityProfileLipschitz_one_le
      linarith
    · exact le_max_left _ _
  · obtain ⟨hp, hbound⟩ := constantIntegerPMF_small K δ hK hδ (lt_of_not_ge hlarge)
    rw [hp]
    simp only [constantIntegerInterpolation, hlarge, ↓reduceIte]
    apply (integerMassTent_spec K hK 0).mono hbound.le
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hK.le hbound.le 2) (by norm_num)).trans
      (le_max_right _ _)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.EmptyLayerChartBounds
namespace OAI

section

namespace Erdos3

open Module Submodule MeasureTheory
open scoped BigOperators

variable {E : Type*} {n : ℕ} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

theorem normalizedOrthogonalChart_integer_coordinates (W : Submodule ℝ E)
    (b : Basis (Fin n) ℝ Wᗮ) (x : E)
    (hx : Wᗮ.orthogonalProjectionOnto x ∈ span ℤ (Set.range b)) :
    ∃ z : Fin n → ℤ, ∀ i,
      (normalizedOrthogonalChart W b x).2 i = (z i : ℝ) / (basisAxisScale b i : ℝ) := by
  have h := (b.mem_span_iff_repr_mem ℤ _).mp hx
  choose z hz using h
  refine ⟨z, ?_⟩
  intro i
  rw [normalizedOrthogonalChart_apply]
  change b.repr (Wᗮ.orthogonalProjectionOnto x) i / (basisAxisScale b i : ℝ) = _
  rw [← hz i]
  simp

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

theorem euclideanCoefficientEquiv_continuous [Fintype K] :
    Continuous (euclideanCoefficientEquiv (K := K) U) := by
  apply continuous_pi
  intro j
  apply continuous_pi
  intro d
  exact (euclideanSubspaceTorusEquiv_symm_continuous (U j)).comp
    ((continuous_apply ⟨j, d⟩).comp (coefficientCoordinateTorus_continuous U))

noncomputable def euclideanCoefficientHomeomorph [Fintype K]
    [CompactSpace (CoefficientTorus (K := K) U)] :
    CoefficientTorus (K := K) U ≃ₜ EuclideanCoefficientLayers (K := K) U := by
  exact Continuous.homeoOfEquivCompactToT2
    (f := (euclideanCoefficientEquiv U).toEquiv) (euclideanCoefficientEquiv_continuous U)

noncomputable def euclideanCoefficientMeasurableEquiv [Fintype K]
    [CompactSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)] :
    CoefficientTorus (K := K) U ≃ᵐ EuclideanCoefficientLayers (K := K) U :=
  (euclideanCoefficientHomeomorph U).toMeasurableEquiv

theorem euclideanCoefficient_measurePreserving [Fintype K]
    [CompactSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)] :
    MeasurePreserving (euclideanCoefficientEquiv U) μ
      (Measure.pi (fun j => Measure.pi (fun _ : BoundedCoefficientExponent K (j.val + 1) => ν j))) := by
  let ξ := Measure.pi (fun j => Measure.pi (fun _ : BoundedCoefficientExponent K (j.val + 1) => ν j))
  let : CompactSpace (EuclideanCoefficientLayers (K := K) U) := by
    have hc := isCompact_univ.image (euclideanCoefficientEquiv_continuous (K := K) U)
    rw [Set.image_univ, Set.range_eq_univ.mpr (euclideanCoefficientEquiv U).surjective] at hc
    exact ⟨hc⟩
  let : ∀ j, IsProbabilityMeasure
      (Measure.pi (fun _ : BoundedCoefficientExponent K (j.val + 1) => ν j)) :=
    fun j => Measure.pi.instIsProbabilityMeasure _
  let : IsProbabilityMeasure ξ := Measure.pi.instIsProbabilityMeasure _
  let : IsFiniteMeasure ξ := ⟨by simp [measure_univ]⟩
  let : ∀ j, (Measure.pi (fun _ : BoundedCoefficientExponent K (j.val + 1) => ν j)).IsAddLeftInvariant :=
    fun j => Measure.pi.isAddLeftInvariant _
  let : ξ.IsAddLeftInvariant := Measure.pi.isAddLeftInvariant _
  let : μ.IsAddHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := inferInstance
      toIsAddLeftInvariant := inferInstance
      toIsOpenPosMeasure := isOpenPosMeasure_of_addLeftInvariant_of_compact
        (μ := μ) Set.univ isCompact_univ (by simp) }
  let : ξ.IsAddHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := ⟨fun _ _ => measure_lt_top ξ _⟩
      toIsAddLeftInvariant := inferInstance
      toIsOpenPosMeasure := isOpenPosMeasure_of_addLeftInvariant_of_compact
        (μ := ξ) Set.univ isCompact_univ (by simp) }
  exact AddMonoidHom.measurePreserving
    (f := (euclideanCoefficientEquiv U).toAddMonoidHom)
    (euclideanCoefficientEquiv_continuous U) (euclideanCoefficientEquiv U).surjective (by simp)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.MixedDensityInterpolation
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

variable {I Z : Type*} [Fintype I] [Fintype Z]

theorem mixedDensityInterpolation_grid (c w : I → ℝ) (f : Z → ℝ → ℝ)
    (K : Z → ℝ) (p : Z → PMF ℤ) (hf : ∀ j (k : ℤ), f j ((k : ℝ) / K j) = K j * (p j k).toReal)
    (u : I → ℝ) (z : Z → ℤ) :
    mixedDensityInterpolation c w f (u, fun j => (z j : ℝ) / K j) =
      (∏ j, K j) * mixedCoefficientDensity c w p (u, z) := by
  simp only [mixedDensityInterpolation, mixedCoefficientDensity, hf, Finset.prod_mul_distrib]
  ring

theorem mixedDensityInterpolation_bounds (c w : I → ℝ) (f : Z → ℝ → ℝ)
    {δ B L : ℝ≥0} (hδ : 0 < δ) (hw : ∀ i, (δ : ℝ) ≤ w i) (hB : 1 ≤ B)
    (hf : ∀ j, LipschitzWith L (f j)) (hb : ∀ j x, 0 ≤ f j x ∧ f j x ≤ B) :
    (∀ x, 0 ≤ mixedDensityInterpolation c w f x ∧
      mixedDensityInterpolation c w f x ≤ (δ : ℝ)⁻¹^Fintype.card I * (B : ℝ)^Fintype.card Z) ∧
    LipschitzWith (δ⁻¹^Fintype.card I * (Fintype.card Z * L * B^Fintype.card Z) +
      B^Fintype.card Z * affineProductProfileLip I δ) (mixedDensityInterpolation c w f) := by
  have hδr : (0 : ℝ) < δ := hδ
  have hwpos : ∀ i, 0 < w i := fun i => hδr.trans_le (hw i)
  have hp (j : Z) : LipschitzWith L (fun x : (I → ℝ) × (Z → ℝ) => f j (x.2 j)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    exact ((hf j).dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left
      ((dist_le_pi_dist x.2 y.2 j).trans (le_max_right _ _)) L.coe_nonneg)
  obtain ⟨hprod, hlprod⟩ := bounded_lipschitz_real_prod
    (fun j (x : (I → ℝ) × (Z → ℝ)) => f j (x.2 j)) hB hp
    (fun j x => by rw [abs_of_nonneg (hb j _).1]; exact (hb j _).2)
  have hlcont : LipschitzWith (affineProductProfileLip I δ)
      (fun x : (I → ℝ) × (Z → ℝ) => affineProductProfile c w x.1) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    exact ((affineProductProfile_lipschitz c w hδ hw).dist_le_mul x.1 y.1).trans
      (mul_le_mul_of_nonneg_left (le_max_left _ _) (NNReal.coe_nonneg _))
  have hc (x : (I → ℝ) × (Z → ℝ)) :
      |affineProductProfile c w x.1| ≤ ((δ⁻¹^Fintype.card I : ℝ≥0) : ℝ) := by
    simpa only [Real.norm_eq_abs, NNReal.coe_pow, NNReal.coe_inv] using
      affineProductProfile_cap c w hδr hw x.1
  refine ⟨?_, lipschitz_real_mul_of_bounds _ _ hlcont hlprod hc ?_⟩
  · intro x
    have h0 : 0 ≤ ∏ j, f j (x.2 j) := Finset.prod_nonneg (fun j _ => (hb j _).1)
    refine ⟨mul_nonneg (affineProductProfile_nonneg c w hwpos x.1) h0, ?_⟩
    have ha := hc x
    have hz := hprod x
    rw [abs_of_nonneg (affineProductProfile_nonneg c w hwpos x.1)] at ha
    rw [abs_of_nonneg h0] at hz
    exact mul_le_mul ha hz h0 (by positivity)
  · intro x
    simpa only [NNReal.coe_pow] using hprod x

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MixedCoefficientSmallSupport
namespace OAI

section

namespace Erdos3

open Module Submodule
open scoped BigOperators

theorem mixedCoefficientDensity_width_cap {I Z : Type*} [Fintype I] [Fintype Z]
    (c w : I → ℝ) (hw : ∀ i, 0 < w i) (p : Z → PMF ℤ) (x : (I → ℝ) × (Z → ℤ)) :
    mixedCoefficientDensity c w p x ≤ profileWidthFactor w := by
  have hprod : (∏ z, (p z (x.2 z)).toReal) ≤ 1 := by
    apply Finset.prod_le_one (fun _ _ => ENNReal.toReal_nonneg)
    intro z _
    simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono ENNReal.one_ne_top ((p z).coe_le_one (x.2 z))
  have hf : affineProductProfile c w x.1 ≤ profileWidthFactor w :=
    (le_abs_self _).trans (affineProductProfile_norm_le c w hw x.1)
  exact (mul_le_of_le_one_right (affineProductProfile_nonneg c w hw x.1) hprod).trans hf

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ScaledArrayLaw
namespace OAI

section

namespace Erdos3

open MeasureTheory Module Submodule _root_.Set

variable {D : Type*} [Fintype D] {n : ℕ}

theorem normalizedQuotientDensity_apply (W : Submodule ℝ (EuclideanSpace ℝ D))
    (b : Basis (Fin n) ℝ Wᗮ) (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
    {Ω : Set (EuclideanSpace ℝ D)} (hΩ : Ω ⊆ standardLatticeSmallBox D)
    (f : W × (Fin n → ℤ) → ℝ) {x : W × (Fin n → ℤ)} (hx : normalizedLatticePoint W b x ∈ Ω) :
    normalizedQuotientDensity W b hb Ω f (normalizedLatticeQuotient W b hb x) =
      ZLattice.covolume (latticeSection (standardEuclideanLattice D) W) * f x :=
  restrictedChartDensity_apply _ _ _ _ (normalizedLatticeQuotient_injOn W b hb hΩ) hx

end Erdos3

end

section

namespace Erdos3

open Module Submodule _root_.Set

theorem normalizedQuotientDensity_recover {D : Type*} [Fintype D] {n : ℕ}
    (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
    (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
    {Ω : Set (EuclideanSpace ℝ D)} (hΩ : Ω ⊆ standardLatticeSmallBox D)
    (f : W × (Fin n → ℤ) → ℝ)
    {y : W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup}
    (hy : normalizedQuotientDensity W b hb Ω f y ≠ 0) :
    ∃ x, normalizedLatticePoint W b x ∈ Ω ∧ normalizedLatticeQuotient W b hb x = y ∧ f x ≠ 0 :=
  restrictedChartDensity_recover _ _ _ _ (normalizedLatticeQuotient_injOn W b hb hΩ) hy

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module Submodule _root_.Set

variable {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W) (o : OrthonormalBasis I ℝ W)

theorem canonicalMixedDensity_apply (c w : I → ℝ) (p : Fin n → PMF ℤ)
    {x : (I → ℝ) × (Fin n → ℤ)}
    (hx : normalizedLatticePoint W b (orthonormalMixedChart o x) ∈ standardLatticeSmallBox D) :
    canonicalMixedDensity W b hb o c w p (normalizedLatticeQuotient W b hb (orthonormalMixedChart o x)) =
      ZLattice.covolume (latticeSection (standardEuclideanLattice D) W) * mixedCoefficientDensity c w p x := by
  exact (normalizedQuotientDensity_apply W b hb (Subset.rfl) (orthonormalMixedDensity o c w p) hx).trans
    (by simp only [orthonormalMixedDensity, MeasurableEquiv.symm_apply_apply])

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedShortAxis
namespace OAI

section

namespace Erdos3

theorem tailAxisInterpolation_spec {V : Type*} (T : V → ℝ) (hT : ∀ v, 0 < T v)
    (K L s : ℕ) (hK : 0 < K) (hL : 0 < L) (hTL : ∀ v, T v ≤ L) (ε : ℝ) (hε : 0 < ε)
    (hεL : 8 * (probabilityProfileLipschitz : ℝ) ≤ ε * L)
    (e : V →₀ ℕ) (he : e.sum (fun _ n => n) ≤ s) :
    IsIntegerMassInterpolation K (integerAxisTailPMF T hT K L s hK hL hTL ε hε hεL e he)
      (tailAxisInterpolationCap L s ε) (tailAxisInterpolationLip L s ε)
      (tailAxisInterpolation T K L s ε e) := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hS := monomialScale_pos T hT e
  have hSL := monomialScale_le_uniform_pow T (fun v => (hT v).le)
    (show (1 : ℝ) ≤ L by exact_mod_cast hL) hTL e he
  by_cases ha : L^(s+1) < K
  · simp only [integerAxisTailPMF, tailAxisInterpolation, ha, ↓reduceDIte, ↓reduceIte]
    apply (normalizedIntegerInterpolation_spec K 0 (ε / monomialScale T e) hKr
      (div_pos hε hS) (integerAxisTail_width T hT hL hTL hε hεL e he ha)).mono
    · apply le_trans _ (le_max_left _ _)
      calc
        2 / (ε / monomialScale T e) = 2 * monomialScale T e / ε := by field_simp
        _ ≤ 2 * (L : ℝ)^s / ε := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hSL (by norm_num)) hε.le
    · apply le_trans _ (le_max_left _ _)
      calc
        2 * (probabilityProfileLipschitz : ℝ) / (ε / monomialScale T e)^2 =
            2 * (probabilityProfileLipschitz : ℝ) * (monomialScale T e)^2 / ε^2 := by field_simp
        _ ≤ 2 * (probabilityProfileLipschitz : ℝ) * ((L : ℝ)^s)^2 / ε^2 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ hS.le hSL 2) (by positivity)) (sq_nonneg ε)
  · have hbound : (K : ℝ) ≤ (L : ℝ)^(s+1) := by exact_mod_cast (Nat.le_of_not_gt ha)
    simp only [integerAxisTailPMF, tailAxisInterpolation, ha, ↓reduceDIte, ↓reduceIte]
    apply (integerMassTent_spec K hKr 0).mono
    · exact hbound.trans (le_max_right _ _)
    · exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hKr.le hbound 2) (by norm_num)).trans
        (le_max_right _ _)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PrincipalIntegerInterpolation
namespace OAI

section

namespace Erdos3

theorem principalIntegerInterpolation_grid (K T γ : ℝ) (hK : 0 < K) (hT : 0 < T)
    (hγ : 0 < γ) (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ (γ / 2) * (K / T)) (k : ℤ) :
    principalIntegerInterpolation K T γ ((k : ℝ) / K) =
      K * (principalIntegerPMF K T γ hK hT hγ hlarge k).toReal := by
  unfold principalIntegerInterpolation principalIntegerPMF
  rw [show T*((k : ℝ)/K) = (k : ℝ)/(K/T) by field_simp,
    normalizedIntegerInterpolation_grid _ _ _ (div_pos hK hT) (by positivity) hlarge]
  field_simp

theorem principalIntegerInterpolation_spec (K T γ : ℝ) (hK : 0 < K) (hT : 0 < T)
    (hγ : 0 < γ) (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ (γ / 2) * (K / T)) :
    IsIntegerMassInterpolation K (principalIntegerPMF K T γ hK hT hγ hlarge)
      (4*T/γ) (8 * (probabilityProfileLipschitz : ℝ) * T^2 / γ^2) (principalIntegerInterpolation K T γ) :=
  ⟨principalIntegerInterpolation_grid K T γ hK hT hγ hlarge,
    principalIntegerInterpolation_range K T γ hK hT hγ hlarge,
    principalIntegerInterpolation_difference K T γ hK hT hγ hlarge⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PrincipalAxisInterpolation
namespace OAI

section

namespace Erdos3

theorem principalAxisInterpolation_spec (h K L : ℕ) (hh : 0 < h) (hK : 0 < K) (hL : 0 < L)
    (γ : ℝ) (hγ : 0 < γ)
    (hgap : L^h < K → (principalSamplingGapRatio γ * L)^h ≤ K) :
    IsIntegerMassInterpolation K (integerAxisPrincipalPMF h K L hh hK hL γ hγ hgap)
      (principalAxisInterpolationCap h L γ) (principalAxisInterpolationLip h L γ)
      (principalAxisInterpolation h K L γ) := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  by_cases ha : L^h < K
  · simp only [integerAxisPrincipalPMF, principalAxisInterpolation, ha, ↓reduceDIte, ↓reduceIte]
    exact (principalIntegerInterpolation_spec K ((L : ℝ)^h) γ hKr
      (pow_pos (by exact_mod_cast hL) _) hγ (integerAxisPrincipal_width hh hL hγ (hgap ha))).mono
      (le_max_left _ _) (le_max_left _ _)
  · have hbound : (K : ℝ) ≤ (L : ℝ)^h := by exact_mod_cast (Nat.le_of_not_gt ha)
    simp only [integerAxisPrincipalPMF, principalAxisInterpolation, ha, ↓reduceDIte, ↓reduceIte,
      inactivePrincipalPMF]
    apply (integerMassTent_spec K hKr (inactivePrincipalCoefficient K (inactiveDenominator γ))).mono
    · exact hbound.trans (le_max_right _ _)
    · exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hKr.le hbound 2) (by norm_num)).trans
        (le_max_right _ _)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.IntegerPolynomialInterpolation
namespace OAI

section

namespace Erdos3

variable {J V : Type*} [Fintype J]

omit [Fintype J] in
theorem integerPolynomialInterpolation_spec (P : Finset J) (j₀ : J) (h K L s : ℕ)
    (hh : 0 < h) (hK : 0 < K) (hL : 0 < L)
    (T : V → ℝ) (hT : ∀ v, 0 < T v) (hTL : ∀ v, T v ≤ L)
    (e : J → V →₀ ℕ) (he : ∀ j, (e j).sum (fun _ n => n) ≤ s)
    (ρ γ ε : ℝ) (hρ : 0 < ρ) (hγ : 0 < γ) (hε : 0 < ε)
    (hgap : L^h < K → (principalSamplingGapRatio γ * L)^h ≤ K)
    (hεL : 8 * (probabilityProfileLipschitz : ℝ) ≤ ε * L) (j : J) :
    IsIntegerMassInterpolation K
      (integerPolynomialCoordinatePMF P j₀ h K L s hh hK hL T hT hTL e he
        ρ γ ε hρ hγ hε hgap hεL j)
      (integerPolynomialInterpolationCap h L s ρ γ ε)
      (integerPolynomialInterpolationLip h L s ρ γ ε)
      (integerPolynomialInterpolation P j₀ h K L s T e ρ γ ε j) := by
  classical
  by_cases hj : j = j₀
  · simp only [integerPolynomialCoordinatePMF, integerPolynomialInterpolation, hj, ↓reduceIte]
    exact (constantIntegerInterpolation_spec K ρ (by exact_mod_cast hK) hρ).mono
      (le_max_left _ _) (le_max_left _ _)
  · by_cases hp : j ∈ P
    · simp only [integerPolynomialCoordinatePMF, integerPolynomialInterpolation, hj, hp, ↓reduceIte]
      exact (principalAxisInterpolation_spec h K L hh hK hL γ hγ hgap).mono
        ((le_max_left _ _).trans (le_max_right _ _)) ((le_max_left _ _).trans (le_max_right _ _))
    · simp only [integerPolynomialCoordinatePMF, integerPolynomialInterpolation, hj, hp, ↓reduceIte]
      exact (tailAxisInterpolation_spec T hT K L s hK hL hTL ε hε hεL (e j) (he j)).mono
        ((le_max_right _ _).trans (le_max_right _ _)) ((le_max_right _ _).trans (le_max_right _ _))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedScalarLogBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

theorem allocatedLayerIntegerInterpolation_spec (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (j : Fin m) (i : Fin (n j)) (d) :
    IsIntegerMassInterpolation (basisAxisScale (b j) i) (allocatedLayerIntegerPMFs B U b hR hσ S j i d)
      (allocatedLayerIntegerInterpolationCap (G := G) B R σ S.value j i)
      (allocatedLayerIntegerInterpolationLip (G := G) B R σ S.value j i)
      (allocatedLayerIntegerInterpolation B U b S j i d) := by
  exact integerPolynomialInterpolation_spec (layerIntegerPrincipalSlots (G := G) B j i) (constantCoefficientSlot _ _)
    (j.val+1) (basisAxisScale (b j) i) S.value (layerTailDegree m) (Nat.zero_lt_succ _) (basisAxisScale_pos (b j) i)
    S.positive (layerSamplerBox B U b S)
    (fun v => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U b S v)) (layerSamplerBox_le B U b S)
    Subtype.val (fun d => d.property.trans (layerDegree_le_tailDegree j)) (R j / 4)
    (principalProfileSize (R j) (layerIntegerPrincipalSlots (G := G) B j i).card)
    (tailProfileSize (R j) (σ j)
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1))))
    (div_pos (hR j) (by norm_num)) (principalProfileSize_pos (hR j) _) (tailProfileSize_pos (hR j) (hσ j) _)
    (S.gap j i) (S.width j) d

theorem allocatedLayerIntegerInterpolation_lipschitz (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (j : Fin m) (i : Fin (n j)) (d) :
    LipschitzWith (Real.toNNReal (allocatedLayerIntegerInterpolationLip (G := G) B R σ S.value j i))
      (allocatedLayerIntegerInterpolation B U b S j i d) := by
  apply (allocatedLayerIntegerInterpolation_spec B U b S hR hσ j i d).lipschitz
  unfold allocatedLayerIntegerInterpolationLip integerPolynomialInterpolationLip
    constantIntegerInterpolationLip principalAxisInterpolationLip tailAxisInterpolationLip
  positivity

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

theorem allocatedLayerWidthFloor_pos {R σ : Fin m → ℝ}
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) {L : ℕ} (hL : 0 < L) (j : Fin m) :
    0 < allocatedLayerWidthFloor (G := G) B R σ L j := by
  apply Real.toNNReal_pos.mpr
  exact allocatedWidthFloor_pos (hR j) (hσ j) hL _ _

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

theorem allocatedLayerWidths_floor (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (j : Fin m) (i : I j) (d) :
    (allocatedLayerWidthFloor (G := G) B R σ S.value j : ℝ) ≤ allocatedLayerWidths B U b S j i d := by
  rw [allocatedLayerWidthFloor, Real.coe_toNNReal _ (allocatedWidthFloor_pos (hR j) (hσ j) S.positive _ _).le]
  exact allocatedArrayWidths_floor Subtype.val (layerSamplerBox B U b S)
    (fun v => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U b S v))
    (layerContinuousPrincipalSlots B j) (constantCoefficientSlot _ _) (hR j) (hσ j) S.positive
    (layerSamplerBox_le B U b S) (fun d => d.property) i d

theorem allocatedLayerInterpolation_common_bounds (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (j : Fin m) (i : Fin (n j)) (d) :
    (∀ x, 0 ≤ allocatedLayerIntegerInterpolation B U b S j i d x ∧
      allocatedLayerIntegerInterpolation B U b S j i d x ≤ allocatedLayerCommonCap (G := G) B R σ S.value j) ∧
    LipschitzWith (allocatedLayerCommonLip (G := G) B R σ S.value j)
      (allocatedLayerIntegerInterpolation B U b S j i d) := by
  have hspec := allocatedLayerIntegerInterpolation_spec B U b S hR hσ j i d
  have hcap : Real.toNNReal (allocatedLayerIntegerInterpolationCap (G := G) B R σ S.value j i) ≤
      allocatedLayerCommonCap (G := G) B R σ S.value j := by
    apply le_trans (Finset.single_le_sum
      (f := fun t : Fin (n j) => Real.toNNReal (allocatedLayerIntegerInterpolationCap (G := G) B R σ S.value j t))
      (fun _ _ => zero_le) (Finset.mem_univ i))
    exact le_add_of_nonneg_left (by norm_num)
  have hlip : Real.toNNReal (allocatedLayerIntegerInterpolationLip (G := G) B R σ S.value j i) ≤
      allocatedLayerCommonLip (G := G) B R σ S.value j := by
    unfold allocatedLayerCommonLip
    exact Finset.single_le_sum
      (f := fun t : Fin (n j) => Real.toNNReal (allocatedLayerIntegerInterpolationLip (G := G) B R σ S.value j t))
      (fun _ _ => zero_le) (Finset.mem_univ i)
  refine ⟨?_, (allocatedLayerIntegerInterpolation_lipschitz B U b S hR hσ j i d).weaken hlip⟩
  intro x
  exact ⟨(hspec.2.1 x).1, (hspec.2.1 x).2.trans ((Real.le_coe_toNNReal _).trans (by exact_mod_cast hcap))⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped BigOperators NNReal

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

theorem allocatedLayerWidthFloor_inv_exp (R σ : Fin m → ℝ) (L : ℕ) (hL : 0 < L) (j : Fin m)
    {P : ℝ} (hP : 0 ≤ P) (hR : 0 < R j) (hσ : 0 < σ j)
    (hRP : (R j)⁻¹ ≤ Real.exp P) (hσP : (σ j)⁻¹ ≤ Real.exp P)
    (hcount : (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ) ≤ P)
    (hLP : (L : ℝ) ≤ Real.exp P) :
    (((allocatedLayerWidthFloor (G := G) B R σ L j)⁻¹ : ℝ≥0) : ℝ) ≤ Real.exp (allocatedWidthLog m P) := by
  rw [NNReal.coe_inv, allocatedLayerWidthFloor,
    Real.coe_toNNReal _ (allocatedWidthFloor_pos hR hσ hL _ _).le]
  exact allocatedWidthFloor_inverse_exp_bound L (j.val+1) m _ (Nat.succ_le_of_lt j.isLt)
    hP hR hσ hRP hσP hcount hLP

end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedRealPoint
namespace OAI

section

namespace Erdos3

open Module Submodule

variable {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (o : OrthonormalBasis I ℝ W)

theorem mixedRealPoint_integer (u : I → ℝ) (z : Fin n → ℤ) :
    mixedRealPoint W b o (u, fun i => (z i : ℝ) / basisAxisScale b i) =
      normalizedLatticePoint W b (orthonormalMixedChart o (u, z)) := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MixedRealCoordinates
namespace OAI

section

namespace Erdos3

open Module Submodule
open scoped NNReal

variable {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (o : OrthonormalBasis I ℝ W)

theorem mixedRealCoordinates_norm_le (x : EuclideanSpace ℝ D) :
    ‖mixedRealCoordinates W b o x‖ ≤ ‖normalizedOrthogonalChart W b x‖ := by
  change ‖((orthonormalChart o).symm ((normalizedOrthogonalChart W b) x).1,
    ((normalizedOrthogonalChart W b) x).2)‖ ≤ _
  rw [Prod.norm_def, Prod.norm_def]
  exact max_le_max (orthonormalChart_symm_norm_le o _) le_rfl

theorem mixedRealCoordinates_lipschitz {C : ℝ≥0}
    (hC : ∀ x, ‖normalizedOrthogonalChart W b x‖ ≤ C * ‖x‖) :
    LipschitzWith C (mixedRealCoordinates W b o) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, ← map_sub, dist_eq_norm]
  exact (mixedRealCoordinates_norm_le W b o _).trans (hC _)

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

theorem mixedAmbientInterpolation_bounds (c w : I → ℝ) (f : Fin n → ℝ → ℝ)
    {M J C V : ℝ≥0}
    (hM : ∀ x, 0 ≤ mixedDensityInterpolation c w f x ∧ mixedDensityInterpolation c w f x ≤ M)
    (hJ : LipschitzWith J (mixedDensityInterpolation c w f))
    (hC : ∀ x, ‖normalizedOrthogonalChart W b x‖ ≤ C * ‖x‖)
    (hV : 0 ≤ mixedDensityCovolumeRatio W b ∧ mixedDensityCovolumeRatio W b ≤ V) :
    (∀ x, 0 ≤ mixedAmbientInterpolation W b o c w f x ∧
      mixedAmbientInterpolation W b o c w f x ≤ V * M) ∧
    LipschitzWith (V * (J * (C * Fintype.card D))) (mixedAmbientInterpolation W b o c w f) := by
  have hg := hJ.comp ((mixedRealCoordinates_lipschitz W b o hC).comp
    (euclideanFromCoordinates_lipschitz (D := D)))
  have hl := lipschitz_real_mul_of_bounds (Bf := V) (Bg := M)
    (fun _ : D → ℝ => mixedDensityCovolumeRatio W b)
    (fun x => mixedDensityInterpolation c w f
      (mixedRealCoordinates W b o ((EuclideanSpace.equiv D ℝ).symm x)))
    (LipschitzWith.const _) hg
    (fun _ => by rw [abs_of_nonneg hV.1]; exact hV.2)
    (fun x => by rw [abs_of_nonneg (hM _).1]; exact (hM _).2)
  refine ⟨?_, ?_⟩
  · intro x
    exact ⟨mul_nonneg hV.1 (hM _).1, mul_le_mul hV.2 (hM _).2 (hM _).1 V.coe_nonneg⟩
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [mixedAmbientInterpolation, mul_zero, add_zero] using hl.dist_le_mul x y

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NormalizedChartLift
namespace OAI

section

namespace Erdos3

open Module Submodule

variable {D : Type*} [Fintype D] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)

theorem normalizedLatticeQuotient_eq_of_sub_mem (u : W) (x : W × (Fin n → ℤ))
    (hx : u.val - normalizedLatticePoint W b x ∈ standardEuclideanLattice D) :
    QuotientAddGroup.mk' (latticeSection (standardEuclideanLattice D) W).toAddSubgroup u =
      normalizedLatticeQuotient W b hb x := by
  let z := latticeBasisEquiv (projectedIntegerLattice W) b hb x.2
  let v : W := x.1 - projectedLatticeShift (standardEuclideanLattice D) W z
  have hv : QuotientAddGroup.mk'
      (latticeSection (standardEuclideanLattice D) W).toAddSubgroup v =
        normalizedLatticeQuotient W b hb x := rfl
  have hdiff := normalizedLatticePoint_sub_mem_of_mk_eq W b hb v x hv
  have hm : (u - v).val ∈ standardEuclideanLattice D := by
    convert (standardEuclideanLattice D).sub_mem hx hdiff using 1
    simp only [Submodule.coe_sub]
    abel
  exact (QuotientAddGroup.eq_iff_sub_mem.mpr hm).trans hv

theorem exists_normalized_chart_lift (u : W) (v : EuclideanSpace ℝ D)
    (hv : u.val - v ∈ standardEuclideanLattice D) :
    ∃ x : W × (Fin n → ℤ), normalizedLatticePoint W b x = v ∧
      normalizedLatticeQuotient W b hb x =
        QuotientAddGroup.mk' (latticeSection (standardEuclideanLattice D) W).toAddSubgroup u := by
  have hproj : Wᗮ.orthogonalProjectionOnto v ∈ span ℤ (Set.range b) := by
    rw [hb]
    apply (projectedIntegerLattice W).neg_mem_iff.mp
    change -(Wᗮ.orthogonalProjectionOnto v) ∈
      (standardEuclideanLattice D).map (Wᗮ.orthogonalProjectionOnto.toLinearMap.restrictScalars ℤ)
    refine ⟨u.val - v, hv, ?_⟩
    change Wᗮ.orthogonalProjectionOnto (u.val - v) = -Wᗮ.orthogonalProjectionOnto v
    rw [map_sub, Wᗮ.orthogonalProjectionOnto_eq_zero_iff.mpr (by simp), zero_sub]
  obtain ⟨z, hz⟩ := normalizedOrthogonalChart_integer_coordinates W b v hproj
  let x : W × (Fin n → ℤ) := ((normalizedOrthogonalChart W b v).1, z)
  have hx : normalizedLatticePoint W b x = v := by
    apply (normalizedOrthogonalChart W b).injective
    change (normalizedOrthogonalChart W b) ((normalizedOrthogonalChart W b).symm
      ((normalizedOrthogonalChart W b v).1, fun i => (z i : ℝ) / basisAxisScale b i)) = _
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact Prod.ext rfl (funext (fun i => (hz i).symm))
  refine ⟨x, hx, (normalizedLatticeQuotient_eq_of_sub_mem W b hb u x ?_).symm⟩
  rwa [hx]

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

theorem canonicalAmbientKernel_support (c w : I → ℝ) (f : Fin n → ℝ → ℝ)
    (v : D → ℝ) (hv : canonicalAmbientKernel W b o c w f v ≠ 0) :
    ∀ i, |v i| < 1/2 :=
  smallBoxCutoff_support v (left_ne_zero_of_mul hv)

theorem canonicalAmbientKernel_bounds (c w : I → ℝ) (f : Fin n → ℝ → ℝ)
    {M J C V : ℝ≥0}
    (hM : ∀ x, 0 ≤ mixedDensityInterpolation c w f x ∧ mixedDensityInterpolation c w f x ≤ M)
    (hJ : LipschitzWith J (mixedDensityInterpolation c w f))
    (hC : ∀ x, ‖normalizedOrthogonalChart W b x‖ ≤ C * ‖x‖)
    (hV : 0 ≤ mixedDensityCovolumeRatio W b ∧ mixedDensityCovolumeRatio W b ≤ V) :
    (∀ x, 0 ≤ canonicalAmbientKernel W b o c w f x ∧
      canonicalAmbientKernel W b o c w f x ≤ V * M) ∧
    LipschitzWith (V * (J * (C * Fintype.card D)) + (V * M) * 8)
      (canonicalAmbientKernel W b o c w f) := by
  obtain ⟨hcap, hlip⟩ := mixedAmbientInterpolation_bounds W b o c w f hM hJ hC hV
  refine ⟨?_, smallBoxCutoff_mul_lipschitz _ hlip ?_⟩
  · intro x
    refine ⟨mul_nonneg (smallBoxCutoff_range x).1 (hcap x).1, ?_⟩
    exact (mul_le_mul_of_nonneg_right (smallBoxCutoff_range x).2 (hcap x).1).trans
      (by simpa only [one_mul] using (hcap x).2)
  · intro x
    rw [abs_of_nonneg (hcap x).1]
    exact (hcap x).2

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

theorem coordinate_integer_translate_sub_mem (u : EuclideanSpace ℝ D) (z : D → ℤ) :
    u - (EuclideanSpace.equiv D ℝ).symm (fun i => u i + (z i : ℝ)) ∈
      standardEuclideanLattice D := by
  apply (mem_standardEuclideanLattice D _).mpr
  intro i
  refine ⟨-z i, ?_⟩
  change ((-z i : ℤ) : ℝ) = u i - (u i + (z i : ℝ))
  push_cast
  ring

variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W) (o : OrthonormalBasis I ℝ W)

noncomputable def canonicalAmbientTorusDensity (c w : I → ℝ) (f : Fin n → ℝ → ℝ) :
    (D → UnitAddCircle) → ℝ :=
  smallBoxTorusKernel (canonicalAmbientKernel W b o c w f)

theorem canonicalAmbientTorusDensity_bounds (c w : I → ℝ) (f : Fin n → ℝ → ℝ)
    {M J C V : ℝ≥0}
    (hM : ∀ x, 0 ≤ mixedDensityInterpolation c w f x ∧ mixedDensityInterpolation c w f x ≤ M)
    (hJ : LipschitzWith J (mixedDensityInterpolation c w f))
    (hC : ∀ x, ‖normalizedOrthogonalChart W b x‖ ≤ C * ‖x‖)
    (hV : 0 ≤ mixedDensityCovolumeRatio W b ∧ mixedDensityCovolumeRatio W b ≤ V) :
    (∀ x, 0 ≤ canonicalAmbientTorusDensity W b o c w f x ∧
      canonicalAmbientTorusDensity W b o c w f x ≤ V * M) ∧
    LipschitzWith (V * (J * (C * Fintype.card D)) + (V * M) * 8)
      (canonicalAmbientTorusDensity W b o c w f) := by
  obtain ⟨hcap, hlip⟩ := canonicalAmbientKernel_bounds W b o c w f hM hJ hC hV
  exact ⟨smallBoxTorusKernel_range _ (mul_nonneg V.coe_nonneg M.coe_nonneg) hcap
      (canonicalAmbientKernel_support W b o c w f),
    smallBoxTorusKernel_lipschitz _ hlip (fun x => (hcap x).1)
      (canonicalAmbientKernel_support W b o c w f)⟩

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

noncomputable def coefficientAmbientFactor (s : CoefficientSlot K m) :
    (J s.1 → UnitAddCircle) → ℝ :=
  canonicalAmbientTorusDensity (euclideanSubspace (U s.1)) (b s.1) (o s.1)
    (fun i => c s.1 i s.2) (fun i => w s.1 i s.2) (fun i => f s.1 i s.2)

noncomputable def coefficientAmbientDensity (v : CoefficientAmbientIndex K J → UnitAddCircle) : ℝ :=
  ∏ s : CoefficientSlot K m,
    coefficientAmbientFactor U b o c w f s (coefficientAmbientSlice s v)

variable (p : ∀ j : Fin m, Fin (n j) → BoundedCoefficientExponent K (j.val + 1) → PMF ℤ)
variable (hf : ∀ j i d (k : ℤ), f j i d ((k : ℝ) / basisAxisScale (b j) i) =
  basisAxisScale (b j) i * (p j i d k).toReal)
variable (hs : ∀ j d x, mixedCoefficientDensity (fun i => c j i d) (fun i => w j i d)
  (fun i => p j i d) x ≠ 0 → ∀ a,
    |normalizedLatticePoint (euclideanSubspace (U j)) (b j) (orthonormalMixedChart (o j) x) a| ≤ 1/4)

theorem coefficientAmbientDensity_bounds {B L : ℝ≥0} (hB : 1 ≤ B)
    (hcap : ∀ s x, 0 ≤ coefficientAmbientFactor U b o c w f s x ∧
      coefficientAmbientFactor U b o c w f s x ≤ B)
    (hlip : ∀ s, LipschitzWith L (coefficientAmbientFactor U b o c w f s)) :
    (∀ x, 0 ≤ coefficientAmbientDensity U b o c w f x ∧
      coefficientAmbientDensity U b o c w f x ≤ (B : ℝ)^Fintype.card (CoefficientSlot K m)) ∧
    LipschitzWith (Fintype.card (CoefficientSlot K m) * L * B^Fintype.card (CoefficientSlot K m))
      (coefficientAmbientDensity U b o c w f) := by
  have hl (s : CoefficientSlot K m) : LipschitzWith L
      (fun x => coefficientAmbientFactor U b o c w f s (coefficientAmbientSlice s x)) := by
    simpa only [mul_one, Function.comp_def] using (hlip s).comp (coefficientAmbientSlice_lipschitz (J := J) s)
  obtain ⟨hbnd, hlprod⟩ := bounded_lipschitz_real_prod
    (fun s x => coefficientAmbientFactor U b o c w f s (coefficientAmbientSlice s x)) hB hl
    (fun s x => by rw [abs_of_nonneg (hcap s _).1]; exact (hcap s _).2)
  refine ⟨?_, hlprod⟩
  intro x
  have h0 : 0 ≤ coefficientAmbientDensity U b o c w f x :=
    Finset.prod_nonneg (fun s _ => (hcap s _).1)
  exact ⟨h0, (le_abs_self _).trans (hbnd x)⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedAmbientLogBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

theorem allocatedAmbientFactorCap_one_le (R σ : Fin m → ℝ) (L : ℕ) (V : Fin m → ℝ≥0) :
    1 ≤ allocatedAmbientFactorCap (G := G) B R σ L V := le_add_of_nonneg_right (by positivity)

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

theorem allocatedLayerMixedInterpolation_bounds (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (j : Fin m) (d) :
    (∀ x, 0 ≤ mixedDensityInterpolation (fun i => allocatedLayerCenters B U b S j i d)
        (fun i => allocatedLayerWidths B U b S j i d) (fun i => allocatedLayerIntegerInterpolation B U b S j i d) x ∧
      mixedDensityInterpolation (fun i => allocatedLayerCenters B U b S j i d)
        (fun i => allocatedLayerWidths B U b S j i d) (fun i => allocatedLayerIntegerInterpolation B U b S j i d) x ≤
          allocatedLayerMixedCap (G := G) B R σ S.value j) ∧
    LipschitzWith (allocatedLayerMixedLip (G := G) B R σ S.value j)
      (mixedDensityInterpolation (fun i => allocatedLayerCenters B U b S j i d)
        (fun i => allocatedLayerWidths B U b S j i d) (fun i => allocatedLayerIntegerInterpolation B U b S j i d)) := by
  have h := mixedDensityInterpolation_bounds
    (fun i => allocatedLayerCenters B U b S j i d) (fun i => allocatedLayerWidths B U b S j i d)
    (fun i => allocatedLayerIntegerInterpolation B U b S j i d)
    (allocatedLayerWidthFloor_pos (G := G) B hR hσ S.positive j)
    (fun i => allocatedLayerWidths_floor B U b S hR hσ j i d)
    (allocatedLayerCommonCap_one_le (G := G) B R σ S.value j)
    (fun i => (allocatedLayerInterpolation_common_bounds B U b S hR hσ j i d).2)
    (fun i x => (allocatedLayerInterpolation_common_bounds B U b S hR hσ j i d).1 x)
  simpa only [allocatedLayerMixedCap, allocatedLayerMixedLip, NNReal.coe_mul, NNReal.coe_pow,
    NNReal.coe_inv, Fintype.card_fin] using h

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)

include hC hV in
theorem allocatedAmbientFactor_bounds (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (s : CoefficientSlot (LayerSamplerVariables G I n B) m) :
    (∀ x, 0 ≤ coefficientAmbientFactor U b o (allocatedLayerCenters B U b S) (allocatedLayerWidths B U b S)
        (allocatedLayerIntegerInterpolation B U b S) s x ∧
      coefficientAmbientFactor U b o (allocatedLayerCenters B U b S) (allocatedLayerWidths B U b S)
        (allocatedLayerIntegerInterpolation B U b S) s x ≤
          allocatedAmbientFactorCap (G := G) B R σ S.value V) ∧
    LipschitzWith (allocatedAmbientFactorLip (G := G) B R σ S.value (fun j => Fintype.card (J j)) C V)
      (coefficientAmbientFactor U b o (allocatedLayerCenters B U b S) (allocatedLayerWidths B U b S)
        (allocatedLayerIntegerInterpolation B U b S) s) := by
  obtain ⟨hcap, hlip⟩ := allocatedLayerMixedInterpolation_bounds B U b S hR hσ s.1 s.2
  obtain ⟨ha, hl⟩ := canonicalAmbientTorusDensity_bounds (euclideanSubspace (U s.1)) (b s.1) (o s.1)
    _ _ _ hcap hlip (hC s.1) (hV s.1)
  have hcaple : V s.1 * allocatedLayerMixedCap (G := G) B R σ S.value s.1 ≤
      allocatedAmbientFactorCap (G := G) B R σ S.value V := by
    apply le_trans (Finset.single_le_sum
      (f := fun j => V j * allocatedLayerMixedCap (G := G) B R σ S.value j)
      (fun _ _ => zero_le) (Finset.mem_univ s.1))
    exact le_add_of_nonneg_left (by norm_num)
  have hliple : allocatedAmbientLayerLip (G := G) B R σ S.value (fun j => Fintype.card (J j)) C V s.1 ≤
      allocatedAmbientFactorLip (G := G) B R σ S.value (fun j => Fintype.card (J j)) C V := by
    unfold allocatedAmbientFactorLip
    exact Finset.single_le_sum
      (f := fun j => allocatedAmbientLayerLip (G := G) B R σ S.value (fun j => Fintype.card (J j)) C V j)
      (fun _ _ => zero_le) (Finset.mem_univ s.1)
  refine ⟨fun x => ⟨(ha x).1, (ha x).2.trans ?_⟩, hl.weaken hliple⟩
  exact_mod_cast hcaple

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

namespace VectorPolynomial

open scoped NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

theorem allocatedLayerMixed_exp_bounds (R σ : Fin m → ℝ) (L : ℕ) (hL : 0 < L) (j : Fin m)
    {P : ℝ} (hP : 0 ≤ P) (hR : 0 < R j) (hσ : 0 < σ j)
    (hRP : (R j)⁻¹ ≤ Real.exp P) (hσP : (σ j)⁻¹ ≤ Real.exp P)
    (hcount : (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ) ≤ P)
    (hI : (Fintype.card (I j) : ℝ) ≤ P) (hn : (n j : ℝ) ≤ P)
    (hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) (hLP : (L : ℝ) ≤ Real.exp P) :
    (allocatedLayerMixedCap (G := G) B R σ L j : ℝ) ≤ Real.exp (allocatedMixedLog m P) ∧
      (allocatedLayerMixedLip (G := G) B R σ L j : ℝ) ≤ Real.exp (allocatedMixedLog m P) := by
  obtain ⟨hc, hl⟩ := allocatedLayerCommonInterpolation_exp_bounds B R σ L j
    hP hR hσ hRP hσP hcount hn hAP hLP
  have hw := allocatedLayerWidthFloor_inv_exp B R σ L hL j hP hR hσ hRP hσP hcount hLP
  have h := mixedInterpolation_constants_exp_bounds (I := I j) (n j)
    hP (allocatedWidthLog_nonneg m hP) (allocatedCommonLog_nonneg m hP) hI hn hw hc hl hAP
  refine ⟨h.1.trans (Real.exp_le_exp.mpr ?_), h.2⟩
  have hw0 := allocatedWidthLog_nonneg m hP
  have hc0 := allocatedCommonLog_nonneg m hP
  have hp := mul_nonneg hP (add_nonneg hw0 hc0)
  unfold allocatedMixedLog
  nlinarith

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

theorem allocatedAmbientConstants_exp_bounds (R σ : Fin m → ℝ) (L : ℕ) (hL : 0 < L)
    (d : Fin m → ℕ) (C V : Fin m → ℝ≥0) {P : ℝ} (hP : 0 ≤ P) (hm : (m : ℝ) ≤ P)
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ) ≤ P)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (hn : ∀ j, (n j : ℝ) ≤ P)
    (hd : ∀ j, (d j : ℝ) ≤ P) (hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (hLP : (L : ℝ) ≤ Real.exp P) (hCP : ∀ j, (C j : ℝ) ≤ Real.exp P)
    (hVP : ∀ j, (V j : ℝ) ≤ Real.exp P) :
    (allocatedAmbientFactorCap (G := G) B R σ L V : ℝ) ≤ Real.exp (allocatedAmbientLog m P) ∧
      (allocatedAmbientFactorLip (G := G) B R σ L d C V : ℝ) ≤ Real.exp (allocatedAmbientLog m P) := by
  have hmix (j : Fin m) := allocatedLayerMixed_exp_bounds (G := G) B R σ L hL j hP (hR j) (hσ j)
    (hRP j) (hσP j) (hcount j) (hI j) (hn j) hAP hLP
  have hlocal (j : Fin m) := ambientInterpolation_constants_exp_bounds (d j) hP
    (allocatedMixedLog_nonneg m hP) (hd j) (hmix j).1 (hmix j).2 (hCP j) (hVP j)
  have hcard : (Fintype.card (Fin m) : ℝ) ≤ P := by simpa only [Fintype.card_fin] using hm
  have hQ := allocatedMixedLog_nonneg m hP
  have hcap := sum_le_exp_of_card_and_uniform_bound
    (fun j => ((V j * allocatedLayerMixedCap (G := G) B R σ L j : ℝ≥0) : ℝ))
    (by positivity : 0 ≤ allocatedMixedLog m P+P) hcard (fun j => (hlocal j).1)
  have hlip := sum_le_exp_of_card_and_uniform_bound
    (fun j => (allocatedAmbientLayerLip (G := G) B R σ L d C V j : ℝ))
    (by positivity : 0 ≤ 2*allocatedMixedLog m P+4*P+9) hcard (fun j => (hlocal j).2)
  constructor
  · simp only [allocatedAmbientFactorCap, NNReal.coe_add, NNReal.coe_one, NNReal.coe_sum]
    apply (one_add_le_exp_succ (by positivity) hcap).trans
    apply Real.exp_le_exp.mpr
    unfold allocatedAmbientLog
    nlinarith
  · simp only [allocatedAmbientFactorLip, NNReal.coe_sum]
    exact hlip.trans (Real.exp_le_exp.mpr (by unfold allocatedAmbientLog; linarith))

end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.AllocatedMaskedCoefficientFourier
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped NNReal

theorem coefficientAmbientBudgetExponent_bound (m : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    (m : ℝ) * (m+1) * (P+1)^m * (P+1) + P + 1 ≤
      (P + coefficientAmbientBudgetExponent m)^coefficientAmbientBudgetExponent m := by
  simpa [coefficientAmbientInputPolynomial, coefficientAmbientBudgetExponent, Polynomial.eval₂_pow]
    using (exists_natPolynomial_eval_budget (coefficientAmbientInputPolynomial m)).choose_spec.2 P hP

theorem allocatedFourierLogBudget_nonneg (m : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ allocatedFourierLogBudget m P := by
  have h := allocatedAmbientLog_nonneg m hP
  unfold allocatedFourierLogBudget
  positivity

end Erdos3.VectorPolynomial

end

end OAI
end


