-- Prove2me | Definitions.Def_OAIE3v2B139
-- name    : OAIE3v2B139
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T11:14:40.744816+00:00
-- url     : https://prove2.me/theorems/fcbf19ab-7f84-46e5-b0e7-f7d2e97a1258
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 141 of 311
-- statement:
--   Definitions bundle 141 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B114`, `OAIE3v2B115`, `OAIE3v2B116`, `OAIE3v2B117`, `OAIE3v2B124`, `OAIE3v2B125`, `OAIE3v2B126` of this split.
--
--   Modules: `Dynamics/AllocatedIdealCoverRadiusBudget.lean`, `Estimates/AllocatedFiberCap.lean`, `Estimates/AllocatedPhysicalLongIdealCap.lean`, `Estimates/AllocatedPhysicalLongImage.lean`, `Estimates/AllocatedSlicedEndpointIdentity.lean`, `Estimates/CenteredFiniteNoiseEventBound.lean`, `Estimates/CenteredFiniteSliceResidualEnvelope.lean`, `Estimates/CoefficientDeckImageCongruence.lean`, `Estimates/CoefficientJetScalar.lean`, `Estimates/MeasurableConstantCenterRepresentative.lean`, `Estimates/ShiftedSmoothSelectedMarginal.lean`, `Estimates/UnconditionedSmoothSlopeCap.lean`, `Fourier/CoefficientFourierTranslation.lean`, `Geometry/CenteredCoefficientDeckChartMeasurable.lean`, `Geometry/CenteredFiniteEventSupport.lean`, `Geometry/SampledCommonBox.lean`, `Lattices/IntegerRowInterpolationMixture.lean`, `Lattices/ResidueSliceUpperFailure.lean`, `Lattices/SelectedResidueApproximation.lean`, `Lattices/StrideSelectedResidueBadProduct.lean`, `Linear/CountingKernelOuter.lean`, `Linear/ProductANOVAEnergyOrder.lean`, `Linear/ProductANOVASectionNormalizedBound.lean`, `Linear/ProductANOVATensorChoices.lean`, `Linear/SmoothMatrixBlockBudget.lean`, `Linear/SpatialMatrixBlockWideProbability.lean`, `Polynomial/ShiftedSmoothPolynomialSublevel.lean`, `Polynomial/SlicedProfilePolynomial.lean`, `Probability/AllocatedFrozenJetDensity.lean`, `Probability/AllocatedLongJetMixture.lean`, `Probability/JointProductiveMeasure.lean`, `Probability/ShiftedProductCoordinateLaw.lean`, `Probability/WeightedCoefficientDensityApproximation.lean`, `Sampling/ShiftedSmoothFiniteGridLaw.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B114
import Definitions.Def_OAIE3v2B115
import Definitions.Def_OAIE3v2B116
import Definitions.Def_OAIE3v2B117
import Definitions.Def_OAIE3v2B124
import Definitions.Def_OAIE3v2B125
import Definitions.Def_OAIE3v2B126

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ShiftedSmoothSelectedMarginal
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem shiftedSmoothProductMass_restrict_pos {A J : Type*} [Fintype A] [Fintype J]
    (e : A → J) (a S : J → ℝ) (hS : ∀ j, 0 < S j)
    (hZ : 0 < shiftedSmoothProductMass a S) :
    0 < shiftedSmoothProductMass (fun i => a (e i)) (fun i => S (e i)) := by
  rw [shiftedSmoothProductMass_eq_prod _ _ (fun i => hS (e i))]
  exact Finset.prod_pos (fun i _ => shiftedSmoothProductMass_coordinate_pos a S hS hZ (e i))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem shiftedSmoothProductPMF_selected_marginal
    {A J : Type*} [Fintype A] [Fintype J]
    (e : A ↪ J) (a S : J → ℝ) (hS : ∀ j, 0 < S j)
    (hZ : 0 < shiftedSmoothProductMass a S) :
    (shiftedSmoothProductPMF a S hS hZ).map (fun z i => z (e i)) =
      shiftedSmoothProductPMF (fun i => a (e i)) (fun i => S (e i))
        (fun i => hS (e i)) (shiftedSmoothProductMass_restrict_pos e a S hS hZ) := by
  simp only [shiftedSmoothProductPMF_eq_independent]
  exact independentProductPMF_marginal _ e e.injective

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ShiftedProductCoordinateLaw
namespace OAI


namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem shiftedSmoothProductMass_slice_pos {K X : Type*} [Fintype K] [Fintype X]
    (a S : K × X → ℝ) (hS : ∀ z, 0 < S z)
    (hZ : 0 < shiftedSmoothProductMass a S) (x : X) :
    0 < shiftedSmoothProductMass (fun k => a (k, x)) (fun k => S (k, x)) := by
  rw [shiftedSmoothProductMass_eq_prod _ _ (fun k => hS (k, x))]
  exact Finset.prod_pos (fun k _ => shiftedSmoothProductMass_coordinate_pos a S hS hZ (k, x))

end Erdos3

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerRowInterpolationMixture
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem affineProfile_coordinate_sum_pos {I : Type*} [Fintype I]
    (c w S : I → ℝ) (hw : ∀ i, 0 < w i) (hS : ∀ i, 0 < S i)
    (hZ : 0 < coefficientWeightSum (affineProductProfile c w) S) (i : I) :
    0 < shiftedSmoothSampleSum (c i * S i) (w i * S i) := by
  classical
  have hn : 0 ≤ shiftedSmoothSampleSum (c i * S i) (w i * S i) :=
    tsum_nonneg (fun k => (smoothProbabilityProfile_range _).1)
  by_contra! hi
  have hz := le_antisymm hi hn
  have hp : (∏ j, shiftedSmoothSampleSum (c j * S j) (w j * S j)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) hz
  rw [affineProductProfile_sample_sum c w S hw hS, hp, mul_zero] at hZ
  exact (lt_irrefl 0) hZ

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SelectedResidueApproximation
namespace OAI

section

namespace Erdos3

noncomputable def residueSmoothScalarPMFs {K I : Type*} [Fintype K] [Fintype I]
    (residue : K × I → ℤ) (modulus : I → ℕ) (hmodulus : ∀ j, 0 < modulus j)
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue modulus)
      (residueProfileWidth modulus V)) : K × I → PMF ℤ :=
  fun z => shiftedSmoothCoefficientPMF
    (residueProfileCenter residue modulus z) (residueProfileWidth modulus V z)
    (residueProfileWidth_pos modulus V hmodulus hV z)
    (shiftedSmoothProductMass_coordinate_pos
      (residueProfileCenter residue modulus) (residueProfileWidth modulus V)
      (residueProfileWidth_pos modulus V hmodulus hV) hZ z)

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

instance coefficientJetAxisReference_sigmaFinite (O : Fin m → Type*) [∀ j, Fintype (O j)]
    (a : LayerSamplerAxis I n) : SigmaFinite (coefficientJetAxisReference O a) := by
  rcases a with ⟨j, a⟩
  cases a with
  | inl i =>
    change SigmaFinite (volume : Measure (O j → ℝ))
    infer_instance
  | inr i =>
    change SigmaFinite (Measure.count : Measure (O j → ℤ))
    infer_instance

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientDeckImageCongruence
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory
open scoped Classical

attribute [local irreducible] coefficientDeckKernelEquiv

variable {K : Type*} [Fintype K] {m : ℕ} {J I B : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] [∀ j, Fintype (B j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (B j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

variable [CompactSpace (CoefficientTorus (K := K) U)]
variable [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]

theorem canonicalCoefficientDeckSample_measurable (d : ℕ) [NeZero d] :
    Measurable (fun p : CoefficientSamplerArrays (K := K) I n × CoefficientDeckResidues (K := K) B d =>
      canonicalCoefficientDeckSample U bW b hb o d (Nat.pos_of_ne_zero (NeZero.ne d)) p.1 p.2) := by
  exact ((canonicalCoefficientCoverLift_measurable U b hb o d).comp measurable_fst).add
    ((measurable_subtype_coe.comp (measurable_of_finite
      (coefficientDeckKernelEquiv U bW d (Nat.pos_of_ne_zero (NeZero.ne d))))).comp measurable_snd)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedFiberCap
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

variable {K : Type*} [Fintype K] {m : ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]

theorem coefficientMixedFiber_joint_measurable
    (D : CoefficientTorus (K := K) U → ℝ) (hD : Measurable D)
    (t : K → ℤ) (y : CoefficientTorus (K := Empty) U) :
    Measurable (fun p : CoefficientTorus (K := K) U × CoefficientTorus (K := K) U =>
      D (coefficientConstantCenter U p.1 + coefficientFiberMap U t y p.2)) :=
  hD.comp (((coefficientConstantCenter_continuous U).measurable.comp measurable_fst).add
    ((coefficientFiberMap_continuous U t y).measurable.comp measurable_snd))

theorem coefficientMixedFiber_joint_integrable
    (μ : Measure (CoefficientTorus (K := K) U)) [IsFiniteMeasure μ]
    (D : CoefficientTorus (K := K) U → ℝ) (hD : Measurable D)
    {M : ℝ} (hbound : ∀ x, ‖D x‖ ≤ M) (t : K → ℤ) (y : CoefficientTorus (K := Empty) U) :
    Integrable (fun p : CoefficientTorus (K := K) U × CoefficientTorus (K := K) U =>
      D (coefficientConstantCenter U p.1 + coefficientFiberMap U t y p.2)) (μ.prod μ) :=
  Integrable.of_bound (coefficientMixedFiber_joint_measurable U D hD t y).aestronglyMeasurable
    M (ae_of_all _ (fun _ => hbound _))

theorem coefficientMixedFiber_integrable
    (μ : Measure (CoefficientTorus (K := K) U)) [IsFiniteMeasure μ]
    (D : CoefficientTorus (K := K) U → ℝ) (hD : Measurable D)
    {M : ℝ} (hbound : ∀ x, ‖D x‖ ≤ M) (t : K → ℤ) (y : CoefficientTorus (K := Empty) U) :
    Integrable (fun c => coefficientFiberAverage U μ t
      (fun x => D (coefficientConstantCenter U c+x)) y) μ :=
  (coefficientMixedFiber_joint_integrable U μ D hD hbound t y).integral_prod_left

theorem coefficientMixedFiber_average
    (μ : Measure (CoefficientTorus (K := K) U)) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    (D : CoefficientTorus (K := K) U → ℝ) (hD : Measurable D)
    {M : ℝ} (hbound : ∀ x, ‖D x‖ ≤ M) (t : K → ℤ) (y : CoefficientTorus (K := Empty) U) :
    (∫ c, coefficientFiberAverage U μ t (fun x => D (coefficientConstantCenter U c+x)) y ∂μ) =
      ∫ x, D x ∂μ := by
  have hi := coefficientMixedFiber_joint_integrable U μ D hD hbound t y
  have hi' : Integrable (fun p : CoefficientTorus (K := K) U × CoefficientTorus (K := K) U =>
      D (coefficientConstantCenter U p.1+p.2)) (μ.prod μ) :=
    Integrable.of_bound (hD.comp (((coefficientConstantCenter_continuous U).measurable.comp
      measurable_fst).add measurable_snd)).aestronglyMeasurable M (ae_of_all _ (fun _ => hbound _))
  have hshift (x : CoefficientTorus (K := K) U) :
      (∫ c, D (coefficientConstantCenter U c + coefficientFiberMap U t y x) ∂μ) =
        ∫ c, D (coefficientConstantCenter U c+x) ∂μ := by
    calc
      _ = ∫ c, D ((coefficientConstantCenter U c + constantCoefficientTorusMap U
          (y-coefficientEvaluationTorus U t x))+x) ∂μ := by
        apply integral_congr_ae
        exact ae_of_all μ (fun c => by
          apply congrArg D
          simp only [coefficientFiberMap, map_sub]
          abel)
      _ = _ := coefficientConstantCenter_integral_add_constant U μ (fun z => D (z+x)) _
  change (∫ c, ∫ x, D (coefficientConstantCenter U c + coefficientFiberMap U t y x) ∂μ ∂μ) = _
  calc
    _ = ∫ x, ∫ c, D (coefficientConstantCenter U c + coefficientFiberMap U t y x) ∂μ ∂μ :=
      integral_integral_swap hi
    _ = ∫ x, ∫ c, D (coefficientConstantCenter U c+x) ∂μ ∂μ :=
      integral_congr_ae (ae_of_all μ hshift)
    _ = ∫ c, ∫ x, D (coefficientConstantCenter U c+x) ∂μ ∂μ :=
      (integral_integral_swap hi').symm
    _ = _ := by simp only [integral_add_left_eq_self, integral_const, probReal_univ, one_smul]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.CoefficientFourierTranslation
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators

variable {K F : Type*} [Fintype K] [Fintype F] {m : ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

theorem bounded_coefficient_translate_fiber_integrable
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (μ : Measure (CoefficientTorus (K := K) U)) [IsFiniteMeasure μ]
    (D : CoefficientTorus (K := K) U → ℝ) (hD : Measurable D)
    {M : ℝ} (hbound : ∀ x, ‖D x‖ ≤ M)
    (y : CoefficientTorus (K := K) U) (t : K → ℤ)
    (z : CoefficientTorus (K := Empty) U) :
    Integrable (fun x => D (y + coefficientFiberMap U t z x)) μ := by
  apply Integrable.of_bound
    (hD.comp (measurable_const.add (coefficientFiberMap_continuous U t z).measurable)).aestronglyMeasurable M
  exact ae_of_all μ (fun x => hbound _)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.StrideSelectedResidueBadProduct
namespace OAI

section

namespace Erdos3

open scoped Classical

theorem selectedResidueTiltedFiniteLaw_mean {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (D : (K × I → ℤ) → ℝ) (hD0 : ∀ x, 0 ≤ D x)
    (hD : 0 < selectedResidueDensityMass modulus G V D) (f : (K × I → ℤ) → ℝ) :
    (selectedResidueTiltedFiniteLaw modulus G V hV hZ D hD0 hD).mean (fun x => f x.val) =
      ∑' x, (selectedResidueDensityPMF modulus G V hV hZ D hD0 hD x).toReal * f x := by
  rw [selectedResidueTiltedFiniteLaw, FiniteProbabilityWeights.reweightPositive_mean,
    selectedResidueFiniteLaw_densityMass,
    selectedResidueFiniteLaw_mean modulus G V hV hZ (fun x => D x * f x),
    selectedResidueDensityPMF_mean]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.JointProductiveMeasure
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

variable {C Ω : Type*} [MeasurableSpace C] [Fintype Ω]
variable [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
variable (μ : Measure C) (law : C → FiniteProbabilityWeights Ω)
variable (hweight : ∀ x, Measurable (fun c => (law c).weight x))

noncomputable def centeredFiniteProbabilityMeasure : Measure (C × Ω) :=
  realDensityMeasure (μ.prod Measure.count) (centeredFiniteWeightDensity law)

include hweight

theorem centeredFiniteProbabilityMeasure_probability [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (centeredFiniteProbabilityMeasure μ law) :=
  realDensityMeasure_probability _ _ (centeredFiniteWeightDensity_integrable law hweight μ)
    (centeredFiniteWeightDensity_nonneg law) (centeredFiniteWeightDensity_integral law hweight μ)

theorem centeredFiniteProbabilityMeasure_ae_positive_weight :
    ∀ᵐ z ∂centeredFiniteProbabilityMeasure μ law, 0 < (law z.1).weight z.2 := by
  exact realDensityMeasure_ae_of_support (μ.prod Measure.count) (centeredFiniteWeightDensity law)
    (centeredFiniteWeightDensity_measurable law hweight) _ (fun z hz =>
      lt_of_le_of_ne (centeredFiniteWeightDensity_nonneg law z) (Ne.symm hz))

omit μ [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
theorem centeredFinite_mean_measurable (f : C → Ω → ℝ)
    (hf : ∀ x, Measurable (fun c => f c x)) :
    Measurable (fun c => (law c).mean (f c)) :=
  Finset.measurable_sum _ (fun x _ => (hweight x).mul (hf x))

omit [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
theorem centeredFinite_mean_integrable (f : C → Ω → ℝ)
    (hf : ∀ x, Integrable (fun c => f c x) μ) :
    Integrable (fun c => (law c).mean (f c)) μ := by
  apply integrable_finsetSum
  intro x _
  exact (hf x).bdd_mul (hweight x).aestronglyMeasurable (ae_of_all μ (fun c => by
    rw [Real.norm_of_nonneg ((law c).nonneg x)]
    exact centeredFiniteWeightDensity_le_one law (c, x)))

theorem centeredFiniteProbabilityMeasure_integral [IsProbabilityMeasure μ]
    (f : C × Ω → ℝ) (hf : Integrable f (centeredFiniteProbabilityMeasure μ law)) :
    (∫ z, f z ∂centeredFiniteProbabilityMeasure μ law) =
      ∫ c, (law c).mean (fun x => f (c, x)) ∂μ := by
  have hi := (integrable_withDensity_iff_integrable_smul'
    (centeredFiniteWeightDensity_measurable law hweight).ennreal_ofReal
    (ae_of_all (μ.prod Measure.count) (fun _ => ENNReal.ofReal_lt_top))).mp hf
  simp only [ENNReal.toReal_ofReal (centeredFiniteWeightDensity_nonneg law _), smul_eq_mul] at hi
  rw [centeredFiniteProbabilityMeasure, realDensityMeasure_integral _ _
    (centeredFiniteWeightDensity_measurable law hweight) (centeredFiniteWeightDensity_nonneg law),
    integral_prod _ hi]
  simp only [integral_count, centeredFiniteWeightDensity, FiniteProbabilityWeights.mean]

theorem centeredFiniteProbabilityMeasure_integral_bounded [IsProbabilityMeasure μ]
    (f : C × Ω → ℝ) (hf : Measurable f) {M : ℝ} (hbound : ∀ z, ‖f z‖ ≤ M) :
    (∫ z, f z ∂centeredFiniteProbabilityMeasure μ law) =
      ∫ c, (law c).mean (fun x => f (c, x)) ∂μ := by
  let := centeredFiniteProbabilityMeasure_probability μ law hweight
  exact centeredFiniteProbabilityMeasure_integral μ law hweight f
    (Integrable.of_bound hf.aestronglyMeasurable M (ae_of_all _ hbound))

theorem centeredFiniteProbabilityMeasure_real_event [IsProbabilityMeasure μ]
    (event : Set (C × Ω)) (hevent : MeasurableSet event) :
    (centeredFiniteProbabilityMeasure μ law).real event =
      ∫ c, (law c).mean (fun x => if (c, x) ∈ event then 1 else 0) ∂μ := by
  rw [← integral_indicator_one (μ := centeredFiniteProbabilityMeasure μ law) hevent]
  have hmeas : Measurable (event.indicator (1 : C × Ω → ℝ)) :=
    measurable_const.indicator hevent
  have hbound (z : C × Ω) : ‖event.indicator (1 : C × Ω → ℝ) z‖ ≤ 1 := by
    by_cases hz : z ∈ event <;> simp [hz]
  rw [centeredFiniteProbabilityMeasure_integral_bounded μ law hweight _ hmeas hbound]
  rfl

theorem centeredFiniteProbabilityMeasure_real_finset_fiber [IsProbabilityMeasure μ]
    (F : Finset Ω) :
    (centeredFiniteProbabilityMeasure μ law).real {z | z.2 ∈ F} =
      ∫ c, (law c).mass F ∂μ := by
  have hevent : MeasurableSet {z : C × Ω | z.2 ∈ F} :=
    (Finset.measurableSet F).preimage measurable_snd
  have h := centeredFiniteProbabilityMeasure_real_event μ law hweight _ hevent
  refine h.trans (integral_congr_ae (ae_of_all μ (fun c => ?_)))
  calc
    _ = (law c).mean (fun x => if x ∈ F then 1 else 0) := by
      apply congrArg (law c).mean
      funext x
      by_cases hx : x ∈ F <;> simp [hx]
    _ = _ := (law c).mean_indicator F

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical

theorem centeredFiniteProbabilityMeasure_productive_family
    {C Ω : Type*} [MeasurableSpace C] [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure C) [IsProbabilityMeasure μ]
    (law : C → FiniteProbabilityWeights Ω)
    (hweight : ∀ z, Measurable (fun c => (law c).weight z))
    (productive : Finset Ω) (Qgood : C × Ω → Prop)
    (hgood : ∀ c z, 0 < (law c).weight z → Qgood (c,z))
    {τ : ℝ} (hmass : τ ≤ ∫ c, (law c).mass productive ∂μ) :
    IsProbabilityMeasure (centeredFiniteProbabilityMeasure μ law) ∧
      MeasurableSet {z : C × Ω | z.2 ∈ productive} ∧
      τ ≤ (centeredFiniteProbabilityMeasure μ law).real {z | z.2 ∈ productive} ∧
      ∀ᵐ z ∂centeredFiniteProbabilityMeasure μ law, Qgood z := by
  refine ⟨centeredFiniteProbabilityMeasure_probability μ law hweight,
    (Finset.measurableSet productive).preimage measurable_snd, ?_, ?_⟩
  · rw [centeredFiniteProbabilityMeasure_real_finset_fiber μ law hweight]
    exact hmass
  · filter_upwards [centeredFiniteProbabilityMeasure_ae_positive_weight μ law hweight] with z hz
    exact hgood z.1 z.2 hz

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CenteredFiniteSliceResidualEnvelope
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

variable {C Ω : Type*} [MeasurableSpace C] [Fintype Ω]
variable (μ : Measure C) [IsProbabilityMeasure μ]
variable (law : C → FiniteProbabilityWeights Ω)
variable (hweight : ∀ z, Measurable (fun c => (law c).weight z))

include hweight

section Site

variable {T X : Type*} [Fintype T] [Nonempty T] [Fintype X]
variable (physical : Ω → T → X)

include hweight in
theorem centeredFinite_siteLaw_weight_measurable (x : X) :
    Measurable (fun c => ((law c).siteLaw physical).weight x) := by
  have h := centeredFinite_mean_measurable law hweight
    (fun _ z => 𝔼 t, ‖(Pi.single x (1 : ℂ) : X → ℂ) (physical z t)‖)
    (fun _ => measurable_const)
  have he (c : C) : (law c).mean
      (fun z => 𝔼 t, ‖(Pi.single x (1 : ℂ) : X → ℂ) (physical z t)‖) =
      ((law c).siteLaw physical).weight x := by
    exact (FiniteProbabilityWeights.siteLaw_mean (law c) physical
      (fun y => ‖(Pi.single x (1 : ℂ) : X → ℂ) y‖)).symm.trans
        (FiniteProbabilityWeights.mean_single_norm _ x)
  simpa only [he] using h

end Site

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SampledCommonBox
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem exists_finite_site_box_inner_family {I T : Type*} [Fintype I] [DecidableEq I]
    [Fintype T] (e : T → I → ℤ) (he : Function.Injective e) {p : ℝ} (hp : 0 ≤ p) (N : I → ℕ) :
    ∃ C : Finset (Finset T),
      (C.card : ℝ) ≤ Real.exp ((5 * p + 20) * Fintype.card I + p + 2) ∧
      (∀ A ∈ C, A.Nonempty → ∃ (c : I → ℤ) (m : ℕ) (H : I → ℕ),
        0 < m ∧ (∀ i, 0 < H i) ∧ A.image e = commonStrideBox c m H) ∧
      ∀ S : Finset T, IsDenseCommonStrideBox N p (S.image e) →
        ∃ A ∈ C, A.Nonempty ∧ A ⊆ S ∧
          2 * (1 - (A.card : ℝ) / S.card) ≤ Fintype.card I * Real.exp (-p) := by
  obtain ⟨D, hD, hshape, hcover⟩ := exists_dense_box_inner_family hp N
  refine ⟨finiteSiteInnerFamily e D, ?_, ?_, ?_⟩
  · exact (show ((finiteSiteInnerFamily e D).card : ℝ) ≤ D.card by
      exact_mod_cast finiteSiteInnerFamily_card e D).trans hD
  · intro A hA hAn
    obtain ⟨c, m, H, hm, _, heq⟩ := hshape (A.image e) (finiteSiteInnerFamily_image_mem e D hA)
    have hBn : (commonStrideBox c m H).Nonempty := heq ▸ hAn.image e
    have haxis := Fintype.piFinset_nonempty.mp hBn
    refine ⟨c, m, H, hm, ?_, heq⟩
    intro i
    have hcard := (haxis i).card_pos
    simpa only [card_integerProgressionSupport _ _ _ hm] using hcard
  · intro S hS
    obtain ⟨c, m, H, hm, hH, hsub, hdense, heq⟩ := hS
    obtain ⟨A, hAD, hAn, hAS, hloss⟩ := hcover c m H hm hH hsub hdense
    have hAS' : A ⊆ S.image e := by rw [heq]; exact hAS
    have hAall : A ⊆ Finset.univ.image e := hAS'.trans (Finset.image_subset_image (Finset.subset_univ S))
    have hcard := finiteSitePreimage_card e he A hAall
    refine ⟨finiteSitePreimage e A, mem_finiteSiteInnerFamily e D hAD hAall,
      Finset.card_pos.mp (by rw [hcard]; exact hAn.card_pos),
      finiteSitePreimage_subset e he A S hAS', ?_⟩
    rw [← heq, Finset.card_image_of_injective _ he] at hloss
    simpa only [hcard] using hloss

end Erdos3

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

instance allocatedLongJetReference_sigmaFinite (O : Fin m → Type*) [∀ j, Fintype (O j)] :
    SigmaFinite (allocatedLongJetReference B U basis S O) := by
  unfold allocatedLongJetReference
  infer_instance

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedPhysicalLongImage
namespace OAI

section

namespace Erdos3

noncomputable def translatedIntegerMappedJetMatrix {Z X K α O N : Type*} [DecidableEq α]
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ X) (z : Z → ℤ)
    (rows : O → Finset α) (x : X → ℤ) (c : K → ℤ) : Matrix O N ℤ :=
  integerJetMatrix (fun n => MvPolynomial.monomial (e n) 1)
    (fun t k => c k + integerMappedCubeTuple input z x t k) rows

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)

variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} (rows : ∀ j, O j → Finset α)

noncomputable def allocatedTranslatedPartitionedJetMatrix
    (c : LayerSamplerVariables G I n B → ℤ) (j : Fin m) :
    Matrix (O j) (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) ℤ :=
  translatedIntegerMappedJetMatrix Subtype.val (partitionedPrincipalInput grid (fun g a => (g, a))) (Sum.elim (fun ga : G × Option α => (x ga.1 ga.2 : ℤ)) (principalTupleIntegers u)) (rows j) (principalTupleIntegers v) c

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)

variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)

local notation "joined" => principalAxisJoin grid u v
local notation "root" => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x joined
local notation "dirs" => allocatedPhysicalCubeDirections B U b S x joined

noncomputable def allocatedPhysicalLongJetMap
    (a : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n) :
    AllocatedLongJetRows B U b S O :=
  fun i => coefficientJetAxisEquiv O I n (canonicalCoefficientJetArrays root dirs rows a) i.val

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedFrozenJetDensity
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module
open scoped BigOperators Classical Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (O : Fin m → Type*) [∀ j, Fintype (O j)]

noncomputable def allocatedFrozenJetReference : Measure (AllocatedFrozenJetRows B U b S O) :=
  Measure.pi (fun a : {a // allocatedGridAxis (I := I) U b S.value a} =>
    coefficientJetAxisReference O a.val)

instance allocatedFrozenJetReference_sigmaFinite : SigmaFinite (allocatedFrozenJetReference B U b S O) := by
  unfold allocatedFrozenJetReference
  infer_instance

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

theorem allocatedIdealCoverSupport_inactive (j : Fin m) :
    (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
      ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)) ≤
        allocatedIdealCoverSupport (G := G) B rowSets j := by
  have hi := partitionedIdealRadius_nonneg α m
  have hw : 0 ≤ ∑ i : Fin (n j), (allocatedSiteCoefficientRadius (G := G) B rowSets ⟨j, i⟩ + 1) :=
    Finset.sum_nonneg (fun i _ => by linarith [allocatedSiteCoefficientRadius_nonneg (G := G) B rowSets ⟨j, i⟩])
  unfold allocatedIdealCoverSupport
  linarith

theorem allocatedIdealCoverSupport_ideal (j : Fin m) :
    partitionedIdealRadius α m + 1 ≤ allocatedIdealCoverSupport (G := G) B rowSets j := by
  have hw : 0 ≤ ∑ i : Fin (n j), (allocatedSiteCoefficientRadius (G := G) B rowSets ⟨j, i⟩ + 1) :=
    Finset.sum_nonneg (fun i _ => by linarith [allocatedSiteCoefficientRadius_nonneg (G := G) B rowSets ⟨j, i⟩])
  unfold allocatedIdealCoverSupport
  exact le_add_of_le_of_nonneg (le_add_of_nonneg_left (by positivity)) hw

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedIdealCoverRadiusBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] (rowSets : Fin m → Finset (Finset α))

theorem allocatedIdealCoverSupport_le_exp {P : ℝ} (hP : 0 ≤ P) (j : Fin m)
    (hA : (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
      ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)) ≤ Real.exp P)
    (hI : partitionedIdealRadius α m + 1 ≤ Real.exp P)
    (hn : (n j : ℝ) ≤ Real.exp P)
    (hW : ∀ i : Fin (n j), allocatedSiteCoefficientRadius (G := G) B rowSets ⟨j, i⟩ + 1 ≤ Real.exp P) :
    allocatedIdealCoverSupport (G := G) B rowSets j ≤ Real.exp (2 * P + 2) := by
  have hs : (∑ i : Fin (n j), (allocatedSiteCoefficientRadius (G := G) B rowSets ⟨j, i⟩ + 1)) ≤
      Real.exp (2 * P) := by
    calc
      _ ≤ ∑ _i : Fin (n j), Real.exp P := Finset.sum_le_sum (fun i _ => hW i)
      _ = (n j : ℝ) * Real.exp P := by simp
      _ ≤ Real.exp P * Real.exp P := mul_le_mul_of_nonneg_right hn (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hp : Real.exp P ≤ Real.exp (2 * P) := Real.exp_le_exp.mpr (by linarith)
  have hthree : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  unfold allocatedIdealCoverSupport
  calc
    _ ≤ Real.exp P + Real.exp P + Real.exp (2 * P) := add_le_add (add_le_add hA hI) hs
    _ ≤ 3 * Real.exp (2 * P) := by linarith
    _ ≤ Real.exp 2 * Real.exp (2 * P) := mul_le_mul_of_nonneg_right hthree (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.SlicedProfilePolynomial
namespace OAI

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators

variable {D G : Type*} [Fintype D] [Fintype G]
variable {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ) (d : D)
variable {I : Type*}

noncomputable def slicedProfileTailPolynomial
    (ε : ℝ) (r : SamplerCoefficientSlot G B h d → ℝ)
    (ξ : SamplerTupleIndex G B h → MvPolynomial I ℝ) : MvPolynomial I ℝ :=
  MvPolynomial.eval₂Hom MvPolynomial.C ξ
    (∑ e ∈ nonprincipalCoefficientSlots Subtype.val (canonicalPrincipalExponent h d),
      MvPolynomial.monomial e.val (ε * r e))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedSlicedEndpointIdentity
namespace OAI

section

namespace Erdos3

open MeasureTheory VectorPolynomial
open scoped BigOperators NNReal

variable {D G E : Type*} [Fintype D] [Fintype G] [Fintype E]
variable {B : D → Type*} [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
variable (h : D → ℕ) (axis : E → D)

local notation "Input" => (Σ e, B (axis e) × Fin (h (axis e)))
local notation "Output" => (Σ _e : E, Unit)

noncomputable def jointSlicedProfileTail
    (ε : D → ℝ) (r : ∀ e, SamplerCoefficientSlot G B h (axis e) → ℝ)
    (ξ : E → SamplerTupleIndex G B h → MvPolynomial Input ℝ) (o : Output) : MvPolynomial Input ℝ :=
  slicedProfileTailPolynomial h (axis o.1) (ε (axis o.1)) (r o.1) (ξ o.1)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CenteredFiniteNoiseEventBound
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped Classical

theorem centeredFiniteProbabilityMeasure_noise_event_le
    {C Ω : Type*} [MeasurableSpace C] [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure C) [IsProbabilityMeasure μ]
    (law : C → FiniteProbabilityWeights Ω)
    (hweight : ∀ x, Measurable (fun c => (law c).weight x))
    (bad : Ω → Prop) {ε : ℝ}
    (hbound : ∀ c, (law c).mean (fun x => if bad x then 1 else 0) ≤ ε) :
    (centeredFiniteProbabilityMeasure μ law).real {z | bad z.2} ≤ ε := by
  have hevent : MeasurableSet {z : C × Ω | bad z.2} :=
    (Set.toFinite {x : Ω | bad x}).measurableSet.preimage measurable_snd
  rw [centeredFiniteProbabilityMeasure_real_event μ law hweight _ hevent]
  have hi := centeredFinite_mean_integrable μ law hweight
    (fun _ x => if bad x then (1 : ℝ) else 0) (fun _ => integrable_const _)
  calc
    _ ≤ ∫ _ : C, ε ∂μ := integral_mono hi (integrable_const ε) hbound
    _ = ε := by simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MeasurableConstantCenterRepresentative
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module

variable {K : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*}
variable [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))

theorem exists_measurable_coefficient_representative_of_layers
    [MeasurableSpace (CoefficientTorus (K := K) U)]
    [BorelSpace (CoefficientTorus (K := K) U)]
    (hsection : ∀ j, ∃ r : (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup) →
        euclideanSubspace (U j), Measurable r ∧
        ∀ x, QuotientAddGroup.mk' _ (r x) = x) :
    ∃ r : CoefficientTorus (K := K) U → CoefficientArray (K := K) U,
      Measurable r ∧ ∀ x, QuotientAddGroup.mk' (coefficientIntegerLattice U) (r x) = x := by
  classical
  choose r hr hright using hsection
  let f : CoefficientTorus (K := K) U → CoefficientArray (K := K) U :=
    fun x s => euclideanSubspaceArrayEquiv (U s.1)
      (r s.1 (euclideanCoefficientEquiv U x s.1 s.2)) ()
  refine ⟨f, ?_, ?_⟩
  · apply measurable_pi_iff.mpr
    intro s
    exact (measurable_pi_apply ()).comp
      ((euclideanSubspaceArrayEquiv (U s.1)).continuous.measurable.comp
        ((hr s.1).comp ((measurable_pi_apply s.2).comp
          ((measurable_pi_apply s.1).comp
            (euclideanCoefficientEquiv_continuous U).measurable))))
  · intro x
    apply coefficientCoordinateTorus_injective U
    funext s
    rw [coefficientCoordinateTorus_mk]
    have hunit : (fun _ : Unit => f x s) = euclideanSubspaceArrayEquiv (U s.1)
        (r s.1 (euclideanCoefficientEquiv U x s.1 s.2)) := by
      funext a
      cases a
      rfl
    rw [hunit, ← euclideanSubspaceTorusEquiv_mk, hright]
    exact (euclideanSubspaceTorusEquiv (U s.1)).apply_symm_apply _

theorem exists_measurable_subtractive_constant_center_of_representative
    [MeasurableSpace (CoefficientTorus (K := K) U)]
    [BorelSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (CoefficientTorus (K := Empty) U)]
    [BorelSpace (CoefficientTorus (K := Empty) U)]
    (r : CoefficientTorus (K := Empty) U → CoefficientArray (K := Empty) U)
    (hr : Measurable r)
    (hright : ∀ x, QuotientAddGroup.mk' (coefficientIntegerLattice U) (r x) = x) :
    ∃ c : CoefficientTorus (K := K) U → ∀ j, U j, Measurable c ∧
      ∀ x, coefficientConstantCenter U x =
        -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
          (constantCoefficientArray (K := K) U (fun s => c x s.1))) := by
  let v : CoefficientTorus (K := K) U → CoefficientArray (K := Empty) U :=
    fun x => r (-(coefficientEvaluationTorus U 0 x))
  let c : CoefficientTorus (K := K) U → ∀ j, U j :=
    fun x j => v x ⟨j, zeroCoefficientExponent Empty (j.val + 1)⟩
  refine ⟨c, ?_, ?_⟩
  · apply measurable_pi_iff.mpr
    intro j
    exact (measurable_pi_apply _).comp
      (hr.comp (coefficientEvaluationTorus_continuous U 0).neg.measurable)
  · intro x
    have hc : (fun s : CoefficientSlot Empty m => c x s.1) = v x := by
      funext s
      rcases s with ⟨j,d⟩
      rw [emptyCoefficientExponent_eq (j.val + 1) d]
    rw [← constantCoefficientTorusMap_mk, hc]
    change coefficientConstantCenter U x = -(constantCoefficientTorusMap U
      (QuotientAddGroup.mk' (coefficientIntegerLattice U)
        (r (-(coefficientEvaluationTorus U 0 x)))))
    rw [hright, map_neg, neg_neg]
    rfl

theorem exists_measurable_subtractive_constant_center
    [MeasurableSpace (CoefficientTorus (K := K) U)]
    [BorelSpace (CoefficientTorus (K := K) U)]
    [∀ j, IsZLattice ℝ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {B : Fin m → Type*} [∀ j, Fintype (B j)]
    (bW : ∀ j, Basis (B j) ℤ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))) :
    ∃ c : CoefficientTorus (K := K) U → ∀ j, U j, Measurable c ∧
      ∀ x, coefficientConstantCenter U x =
        -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
          (constantCoefficientArray (K := K) U (fun s => c x s.1))) := by
  let : MeasurableSpace (CoefficientTorus (K := Empty) U) := borel _
  let : BorelSpace (CoefficientTorus (K := Empty) U) := ⟨rfl⟩
  obtain ⟨r, hr, hright⟩ := exists_measurable_coefficient_representative_of_layers
    (K := Empty) U (fun j => lattice_exists_measurable_representative
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))) (bW j))
  exact exists_measurable_subtractive_constant_center_of_representative U r hr hright

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnconditionedSmoothSlopeCap
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem selectedResidueSmoothMass_one {K I : Type*} [Fintype K] [Fintype I]
    (W : K × I → ℝ) :
    (∑' z, selectedResidueSmoothWeight (fun _ => 1) {0} W z) =
      shiftedSmoothProductMass 0 W := by
  simp only [selectedResidueSmoothWeight_one, shiftedSmoothProductMass]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CenteredCoefficientDeckChartMeasurable
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped Classical

variable {K : Type*} [Fintype K] {m : ℕ} {J I E : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

omit [Fintype K] in

theorem coefficientSamplerAmbientPoint_measurable (a : CoefficientAmbientIndex K J) :
    Measurable (fun x : CoefficientSamplerArrays (K := K) I n =>
      coefficientSamplerAmbientPoint U b o x a) := by
  exact (PiLp.continuous_apply 2 (fun _ : J a.1.1 => ℝ) a.2).measurable.comp
    ((normalizedLatticePoint_continuous (euclideanSubspace (U a.1.1)) (b a.1.1)).measurable.comp
      ((orthonormalMixedChart (o a.1.1)).measurable.comp
        ((measurable_pi_apply a.1.2).comp
          ((mixedArrayRegroup _ _ _).measurable.comp (measurable_pi_apply a.1.1)))))

variable [CompactSpace (CoefficientTorus (K := K) U)]
variable [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]

theorem coefficientDeckChartEvent_measurableSet (q : ℕ) [NeZero q]
    (event : CoefficientChartResidues K n E q → Prop) :
    MeasurableSet {y | coefficientDeckChartEvent U bW b hb o q event y} := by
  let T := CoefficientSamplerArrays (K := K) I n × CoefficientDeckResidues (K := K) E q
  let chart : Set T := {z | (∀ a, |coefficientSamplerAmbientPoint U b o z.1 a| < 1/2) ∧
    event (coefficientSamplerChartResidues q z.1 z.2)}
  have hsmall : MeasurableSet {z : T | ∀ a,
      |coefficientSamplerAmbientPoint U b o z.1 a| < 1/2} := by
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro a
    exact measurableSet_lt ((coefficientSamplerAmbientPoint_measurable U b o a).comp measurable_fst).abs
      measurable_const
  have hread : Measurable (fun z : T => coefficientSamplerChartResidues q z.1 z.2) := by
    apply measurable_pi_iff.mpr
    intro j
    apply measurable_pi_iff.mpr
    intro e
    apply measurable_pi_iff.mpr
    intro i
    cases i with
    | inl i =>
      exact (measurable_of_countable (fun v : ℤ => (v : ZMod q))).comp
        ((measurable_pi_apply e).comp ((measurable_pi_apply i).comp
          (measurable_snd.comp ((measurable_pi_apply j).comp measurable_fst))))
    | inr i =>
      exact (measurable_pi_apply i).comp ((measurable_pi_apply e).comp
        ((measurable_pi_apply j).comp measurable_snd))
  have hchart : MeasurableSet chart := hsmall.inter
    (hread (Set.toFinite {r | event r}).measurableSet)
  have instS : StandardBorelSpace (CoefficientSamplerArrays (K := K) I n) := by infer_instance
  have instR : StandardBorelSpace (CoefficientDeckResidues (K := K) E q) := by infer_instance
  let : StandardBorelSpace T := @StandardBorelSpace.prod _ _ _ _ instS instR
  have himage := hchart.image_of_measurable_injOn
    (canonicalCoefficientDeckSample_measurable U bW b hb o q)
    ((canonicalCoefficientDeckSample_injOn_smallAmbient U bW b hb o q (NeZero.pos q)).mono
      (fun _ hz => hz.1))
  convert himage using 1
  ext y
  constructor
  · rintro ⟨x, r, hs, hy, he⟩
    exact ⟨(x,r), ⟨hs,he⟩, hy⟩
  · rintro ⟨⟨x,r⟩, ⟨hs,he⟩, hy⟩
    exact ⟨x,r,hs,hy,he⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CenteredFiniteEventSupport
namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical

variable {C Ω : Type*} [MeasurableSpace C] [Fintype Ω]
variable [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
variable (μ : Measure C) (law : C → FiniteProbabilityWeights Ω)
variable (hweight : ∀ x, Measurable (fun c => (law c).weight x))

include hweight in

theorem centeredFiniteProbabilityMeasure_real_event_of_support [IsProbabilityMeasure μ]
    (event test : Set (C × Ω)) (htest : MeasurableSet test)
    (heq : ∀ c x, 0 < (law c).weight x → ((c,x) ∈ event ↔ (c,x) ∈ test)) :
    (centeredFiniteProbabilityMeasure μ law).real event =
      ∫ c, (law c).mean (fun x => if (c,x) ∈ event then 1 else 0) ∂μ := by
  have hae : event =ᵐ[centeredFiniteProbabilityMeasure μ law] test :=
    (centeredFiniteProbabilityMeasure_ae_positive_weight μ law hweight).mono
      (fun z hz => propext (heq z.1 z.2 hz))
  rw [measureReal_def, measure_congr hae, ← measureReal_def,
    centeredFiniteProbabilityMeasure_real_event μ law hweight test htest]
  apply integral_congr_ae
  apply ae_of_all
  intro c
  unfold FiniteProbabilityWeights.mean
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : (law c).weight x = 0
  · simp only [hx, zero_mul]
  · have hpos := lt_of_le_of_ne ((law c).nonneg x) (Ne.symm hx)
    simp only [heq c x hpos]

include hweight in

theorem centeredFiniteProbabilityMeasure_real_event_le_of_support [IsProbabilityMeasure μ]
    (event test : Set (C × Ω)) (htest : MeasurableSet test)
    (heq : ∀ c x, 0 < (law c).weight x → ((c,x) ∈ event ↔ (c,x) ∈ test))
    {ε : ℝ} (hbound : ∀ c, (law c).mean (fun x => if (c,x) ∈ event then 1 else 0) ≤ ε) :
    (centeredFiniteProbabilityMeasure μ law).real event ≤ ε := by
  rw [centeredFiniteProbabilityMeasure_real_event_of_support μ law hweight event test htest heq]
  calc
    _ ≤ ∫ _ : C, ε ∂μ := by
      apply integral_mono_of_nonneg
      · exact ae_of_all μ (fun c => (law c).mean_nonneg (fun _ => by split_ifs <;> norm_num))
      · exact integrable_const ε
      · exact ae_of_all μ hbound
    _ = ε := by simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ProductANOVAEnergyOrder
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

noncomputable def productANOVAEnergy (D : Finset (Finset I)) (f : (∀ i, X i) → ℝ) : ℝ :=
  ∑ S ∈ D, (FiniteProbabilityWeights.pi μ).mean (fun x => productANOVA μ S f x ^ 2)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ProductANOVATensorChoices
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

noncomputable def productANOVATensor (k : ℕ) (base : ∀ i, X i)
    (f : (∀ i, X i) → ℝ) (z : Fin k → Sigma X) : ℝ := by
  classical
  exact if h : StrictMono (fun j => (z j).1) then
    if (∏ j, coordinateUnionWeight μ (z j)) = 0 then 0 else
      productANOVA μ (Finset.univ.image (fun j => (z j).1)) f
        (productTuplePoint (fun j => (z j).1) h.injective (fun j => (z j).2) base)
    else 0

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ProductANOVASectionNormalizedBound
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

noncomputable def productANOVASectionEnergy (T : Finset I) (D : Finset (Finset I))
    (z : ∀ i, X i) (f : (∀ i, X i) → ℝ) : ℝ :=
  ∑ U ∈ D, (FiniteProbabilityWeights.pi μ).mean
    (fun x => productANOVA μ (T ∪ U) f (productCoordinateMix T z x) ^ 2)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

noncomputable def productANOVASectionTensor (T : Finset I) (d : ℕ)
    (z base : ∀ i, X i) (f : (∀ i, X i) → ℝ) : (Fin d → Sigma X) → ℝ :=
  orderedFamilyTensor d base (fun U x =>
    if Disjoint T U then productANOVA μ (T ∪ U) f (productCoordinateMix T z x) else 0)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueSliceUpperFailure
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def residuePrimeCoordinateOutsideEquiv {ι σ : Type*}
    [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ) (q : ι → ℕ)
    (hcop : Pairwise (fun i j => (q i).Coprime (q j)))
    (K : Finset ι) (base : ∀ i, σ → ZMod (q i))
    (u : ResiduePrimeCoordinateCell lo N M a q K base)
    (S : Finset {i // i ∉ K}) (x : ∀ i, σ → ZMod (q i)) (hx : ∀ i ∈ K, x i = base i) :
    ResiduePrimeCoordinateCell lo N M a q (K ∪ S.image Subtype.val) x ≃
      ResiduePrimeCoordinateCell lo N (M.lcm (∏ i ∈ K, q i)) (fun j => (u.val j).val)
        (fun i : {i // i ∉ K} => q i.val) S (fun i => x i.val) := by
  let uv := fun j => (u.val j).val
  have huM : ∀ j, uv j ≡ a j [ZMOD (M : ℤ)] :=
    fun j => (Finset.mem_filter.mp (u.val j).property).2
  have hux : ∀ i ∈ K, (fun j => (uv j : ZMod (q i))) = x i :=
    fun i hi => (u.property i hi).trans (hx i hi).symm
  have hc := fun z => residuePrimeCoordinate_constraints_lcm M a uv z q hcop K x huM hux
  exact {
    toFun := fun z => ⟨fun j => ⟨(z.val j).val, Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp (z.val j).property).1,
        (hc _).mp ⟨fun k => (Finset.mem_filter.mp (z.val k).property).2,
          fun i hi => z.property i (Finset.mem_union_left _ hi)⟩ j⟩⟩,
      fun i hi => z.property i.val (Finset.mem_union_right K (Finset.mem_image.mpr ⟨i, hi, rfl⟩))⟩
    invFun := fun z => ⟨fun j => ⟨(z.val j).val, Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp (z.val j).property).1,
        ((hc _).mpr (fun k => (Finset.mem_filter.mp (z.val k).property).2)).1 j⟩⟩, by
      intro i hi
      rcases Finset.mem_union.mp hi with hi | hi
      · exact ((hc _).mpr (fun k => (Finset.mem_filter.mp (z.val k).property).2)).2 i hi
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
        exact z.property j hj⟩
    left_inv := fun z => by apply Subtype.ext; funext j; apply Subtype.ext; rfl
    right_inv := fun z => by apply Subtype.ext; funext j; apply Subtype.ext; rfl }

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.CountingKernelOuter
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def countingBernoulli {b : ℝ} (hb : 0 ≤ b) (hb1 : b ≤ 1) :
    FiniteProbabilityWeights Bool where
  weight sigma := if sigma then b else 1 - b
  nonneg sigma := by cases sigma <;> simp <;> linarith
  total := by simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ShiftedSmoothFiniteGridLaw
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem shiftedSmoothProductPMF_point_le {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (hlarge : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ S i) (k : I → ℤ) :
    (shiftedSmoothProductPMF a S hS hZ k).toReal ≤
      (2 : ℝ) ^ Fintype.card I * (∏ i, S i)⁻¹ := by
  rw [shiftedSmoothProductPMF_eq_independent, independentProductPMF_toReal]
  calc
    _ ≤ ∏ i, 2 / S i := Finset.prod_le_prod
      (fun _ _ => ENNReal.toReal_nonneg)
      (fun i _ => shiftedSmoothCoefficientPMF_le (a i) (hlarge i) (k i))
    _ = _ := by simp only [div_eq_mul_inv, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ, Finset.prod_inv_distrib]

theorem shiftedSmoothProductFiniteWeights_point_le {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (hlarge : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ S i)
    (k : rectangularWeightIndices a S 1) :
    (shiftedSmoothProductFiniteWeights a S hS hZ).weight k ≤
      (2 : ℝ) ^ Fintype.card I * (∏ i, S i)⁻¹ :=
  shiftedSmoothProductPMF_point_le a S hS hZ hlarge k.val

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ShiftedSmoothPolynomialSublevel
namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical

theorem shiftedSmoothProduct_polynomial_sublevel {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (a S : Fin N → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (hlarge : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ S i)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ i, 1 / S i ≤ δ)
    (P : MvPolynomial (Fin N) ℝ) (hdeg : ∀ i, P.degreeOf i ≤ d)
    (K u : ℝ) (hK : 0 ≤ K) (hu : 0 < u)
    (hLip : ∀ x y : Fin N → ℝ, (∀ i, |x i| ≤ 2) → (∀ i, |y i| ≤ 2) →
      |MvPolynomial.eval x P - MvPolynomial.eval y P| ≤ K * ‖x - y‖)
    (x₀ : Fin N → ℝ) (hx₀ : ∀ i, |x₀ i| ≤ 1) (hval : 1 ≤ |MvPolynomial.eval x₀ P|) :
    (shiftedSmoothProductFiniteWeights a S hS hZ).eventProbability
      (fun k => |MvPolynomial.eval (rectangularLatticePoint a S k.val) P| ≤ u) ≤
      shiftedSmoothSublevelConstant N d *
        ((u + K * δ) * (d + 1 : ℝ) ^ N) ^ (((N * d : ℕ) : ℝ)⁻¹) := by
  have h := shiftedPolynomial_grid_sublevel_bound_of_value hN hd
    (shiftedSmoothProductFiniteWeights a S hS hZ) Subtype.val Subtype.val_injective
    a S hS hδ hδ1 hmesh (rectangularWeightIndices_normalized_bound a S hS)
    P hdeg (2 ^ N) K u (by positivity) hK hu
    (fun k => by simpa only [Fintype.card_fin] using
      shiftedSmoothProductFiniteWeights_point_le a S hS hZ hlarge k)
    hLip x₀ hx₀ hval
  simpa only [shiftedSmoothSublevelConstant, mul_assoc] using h

theorem shiftedSmoothProduct_polynomial_family_threshold {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    {T : Type*} [Fintype T]
    (a S : Fin N → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (hlarge : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ S i)
    {δ η : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hη : 0 < η) (hmesh : ∀ i, 1 / S i ≤ δ)
    (P : T → MvPolynomial (Fin N) ℝ) (hdeg : ∀ t i, (P t).degreeOf i ≤ d)
    (K : ℝ) (hK : 0 ≤ K)
    (hLip : ∀ t x y, (∀ i, |x i| ≤ 2) → (∀ i, |y i| ≤ 2) →
      |MvPolynomial.eval x (P t) - MvPolynomial.eval y (P t)| ≤ K * ‖x - y‖)
    (x₀ : T → Fin N → ℝ) (hx₀ : ∀ t i, |x₀ t i| ≤ 1)
    (hval : ∀ t, 1 ≤ |MvPolynomial.eval (x₀ t) (P t)|)
    (hsmall : K * δ ≤ shiftedSmoothSublevelThreshold N d (Fintype.card T) η) :
    ((shiftedSmoothProductPMF a S hS hZ).map (fun k => decide
      (∃ t, |MvPolynomial.eval (rectangularLatticePoint a S k) (P t)| ≤
        shiftedSmoothSublevelThreshold N d (Fintype.card T) η)) true).toReal ≤ η / 2 := by
  let κ := shiftedSmoothSublevelThreshold N d (Fintype.card T) η
  let C := shiftedSmoothSublevelConstant N d
  let scale := (d + 1 : ℝ) ^ N
  have hκ : 0 < κ := shiftedSmoothSublevelThreshold_pos hN d _ hη
  have hC : 0 ≤ C := shiftedSmoothSublevelConstant_nonneg hN d
  have hs : 0 ≤ scale := by positivity
  simp only [decide_eq_classical]
  rw [← shiftedSmoothProductFiniteWeights_event_eq_map a S hS hZ]
  apply ((shiftedSmoothProductFiniteWeights a S hS hZ).eventProbability_union_bound _
    (fun t k => |MvPolynomial.eval (rectangularLatticePoint a S k.val) (P t)| ≤ κ)
    (fun _ h => h)).trans
  calc
    _ ≤ ∑ _t : T, C * (2 * κ * scale) ^ (((N * d : ℕ) : ℝ)⁻¹) := by
      apply Finset.sum_le_sum
      intro t _
      apply (shiftedSmoothProduct_polynomial_sublevel hN hd a S hS hZ hlarge hδ hδ1 hmesh
        (P t) (hdeg t) K κ hK hκ (hLip t) (x₀ t) (hx₀ t) (hval t)).trans
      apply mul_le_mul_of_nonneg_left _ hC
      apply Real.rpow_le_rpow
      · exact mul_nonneg (add_nonneg hκ.le (mul_nonneg hK hδ)) hs
      · exact mul_le_mul_of_nonneg_right (by dsimp only [κ] at *; linarith) hs
      · positivity
    _ = (Fintype.card T : ℝ) * C * (2 * κ * scale) ^ (((N * d : ℕ) : ℝ)⁻¹) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]
    _ ≤ η / 2 := polynomialSublevelThreshold_total_bound (Nat.mul_pos hN hd) hC hs hη

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SmoothMatrixBlockBudget
namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical

theorem smoothMatrixBlock_bad_probability {n N : ℕ} (hn : 0 < n) (hN : 0 < N)
    {T : Type*} [Fintype T] (entry : T → (Fin n × Fin n ↪ Fin N))
    (a S : Fin N → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (hlarge : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ S i)
    {δ η : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hη : 0 < η) (hmesh : ∀ i, 1 / S i ≤ δ)
    (hsmall : embeddedMatrixDeterminantLip n N * δ ≤
      shiftedSmoothSublevelThreshold N n (Fintype.card T) η) :
    ((shiftedSmoothProductPMF a S hS hZ).map (fun k => decide
      (∃ t, |Matrix.det (fun i j : Fin n => rectangularLatticePoint a S k (entry t (i,j)))| ≤
        shiftedSmoothSublevelThreshold N n (Fintype.card T) η)) true).toReal ≤ η / 2 := by
  have h := shiftedSmoothProduct_polynomial_family_threshold hN hn a S hS hZ hlarge
    hδ hδ1 hη hmesh (fun t => embeddedMatrixDeterminantPolynomial (entry t))
    (fun t => embeddedMatrixDeterminantPolynomial_degree (entry t))
    (embeddedMatrixDeterminantLip n N) (embeddedMatrixDeterminantLip_nonneg n N)
    (fun t => embeddedMatrixDeterminantPolynomial_lipschitz (entry t))
    (fun t => embeddedMatrixIdentityPoint (entry t))
    (fun t => embeddedMatrixIdentityPoint_bound (entry t))
    (fun t => by rw [embeddedMatrixDeterminantPolynomial_identity]; norm_num) hsmall
  simpa only [embeddedMatrixDeterminantPolynomial_eval, matrixBlock_decide_eq_classical] using h

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

theorem spatialMatrixIndexMass_pos (e : Fin 2 × X ↪ G)
    (residue : Option (G ⊕ P) × X → ℤ) (q : X → ℕ) (hq : ∀ x, 0 < q x)
    (V : Option (G ⊕ P) × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue q) (residueProfileWidth q V)) :
    0 < shiftedSmoothProductMass (spatialMatrixIndexCenter e residue q) (spatialMatrixIndexWidth e q V) :=
  shiftedSmoothProductMass_restrict_pos (spatialMatrixBlockSlot e)
    (residueProfileCenter residue q) (residueProfileWidth q V)
    (residueProfileWidth_pos q V hq hV) hZ

theorem spatialMatrixIndexPMF_marginal (e : Fin 2 × X ↪ G)
    (residue : Option (G ⊕ P) × X → ℤ) (q : X → ℕ) (hq : ∀ x, 0 < q x)
    (V : Option (G ⊕ P) × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue q) (residueProfileWidth q V)) :
    (residueSmoothIndexPMF residue q hq V hV hZ).map
      (fun t i => t (spatialMatrixBlockSlot e i)) =
      shiftedSmoothProductPMF (spatialMatrixIndexCenter e residue q) (spatialMatrixIndexWidth e q V)
        (spatialMatrixIndexWidth_pos e q hq V hV) (spatialMatrixIndexMass_pos e residue q hq V hV hZ) := by
  exact shiftedSmoothProductPMF_selected_marginal (spatialMatrixBlockSlot e)
    (residueProfileCenter residue q) (residueProfileWidth q V)
    (residueProfileWidth_pos q V hq hV) hZ

theorem spatialMatrixNormalizedEntries_residue_law (e : Fin 2 × X ↪ G)
    (residue : Option (G ⊕ P) × X → ℤ) (q : X → ℕ) (hq : ∀ x, 0 < q x)
    (V : Option (G ⊕ P) × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue q) (residueProfileWidth q V)) :
    (residueSmoothPMF residue q hq V hV hZ).map (spatialMatrixNormalizedEntries e V) =
      (shiftedSmoothProductPMF (spatialMatrixIndexCenter e residue q) (spatialMatrixIndexWidth e q V)
        (spatialMatrixIndexWidth_pos e q hq V hV) (spatialMatrixIndexMass_pos e residue q hq V hV hZ)).map
        (rectangularLatticePoint (spatialMatrixIndexCenter e residue q) (spatialMatrixIndexWidth e q V)) := by
  rw [residueSmoothPMF, PMF.map_comp]
  have hf : spatialMatrixNormalizedEntries e V ∘ residueLatticeArray residue q =
      rectangularLatticePoint (spatialMatrixIndexCenter e residue q) (spatialMatrixIndexWidth e q V) ∘
        (fun t i => t (spatialMatrixBlockSlot e i)) := by
    funext t
    exact spatialMatrixNormalizedEntries_residue e residue q hq V hV t
  rw [hf, ← PMF.map_comp, spatialMatrixIndexPMF_marginal]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem shiftedSmoothProductPMF_reindex {D J : Type*} [Fintype D] [Fintype J]
    (e : D ≃ J) (a S : J → ℝ) (hS : ∀ j, 0 < S j)
    (hZ : 0 < shiftedSmoothProductMass a S) :
    (shiftedSmoothProductPMF a S hS hZ).map (fun z d => z (e d)) =
      shiftedSmoothProductPMF (fun d => a (e d)) (fun d => S (e d))
        (fun d => hS (e d)) (shiftedSmoothProductMass_restrict_pos e a S hS hZ) :=
  shiftedSmoothProductPMF_selected_marginal e.toEmbedding a S hS hZ

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem spatialMatrixBlock_flat_bad_probability {n : ℕ} (hn : 0 < n)
    (a S : SpatialMatrixBlockIndex (Fin n) → ℝ) (hS : ∀ i, 0 < S i)
    (hZ : 0 < shiftedSmoothProductMass a S)
    (hlarge : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ S i)
    {δ η : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hη : 0 < η) (hmesh : ∀ i, 1 / S i ≤ δ)
    (hsmall : embeddedMatrixDeterminantLip n (2*n*n) * δ ≤ spatialMatrixBlockThreshold n η) :
    ((shiftedSmoothProductPMF a S hS hZ).map (fun k => decide
      (∃ b : Fin 2, |Matrix.det (fun i j : Fin n => rectangularLatticePoint a S k (b,j,i))| ≤
        spatialMatrixBlockThreshold n η)) true).toReal ≤ η / 2 := by
  unfold spatialMatrixBlockThreshold at hsmall ⊢
  simp only [spatialMatrix_decide_eq_classical]
  have h := smoothMatrixBlock_bad_probability hn (show 0 < 2*n*n by positivity)
    (spatialMatrixBlockEntry n)
    (fun k => a ((spatialMatrixBlockEquiv n).symm k))
    (fun k => S ((spatialMatrixBlockEquiv n).symm k))
    (fun k => hS ((spatialMatrixBlockEquiv n).symm k))
    (shiftedSmoothProductMass_restrict_pos (spatialMatrixBlockEquiv n).symm a S hS hZ)
    (fun k => hlarge ((spatialMatrixBlockEquiv n).symm k)) hδ hδ1 hη
    (fun k => hmesh ((spatialMatrixBlockEquiv n).symm k))
    (by simpa only [Fintype.card_fin, spatialMatrixBlockThreshold] using hsmall)
  rw [← shiftedSmoothProductPMF_reindex (spatialMatrixBlockEquiv n).symm a S hS hZ,
    PMF.map_comp] at h
  simpa only [Function.comp_def, rectangularLatticePoint_reindex,
    spatialMatrixBlockEntry_reindex_eval, Fintype.card_fin, spatialMatrixBlockThreshold,
    spatialMatrix_decide_eq_classical] using h

variable {G P : Type*} [Fintype G] [Fintype P] {n : ℕ}

theorem spatialMatrixBlock_residue_bad_probability (hn : 0 < n) (e : Fin 2 × Fin n ↪ G)
    (residue : Option (G ⊕ P) × Fin n → ℤ) (q : Fin n → ℕ) (hq : ∀ x, 0 < q x)
    (V : Option (G ⊕ P) × Fin n → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue q) (residueProfileWidth q V))
    (hlarge : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ spatialMatrixIndexWidth e q V i)
    {δ η : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hη : 0 < η)
    (hmesh : ∀ i, 1 / spatialMatrixIndexWidth e q V i ≤ δ)
    (hsmall : embeddedMatrixDeterminantLip n (2*n*n) * δ ≤ spatialMatrixBlockThreshold n η) :
    ((residueSmoothPMF residue q hq V hV hZ).map
      (fun z => decide (spatialMatrixBlockBad e V (spatialMatrixBlockThreshold n η) z)) true).toReal ≤ η / 2 := by
  let test : (SpatialMatrixBlockIndex (Fin n) → ℝ) → Bool := fun z => decide
    (∃ b : Fin 2, |Matrix.det (fun i j : Fin n => z (b,j,i))| ≤ spatialMatrixBlockThreshold n η)
  have heq := congrArg (fun law : PMF (SpatialMatrixBlockIndex (Fin n) → ℝ) =>
      (law.map test true).toReal)
    (spatialMatrixNormalizedEntries_residue_law e residue q hq V hV hZ)
  have hbound := spatialMatrixBlock_flat_bad_probability hn
    (spatialMatrixIndexCenter e residue q) (spatialMatrixIndexWidth e q V)
    (spatialMatrixIndexWidth_pos e q hq V hV) (spatialMatrixIndexMass_pos e residue q hq V hV hZ)
    hlarge hδ hδ1 hη hmesh hsmall
  simp only [PMF.map_comp, Function.comp_def, test, spatialMatrixBlockBad,
    spatialMatrix_decide_eq_classical] at heq hbound ⊢
  exact heq.trans_le hbound

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.WeightedCoefficientDensityApproximation
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

theorem selectedResidueSmoothPMF_weighted_coefficient_density
    {I K L F : Type*} [Fintype I] [Fintype K] [Fintype L] [Fintype F]
    {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := K) U)]
    [BorelSpace (CoefficientTorus (K := K) U)]
    (μ : Measure (CoefficientTorus (K := K) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (c : F → ℂ)
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern L I modulus))
    (V : L × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (sample : (L × I → ℤ) → CoefficientTorus (K := K) U)
    (w : (L × I → ℤ) → ℂ)
    (hw : ∀ x ∈ rectangularWeightIndices 0 V 1, ‖w x‖ ≤ 1)
    (D : CoefficientTorus (K := K) U → ℝ) (hD : Integrable D μ)
    (hDmass : (∫ x, D x ∂μ) = 1)
    {η ε : ℝ} (hη : 0 ≤ η)
    (happrox : ∀ x, ‖(D x : ℂ) - coefficientTorusFourierSum U frequency c x‖ ≤ η)
    (hfourier : ‖(∑' z, ((selectedResidueSmoothPMF modulus G V hV hZ z).toReal : ℂ) *
        (w z * coefficientTorusFourierSum U frequency c (sample z))) -
      (∑' z, ((selectedResidueSmoothPMF modulus G V hV hZ z).toReal : ℂ) * w z) *
        (∑ a, if affineCoefficientModeTrivial U (frequency a) then c a else 0)‖ ≤ ε) :
    ‖(∑' z, ((selectedResidueSmoothPMF modulus G V hV hZ z).toReal : ℂ) *
        (w z * (D (sample z) : ℂ))) -
      ∑' z, ((selectedResidueSmoothPMF modulus G V hV hZ z).toReal : ℂ) * w z‖ ≤
        2 * η + ε := by
  classical
  have hmass := probability_integral_approximation μ
    (coefficientTorusFourierSum U frequency c) (fun x => (D x : ℂ))
    (coefficientTorusFourierSum_integrable U frequency c μ) hD.ofReal
    (fun x => by simpa only [norm_sub_rev] using happrox x)
  rw [coefficientTorusFourierSum_integral, integral_complex_ofReal, hDmass,
    Complex.ofReal_one] at hmass
  have h := selectedResidueSmoothPMF_projection_approximation modulus G V hV hZ
    w (fun z => (D (sample z) : ℂ))
    (fun z => coefficientTorusFourierSum U frequency c (sample z))
    (fun _ => ∑ a, if affineCoefficientModeTrivial U (frequency a) then c a else 0)
    (fun _ => 1) hη hw (fun z _ => happrox (sample z)) (fun _ _ => hmass)
    (by simpa only [← mul_assoc, tsum_mul_right] using hfourier)
  simpa only [mul_one] using h

end Erdos3.VectorPolynomial

end

end OAI
end


