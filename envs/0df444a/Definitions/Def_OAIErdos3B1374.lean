-- Prove2me | Definitions.Def_OAIErdos3B1374
-- name    : OAIErdos3B1374
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-15T23:27:50.070324+00:00
-- url     : https://prove2.me/theorems/ecef3404-1cc9-4032-814a-4abec340a05c
-- title:
--   OpenAI Erdős-3 split, definitions bundle 1375 of 1376
-- statement:
--   Definitions bundle 1375 of 1376 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B1373`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 1375 available.
--
--   Modules: `OAI.Erdos3.BooleanCubeKernel.trimmedSpatial_scale_lower`, `OAI.Erdos3.FiniteProbabilityWeights.condition_weight_pos_iff`, `OAI.Erdos3.FiniteProbabilityWeights.mean_congr_on_support`, `OAI.Erdos3.FiniteProbabilityWeights.pi_weight_pos_component`, `OAI.Erdos3.VectorPolynomial.allocatedCoefficientAxisLaw_probability`, `OAI.Erdos3.VectorPolynomial.allocatedCoefficientSource_probability`, `OAI.Erdos3.VectorPolynomial.allocatedContinuousKernelDensity_probability_data`, `OAI.Erdos3.VectorPolynomial.allocatedContinuousProfileWidths_pos`, `OAI.Erdos3.VectorPolynomial.allocatedContinuousProfile_bound`, `OAI.Erdos3.VectorPolynomial.allocatedIntegerKernelMask_bound`, `OAI.Erdos3.VectorPolynomial.allocatedKernelJet_full_image`, `OAI.Erdos3.VectorPolynomial.allocatedKernelJet_split`, `OAI.Erdos3.VectorPolynomial.allocatedLongJetDensity_probability_data`, `OAI.Erdos3.VectorPolynomial.allocatedLongJetFactor_probability_data`, `OAI.Erdos3.VectorPolynomial.allocatedPartitionedJetMatrix_eq_physical`, `OAI.Erdos3.VectorPolynomial.allocatedPhysicalCube_mapped_directions`, `OAI.Erdos3.VectorPolynomial.allocatedPhysicalCube_mapped_root`, `OAI.Erdos3.VectorPolynomial.allocatedPhysicalCube_vertex`, `OAI.Erdos3.VectorPolynomial.allocatedPhysicalEntryBudget_one_le`, `OAI.Erdos3.VectorPolynomial.allocatedTranslatedPartitionedJetMatrix_eq_physical`, `OAI.Erdos3.VectorPolynomial.canonicalCoefficientCoverLift_jets`, `OAI.Erdos3.VectorPolynomial.canonicalCoefficientDeckSample_chart`, `OAI.Erdos3.VectorPolynomial.canonicalCoefficientDeckSample_mixed_jets`, `OAI.Erdos3.VectorPolynomial.canonicalCoefficientJetArrays_measurable`, `OAI.Erdos3.VectorPolynomial.coveredJetChart_continuous`, `OAI.Erdos3.VectorPolynomial.coveredJetChart_embedding`, `OAI.Erdos3.VectorPolynomial.coveredJetChart_injOn`, `OAI.Erdos3.VectorPolynomial.coveredJetChart_reference_map`, `OAI.Erdos3.VectorPolynomial.coveredJetSourceRegion_measurable`, `OAI.Erdos3.VectorPolynomial.integerMappedCubeTuple_kernel`, `OAI.Erdos3.VectorPolynomial.integerMappedJetMatrix_kernel`, `OAI.Erdos3.VectorPolynomial.integerMappedJetMatrix_kernel_split`, `OAI.Erdos3.VectorPolynomial.kernelExponent_eval_monomial`, `OAI.Erdos3.VectorPolynomial.mixedCoveredJetChart_image`, `OAI.Erdos3.VectorPolynomial.mixedCoveredJetChart_injOn`, `OAI.Erdos3.VectorPolynomial.mixedCoveredJetCoordinates_measurable`, `OAI.Erdos3.VectorPolynomial.mixedCoveredJetIntegerImage_chart`, `OAI.Erdos3.VectorPolynomial.mixedCoveredRowsSiteValue_chart`, `OAI.Erdos3.affineSelectedJetDensity_probability_data`, `OAI.Erdos3.affineSelectedJetProfile_probability_data`, `OAI.Erdos3.circleQuarterCover_center_dist`, `OAI.Erdos3.circleQuarterCover_dist`, `OAI.Erdos3.circleQuarterCover_separated`, `OAI.Erdos3.circleQuarterCover_zero`, `OAI.Erdos3.containedProgressionCubeMap_value`, `OAI.Erdos3.exists_bounded_extension_on_separated_charts`, `OAI.Erdos3.exists_complex_extension_of_distance_bound`, `OAI.Erdos3.exists_covered_representative_offset`, `OAI.Erdos3.exists_integer_quarter_cover_extension`, `OAI.Erdos3.exists_quarter_cover_extension`, `OAI.Erdos3.goodKernelUniformCandidate_spec`, `OAI.Erdos3.integerScalarLattice_le_of_nat_dvd`, `OAI.Erdos3.kernelGeometryLog_bounds`, `OAI.Erdos3.kernelLiftChart_image`, `OAI.Erdos3.kernelLiftChart_injOn`, `OAI.Erdos3.kernelLiftChart_relabel_image`, `OAI.Erdos3.kernelLiftChart_relabel_injOn`, `OAI.Erdos3.layerKernelIndexBound_row`, `OAI.Erdos3.mixedArrayIntegerImage_measurable`, `OAI.Erdos3.normalizedCoverLift_sum_zsmul`, `OAI.Erdos3.normalizedCoveredChart_continuous`, `OAI.Erdos3.normalizedCoveredChart_image`, `OAI.Erdos3.normalizedCoveredChart_injOn`, `OAI.Erdos3.normalizedCoveredChart_reference_map`, `OAI.Erdos3.normalizedCoveredChart_sum_zsmul`, `OAI.Erdos3.normalizedCoveredReference_restrict`, `OAI.Erdos3.normalizedCoveredReference_sigmaFinite`, `OAI.Erdos3.normalizedLatticeRepresentative_sum_zsmul`, `OAI.Erdos3.partitionedPrincipalInput_value`, `OAI.Erdos3.pmf_real_integral_count`, `OAI.Erdos3.quarterCoverPoint_intCast`, `OAI.Erdos3.quarterCoverPoint_separated`, `OAI.Erdos3.quarterCoverPoint_within`, `OAI.Erdos3.realDensityMeasure_integral_complex`, `OAI.Erdos3.restrictedChartDensity_eq_of_values`, `OAI.Erdos3.restrictedComplexChartDensity_measurable`, `OAI.Erdos3.restrictedComplexChartDensity_norm_le`, `OAI.Erdos3.scalarCubeResidueWeights_cube_support`, `OAI.Erdos3.translatedIntegerMappedJetMatrix_eq_boundedCoefficient`, `OAI.Erdos3.translatedIntegerMappedJetMatrix_zero`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B135
import Definitions.Def_OAIErdos3B1372

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoveredMixedArrayImage
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped BigOperators

variable {α K : Type*} [Fintype α] [DecidableEq α] [Fintype K]
variable {m : ℕ} {O J I : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (root : K → ℤ) (D : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)

variable [∀ j, Fintype (O j)]
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [CompactSpace (CoefficientTorus (K := K) U)]
variable [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
variable (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped BigOperators Matrix

variable {α K : Type*} [Fintype α] [DecidableEq α] [Fintype K]
variable {m : ℕ} {O J I : Fin m → Type*} [∀ j, Fintype (O j)]
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (root : K → ℤ) (D : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [CompactSpace (CoefficientTorus (K := K) U)]
variable [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
variable (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open Module Submodule
open scoped BigOperators Matrix

variable {D : Type*} [Fintype D] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)

theorem normalizedLatticeRepresentative_sum_zsmul {S : Type*} (s : Finset S)
    (a : S → ℤ) (x : S → W × (Fin n → ℤ)) :
    normalizedLatticeRepresentative W b hb (∑ i ∈ s, a i • x i) =
      ∑ i ∈ s, a i • normalizedLatticeRepresentative W b hb (x i) := by
  change normalizedLatticeRepresentativeHom W b hb _ = _
  simp only [map_sum, map_zsmul, normalizedLatticeRepresentativeHom,
    AddMonoidHom.coe_mk, ZeroHom.coe_mk]

theorem normalizedCoverLift_sum_zsmul (d : ℕ) {S : Type*} (s : Finset S)
    (a : S → ℤ) (x : S → W × (Fin n → ℤ)) :
    normalizedCoverLift W b hb d (∑ i ∈ s, a i • x i) =
      ∑ i ∈ s, a i • normalizedCoverLift W b hb d (x i) := by
  have he (i) : (d : ℝ)⁻¹ • (a i • normalizedLatticeRepresentative W b hb (x i)) =
      a i • ((d : ℝ)⁻¹ • normalizedLatticeRepresentative W b hb (x i)) := smul_comm _ _ _
  simp only [normalizedCoverLift, normalizedLatticeRepresentative_sum_zsmul,
    Finset.smul_sum, he]
  change QuotientAddGroup.mk' _ (∑ i ∈ s, a i • ((d : ℝ)⁻¹ •
    normalizedLatticeRepresentative W b hb (x i))) = _
  simp only [map_sum, map_zsmul]
  rfl

namespace VectorPolynomial

variable {α K : Type*} [Fintype α] [DecidableEq α] [Fintype K]
variable {m : ℕ} {O J I : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, Fintype (I j)]
variable {ns : Fin m → ℕ} (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bs : ∀ j, Basis (Fin (ns j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hbs : ∀ j, span ℤ (Set.range (bs j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (root : K → ℤ) (A : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)

theorem canonicalCoefficientCoverLift_jets (d : ℕ)
    (x : CoefficientSamplerArrays (K := K) I ns) (j : Fin m) (t : O j) :
    euclideanCoefficientJetMap U root A rows (canonicalCoefficientCoverLift U bs hbs o d x) j t =
      normalizedCoverLift (euclideanSubspace (U j)) (bs j) (hbs j) d
        (orthonormalMixedChart (o j) (mixedArrayRegroup _ _ _
          (canonicalCoefficientJetArrays root A rows x j) t)) := by
  rw [euclideanCoefficientJetMap_apply]
  simp only [canonicalCoefficientCoverLift, AddEquiv.apply_symm_apply]
  rw [canonicalCoefficientJetArrays, mixedArrayIntegerImage_regroup,
    orthonormalMixedChart_sum_zsmul, normalizedCoverLift_sum_zsmul]

theorem canonicalCoefficientDeckSample_mixed_jets
    {B : Fin m → Type*} [∀ j, Fintype (B j)]
    (bW : ∀ j, Basis (B j) ℤ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (d : ℕ) (hd : 0 < d) (x : CoefficientSamplerArrays (K := K) I ns)
    (r : CoefficientDeckResidues (K := K) B d) (j : Fin m) (t : O j) :
    euclideanCoefficientJetMap U root A rows
        (canonicalCoefficientDeckSample U bW bs hbs o d hd x r) j t =
      normalizedCoverLift (euclideanSubspace (U j)) (bs j) (hbs j) d
        (orthonormalMixedChart (o j) (mixedArrayRegroup _ _ _
          (canonicalCoefficientJetArrays root A rows x j) t)) +
      (coverKernelBasisEquiv
        (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup
        (bW j) d hd (coefficientDeckJetMap root A rows d r j t)).val := by
  rw [canonicalCoefficientDeckSample_jets, canonicalCoefficientCoverLift_jets]

end VectorPolynomial

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.JointAffineL1Parameter
namespace OAI

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open scoped NNReal BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem affineSelectedJetProfile_probability_data {I J N : Type*}
    [Fintype I] [Fintype J] [Fintype N] (s : I ↪ J) (c w : J ⊕ N → ℝ)
    (hw : ∀ j, 0 < w j) (R : ℝ≥0) (hsupport : ∀ j, |c j|+w j ≤ R) :
    Integrable (affineSelectedJetProfile s c w) ∧
      (∀ u, 0 ≤ affineSelectedJetProfile s c w u) ∧
      (∫ u, affineSelectedJetProfile s c w u) = 1 := by
  have hf : Continuous (selectedCoefficientProfile s
      (affineProductProfile (fun j => c (.inl j)) (fun j => w (.inl j)))) :=
    (affineProductProfile_contDiff (fun j => c (.inl j)) (fun j => w (.inl j))).continuous.comp
      (selectedCoefficientEquiv_lipschitz s).continuous
  have hg := (affineProductProfile_contDiff (fun n => c (.inr n)) (fun n => w (.inr n))).continuous
  have hfs := selectedCoefficientProfile_zero_outside s
    (affineProductProfile_zero_outside _ _ (fun j => hw (.inl j)) R.coe_nonneg (fun j => hsupport (.inl j)))
  have hgs := affineProductProfile_zero_outside _ _ (fun n => hw (.inr n)) R.coe_nonneg
    (fun n => hsupport (.inr n))
  refine ⟨splitFreeProfile_integrable hf hg hfs hgs,
    splitFreeProfile_nonneg (selectedCoefficientProfile_nonneg s
      (affineProductProfile_nonneg _ _ (fun j => hw (.inl j))))
      (affineProductProfile_nonneg _ _ (fun n => hw (.inr n))), ?_⟩
  change (∫ u, splitFreeProfile _ _ u) = 1
  rw [splitFreeProfile_integral hf hg hfs hgs, selectedCoefficientProfile_integral,
    affineProductProfile_integral _ _ (fun j => hw (.inl j)),
    affineProductProfile_integral _ _ (fun n => hw (.inr n)), one_mul]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem affineSelectedJetDensity_probability_data {Z P K α I J N : Type*}
    [Fintype α] [DecidableEq α] [Fintype I] [Fintype J] [Fintype N]
    (s : I ↪ J) (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (F : (UnselectedColumn s → ℝ) →L[ℝ] (I → ℝ))
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ P) (z : Z → ℝ) (rows : I → Finset α)
    (c w : J ⊕ N → ℝ) (hw : ∀ j, 0 < w j) (R : ℝ≥0) (hsupport : ∀ j, |c j| + w j ≤ R)
    (x : P → ℝ) :
    (∀ v, 0 ≤ affineSelectedJetDensity s A F e input z rows c w x v) ∧
      Integrable (affineSelectedJetDensity s A F e input z rows c w x) ∧
      (∫ v, affineSelectedJetDensity s A F e input z rows c w x v) = 1 := by
  have hp := affineSelectedJetProfile_probability_data s c w hw R hsupport
  exact ⟨pivotOutputDensity_nonneg _ _ hp.2.1, pivotOutputDensity_integrable _ _ hp.1,
    (pivotOutputDensity_integral _ _ hp.1).trans hp.2.2⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ControlledJointGrid
namespace OAI

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem pmf_real_integral_count {X : Type*} [Countable X]
    [MeasurableSpace X] [MeasurableSingletonClass X] (p : PMF X) :
    (∫ x, (p x).toReal ∂Measure.count) = 1 := by
  rw [integral_countable (pmf_real_integrable p)]
  simpa only [measureReal_def, Measure.count_singleton, ENNReal.toReal_one, one_smul]
    using pmf_real_mass p

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem realDensityMeasure_integral_complex {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (φ : X → ℂ) :
    (∫ x, φ x ∂realDensityMeasure μ f) = ∫ x, (f x : ℂ) * φ x ∂μ := by
  unfold realDensityMeasure
  rw [integral_withDensity_eq_integral_toReal_smul hf.ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hf0 _), Complex.real_smul]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelLiftChart
namespace OAI

section

namespace Erdos3

variable {G H X : Type*} [AddCommGroup G] [AddCommGroup H]
variable (C : G →+ H) (s : X → G) (q : X → H)

theorem kernelLiftChart_injOn (hproj : ∀ x, C (s x) = q x)
    {S : Set X} (hq : Set.InjOn q S) :
    Set.InjOn (fun p : X × C.ker => s p.1 + p.2.val) (S ×ˢ Set.univ) := by
  intro x hx y hy he
  change s x.1 + x.2.val = s y.1 + y.2.val at he
  have hkx : C x.2.val = 0 := x.2.property
  have hky : C y.2.val = 0 := y.2.property
  have hb : q x.1 = q y.1 := by
    have ht := congrArg C he
    simpa only [map_add, hproj, hkx, hky, add_zero] using ht
  have hxy : x.1 = y.1 := hq hx.1 hy.1 hb
  apply Prod.ext hxy
  apply Subtype.ext
  rw [hxy] at he
  exact add_left_cancel he

theorem kernelLiftChart_image (hproj : ∀ x, C (s x) = q x) (S : Set X) :
    (fun p : X × C.ker => s p.1 + p.2.val) '' (S ×ˢ Set.univ) = C ⁻¹' (q '' S) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.1, hx.1, ?_⟩
    have hk : C x.2.val = 0 := x.2.property
    simp only [map_add, hproj, hk, add_zero]
  · rintro ⟨x, hx, hxy⟩
    have hk : y - s x ∈ C.ker := by
      change C (y - s x) = 0
      rw [map_sub, hproj, ← hxy, sub_self]
    refine ⟨(x, ⟨y - s x, hk⟩), ⟨hx, Set.mem_univ _⟩, ?_⟩
    change s x + (y - s x) = y
    rw [← add_sub_assoc, add_sub_cancel_left]

theorem kernelLiftChart_relabel_injOn {R : Type*} (e : R ≃ C.ker)
    (hproj : ∀ x, C (s x) = q x) {S : Set X} (hq : Set.InjOn q S) :
    Set.InjOn (fun p : X × R => s p.1 + (e p.2).val) (S ×ˢ Set.univ) := by
  intro x hx y hy he
  have hp := kernelLiftChart_injOn C s q hproj hq
    (show (x.1, e x.2) ∈ S ×ˢ Set.univ from ⟨hx.1, Set.mem_univ _⟩)
    (show (y.1, e y.2) ∈ S ×ˢ Set.univ from ⟨hy.1, Set.mem_univ _⟩) he
  exact Prod.ext (congrArg (fun z : X × C.ker => z.1) hp)
    (e.injective (congrArg (fun z : X × C.ker => z.2) hp))

theorem kernelLiftChart_relabel_image {R : Type*} (e : R ≃ C.ker)
    (hproj : ∀ x, C (s x) = q x) (S : Set X) :
    (fun p : X × R => s p.1 + (e p.2).val) '' (S ×ˢ Set.univ) = C ⁻¹' (q '' S) := by
  rw [← kernelLiftChart_image C s q hproj S]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(x.1, e x.2), ⟨hx.1, Set.mem_univ _⟩, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(x.1, e.symm x.2), ⟨hx.1, Set.mem_univ _⟩, by simp only [e.apply_symm_apply]⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NormalizedCoveredChart
namespace OAI

section

namespace Erdos3

open Module Submodule MeasureTheory
open scoped Classical

variable {D R : Type*} [Fintype D] [Fintype R] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
variable (bW : Basis R ℤ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup)
variable (d : ℕ) [NeZero d]

theorem normalizedCoveredChart_continuous :
    Continuous (normalizedCoveredChart W b hb bW d) := by
  have hk : Continuous (fun r : R → ZMod d =>
      (coverKernelBasisEquiv (latticeSection (standardEuclideanLattice D) W).toAddSubgroup
        bW d (Nat.pos_of_ne_zero (NeZero.ne d)) r).val) := continuous_of_discreteTopology
  exact ((normalizedCoverLift_continuous W b hb d).comp continuous_fst).add
    (hk.comp continuous_snd)

theorem normalizedCoveredChart_injOn
    {Ω : Set (EuclideanSpace ℝ D)} (hΩ : Ω ⊆ standardLatticeSmallBox D) :
    Set.InjOn (normalizedCoveredChart W b hb bW d)
      ((normalizedLatticePoint W b ⁻¹' Ω) ×ˢ Set.univ) :=
  kernelLiftChart_relabel_injOn _ _ _
    (coverKernelBasisEquiv _ bW d (Nat.pos_of_ne_zero (NeZero.ne d))).toEquiv
    (normalizedCoverLift_projection W b hb d (Nat.pos_of_ne_zero (NeZero.ne d)))
    (normalizedLatticeQuotient_injOn W b hb hΩ)

theorem normalizedCoveredChart_image (Ω : Set (EuclideanSpace ℝ D)) :
    normalizedCoveredChart W b hb bW d ''
      ((normalizedLatticePoint W b ⁻¹' Ω) ×ˢ Set.univ) =
    quotientIntegerCover (latticeSection (standardEuclideanLattice D) W).toAddSubgroup d ⁻¹'
      normalizedChartRegion W b hb Ω :=
  kernelLiftChart_relabel_image _ _ _
    (coverKernelBasisEquiv _ bW d (Nat.pos_of_ne_zero (NeZero.ne d))).toEquiv
    (normalizedCoverLift_projection W b hb d (Nat.pos_of_ne_zero (NeZero.ne d))) _

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.NormalizedCoveredDensity
namespace OAI

section

namespace Erdos3

open Module Submodule MeasureTheory
open scoped Classical

variable {D R : Type*} [Fintype D] [Fintype R] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D))

variable (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
variable (bW : Basis R ℤ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup)
variable (d : ℕ) [NeZero d]

theorem normalizedCoveredReference_restrict (Ω : Set (EuclideanSpace ℝ D)) :
    (normalizedCoveredReference (R := R) (n := n) W d).restrict
      ((normalizedLatticePoint W b ⁻¹' Ω) ×ˢ Set.univ) =
    (normalizedChartReference W b Ω).prod (PMF.uniformOfFintype (R → ZMod d)).toMeasure := by
  rw [normalizedCoveredReference, ← Measure.restrict_prod_eq_prod_univ, Measure.restrict_smul]
  rfl

variable [IsZLattice ℝ (latticeSection (standardEuclideanLattice D) W)]
variable (μ : Measure (W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup))
variable [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]

theorem normalizedCoveredChart_reference_map
    {Ω : Set (EuclideanSpace ℝ D)} (hΩm : MeasurableSet Ω)
    (hΩ : Ω ⊆ standardLatticeSmallBox D) :
    ((normalizedCoveredReference (R := R) (n := n) W d).restrict
      ((normalizedLatticePoint W b ⁻¹' Ω) ×ˢ Set.univ)).map
        (normalizedCoveredChart W b hb bW d) =
    μ.restrict (normalizedCoveredChart W b hb bW d ''
      ((normalizedLatticePoint W b ⁻¹' Ω) ×ˢ Set.univ)) := by
  rw [normalizedCoveredReference_restrict W b d Ω, normalizedCoveredChart_image]
  exact normalizedCoverResidues_reference W b hb μ bW d hΩm hΩ

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoveredJetChart
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped Classical

variable {m : ℕ} {O J B : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, Fintype (B j)]
variable {n : Fin m → ℕ} (U : ∀ j, Submodule ℝ (J j → ℝ))

variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (B j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

theorem coveredJetChart_continuous : Continuous (coveredJetChart (O := O) U b hb bW d) := by
  apply continuous_pi
  intro j
  apply continuous_pi
  intro t
  exact (normalizedCoveredChart_continuous _ (b j) (hb j) (bW j) d).comp
    ((continuous_apply t).comp (continuous_apply j))

theorem coveredJetChart_injOn (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j)))
    (hΩ : ∀ j t, Ω j t ⊆ standardLatticeSmallBox (J j)) :
    Set.InjOn (coveredJetChart U b hb bW d) (coveredJetSourceRegion U b d Ω) := by
  intro x hx y hy he
  funext j t
  exact normalizedCoveredChart_injOn _ (b j) (hb j) (bW j) d (hΩ j t)
    (hx j (Set.mem_univ j) t (Set.mem_univ t)) (hy j (Set.mem_univ j) t (Set.mem_univ t))
    (congrFun (congrFun he j) t)

variable [∀ j, Fintype (O j)]

omit [∀ j, Fintype (B j)] [NeZero d] in
theorem coveredJetSourceRegion_measurable (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j)))
    (hΩm : ∀ j t, MeasurableSet (Ω j t)) :
    MeasurableSet (coveredJetSourceRegion (B := B) U b d Ω) := by
  apply MeasurableSet.univ_pi
  intro j
  apply MeasurableSet.univ_pi
  intro t
  exact ((hΩm j t).preimage (normalizedLatticePoint_continuous _ (b j)).measurable).prod
    MeasurableSet.univ

theorem coveredJetChart_embedding (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j)))
    (hΩm : ∀ j t, MeasurableSet (Ω j t))
    (hΩ : ∀ j t, Ω j t ⊆ standardLatticeSmallBox (J j)) :
    MeasurableEmbedding (fun x : coveredJetSourceRegion (B := B) U b d Ω =>
      coveredJetChart U b hb bW d x.val) := by
  let : ∀ j, PolishSpace ((euclideanSubspace (U j) × (Fin (n j) → ℤ)) × (B j → ZMod d)) :=
    fun _ => inferInstance
  let : ∀ j, PolishSpace (O j → (euclideanSubspace (U j) × (Fin (n j) → ℤ)) × (B j → ZMod d)) :=
    fun _ => by constructor
  let : PolishSpace (CoveredJetChartSource U O B n d) := by constructor
  exact ContinuousOn.measurableEmbedding (coveredJetSourceRegion_measurable U b d Ω hΩm)
    (coveredJetChart_continuous U b hb bW d).continuousOn
    (coveredJetChart_injOn U b hb bW d Ω hΩ)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoveredJetReference
namespace OAI

section

namespace Erdos3

open MeasureTheory Module Submodule
open scoped Classical

theorem normalizedCoveredReference_sigmaFinite {D R : Type*} [Fintype D] [Fintype R]
    {n : ℕ} (W : Submodule ℝ (EuclideanSpace ℝ D))
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice D) W)] (d : ℕ) [NeZero d] :
    SigmaFinite (normalizedCoveredReference (R := R) (n := n) W d) := by
  have hc : (ENNReal.ofReal (ZLattice.covolume
      (latticeSection (standardEuclideanLattice D) W)))⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr (ZLattice.covolume_pos _ volume)).ne'
  let : SigmaFinite ((ENNReal.ofReal (ZLattice.covolume
      (latticeSection (standardEuclideanLattice D) W)))⁻¹ •
        ((volume : Measure W).prod (Measure.count : Measure (Fin n → ℤ)))) :=
    ennreal_smul_sigmaFinite ((volume : Measure W).prod (Measure.count : Measure (Fin n → ℤ))) _ hc
  unfold normalizedCoveredReference
  infer_instance

namespace VectorPolynomial

variable {m : ℕ} {O J B : Fin m → Type*}
variable [∀ j, Fintype (O j)] [∀ j, Fintype (J j)] [∀ j, Fintype (B j)]
variable {n : Fin m → ℕ} (U : ∀ j, Submodule ℝ (J j → ℝ))

variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (B j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

theorem coveredJetChart_reference_map (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j)))
    (hΩm : ∀ j t, MeasurableSet (Ω j t))
    (hΩ : ∀ j t, Ω j t ⊆ standardLatticeSmallBox (J j)) :
    ((coveredJetReference U d).restrict (coveredJetSourceRegion U b d Ω)).map
      (coveredJetChart U b hb bW d) =
    (Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))).restrict
      (coveredJetChart U b hb bW d '' coveredJetSourceRegion U b d Ω) := by
  let : ∀ j, SigmaFinite (normalizedCoveredReference (R := B j) (n := n j)
      (euclideanSubspace (U j)) d) := fun j => normalizedCoveredReference_sigmaFinite _ d
  let : ∀ j, BorelSpace (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup) :=
    fun _ => QuotientAddGroup.borelSpace
  let q := fun j => normalizedCoveredChart (euclideanSubspace (U j)) (b j) (hb j) (bW j) d
  have hq (j) : Measurable (q j) := (normalizedCoveredChart_continuous _ (b j) (hb j) (bW j) d).measurable
  unfold coveredJetReference coveredJetSourceRegion coveredJetChart
  refine piChart_reference_map
    (fun j => Measure.pi (fun _ : O j => normalizedCoveredReference (R := B j) (n := n j)
      (euclideanSubspace (U j)) d))
    (fun j => Measure.pi (fun _ : O j => ν j))
    (fun j (x : O j → (euclideanSubspace (U j) × (Fin (n j) → ℤ)) × (B j → ZMod d)) t => q j (x t))
    (fun j => measurable_pi_iff.mpr (fun t => (hq j).comp (measurable_pi_apply t))) _ ?_
  intro j
  refine piChart_reference_map
    (fun _ : O j => normalizedCoveredReference (R := B j) (n := n j) (euclideanSubspace (U j)) d)
    (fun _ : O j => ν j) (fun _ : O j => q j) (fun _ => hq j) _ ?_
  intro t
  exact normalizedCoveredChart_reference_map _ (b j) (hb j) (bW j) d (ν j) (hΩm j t) (hΩ j t)

end VectorPolynomial

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.CoveredJetSampler
namespace OAI

section

namespace Erdos3

open MeasureTheory Module Submodule
open scoped Classical Matrix

theorem mixedArrayIntegerImage_measurable {I Z J O : Type*} [Fintype J]
    (A : Matrix O J ℤ) :
    Measurable (mixedArrayIntegerImage (I := I) (Z := Z) A) := by
  unfold mixedArrayIntegerImage Matrix.mulVec dotProduct
  fun_prop

namespace VectorPolynomial

variable {m : ℕ} {O J I B : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

theorem mixedCoveredJetCoordinates_measurable (d : ℕ) :
    Measurable (mixedCoveredJetCoordinates (O := O) (B := B) (n := n) U o d) := by
  apply measurable_pi_iff.mpr
  intro j
  apply measurable_pi_iff.mpr
  intro t
  exact ((orthonormalMixedChart (o j)).measurable.comp
    (((measurable_pi_apply t).comp (mixedArrayRegroup _ _ _).measurable).comp
      ((measurable_pi_apply j).comp measurable_fst))).prodMk
    ((measurable_pi_apply t).comp ((measurable_pi_apply j).comp measurable_snd))

variable {α K : Type*} [Fintype α] [DecidableEq α] [Fintype K]
variable (root : K → ℤ) (A : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)

omit [∀ j, Fintype (I j)] [Fintype α] in
theorem canonicalCoefficientJetArrays_measurable :
    Measurable (canonicalCoefficientJetArrays (I := I) (n := n) root A rows) := by
  apply measurable_pi_iff.mpr
  intro j
  exact (mixedArrayIntegerImage_measurable
    (boundedCoefficientJetMatrix root A (j.val + 1) (rows j))).comp (measurable_pi_apply j)

variable [∀ j, Fintype (B j)]
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (B j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

theorem canonicalCoefficientDeckSample_chart (d : ℕ) [NeZero d]
    (x : CoefficientSamplerArrays (K := K) I n) (r : CoefficientDeckResidues (K := K) B d) :
    euclideanCoefficientJetMap U root A rows
      (canonicalCoefficientDeckSample U bW b hb o d (Nat.pos_of_ne_zero (NeZero.ne d)) x r) =
    coveredJetChart U b hb bW d (mixedCoveredJetCoordinates U o d
      (canonicalCoefficientJetArrays root A rows x, coefficientDeckJetMap root A rows d r)) := by
  funext j t
  exact canonicalCoefficientDeckSample_mixed_jets U b hb o root A rows bW d
    (Nat.pos_of_ne_zero (NeZero.ne d)) x r j t

variable [∀ j, Fintype (O j)]

end VectorPolynomial

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ProgressionTupleSliceSupport
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

namespace FiniteProbabilityWeights

theorem condition_weight_pos_iff {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (p : FiniteProbabilityWeights Ω) (S : Finset Ω) (hS : 0 < p.mass S) (x : Ω) :
    0 < (p.condition S hS).weight x ↔ x ∈ S ∧ 0 < p.weight x := by
  change 0 < (if x ∈ S then p.weight x else 0) / p.mass S ↔ _
  rw [lt_div_iff₀ hS, zero_mul]
  by_cases hx : x ∈ S <;> simp [hx]

theorem pi_weight_pos_component {J : Type*} [Fintype J] [DecidableEq J]
    {Ω : J → Type*} [∀ j, Fintype (Ω j)] (p : ∀ j, FiniteProbabilityWeights (Ω j))
    (x : ∀ j, Ω j) (hx : 0 < (pi p).weight x) (j : J) : 0 < (p j).weight (x j) := by
  apply lt_of_le_of_ne ((p j).nonneg (x j))
  intro he
  have hz : (pi p).weight x = 0 := by
    exact Finset.prod_eq_zero (Finset.mem_univ j) he.symm
  linarith

end FiniteProbabilityWeights

theorem scalarCubeResidueWeights_cube_support (I : Type*) [Fintype I] [DecidableEq I]
    (H M : ℕ) (hH : 0 < H) (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M)
    (hsize : (Fintype.card I + 1) * M ≤ H) (z : IntegerScalarCubeBox I H)
    (hz : 0 < (scalarCubeResidueWeights I H M hH m r hm hmM hsize).weight z) :
    IntegerScalarCube H (fun i => (z i : ℤ)) := by
  have h1 := (FiniteProbabilityWeights.condition_weight_pos_iff _ _ _ z).mp hz
  have h2 := (FiniteProbabilityWeights.condition_weight_pos_iff _ _ _ z).mp h1.2
  exact (mem_integerScalarCubeSet H z).mp h2.1

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ContainedProgressionCubeMap
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem containedProgressionCubeMap_value (I : Type*) [Fintype I] [DecidableEq I]
    (L H step : ℕ) (c : ℤ) (hL : 0 < L)
    (hsubset : integerProgressionSupport c (step : ℤ) H ⊆ Finset.Ico (0 : ℤ) (L : ℤ))
    (z : IntegerScalarCubeBox I H) (hz : IntegerScalarCube H (fun i => (z i : ℤ)))
    (i : Option I) :
    (containedProgressionCubeMap I L H step c hL hsubset z i : ℤ) =
      (if i = none then c else 0) + (step : ℤ) * (z i : ℤ) := by
  rw [containedProgressionCubeMap, dif_pos hz]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.FiniteGoodSupport
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

variable {X : Type*} [Fintype X] (p : FiniteProbabilityWeights X)

theorem mean_congr_on_support {f g : X → ℝ}
    (h : ∀ x, p.weight x ≠ 0 → f x = g x) : p.mean f = p.mean g :=
  le_antisymm (p.mean_mono_on_support (fun x hx => (h x hx).le))
    (p.mean_mono_on_support (fun x hx => (h x hx).ge))

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

variable {X Y : Type*} (q : X → Y) (S : Set X) (hinj : Set.InjOn q S)

include hinj

theorem restrictedChartDensity_eq_of_values (g : Y → ℝ) (f : X → ℝ)
    (hvalue : ∀ x ∈ S, g (q x) = f x) (hzero : ∀ y ∉ q '' S, g y = 0) :
    g = restrictedChartDensity q S 1 f := by
  funext y
  by_cases hy : y ∈ q '' S
  · obtain ⟨x, hx, rfl⟩ := hy
    rw [restrictedChartDensity_apply q S 1 f hinj hx, one_mul, hvalue x hx]
  · rw [hzero y hy, restrictedChartDensity_zero q S 1 f hy]

end Erdos3

end

section

namespace Erdos3

variable {X Y : Type*} (q : X → Y) (S : Set X) (hinj : Set.InjOn q S)

include hinj

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped Classical

end Erdos3.FiniteProbabilityWeights

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedCoefficientSampler
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)

theorem allocatedCoefficientSource_probability :
    IsProbabilityMeasure (allocatedCoefficientSource B U b hR hσ S) := by
  let : ∀ j, IsProbabilityMeasure (mixedScalarArrayLaw (allocatedLayerCenters B U b S j)
      (allocatedLayerWidths B U b S j) (allocatedLayerIntegerPMFs B U b hR hσ S j)) :=
    fun j => mixedScalarArrayLaw_probability _ _ (allocatedLayerWidths_pos B U b hR hσ S j) _
  exact Measure.pi.instIsProbabilityMeasure _

variable (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hsmall : ∀ j, C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

include hσ1 C hC hchart hsmall ν

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedEnormousProfiles
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {D α : Type*} {B : D → Type*} {h : D → ℕ}

variable [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped Classical

variable {D α : Type*} [Fintype α] [DecidableEq α]
variable (B : D → Type*) (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (c : PrincipalTupleIndex B h → ℤ)
variable (hL : ∀ j, 0 < L j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (L j : ℤ))

end Erdos3

end

section

namespace Erdos3

variable {D G Z α : Type*} {B : D → Type*} {h : D → ℕ}

theorem partitionedPrincipalInput_value (P : D → Prop) [DecidablePred P]
    (extra : G → Option α → Z) (z : Z → ℤ) {L : PrincipalTupleIndex B h → ℕ}
    (u : PrincipalAxisTuples (α := α) P L) (v : PrincipalAxisTuples (α := α) (fun d => ¬P d) L)
    (k : SamplerTupleIndex G B h) (a : Option α) :
    Sum.elim (Sum.elim z (principalTupleIntegers u)) (principalTupleIntegers v)
        (partitionedPrincipalInput P extra k a) =
      Sum.elim z (principalTupleIntegers (principalAxisJoin P u v)) (canonicalTupleInput extra k a) := by
  rcases k with g | ⟨d, b, r⟩
  · rfl
  · by_cases hp : P d <;>
      simp [partitionedPrincipalInput, canonicalTupleInput, principalTupleIntegers, principalAxisJoin, hp]

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix

variable {m : ℕ} {I : Fin m → Type*} {n : Fin m → ℕ}
variable {G : Type*} [Fintype G] [∀ j, Fintype (I j)]
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "degree" => layerSamplerDegree I n

section Law

variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]

end Law

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)


theorem allocatedCoefficientAxisLaw_probability (a : LayerSamplerAxis I n) :
    IsProbabilityMeasure (allocatedCoefficientAxisLaw B U basis hR hσ S a) :=
  coefficientAxisLaw_probability _ _ _ (allocatedLayerWidths_pos B U basis hR hσ S) a

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

variable (j : Fin m) (i : Fin (n j)) (hσ1 : σ j ≤ 1)
variable (henormous : S.value^(layerTailDegree m+1) < basisAxisScale (basis j) i)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PhysicalSpatialScales
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory
open scoped BigOperators NNReal

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

theorem trimmedSpatial_scale_lower {X : Type*} {B τ ρ : ℝ}
    (hB : 0 ≤ B) (hρ : 0 ≤ ρ) (N modulus : X → ℕ) (x : X) (hq : 0 < modulus x)
    (hlarge : 8 * (1 + B) * (modulus x : ℝ) * ρ ≤ τ * (N x : ℝ)) :
    ρ ≤ trimmedSpatialRootScale τ N modulus x ∧ ρ ≤ trimmedSpatialSlopeScale B τ N modulus x := by
  have hq' : (0 : ℝ) < modulus x := by exact_mod_cast hq
  have hb : (0 : ℝ) < 8 * (1 + B) := by positivity
  have hs : ρ ≤ trimmedSpatialSlopeScale B τ N modulus x := by
    unfold trimmedSpatialSlopeScale
    apply (le_div_iff₀ hq').mpr
    apply (le_div_iff₀ hb).mpr
    nlinarith [hlarge]
  refine ⟨?_, hs⟩
  unfold trimmedSpatialRootScale
  apply (le_div_iff₀ hq').mpr
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 8)).mpr
  nlinarith [mul_nonneg hB (mul_nonneg hq'.le hρ)]

end Erdos3.BooleanCubeKernel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SeparatedChartExtension
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem exists_complex_extension_of_distance_bound
    {A Y : Type*} [PseudoMetricSpace Y] (embed : A → Y) (f : A → ℂ) (L B : ℝ≥0)
    (hf : ∀ a b, dist (f a) (f b) ≤ L * dist (embed a) (embed b))
    (hb : ∀ a, ‖f a‖ ≤ B) :
    ∃ g : Y → ℂ, LipschitzWith (2 * L) g ∧ (∀ a, g (embed a) = f a) ∧
      ∀ y, ‖g y‖ ≤ 2 * B := by
  classical
  let S := Set.range embed
  let pre (y : S) : A := Classical.choose y.property
  have hpre (y : S) : embed (pre y) = y.val := Classical.choose_spec y.property
  have hF : LipschitzWith L (fun y : S => f (pre y)) := by
    apply LipschitzWith.of_dist_le_mul
    intro y z
    have h := hf (pre y) (pre z)
    rw [hpre y, hpre z] at h
    exact h
  obtain ⟨g, hg, heq, hgb⟩ := exists_complex_extension_from_subset S
    (fun y => f (pre y)) L B hF (fun y => hb (pre y))
  refine ⟨g, hg, ?_, hgb⟩
  intro a
  let y : S := ⟨embed a, ⟨a, rfl⟩⟩
  have hzero : dist (f (pre y)) (f a) ≤ 0 := by
    have h := hf (pre y) a
    rw [hpre y] at h
    simpa only [y, dist_self, mul_zero] using h
  exact (heq y).trans (dist_le_zero.mp hzero)

theorem exists_bounded_extension_on_separated_charts
    {A X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (chart : A → X → Y) (S : Set X) (K D L B : ℝ≥0)
    (hwithin : ∀ a x, x ∈ S → ∀ y, y ∈ S → dist x y ≤ K * dist (chart a x) (chart a y))
    (hsep : ∀ a b, a ≠ b → ∀ x, x ∈ S → ∀ y, y ∈ S →
      (1 : ℝ) ≤ D * dist (chart a x) (chart b y))
    (f : A → X → ℂ) (hf : ∀ a, LipschitzOnWith L (f a) S)
    (hb : ∀ a x, x ∈ S → ‖f a x‖ ≤ B) :
    ∃ g : Y → ℂ, LipschitzWith (2 * max (L * K) (2 * B * D)) g ∧
      (∀ a x, x ∈ S → g (chart a x) = f a x) ∧ ∀ y, ‖g y‖ ≤ 2 * B := by
  let P := {p : A × X // p.2 ∈ S}
  let embed : P → Y := fun p => chart p.val.1 p.val.2
  let F : P → ℂ := fun p => f p.val.1 p.val.2
  let C := max (L * K) (2 * B * D)
  have hLC : ((L * K : ℝ≥0) : ℝ) ≤ C := by exact_mod_cast le_max_left (L * K) (2 * B * D)
  have hDC : ((2 * B * D : ℝ≥0) : ℝ) ≤ C := by exact_mod_cast le_max_right (L * K) (2 * B * D)
  have hF (p q : P) : dist (F p) (F q) ≤ C * dist (embed p) (embed q) := by
    rcases p with ⟨⟨a, x⟩, hx⟩
    rcases q with ⟨⟨b, y⟩, hy⟩
    change dist (f a x) (f b y) ≤ C * dist (chart a x) (chart b y)
    by_cases hab : a = b
    · subst b
      calc
        _ ≤ (L : ℝ) * dist x y := (hf a).dist_le_mul x hx y hy
        _ ≤ (L : ℝ) * (K * dist (chart a x) (chart a y)) :=
          mul_le_mul_of_nonneg_left (hwithin a x hx y hy) L.coe_nonneg
        _ = ((L * K : ℝ≥0) : ℝ) * dist (chart a x) (chart a y) := by
          rw [NNReal.coe_mul, mul_assoc]
        _ ≤ _ := mul_le_mul_of_nonneg_right hLC dist_nonneg
    · have hs := hsep a b hab x hx y hy
      have hn : dist (f a x) (f b y) ≤ 2 * (B : ℝ) := by
        rw [dist_eq_norm]
        exact (norm_sub_le _ _).trans (by linarith [hb a x hx, hb b y hy])
      calc
        _ ≤ 2 * (B : ℝ) := hn
        _ ≤ (2 * (B : ℝ)) * (D * dist (chart a x) (chart b y)) := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 2 * (B : ℝ))
        _ = ((2 * B * D : ℝ≥0) : ℝ) * dist (chart a x) (chart b y) := by
          simp only [NNReal.coe_mul, NNReal.coe_ofNat]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hDC dist_nonneg
  obtain ⟨g, hg, heq, hgb⟩ := exists_complex_extension_of_distance_bound embed F C B hF
    (fun p => hb p.val.1 p.val.2 p.property)
  exact ⟨g, hg, fun a x hx => heq ⟨(a, x), hx⟩, hgb⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LayeredCoverSiteExtension
namespace OAI

section

namespace Erdos3

open scoped NNReal

variable (q : ℕ) [NeZero q]

theorem circleQuarterCover_zero (a : ZMod q) :
    circleQuarterCover q a 0 = ZMod.toAddCircle a := by
  simp only [circleQuarterCover, zero_div, AddCircle.coe_zero, add_zero]

theorem circleQuarterCover_dist (a : ZMod q) {x y : ℝ}
    (hx : |x| ≤ 1 / 4) (hy : |y| ≤ 1 / 4) :
    (q : ℝ) * dist (circleQuarterCover q a x) (circleQuarterCover q a y) = dist x y := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hxy : |x - y| ≤ 1 / 2 := by
    have htri : |x - y| ≤ |x| + |y| := by
      simpa only [sub_eq_add_neg, abs_neg] using abs_add_le x (-y)
    linarith
  have hsmall : |(x - y) / q| ≤ 1 / 2 := by
    rw [abs_div, abs_of_pos hq]
    exact (div_le_iff₀ hq).mpr (hxy.trans (by linarith))
  have hn : ‖(((x - y) / q : ℝ) : UnitAddCircle)‖ = |(x - y) / q| :=
    (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) (by norm_num)).mpr (by simpa using hsmall)
  unfold circleQuarterCover
  rw [dist_add_left, dist_eq_norm, ← AddCircle.coe_sub, ← sub_div, hn,
    abs_div, abs_of_pos hq, mul_div_cancel₀ _ hq.ne', Real.dist_eq]

theorem circleQuarterCover_center_dist (a : ZMod q) {x : ℝ} (hx : |x| ≤ 1 / 4) :
    (q : ℝ) * dist (circleQuarterCover q a x) (ZMod.toAddCircle a) ≤ 1 / 4 := by
  have h := circleQuarterCover_dist q a hx (by norm_num : |(0 : ℝ)| ≤ 1 / 4)
  rw [circleQuarterCover_zero, Real.dist_eq, sub_zero] at h
  exact h.le.trans hx

theorem circleQuarterCover_separated {a b : ZMod q} (hab : a ≠ b) {x y : ℝ}
    (hx : |x| ≤ 1 / 4) (hy : |y| ≤ 1 / 4) :
    (1 : ℝ) ≤ (2 * q) * dist (circleQuarterCover q a x) (circleQuarterCover q b y) := by
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have ha := circleQuarterCover_center_dist q a hx
  have hb := circleQuarterCover_center_dist q b hy
  rw [dist_comm] at ha
  have ht : dist (ZMod.toAddCircle a) (ZMod.toAddCircle b) ≤
      dist (ZMod.toAddCircle a) (circleQuarterCover q a x) +
        dist (circleQuarterCover q a x) (circleQuarterCover q b y) +
          dist (circleQuarterCover q b y) (ZMod.toAddCircle b) := by
    linarith [dist_triangle (ZMod.toAddCircle a) (circleQuarterCover q a x) (ZMod.toAddCircle b),
      dist_triangle (circleQuarterCover q a x) (circleQuarterCover q b y) (ZMod.toAddCircle b)]
  have hs := CircleFourier.one_le_mul_dist_toAddCircle hab
  have hm := mul_le_mul_of_nonneg_left ht hq
  nlinarith

theorem quarterCoverPoint_intCast {D : Type*} (a : D → ℤ) (x : D → ℝ) :
    quarterCoverPoint q (fun i => (a i : ZMod q)) x =
      fun i => ((((a i : ℝ) + x i) / q : ℝ) : UnitAddCircle) := by
  funext i
  change ZMod.toAddCircle (a i : ZMod q) + ((x i / q : ℝ) : UnitAddCircle) = _
  rw [ZMod.toAddCircle_intCast, ← AddCircle.coe_add, ← add_div]

theorem quarterCoverPoint_within {D : Type*} [Fintype D] (a : D → ZMod q) {x y : D → ℝ}
    (hx : ∀ i, |x i| ≤ 1 / 4) (hy : ∀ i, |y i| ≤ 1 / 4) :
    dist x y ≤ (q : ℝ) * dist (quarterCoverPoint q a x) (quarterCoverPoint q a y) := by
  apply (dist_pi_le_iff (mul_nonneg (Nat.cast_nonneg q) dist_nonneg)).mpr
  intro i
  calc
    dist (x i) (y i) = (q : ℝ) * dist (circleQuarterCover q (a i) (x i))
        (circleQuarterCover q (a i) (y i)) := (circleQuarterCover_dist q (a i) (hx i) (hy i)).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (dist_le_pi_dist (quarterCoverPoint q a x) (quarterCoverPoint q a y) i) (Nat.cast_nonneg q)

theorem quarterCoverPoint_separated {D : Type*} [Fintype D] {a b : D → ZMod q} (hab : a ≠ b)
    {x y : D → ℝ} (hx : ∀ i, |x i| ≤ 1 / 4) (hy : ∀ i, |y i| ≤ 1 / 4) :
    (1 : ℝ) ≤ (2 * q) * dist (quarterCoverPoint q a x) (quarterCoverPoint q b y) := by
  obtain ⟨i, hi⟩ := not_forall.mp (fun h : ∀ i, a i = b i => hab (funext h))
  exact (circleQuarterCover_separated q hi (hx i) (hy i)).trans
    (mul_le_mul_of_nonneg_left
      (dist_le_pi_dist (quarterCoverPoint q a x) (quarterCoverPoint q b y) i) (by positivity))

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem exists_quarter_cover_extension {D : Type*} [Fintype D] (q : ℕ) [NeZero q]
    (f : (D → ZMod q) → (D → ℝ) → ℂ) (L B : ℝ≥0)
    (hf : ∀ a, LipschitzWith L (f a)) (hb : ∀ a x, ‖f a x‖ ≤ B) :
    ∃ g : (D → UnitAddCircle) → ℂ,
      LipschitzWith (2 * max (L * q) (4 * B * q)) g ∧
      (∀ a x, (∀ i, |x i| ≤ 1 / 4) → g (quarterCoverPoint q a x) = f a x) ∧
      ∀ y, ‖g y‖ ≤ 2 * B := by
  obtain ⟨g, hg, hvalue, hbound⟩ := exists_bounded_extension_on_separated_charts
    (quarterCoverPoint (D := D) q) {x | ∀ i, |x i| ≤ 1 / 4}
    (q : ℝ≥0) (2 * q) L B
    (fun a x hx y hy => quarterCoverPoint_within q a hx hy)
    (by
      intro a b hab x hx y hy
      simpa using quarterCoverPoint_separated q hab hx hy)
    f (fun a => (hf a).lipschitzOnWith) (fun a x _ => hb a x)
  refine ⟨g, ?_, hvalue, hbound⟩
  have heq : 2 * B * (2 * (q : ℝ≥0)) = 4 * B * q := by ring
  simpa only [heq] using hg

theorem exists_integer_quarter_cover_extension {D : Type*} [Fintype D] (q : ℕ) [NeZero q]
    (f : (D → ZMod q) → (D → ℝ) → ℂ) (L B : ℝ≥0)
    (hf : ∀ a, LipschitzWith L (f a)) (hb : ∀ a x, ‖f a x‖ ≤ B) :
    ∃ g : (D → UnitAddCircle) → ℂ,
      LipschitzWith (2 * max (L * q) (4 * B * q)) g ∧ (∀ y, ‖g y‖ ≤ 2 * B) ∧
      ∀ (a : D → ℤ) (x : D → ℝ), (∀ i, |x i| ≤ 1 / 4) →
        g (fun i => ((((a i : ℝ) + x i) / q : ℝ) : UnitAddCircle)) = f (fun i => (a i : ZMod q)) x := by
  obtain ⟨g, hg, hvalue, hbound⟩ := exists_quarter_cover_extension q f L B hf hb
  refine ⟨g, hg, hbound, ?_⟩
  intro a x hx
  rw [← quarterCoverPoint_intCast]
  exact hvalue (fun i => (a i : ZMod q)) x hx

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open Module Submodule
open scoped BigOperators Matrix NNReal Classical

variable {D I : Type*} [Fintype D] [DecidableEq D] [Fintype I] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D))
variable (bW : Basis I ℤ (latticeSection (standardEuclideanLattice D) W))
variable (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
variable (q : ℕ) [NeZero q]

end Erdos3

end

section

namespace Erdos3

open Module Submodule

theorem exists_covered_representative_offset
    {D E : Type*} [Fintype D] [Fintype E] {n : ℕ}
    (W : Submodule ℝ (EuclideanSpace ℝ D))
    (bW : Basis E ℤ (latticeSection (standardEuclideanLattice D) W))
    (b : Basis (Fin n) ℝ Wᗮ)
    (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
    (d : ℕ) [NeZero d] (u : W) (x : W × (Fin n → ℤ)) (r : E → ZMod d)
    (hu : (QuotientAddGroup.mk u : W ⧸
      (latticeSection (standardEuclideanLattice D) W).toAddSubgroup) =
        normalizedCoveredChart W b hb bW d (x, r)) :
    ∃ w : E → ℤ, normalizedLatticeRepresentative W b hb x + (bW.equivFun.symm w).val =
        (d : ℝ) • u ∧ integerResidueMap E d w = r := by
  let Γ := (latticeSection (standardEuclideanLattice D) W).toAddSubgroup
  let e := coverKernelBasisEquiv Γ bW d (NeZero.pos d)
  have hp := congrArg (quotientIntegerCover Γ d) hu
  change quotientIntegerCover Γ d (QuotientAddGroup.mk' Γ u) =
    quotientIntegerCover Γ d (normalizedCoverLift W b hb d x + (e r).val) at hp
  rw [quotientIntegerCover_mk, map_add, (e r).property, add_zero,
    normalizedCoverLift_projection W b hb d (NeZero.pos d)] at hp
  obtain ⟨w, hw⟩ := exists_normalized_representative_offset W bW b hb ((d : ℝ) • u) x hp
  refine ⟨w, hw, ?_⟩
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have he := normalizedCoverLift_add_deck W bW b hb d (NeZero.pos d) x w
  rw [hw, smul_smul, inv_mul_cancel₀ hd0, one_smul] at he
  have hsum : normalizedCoverLift W b hb d x + (e (integerResidueMap E d w)).val =
      normalizedCoverLift W b hb d x + (e r).val := he.trans hu
  apply e.injective
  exact Subtype.ext (add_left_cancel hsum)

end Erdos3

end

section

namespace Erdos3

open Module Submodule
open scoped NNReal Classical

variable {M : Type*} [Fintype M] {D E : M → Type*}
variable [∀ j, Fintype (D j)] [∀ j, DecidableEq (D j)] [∀ j, Fintype (E j)]
variable {n : M → ℕ}
variable (W : ∀ j, Submodule ℝ (EuclideanSpace ℝ (D j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (D j)) (W j)))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (W j)ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (W j))
variable (q : ℕ) [NeZero q]


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

variable {m : ℕ} {I O J E : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

variable [∀ j, Fintype (E j)]
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

theorem mixedCoveredJetChart_injOn (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j)))
    (hΩ : ∀ j t, Ω j t ⊆ standardLatticeSmallBox (J j)) :
    Set.InjOn (mixedCoveredJetChart U o b hb bW d) (mixedCoveredJetRegion U o b d Ω) := by
  intro z hz w hw he
  apply (mixedCoveredJetCoordinatesEquiv U o d).injective
  exact coveredJetChart_injOn U b hb bW d Ω hΩ hz hw he

theorem mixedCoveredJetChart_image (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j))) :
    mixedCoveredJetChart U o b hb bW d '' mixedCoveredJetRegion U o b d Ω =
      coveredJetChart U b hb bW d '' coveredJetSourceRegion U b d Ω := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨mixedCoveredJetCoordinates U o d z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨w, hw⟩ := (mixedCoveredJetCoordinatesEquiv (O := O) (E := E) (n := n) U o d).surjective z
    refine ⟨w, ?_, ?_⟩
    · change mixedCoveredJetCoordinates U o d w ∈ coveredJetSourceRegion U b d Ω
      change mixedCoveredJetCoordinates U o d w = z at hw
      rwa [hw]
    · change coveredJetChart U b hb bW d (mixedCoveredJetCoordinates U o d w) = _
      exact congrArg (coveredJetChart U b hb bW d) hw

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.MixedCoveredIntegerReconstruction
namespace OAI

section

namespace Erdos3

open Module Submodule
open scoped BigOperators

variable {D Q : Type*} [Fintype D] [Fintype Q] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
variable (bW : Basis Q ℤ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup)
variable (d : ℕ) [NeZero d]

theorem normalizedCoveredChart_sum_zsmul {S : Type*} (s : Finset S)
    (a : S → ℤ) (x : S → W × (Fin n → ℤ)) (r : S → Q → ZMod d) :
    normalizedCoveredChart W b hb bW d (∑ i ∈ s, a i • x i, ∑ i ∈ s, a i • r i) =
      ∑ i ∈ s, a i • normalizedCoveredChart W b hb bW d (x i, r i) := by
  let Γ := (latticeSection (standardEuclideanLattice D) W).toAddSubgroup
  let e := coverKernelBasisEquiv Γ bW d (Nat.pos_of_ne_zero (NeZero.ne d))
  let deck : (Q → ZMod d) →+ W ⧸ Γ := (quotientIntegerCover Γ d).ker.subtype.comp e.toAddMonoidHom
  change normalizedCoverLift W b hb d (∑ i ∈ s, a i • x i) + deck (∑ i ∈ s, a i • r i) =
    ∑ i ∈ s, a i • (normalizedCoverLift W b hb d (x i) + deck (r i))
  rw [normalizedCoverLift_sum_zsmul]
  simp only [map_sum, map_zsmul, smul_add, Finset.sum_add_distrib]

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical

variable {m : ℕ} {I O P J Q : Fin m → Type*} {n : Fin m → ℕ}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (O j)] [∀ j, Fintype (J j)] [∀ j, Fintype (Q j)]

variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

theorem mixedCoveredJetIntegerImage_chart
    (A : ∀ j, Matrix (P j) (O j) ℤ) (z : MixedCoveredJetSource I O Q n d)
    (j : Fin m) (t : P j) :
    mixedCoveredJetChart U o b hb bW d (mixedCoveredJetIntegerImage d A z) j t =
      ∑ r, A j t r • mixedCoveredJetChart U o b hb bW d z j r := by
  change normalizedCoveredChart (euclideanSubspace (U j)) (b j) (hb j) (bW j) d
    (orthonormalMixedChart (o j) (mixedArrayRegroup _ _ _ (mixedArrayIntegerImage (A j) (z.1 j)) t),
      fun k => ∑ r, A j t r • z.2 j r k) = _
  rw [mixedArrayIntegerImage_regroup, orthonormalMixedChart_sum_zsmul]
  have hdeck : (fun k => ∑ r, A j t r • z.2 j r k) = ∑ r, A j t r • z.2 j r := by
    funext k
    simp only [Finset.sum_apply, Pi.smul_apply]
  rw [hdeck]
  exact normalizedCoveredChart_sum_zsmul (euclideanSubspace (U j)) (b j) (hb j) (bW j) d
      Finset.univ (A j t) (fun r => orthonormalMixedChart (o j) (mixedArrayRegroup _ _ _ (z.1 j) r))
      (z.2 j)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RowRestrictedDeckSiteMask
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical Matrix

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {α K : Type*} [DecidableEq α] [Fintype K]
variable {m : ℕ} {O B : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Fintype (B j)]
variable (root : K → ℤ) (D : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)
variable (d period : ℕ) [NeZero d]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical Matrix

variable {α K : Type*} [Fintype α] [DecidableEq α] [Fintype K]
variable {m : ℕ} {O B : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Fintype (B j)]
variable (root : K → ℤ) (D : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)
variable (d period : ℕ) [NeZero d] [NeZero period]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical

variable {m : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
variable {I J Q : Fin m → Type*} {n : Fin m → ℕ}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)] [∀ j, Fintype (Q j)]


variable (U : ∀ j, Submodule ℝ (J j → ℝ))

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped BigOperators Matrix Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

namespace VectorPolynomial

open Module Submodule

variable {m : ℕ} {I J E : Fin m → Type*} {n : Fin m → ℕ}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)] [∀ j, Fintype (E j)]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rows" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})

variable (U : ∀ j, Submodule ℝ (J j → ℝ))

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

omit [Fintype α] in
theorem mixedCoveredRowsSiteValue_chart (z : MixedCoveredJetSource I rows E n d) (s : Finset α) :
    mixedCoveredJetChart U o b hb bW d (mixedCoveredRowsSiteValue rowSets d z s) =
      coveredRowsSiteValue rowSets U (mixedCoveredJetChart U o b hb bW d z) s := by
  funext j t
  exact mixedCoveredJetIntegerImage_chart U o b hb bW d
    (fun j (_ : Unit) => rowRestrictedSiteMatrix (rowSets j) s) z j t

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped Classical BigOperators Matrix

variable {α K : Type*} [Fintype α] [DecidableEq α] [Fintype K]
variable {m : ℕ} {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (root : K → ℤ) (D : Matrix α K ℤ)
variable (d period : ℕ) [NeZero d] [NeZero period]

local notation "jets" => (fun j : Fin m => BoundedBooleanJet α (Fin.val j + 1))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped BigOperators Classical

namespace VectorPolynomial

variable {m : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))


end VectorPolynomial
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

namespace VectorPolynomial

variable {K : Type*} [Fintype K] {m : ℕ}
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (root : K → ℤ) (D : Matrix α K ℤ)
variable (rowSets : Fin m → Finset (Finset α))
variable (d period : ℕ) [NeZero d] [NeZero period]

local notation "rows" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})

end VectorPolynomial
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedFixedKernelCover
namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α]
variable (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox α S.value)
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))

theorem allocatedPhysicalCube_vertex (t : Finset α) :
    integerAffineCube (allocatedPhysicalCubeRoot B U basis S c x y)
        (allocatedPhysicalCubeDirections B U basis S x y) t =
      fun k => c k + Sum.elim
        (fun g => integerScalarCubeValue (fun i => (x g i : ℤ)) t)
        (fun j => integerScalarCubeValue (fun i => (y j i : ℤ)) t) k := by
  funext k
  cases k <;> simp only [integerAffineCube, allocatedPhysicalCubeRoot,
    allocatedPhysicalCubeDirections, Sum.elim_inl, Sum.elim_inr, integerScalarCubeValue] <;> ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped BigOperators

namespace VectorPolynomial

open BooleanCubeKernel Polynomial

end VectorPolynomial
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedKernelScaleWithCutoff
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix

theorem kernelExponent_eval_monomial {G X : Type*} {h : ℕ} (x : G ⊕ X → ℤ)
    (d : BoundedIntegerExponent G h) :
    MvPolynomial.eval x (MvPolynomial.monomial (kernelExponentEmbedding G X h d).val 1) =
      MvPolynomial.eval (fun g => x (.inl g)) (MvPolynomial.monomial d.val 1) := by
  change MvPolynomial.eval x (MvPolynomial.monomial (d.val.embDomain Function.Embedding.inl) 1) = _
  simp only [MvPolynomial.eval_monomial, Finsupp.prod_embDomain]
  rfl

theorem integerMappedCubeTuple_kernel {G X Z Y α : Type*}
    (input : G ⊕ X → Option α → Z ⊕ Y) (z : Z → ℤ) (y : Y → ℤ)
    {L : ℕ} (x : G → IntegerScalarCubeBox α L)
    (hfixed : ∀ g a, Sum.elim z y (input (.inl g) a) = (x g a : ℤ)) (t : Finset α) :
    (fun g => integerMappedCubeTuple input z y t (.inl g)) =
      integerAffineCube (fun g => (x g none : ℤ)) (scalarCubeDifferenceMatrix x) t := by
  funext g
  simp only [integerMappedCubeTuple, integerAffineCube, hfixed, scalarCubeDifferenceMatrix, sampledColumnMatrix]

theorem integerMappedJetMatrix_kernel {G X Z Y α O : Type*} [Fintype G] [DecidableEq α]
    (h : ℕ) (input : G ⊕ X → Option α → Z ⊕ Y) (z : Z → ℤ) (y : Y → ℤ)
    {L : ℕ} (x : G → IntegerScalarCubeBox α L)
    (hfixed : ∀ g a, Sum.elim z y (input (.inl g) a) = (x g a : ℤ)) (rows : O → Finset α) :
    (integerMappedJetMatrix (fun d : BoundedCoefficientExponent (G ⊕ X) h => d.val)
      input z rows y).submatrix id (kernelExponentEmbedding G X h) = scalarKernelIntegerJet x h rows := by
  ext o d
  change booleanCoefficient (fun t => MvPolynomial.eval (integerMappedCubeTuple input z y t)
      (MvPolynomial.monomial (kernelExponentEmbedding G X h d).val 1)) (rows o) =
    booleanCoefficient (fun t => MvPolynomial.eval
      (integerAffineCube (fun g => (x g none : ℤ)) (scalarCubeDifferenceMatrix x) t)
      (MvPolynomial.monomial d.val 1)) (rows o)
  apply congrArg (fun f : Finset α → ℤ => booleanCoefficient f (rows o))
  funext t
  rw [kernelExponent_eval_monomial, integerMappedCubeTuple_kernel input z y x hfixed t]

theorem integerMappedJetMatrix_kernel_split {G X Z Y α O : Type*} [Fintype G] [DecidableEq α]
    (h : ℕ) (input : G ⊕ X → Option α → Z ⊕ Y) (z : Z → ℤ) (y : Y → ℤ)
    {L : ℕ} (x : G → IntegerScalarCubeBox α L)
    (hfixed : ∀ g a, Sum.elim z y (input (.inl g) a) = (x g a : ℤ)) (rows : O → Finset α) :
    (integerMappedJetMatrix (fun d : BoundedCoefficientExponent (G ⊕ X) h => d.val)
      input z rows y).submatrix id (kernelCoefficientEquiv G X h) =
      Matrix.fromCols (scalarKernelIntegerJet x h rows)
        (integerMappedJetMatrix (fun d : NonkernelCoefficient G X h => d.val.val) input z rows y) := by
  ext o d
  cases d with
  | inl d => exact congrFun (congrFun (integerMappedJetMatrix_kernel h input z y x hfixed rows) o) d
  | inr d => rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open MeasureTheory
open scoped Matrix NNReal

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

variable (j : Fin m) (i : Fin (n j)) (hσ1 : σ j ≤ 1)
variable (henormous : S.value^(layerTailDegree m+1) < basisAxisScale (basis j) i)

local notation "reindex" => allocatedKernelCoefficientEquiv (G := G) B j

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)

theorem allocatedKernelJet_split {α O : Type*} [DecidableEq α]
    (x : G → IntegerScalarCubeBox α S.value)
    (u : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) grid → ℤ)
    (v : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) (fun a => ¬grid a) → ℤ)
    (rows : O → Finset α) :
    (integerMappedJetMatrix (fun d : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1) => d.val)
      (partitionedPrincipalInput grid (fun g a => (g, a)))
      (Sum.elim (fun ga : G × Option α => (x ga.1 ga.2 : ℤ)) u) rows v).submatrix id reindex =
      Matrix.fromCols (scalarKernelIntegerJet x (j.val+1) rows)
        (integerMappedJetMatrix (allocatedNonkernelExponent B j)
          (partitionedPrincipalInput grid (fun g a => (g, a)))
          (Sum.elim (fun ga : G × Option α => (x ga.1 ga.2 : ℤ)) u) rows v) :=
  integerMappedJetMatrix_kernel_split (j.val+1) _ _ _ x (fun _ _ => rfl) rows

theorem allocatedKernelJet_full_image {α O : Type*} [DecidableEq α]
    (x : G → IntegerScalarCubeBox α S.value)
    (u : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) grid → ℤ)
    (v : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) (fun a => ¬grid a) → ℤ)
    (rows : O → Finset α) :
    (Matrix.fromCols (scalarKernelIntegerJet x (j.val+1) rows)
      (integerMappedJetMatrix (allocatedNonkernelExponent B j)
        (partitionedPrincipalInput grid (fun g a => (g, a)))
        (Sum.elim (fun ga : G × Option α => (x ga.1 ga.2 : ℤ)) u) rows v)).mulVecLin.range =
      (integerMappedJetMatrix (fun d : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1) => d.val)
        (partitionedPrincipalInput grid (fun g a => (g, a)))
        (Sum.elim (fun ga : G × Option α => (x ga.1 ga.2 : ℤ)) u) rows v).mulVecLin.range := by
  rw [← allocatedKernelJet_split B U basis S j x u v rows]
  exact integerColumnEquiv_range _ reindex

end Erdos3.VectorPolynomial

end

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

include hR hσ in
theorem allocatedContinuousProfileWidths_pos (j : Fin m) (i : I j) (d) :
    0 < allocatedContinuousProfileWidths (G := G) B R σ j i d :=
  coefficientProfileWidth_pos _ _ (div_pos (hR j) (by norm_num))
    (principalProfileSize_pos (hR j) _) (tailProfileSize_pos (hR j) (hσ j) _) d

include hR hσ in
theorem allocatedContinuousProfile_bound (j : Fin m) (i : I j) (hσ1 : σ j ≤ 1) (d) :
    |allocatedContinuousProfileCenters (G := G) B R j i d| +
      allocatedContinuousProfileWidths B R σ j i d ≤ R j :=
  (allocatedProfile_term_bound (layerContinuousPrincipalSlots B j i) (constantCoefficientSlot _ _)
    (layerContinuousPrincipalSlots_not_constant B j i) (hR j) (hσ j) hσ1 d).trans (by linarith [hR j])

variable (j : Fin m) (i : I j)


local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S

variable {α O : Type*} [Fintype α] [DecidableEq α] [Fintype O] [DecidableEq O]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable (rows : O → Finset α) (s : O ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ((scalarKernelIntegerJet x (j.val+1) rows).submatrix id s).det ≠ 0)


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators Matrix Classical

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (j : Fin m) (i : I j)


local notation "centers" => allocatedContinuousProfileCenters (G := G) B R j i
local notation "widths" => allocatedContinuousProfileWidths (G := G) B R σ j i
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
local notation "kernelScale" => kernelJetCoefficientScale G (j.val+1) (S.value : ℝ) 1
local notation "pivot" => normalizedPivotEquiv (Matrix.submatrix (scalarKernelIntegerJet x (j.val+1) rows) id s) hA
  (fun o => kernelScale (s o)) (fun _ => 1)
  (fun o => kernelJetCoefficientScale_pos G (j.val+1)
    (Nat.cast_pos.mpr (LayerSamplerScale.positive S)) zero_lt_one (s o))
  (fun _ => zero_lt_one)
local notation "free" => matrixSupCLM (normalizedIntegerColumns
  (remainingMatrixColumns (scalarKernelIntegerJet x (j.val+1) rows) s)
  (fun d => kernelScale (Subtype.val d)) (fun _ => 1))
local notation "radius" => NNReal.mk (R j) (le_of_lt (hR j))

include hR hσ in
theorem allocatedContinuousKernelDensity_probability_data (hσ1 : σ j ≤ 1)
    (y : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) (fun a => ¬grid a) → ℝ) :
    (∀ v, 0 ≤ allocatedContinuousKernelDensity B U basis S j i x u rows s hA y v) ∧
      Integrable (allocatedContinuousKernelDensity B U basis S j i x u rows s hA y) ∧
      (∫ v, allocatedContinuousKernelDensity B U basis S j i x u rows s hA y v) = 1 :=
  affineSelectedJetDensity_probability_data s pivot free (allocatedNonkernelExponent B j) input fixedReal rows
    (centers ∘ reindex) (widths ∘ reindex)
    (fun d => allocatedContinuousProfileWidths_pos B hR hσ j i (reindex d)) radius
    (fun d => allocatedContinuousProfile_bound B hR hσ j i hσ1 (reindex d)) y

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

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
local notation "sides" => allocatedPrincipalSides B U basis S

variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U basis S.value a)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)

variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0)
variable (hσ1 : ∀ j, σ j ≤ 1)

theorem allocatedLongJetFactor_probability_data (a : {a // ¬grid a}) :
    (∀ z, 0 ≤ allocatedLongJetFactor B U basis hR hσ S x u v rows s hA hσ1 a z) ∧
      Integrable (allocatedLongJetFactor B U basis hR hσ S x u v rows s hA hσ1 a)
        (coefficientJetAxisReference O a.val) ∧
      (∫ z, allocatedLongJetFactor B U basis hR hσ S x u v rows s hA hσ1 a z
        ∂coefficientJetAxisReference O a.val) = 1 := by
  rcases a with ⟨⟨j, a⟩, ha⟩
  cases a with
  | inl i =>
    exact allocatedContinuousKernelDensity_probability_data B U basis hR hσ S j i x u
      (rows j) (s j) (hA j) (hσ1 j)
      (principalTupleNormalized (principalAxisLength (fun a => ¬grid a) sides) v)
  | inr i =>
    let p := allocatedIntegerKernelPMF B U basis hR hσ S x u v rows j i (hσ1 j) (Nat.lt_of_not_ge ha)
    change (∀ z, 0 ≤ (p z).toReal) ∧ Integrable (fun z => (p z).toReal) Measure.count ∧
      (∫ z, (p z).toReal ∂Measure.count) = 1
    exact ⟨fun _ => ENNReal.toReal_nonneg, pmf_real_integrable p, pmf_real_integral_count p⟩

theorem allocatedLongJetDensity_probability_data :
    (∀ z, 0 ≤ allocatedLongJetDensity B U basis hR hσ S x u v rows s hA hσ1 z) ∧
      Integrable (allocatedLongJetDensity B U basis hR hσ S x u v rows s hA hσ1)
        (allocatedLongJetReference B U basis S O) ∧
      (∫ z, allocatedLongJetDensity B U basis hR hσ S x u v rows s hA hσ1 z
        ∂allocatedLongJetReference B U basis S O) = 1 := by
  have hp := allocatedLongJetFactor_probability_data B U basis hR hσ S x u v rows s hA hσ1
  refine ⟨fun z => Finset.prod_nonneg (fun a _ => (hp a).1 (z a)),
    Integrable.fintype_prod_dep (fun a => (hp a).2.1), ?_⟩
  change (∫ z, (∏ a, allocatedLongJetFactor B U basis hR hσ S x u v rows s hA hσ1 a (z a))
    ∂Measure.pi (fun a : {a // ¬grid a} => coefficientJetAxisReference O a.val)) = 1
  rw [integral_fintype_prod_eq_prod]
  exact Finset.prod_eq_one (fun a _ => (hp a).2.2)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α) (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0)
variable (hσ1 : ∀ j, σ j ≤ 1)


variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedPhysicalLongImage
namespace OAI

section

namespace Erdos3

theorem translatedIntegerMappedJetMatrix_zero {Z X K α O N : Type*} [DecidableEq α]
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ X) (z : Z → ℤ)
    (rows : O → Finset α) (x : X → ℤ) :
    translatedIntegerMappedJetMatrix e input z rows x (fun _ => 0) =
      integerMappedJetMatrix e input z rows x := by
  simp only [translatedIntegerMappedJetMatrix, zero_add, integerMappedJetMatrix]

theorem translatedIntegerMappedJetMatrix_eq_boundedCoefficient {Z X K α O : Type*}
    [DecidableEq α] [Fintype K] (h : ℕ) (input : K → Option α → Z ⊕ X)
    (z : Z → ℤ) (rows : O → Finset α) (x : X → ℤ) (c : K → ℤ) :
    translatedIntegerMappedJetMatrix (fun e : VectorPolynomial.BoundedCoefficientExponent K h => e.val)
      input z rows x c =
      boundedCoefficientJetMatrix (fun k => c k + Sum.elim z x (input k none))
        (fun i k => Sum.elim z x (input k (some i))) h rows := by
  have hv : (fun t k => c k + integerMappedCubeTuple input z x t k) =
      integerAffineCube (fun k => c k + Sum.elim z x (input k none))
        (fun i k => Sum.elim z x (input k (some i))) := by
    funext t k
    simp only [integerMappedCubeTuple, integerAffineCube, add_assoc]
  change integerJetMatrix
      (fun e : VectorPolynomial.BoundedCoefficientExponent K h => MvPolynomial.monomial e.val 1)
      (fun t k => c k + integerMappedCubeTuple input z x t k) rows =
    integerJetMatrix
      (fun e : VectorPolynomial.BoundedCoefficientExponent K h => MvPolynomial.monomial e.val 1)
      (integerAffineCube (fun k => c k + Sum.elim z x (input k none))
        (fun i k => Sum.elim z x (input k (some i)))) rows
  rw [hv]

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

omit [DecidableEq α] in
theorem allocatedPhysicalCube_mapped_root (c : LayerSamplerVariables G I n B → ℤ) :
    (fun k => c k + Sum.elim (Sum.elim (fun ga : G × Option α => (x ga.1 ga.2 : ℤ)) (principalTupleIntegers u)) (principalTupleIntegers v) ((partitionedPrincipalInput grid (fun g a => (g, a))) k none)) =
      allocatedPhysicalCubeRoot B U b S c x (principalAxisJoin grid u v) := by
  funext k
  rw [partitionedPrincipalInput_value]
  cases k <;> rfl

omit [DecidableEq α] in
theorem allocatedPhysicalCube_mapped_directions :
    (fun i k => Sum.elim (Sum.elim (fun ga : G × Option α => (x ga.1 ga.2 : ℤ)) (principalTupleIntegers u)) (principalTupleIntegers v) ((partitionedPrincipalInput grid (fun g a => (g, a))) k (some i))) = (allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)) := by
  funext i k
  rw [partitionedPrincipalInput_value]
  cases k <;> rfl

theorem allocatedTranslatedPartitionedJetMatrix_eq_physical
    (c : LayerSamplerVariables G I n B → ℤ) (j : Fin m) :
    allocatedTranslatedPartitionedJetMatrix B U b S x u v rows c j =
      boundedCoefficientJetMatrix (allocatedPhysicalCubeRoot B U b S c x (principalAxisJoin grid u v)) (allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)) (j.val + 1) (rows j) := by
  unfold allocatedTranslatedPartitionedJetMatrix
  rw [translatedIntegerMappedJetMatrix_eq_boundedCoefficient,
    allocatedPhysicalCube_mapped_root, allocatedPhysicalCube_mapped_directions]

theorem allocatedPartitionedJetMatrix_eq_physical (j : Fin m) :
    allocatedPartitionedJetMatrix B U b S x u v rows j =
      boundedCoefficientJetMatrix (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v))
        (allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)) (j.val + 1) (rows j) := by
  rw [← allocatedTranslatedPartitionedJetMatrix_eq_physical B U b S x u v rows (fun _ => 0) j]
  exact (translatedIntegerMappedJetMatrix_zero _ (partitionedPrincipalInput grid (fun g a => (g, a))) (Sum.elim (fun ga : G × Option α => (x ga.1 ga.2 : ℤ)) (principalTupleIntegers u)) (rows j) (principalTupleIntegers v)).symm

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

variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
variable (hσ1 : ∀ j, σ j ≤ 1)

variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedTrimmedVectorSite
namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α]
variable (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox α S.value)
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))

theorem allocatedPhysicalEntryBudget_one_le : 1 ≤ allocatedPhysicalEntryBudget B U basis S c := by
  have h := allocatedPhysicalRootBudget_nonneg B U basis S c
  unfold allocatedPhysicalEntryBudget
  linarith [Nat.cast_nonneg (α := ℝ) S.value]

variable [DecidableEq α] [DecidableEq G]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α]
variable (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox α S.value)
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox α S.value)
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox α S.value)
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))

local notation "root" => allocatedPhysicalCubeRoot B U basis S c x y

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RestrictedComplexChartSupport
namespace OAI

section

namespace Erdos3

variable {X Y : Type*}

theorem restrictedComplexChartDensity_norm_le (q : X → Y) (S : Set X)
    (hinj : Set.InjOn q S) (f : X → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ x, ‖f x‖ ≤ C) (y : Y) : ‖restrictedComplexChartDensity q S 1 f y‖ ≤ C := by
  by_cases hy : y ∈ q '' S
  · obtain ⟨x, hx, rfl⟩ := hy
    rw [restrictedComplexChartDensity_apply q S 1 f hinj hx, Complex.ofReal_one, one_mul]
    exact hf x
  · rw [restrictedComplexChartDensity_zero q S 1 f hy, norm_zero]
    exact hC

theorem restrictedComplexChartDensity_measurable [MeasurableSpace X] [MeasurableSpace Y]
    (q : X → Y) (S : Set X) (he : MeasurableEmbedding (fun x : S => q x.val))
    (c : ℝ) (f : X → ℂ) (hf : Measurable f) :
    Measurable (restrictedComplexChartDensity q S c f) :=
  measurable_const.mul (he.measurable_extend (hf.comp measurable_subtype_coe) measurable_const)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelCoefficientLogBudget
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

theorem goodKernelUniformCandidate_spec {α J : Type*}
    [Fintype α] [DecidableEq α] [Fintype J] {L B : ℕ} {κ : ℝ}
    (selection : α ↪ J) (x : J → IntegerScalarCubeBox α L)
    (hx : GoodScalarKernelTuple selection κ B x) (height : ℕ) :
    let period := kernelPeriodCandidate (height + 1) (goodKernelUniformCandidate selection x hx height)
    (∀ root : J → ℤ, integerScalarLattice (Unit ⊕ α) (period : ℤ) ≤
      pivotFullImage (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) selection)) ∧
    ∀ (O : Type*) [Fintype O] (degree : ℕ), degree ≤ height + 1 →
      ∀ rows : O → Finset α, Function.Injective rows →
        (∀ o, (rows o).card ≤ degree) →
          integerScalarLattice O (period : ℤ) ≤ (scalarKernelIntegerJet x degree rows).mulVecLin.range :=
by
  let a := Classical.choose hx.2
  obtain ⟨ha, haB, hp⟩ := Classical.choose_spec hx.2
  have hc : (goodKernelUniformCandidate selection x hx height).val + 1 = a := by
    dsimp only [goodKernelUniformCandidate, a]
    omega
  refine ⟨?_, ?_⟩
  · intro root
    rw [selectedSpatial_full_image, kernelPeriodCandidate, hc, Nat.cast_pow]
    apply (integerScalarLattice_pow_le (a : ℤ) (by omega : 1 ≤ height + 1)).trans
    simpa only [pow_one] using rootDifferenceMatrix_period root (scalarCubeDifferenceMatrix x) (a : ℤ) hp
  · intro O hO degree hdegree rows hinj hrows
    rw [kernelPeriodCandidate, hc, Nat.cast_pow]
    exact boundedDegreeIntegerJetMatrix_common_period _ _ (a : ℤ) hp (height + 1) degree
      hdegree rows hinj hrows

theorem integerScalarLattice_le_of_nat_dvd {O : Type*} [Fintype O] {a b : ℕ}
    (h : a ∣ b) : integerScalarLattice O (b : ℤ) ≤ integerScalarLattice O (a : ℤ) := by
  obtain ⟨c, rfl⟩ := h
  rintro y ⟨z, rfl⟩
  refine ⟨(c : ℤ) • z, ?_⟩
  change (a : ℤ) • ((c : ℤ) • z) = ((a * c : ℕ) : ℤ) • z
  rw [smul_smul, Nat.cast_mul]

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem kernelGeometryLog_bounds (q n j k d : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ kernelGeometryLog q n j k d p ∧ p ≤ kernelGeometryLog q n j k d p ∧
    kernelInverseLog q n j d p ≤ kernelGeometryLog q n j k d p ∧
    (j : ℝ) + (q : ℝ) * (d + 1) ≤ kernelGeometryLog q n j k d p ∧
    (k : ℝ) + (q : ℝ) * (d + 1) ≤ kernelGeometryLog q n j k d p := by
  have hi : 0 ≤ kernelInverseLog q n j d p := by unfold kernelInverseLog; positivity
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have he : 0 ≤ (q : ℝ) * (d + 1) := by positivity
  unfold kernelGeometryLog
  constructor
  · positivity
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedFixedKernelReplacement
namespace OAI

section

namespace Erdos3

theorem layerKernelIndexBound_row {m B : ℕ} {α O : Type*} [Fintype α] [Fintype O]
    (hB : 0 < B) (hq : Fintype.card α ≤ m+1) (rows : O → Finset α)
    (hinj : Function.Injective rows) (j : Fin m) :
    (B^(j.val+1))^Fintype.card O ≤ layerKernelIndexBound m B := by
  have hc : Fintype.card O ≤ 2^(m+1) := by
    have hr : Fintype.card O ≤ 2^Fintype.card α := by
      simpa only [Fintype.card_finset] using Fintype.card_le_of_injective rows hinj
    exact hr.trans (Nat.pow_le_pow_right (by decide : 0 < 2) hq)
  rw [← pow_mul]
  exact Nat.pow_le_pow_right hB (Nat.mul_le_mul (Nat.succ_le_of_lt j.isLt) hc)

namespace VectorPolynomial

open scoped Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)

variable [DecidableEq G]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable [∀ j : Fin m, DecidableEq (BoundedIntegerExponent G (j.val+1))]
variable [∀ j : Fin m, DecidableEq (AllocatedNonkernelCoefficient (G := G) B j)]
variable (rows : ∀ j, O j → Finset α)

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)

variable [DecidableEq G]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable [∀ j : Fin m, DecidableEq (BoundedIntegerExponent G (j.val+1))]
variable [∀ j : Fin m, DecidableEq (AllocatedNonkernelCoefficient (G := G) B j)]
variable (rows : ∀ j, O j → Finset α)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

namespace VectorPolynomial

open scoped Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable [DecidableEq G]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable [∀ j : Fin m, DecidableEq (BoundedIntegerExponent G (j.val + 1))]
variable [∀ j : Fin m, DecidableEq (AllocatedNonkernelCoefficient (G := G) B j)]
variable (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable (rows : ∀ j, O j → Finset α)

theorem allocatedIntegerKernelMask_bound {M : ℕ} {κ : ℝ} (hM : 0 < M)
    (selection : α ↪ G) (hx : GoodScalarKernelTuple selection κ M x)
    (hq : Fintype.card α ≤ m + 1) (hinj : ∀ j, Function.Injective (rows j))
    (hrows : ∀ j o, (rows j o).card ≤ j.val + 1)
    (j : Fin m) (modulus : ℕ)
    (residue : Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
    (z : O j → ℤ) :
    0 ≤ allocatedIntegerKernelMask B U basis S x rows j modulus residue z ∧
      allocatedIntegerKernelMask B U basis S x rows j modulus residue z ≤ layerKernelIndexBound m M := by
  unfold allocatedIntegerKernelMask coefficientResidueMultiplier
  refine ⟨coefficientImageMultiplier_nonneg _ _, (coefficientImageMultiplier_le_index _ _).trans ?_⟩
  have hi := scalarKernelJet_extended_index selection x hx (j.val + 1) (rows j)
    (hinj j) (hrows j) (liftResidueMatrix residue)
  exact_mod_cast hi.trans (layerKernelIndexBound_row hM hq (rows j) (hinj j) j)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped BigOperators Matrix

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable [DecidableEq G] [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable [∀ j : Fin m, DecidableEq (BoundedIntegerExponent G (j.val+1))]
variable [∀ j : Fin m, DecidableEq (AllocatedNonkernelCoefficient (G := G) B j)]
variable (rows : ∀ j, O j → Finset α)


end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)

variable [DecidableEq G]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable [∀ j : Fin m, DecidableEq (BoundedIntegerExponent G (j.val+1))]
variable [∀ j : Fin m, DecidableEq (AllocatedNonkernelCoefficient (G := G) B j)]
variable (rows : ∀ j, O j → Finset α)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable [DecidableEq G] [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable [∀ j : Fin m, DecidableEq (BoundedIntegerExponent G (j.val+1))]
variable [∀ j : Fin m, DecidableEq (AllocatedNonkernelCoefficient (G := G) B j)]
variable (rows : ∀ j, O j → Finset α)


end Erdos3.VectorPolynomial

end

end OAI

end


