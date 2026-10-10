-- Prove2me | Definitions.Def_OAIErdos3B054
-- name    : OAIErdos3B054
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-09T18:34:12.119147+00:00
-- url     : https://prove2.me/theorems/a5d94bc4-8592-4c19-9f41-c4765c09a85e
-- title:
--   OpenAI Erdős-3 split, definitions bundle 55 of 160
-- statement:
--   Definitions bundle 55 of 160 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B053`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 55 available.
--
--   Modules: `OAI.Erdos3.BooleanCubeKernel.affineCoveredSiteSample_physical`, `OAI.Erdos3.BooleanCubeKernel.affineCoveredSiteSample_zero_base_physical`, `OAI.Erdos3.BooleanCubeKernel.boundedCoefficientJetMatrix_standard`, `OAI.Erdos3.BooleanCubeKernel.boundedSiteMatrix_standard`, `OAI.Erdos3.BooleanCubeKernel.centeredPhysicalCubeMap`, `OAI.Erdos3.BooleanCubeKernel.centeredPhysicalCubeWindow`, `OAI.Erdos3.BooleanCubeKernel.centeredSpatialWidths_fit`, `OAI.Erdos3.BooleanCubeKernel.coarseReferenceMassConstant`, `OAI.Erdos3.BooleanCubeKernel.coefficientCoverSample_physicalJet`, `OAI.Erdos3.BooleanCubeKernel.coefficientCoverSample_sites`, `OAI.Erdos3.BooleanCubeKernel.coefficientCoverSample_standardPhysicalJet`, `OAI.Erdos3.BooleanCubeKernel.coefficientTorusFourierSum_sample`, `OAI.Erdos3.BooleanCubeKernel.fixedScaleJointMarginalTransfer`, `OAI.Erdos3.BooleanCubeKernel.integerAffineMap_jointIntegerFrame`, `OAI.Erdos3.BooleanCubeKernel.integerPhysicalSite`, `OAI.Erdos3.BooleanCubeKernel.integerPhysicalSite_abs_bound`, `OAI.Erdos3.BooleanCubeKernel.integerPhysicalSite_cast_apply`, `OAI.Erdos3.BooleanCubeKernel.integerSiteValue_affine_physical`, `OAI.Erdos3.BooleanCubeKernel.jointIntegerFrame`, `OAI.Erdos3.BooleanCubeKernel.jointIntegerPhysicalSite`, `OAI.Erdos3.BooleanCubeKernel.jointIntegerPhysicalSite_cast`, `OAI.Erdos3.BooleanCubeKernel.jointIntegerPhysicalSite_mem_box`, `OAI.Erdos3.BooleanCubeKernel.layeredSiteWeight_physicalCube`, `OAI.Erdos3.BooleanCubeKernel.physicalCubeCoefficient`, `OAI.Erdos3.BooleanCubeKernel.physicalCubeCoveredSample`, `OAI.Erdos3.BooleanCubeKernel.physicalCubeCoveredSample_translate`, `OAI.Erdos3.BooleanCubeKernel.physicalCubeEuclideanSample`, `OAI.Erdos3.BooleanCubeKernel.physicalCubeEuclideanSample_frame`, `OAI.Erdos3.BooleanCubeKernel.physicalCubeOffset`, `OAI.Erdos3.BooleanCubeKernel.physicalCubeParametersEquiv`, `OAI.Erdos3.BooleanCubeKernel.physicalCubeParametersEquiv_support_iff`, `OAI.Erdos3.BooleanCubeKernel.physicalCubeParametersEquiv_vertex`, `OAI.Erdos3.BooleanCubeKernel.physicalCubePositiveTest`, `OAI.Erdos3.BooleanCubeKernel.physicalCubeResidueCoordinates`, `OAI.Erdos3.BooleanCubeKernel.physicalCubeRootDifferences`, `OAI.Erdos3.BooleanCubeKernel.physicalCubeRootDifferences_direction`, `OAI.Erdos3.BooleanCubeKernel.physicalCubeRootDifferences_root`, `OAI.Erdos3.BooleanCubeKernel.physicalCubeRootDifferences_standard`, `OAI.Erdos3.BooleanCubeKernel.physicalCubeRootDifferences_vertex`, `OAI.Erdos3.BooleanCubeKernel.physicalCubeRowSample`, `OAI.Erdos3.BooleanCubeKernel.physicalCubeRowSample_translate`, `OAI.Erdos3.BooleanCubeKernel.physicalCubeSiteTest`, `OAI.Erdos3.BooleanCubeKernel.physicalCubeSiteTest_norm_le`, `OAI.Erdos3.BooleanCubeKernel.physicalCubeVertexValue`, `OAI.Erdos3.BooleanCubeKernel.physicalCubeVertexValue_rootDifferences`, `OAI.Erdos3.BooleanCubeKernel.physicalCubeVertexValue_translate`, `OAI.Erdos3.BooleanCubeKernel.physicalCube_zero_residue_bound`, `OAI.Erdos3.BooleanCubeKernel.physicalIntegerBoxCubes`, `OAI.Erdos3.BooleanCubeKernel.physicalReconstruction_sum_le_sampled_mass`, `OAI.Erdos3.BooleanCubeKernel.physicalResidueOffsetShift`, `OAI.Erdos3.BooleanCubeKernel.physicalResidueQuotient`, `OAI.Erdos3.BooleanCubeKernel.physicalResidueReconstruction`, `OAI.Erdos3.BooleanCubeKernel.physicalResidueReconstruction_columnResidue`, `OAI.Erdos3.BooleanCubeKernel.physicalResidueReconstruction_envelope`, `OAI.Erdos3.BooleanCubeKernel.physicalResidueReconstruction_injective`, `OAI.Erdos3.BooleanCubeKernel.physicalResidueReconstruction_translate`, `OAI.Erdos3.BooleanCubeKernel.physicalResidueSpatialMask`, `OAI.Erdos3.BooleanCubeKernel.physicalResidueSpatialSiteFactor`, `OAI.Erdos3.BooleanCubeKernel.physicalResidueSpatialSiteFactor_normalized`, `OAI.Erdos3.BooleanCubeKernel.physicalResidueSpatialSmooth`, `OAI.Erdos3.BooleanCubeKernel.physicalResidueSpatialSmooth_bounds`, `OAI.Erdos3.BooleanCubeKernel.physicalResidueSpatialSmooth_pre_lipschitz`, `OAI.Erdos3.BooleanCubeKernel.physicalResidueStarFactor`, `OAI.Erdos3.BooleanCubeKernel.physicalSingleSiteValue`, `OAI.Erdos3.BooleanCubeKernel.physicalSiteWidth`, `OAI.Erdos3.BooleanCubeKernel.physicalSupportedCubeEquiv`, `OAI.Erdos3.BooleanCubeKernel.physicalWindow_sum_le_sampled_mass`, `OAI.Erdos3.BooleanCubeKernel.referenceJetEnvelopeWidths`, `OAI.Erdos3.BooleanCubeKernel.referenceJetEnvelopeWidths_pos`, `OAI.Erdos3.BooleanCubeKernel.referenceJetEnvelopeWidths_residue`, `OAI.Erdos3.BooleanCubeKernel.referenceJetEnvelope_volume`, `OAI.Erdos3.BooleanCubeKernel.rowDifferenceCoefficients`, `OAI.Erdos3.BooleanCubeKernel.rowDifferenceCoefficients_linear`, `OAI.Erdos3.BooleanCubeKernel.selectedResidue_distinct_collision_le`, `OAI.Erdos3.BooleanCubeKernel.selectedResidue_site_collision_le`, `OAI.Erdos3.BooleanCubeKernel.selectedResidue_trimmed_comparison_transfer`, `OAI.Erdos3.BooleanCubeKernel.selectedResidue_trimmed_reference_compare`, `OAI.Erdos3.BooleanCubeKernel.spatialWindow_four_coordinate_bound`, `OAI.Erdos3.BooleanCubeKernel.standardPhysicalCubeFrame`, `OAI.Erdos3.BooleanCubeKernel.standardPhysicalCubeFrame_injective`, `OAI.Erdos3.BooleanCubeKernel.standardPhysicalCubeOutput`, `OAI.Erdos3.BooleanCubeKernel.standardPhysicalCubeOutput_frame`, `OAI.Erdos3.BooleanCubeKernel.standardPhysicalJetMap`, `OAI.Erdos3.BooleanCubeKernel.standardPhysicalJetMap_measurePreserving`, `OAI.Erdos3.BooleanCubeKernel.standardPhysicalSite`, `OAI.Erdos3.BooleanCubeKernel.standardPhysicalSite_apply`, `OAI.Erdos3.BooleanCubeKernel.starVertexSiteFactor`, `OAI.Erdos3.BooleanCubeKernel.starVertexSiteFactor_bound`, `OAI.Erdos3.BooleanCubeKernel.translatePhysicalCube`, `OAI.Erdos3.BooleanCubeKernel.trimmedSpatialRootScale_normalized_ratio`, `OAI.Erdos3.BooleanCubeKernel.trimmedSpatialWidths_fit`, `OAI.Erdos3.FiniteProbabilityWeights.joint_normalization_integral_compare`, `OAI.Erdos3.FiniteProbabilityWeights.mean_fintype_sum`, `OAI.Erdos3.FiniteProbabilityWeights.noninjectivity_le`, `OAI.Erdos3.FiniteProbabilityWeights.productive_mass_lower_bound`, `OAI.Erdos3.FiniteProbabilityWeights.reweightPositive_noninjectivity_le`, `OAI.Erdos3.ResidueBoxSlice.composeSlice`, `OAI.Erdos3.ResidueBoxSlice.composeSlice_length_lower`, `OAI.Erdos3.ResidueBoxSlice.composeSlice_point`, `OAI.Erdos3.ResidueBoxSlice.length_large_of_cost`, `OAI.Erdos3.ResidueBoxSlice.parameterCell`, `OAI.Erdos3.ResidueBoxSlice.stride_le_twice_exp_cost`, `OAI.Erdos3.ResidueBoxSlice.stride_mul_length_le_twice`, `OAI.Erdos3.VectorPolynomial.affineSampleCoefficientArray_joint_frame`, `OAI.Erdos3.VectorPolynomial.affineSampleCoefficientTorus_joint_frame`, `OAI.Erdos3.VectorPolynomial.allocatedAffineDensity`, `OAI.Erdos3.VectorPolynomial.allocatedPhysicalCube_site_le_exp`, `OAI.Erdos3.VectorPolynomial.coveredJetAmbientTorus`, `OAI.Erdos3.VectorPolynomial.coveredJetAmbientTorus_coefficient`, `OAI.Erdos3.VectorPolynomial.coveredJetAmbientTorus_continuous`, `OAI.Erdos3.VectorPolynomial.substitute_translate_joint_frame`, `OAI.Erdos3.affineResidueIntervalSiteWeight`, `OAI.Erdos3.affineVectorInterval_normalized_lipschitz`, `OAI.Erdos3.affineVectorResidueSiteWeight`, `OAI.Erdos3.affineVectorResidueSiteWeight_factorization`, `OAI.Erdos3.centeredSpatialWidths`, `OAI.Erdos3.centeredSpatialWidths_pos`, `OAI.Erdos3.integerArrayLinearForm`, `OAI.Erdos3.integerArrayLinearForm_affine_join`, `OAI.Erdos3.integerArrayLinearForm_pivot_injective`, `OAI.Erdos3.integerBaseTranslation`, `OAI.Erdos3.integral_productive_injective_mass`, `OAI.Erdos3.integral_productive_injective_mass_of_complex_marginals`, `OAI.Erdos3.integral_productive_sampler_mass`, `OAI.Erdos3.le_spatialSamplingBudget`, `OAI.Erdos3.mem_rectangularWeightIndices_zero_iff`, `OAI.Erdos3.narrowTrimmedSpatialWidths`, `OAI.Erdos3.narrowTrimmedSpatialWidths_le`, `OAI.Erdos3.narrowTrimmedSpatialWidths_lower`, `OAI.Erdos3.narrowTrimmedSpatialWidths_pos`, `OAI.Erdos3.noninjectivityIndicator`, `OAI.Erdos3.noninjectivityIndicator_le_pairs`, `OAI.Erdos3.noninjectivityIndicator_nonneg`, `OAI.Erdos3.rectangularWeightIndices_zero_bound`, `OAI.Erdos3.residueSmoothPMF_linear_cap`, `OAI.Erdos3.selectedJointFiniteLaw_integral_local_comparison`, `OAI.Erdos3.selectedResidueSmoothPMF_linear_cap`, `OAI.Erdos3.shiftedSmoothProductMass_pos_of_scales`, `OAI.Erdos3.spatialSamplingBudget`, `OAI.Erdos3.spatialTrimMargin`, `OAI.Erdos3.spatialTrimMargin_bound`, `OAI.Erdos3.spatialTrimMargin_error_bound`, `OAI.Erdos3.spatialTrimMargin_fits`, `OAI.Erdos3.spatialTrimMargin_proper`, `OAI.Erdos3.spatialTrimMargin_size_of_exp_size`, `OAI.Erdos3.spatialWidthFraction`, `OAI.Erdos3.spatialWidthFraction_inv_le`, `OAI.Erdos3.spatialWidthFraction_le_allocated_width`, `OAI.Erdos3.spatialWidthFraction_le_trimmed_width`, `OAI.Erdos3.spatialWidthFraction_mul_le_width`, `OAI.Erdos3.spatialWidthFraction_pos`, `OAI.Erdos3.spatial_scale_of_exp_size`, `OAI.Erdos3.spatial_threshold_large`, `OAI.Erdos3.trimmedSpatialWidths`, `OAI.Erdos3.trimmedSpatialWidths_antitone_budget`, `OAI.Erdos3.trimmedSpatialWidths_pos`, `OAI.Erdos3.trimmedSpatialWidths_scale`, `OAI.Erdos3.unconditionedSpatialTrimFraction`, `OAI.Erdos3.unconditionedSpatialTrimFraction_bounds`, `OAI.Erdos3.unconditionedSpatialWidthBudget`, `OAI.Erdos3.unconditionedSpatialWidthCutoff`, `OAI.Erdos3.unconditionedSpatialWidthCutoff_bounds`, `OAI.Erdos3.vectorIntervalSiteWeight_affine_lipschitz`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B052
import Definitions.Def_OAIErdos3B135

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerBoxObservedMean
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

def integerPhysicalSite {K I : Type*} [Fintype K] (root : K → ℤ)
    (z : Option K × I → ℤ) : I → ℤ :=
  fun i => z (none,i) + ∑ k, root k * z (some k,i)

theorem integerPhysicalSite_cast_apply {K I : Type*} [Fintype K]
    (root : K → ℤ) (z : Option K × I → ℤ) (i : I) :
    (integerPhysicalSite root z i : ℝ) = physicalAffineSite root z i := by
  have h := physicalAffineSite_baseArrayJoin_apply root
    (fun k => z (some k.1,k.2)) (fun i => z (none,i)) i
  rw [baseArrayJoin_eta] at h
  simpa only [integerPhysicalSite, Int.cast_add, Int.cast_sum, Int.cast_mul] using h.symm

noncomputable def physicalSiteWidth {K I : Type*} [Fintype K]
    (root : K → ℤ) (W : Option K × I → ℝ) (i : I) : ℝ :=
  W (none,i) + ∑ k, |(root k : ℝ)| * W (some k,i)

theorem integerPhysicalSite_abs_bound {K I : Type*} [Fintype K]
    (root : K → ℤ) (W : Option K × I → ℝ) (z : Option K × I → ℤ)
    (hz : ∀ a, |(z a : ℝ)| ≤ W a) (i : I) :
    |(integerPhysicalSite root z i : ℝ)| ≤ physicalSiteWidth root W i := by
  simp only [integerPhysicalSite, Int.cast_add, Int.cast_sum, Int.cast_mul, physicalSiteWidth]
  calc
    _ ≤ |(z (none,i) : ℝ)| + |∑ k, (root k : ℝ) * (z (some k,i) : ℝ)| := abs_add_le _ _
    _ ≤ |(z (none,i) : ℝ)| + ∑ k, |(root k : ℝ) * (z (some k,i) : ℝ)| :=
      add_le_add_right (Finset.abs_sum_le_sum_abs _ _) _
    _ ≤ _ := add_le_add (hz _) (Finset.sum_le_sum (fun k _ => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hz _) (abs_nonneg _)))

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3

def integerBaseTranslation {K I : Type*} (b : I → ℤ) : Option K × I → ℤ :=
  baseArrayJoin 0 b

namespace BooleanCubeKernel

open scoped BigOperators

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I]
variable (N : I → ℕ) (hN : (integerBox N).Nonempty)

namespace BooleanCubeKernel

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3.ResidueBoxSlice

open BooleanCubeKernel
open scoped BigOperators Classical

variable {K : Type*} {P : K → ℕ} {q r : ℕ}

def composeSlice (S : ResidueBoxSlice P q) (T : ResidueBoxSlice S.length r) :
    ResidueBoxSlice P (q * r) where
  start k := S.start k + q * T.start k
  length := T.length
  inside k j hj := by
    have h := S.inside k _ (T.inside k j hj)
    convert h using 1; ring

theorem composeSlice_point (S : ResidueBoxSlice P q) (T : ResidueBoxSlice S.length r)
    (u : ∀ k, Fin (T.length k)) : (S.composeSlice T).point u = S.point (T.point u) := by
  funext k
  apply Fin.ext
  change S.start k + q * T.start k + (q * r) * (u k).val =
    S.start k + q * (T.start k + r * (u k).val)
  ring

def parameterCell (Q : ∀ k, FiniteProgressionPartition (P k))
    (hstep : ∀ k c, (Q k).step c = r) (c : ∀ k, (Q k).Label) : ResidueBoxSlice P r where
  start k := (Q k).start (c k)
  length k := (Q k).length (c k)
  inside k j hj := by simpa only [hstep] using (Q k).point_lt (c k) hj

theorem stride_mul_length_le_twice (S : ResidueBoxSlice P q) (k : K)
    (hlen : 2 ≤ S.length k) : q * S.length k ≤ 2 * P k := by
  have hlast := S.inside k (S.length k - 1) (by omega)
  have hlen' : S.length k ≤ 2 * (S.length k - 1) := by omega
  have hmul := Nat.mul_le_mul_left q hlen'
  nlinarith

theorem composeSlice_length_lower (S : ResidueBoxSlice P q)
    (T : ResidueBoxSlice S.length r) {cost loss : ℝ}
    (hS : ∀ k, Real.exp (-cost) * (P k : ℝ) ≤ S.length k)
    (hT : ∀ k, (S.length k : ℝ) * Real.exp (-loss) ≤ T.length k) (k : K) :
    Real.exp (-(cost + loss)) * (P k : ℝ) ≤ (S.composeSlice T).length k := by
  calc
    _ = (Real.exp (-cost) * (P k : ℝ)) * Real.exp (-loss) := by
      rw [mul_right_comm, ← Real.exp_add]
      congr 2
      ring
    _ ≤ (S.length k : ℝ) * Real.exp (-loss) :=
      mul_le_mul_of_nonneg_right (hS k) (Real.exp_nonneg _)
    _ ≤ _ := hT k

theorem length_large_of_cost (S : ResidueBoxSlice P q) {cost target : ℝ}
    (hS : ∀ k, Real.exp (-cost) * (P k : ℝ) ≤ S.length k)
    (hP : ∀ k, Real.exp (cost + target) ≤ (P k : ℝ)) (k : K) :
    Real.exp target ≤ (S.length k : ℝ) := by
  calc
    _ = Real.exp (-cost) * Real.exp (cost + target) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-cost) * (P k : ℝ) :=
      mul_le_mul_of_nonneg_left (hP k) (Real.exp_nonneg _)
    _ ≤ _ := hS k

theorem stride_le_twice_exp_cost (S : ResidueBoxSlice P q) {cost : ℝ}
    (k : K) (hlen : 2 ≤ S.length k)
    (hS : Real.exp (-cost) * (P k : ℝ) ≤ S.length k) :
    (q : ℝ) ≤ 2 * Real.exp cost := by
  have hP : (0 : ℝ) < P k := by
    have h := S.inside k 0 (by omega)
    exact_mod_cast (show 0 < P k by omega)
  have hspan : (q : ℝ) * S.length k ≤ 2 * (P k : ℝ) := by
    exact_mod_cast S.stride_mul_length_le_twice k hlen
  have hmul := (mul_le_mul_of_nonneg_left hS (Nat.cast_nonneg q)).trans hspan
  have hq : (q : ℝ) * Real.exp (-cost) ≤ 2 := by nlinarith
  have h := mul_le_mul_of_nonneg_right hq (Real.exp_nonneg cost)
  simpa only [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one] using h

variable [Fintype K] {X : Type*}

end Erdos3.ResidueBoxSlice

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.UnconditionedSpatialWidthBudget
namespace OAI

section

namespace Erdos3

theorem rectangularWeightIndices_zero_bound {I : Type*} [Fintype I]
    (W : I → ℝ) {z : I → ℤ} (hz : z ∈ rectangularWeightIndices 0 W 1) (i : I) :
    |(z i : ℝ)| ≤ W i := by
  classical
  have hi := Fintype.mem_piFinset.mp hz i
  change z i ∈ sampledWeightIndices 0 (W i) 1 at hi
  simp only [sampledWeightIndices, mul_one, zero_sub, zero_add, Finset.mem_Icc] at hi
  exact abs_le.mpr ⟨Int.ceil_le.mp hi.1, Int.le_floor.mp hi.2⟩

namespace BooleanCubeKernel

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3

theorem mem_rectangularWeightIndices_zero_iff {I : Type*} [Fintype I]
    (W : I → ℝ) (z : I → ℤ) :
    z ∈ rectangularWeightIndices 0 W 1 ↔ ∀ i, |(z i : ℝ)| ≤ W i := by
  classical
  constructor
  · exact fun hz => rectangularWeightIndices_zero_bound W hz
  · intro hz
    apply Fintype.mem_piFinset.mpr
    intro i
    change z i ∈ sampledWeightIndices 0 (W i) 1
    simp only [sampledWeightIndices, mul_one, zero_sub, zero_add, Finset.mem_Icc]
    exact ⟨Int.ceil_le.mpr (abs_le.mp (hz i)).1, Int.le_floor.mpr (abs_le.mp (hz i)).2⟩

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

theorem selectedResidue_trimmed_reference_compare {K I : Type*}
    [Fintype K] [Fintype I] [DecidableEq I]
    (root : K → ℤ) (N R : I → ℕ) (hR : ∀ i, 2 * R i < N i)
    (modulus : I → ℕ) (T : Finset (ColumnResiduePattern (Option K) I modulus))
    (W : Option K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
    (hwidth : ∀ i, physicalSiteWidth root W i ≤ (R i : ℝ))
    (f : (I → ℤ) → ℂ) (hf : ∀ x ∈ integerBox N, ‖f x‖ ≤ 1) :
    ‖(𝔼 a ∈ trimmedIntegerBox N R,
        ∑' z, ((selectedResidueSmoothPMF modulus T W hW hZ z).toReal : ℂ) *
          f (a + integerPhysicalSite root z)) - 𝔼 x ∈ integerBox N, f x‖ ≤
      2 * ∑ i, 2 * (R i : ℝ) / N i := by
  let p := selectedResidueFiniteLaw modulus T W hW hZ
  have hnoise (z : rectangularWeightIndices 0 W 1) (i : I) :
      |integerPhysicalSite root z.val i| ≤ (R i : ℤ) := by
    have h := (integerPhysicalSite_abs_bound root W z.val
      (rectangularWeightIndices_zero_bound W z.property) i).trans (hwidth i)
    exact_mod_cast h
  have h := p.translated_subset_mixture_compare (trimmedIntegerBox N R) (integerBox N)
    (trimmedIntegerBox_nonempty N R hR) (fun z a => a + integerPhysicalSite root z.val)
    (fun _ _ _ _ _ he => add_right_cancel he)
    (fun z _ ha => trimmedIntegerBox_add_mem N R (fun i => (hR i).le) ha _ (hnoise z)) f hf
  have hdef := trimmedIntegerBox_card_deficit N R
    (fun i => lt_of_le_of_lt (Nat.zero_le _) (hR i)) (fun i => (hR i).le)
  have hbound := h.trans (mul_le_mul_of_nonneg_left hdef (by norm_num : (0 : ℝ) ≤ 2))
  dsimp only [p] at hbound
  have he (a : I → ℤ) := selectedResidueFiniteLaw_complexMean modulus T W hW hZ
    (fun z => f (a + integerPhysicalSite root z))
  simpa only [he] using hbound

theorem selectedResidue_trimmed_comparison_transfer {K I : Type*}
    [Fintype K] [Fintype I] [DecidableEq I]
    (root : K → ℤ) (N R : I → ℕ) (hR : ∀ i, 2 * R i < N i)
    (modulus : I → ℕ) (T : Finset (ColumnResiduePattern (Option K) I modulus))
    (W : Option K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
    (hwidth : ∀ i, physicalSiteWidth root W i ≤ (R i : ℝ))
    (f : (I → ℤ) → ℂ) (hf : ∀ x ∈ integerBox N, ‖f x‖ ≤ 1)
    (L : (I → ℤ) → ℂ) {ε : ℝ}
    (hL : ∀ a ∈ trimmedIntegerBox N R,
      ‖L a - ∑' z, ((selectedResidueSmoothPMF modulus T W hW hZ z).toReal : ℂ) *
        f (a + integerPhysicalSite root z)‖ ≤ ε) :
    ‖(𝔼 a ∈ trimmedIntegerBox N R, L a) - 𝔼 x ∈ integerBox N, f x‖ ≤
      ε + 2 * ∑ i, 2 * (R i : ℝ) / N i := by
  have hlocal : ‖(𝔼 a ∈ trimmedIntegerBox N R, L a) -
      (𝔼 a ∈ trimmedIntegerBox N R,
        ∑' z, ((selectedResidueSmoothPMF modulus T W hW hZ z).toReal : ℂ) *
          f (a + integerPhysicalSite root z))‖ ≤ ε := by
    rw [← Finset.expect_sub_distrib]
    exact (RCLike.norm_expect_le (K := ℂ)).trans
      (Finset.expect_le (trimmedIntegerBox_nonempty N R hR) hL)
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
    (add_le_add hlocal (selectedResidue_trimmed_reference_compare
      root N R hR modulus T W hW hZ hwidth f hf))

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3

open scoped BigOperators

theorem shiftedSmoothProductMass_pos_of_scales {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 8*(probabilityProfileLipschitz : ℝ) ≤ S i) :
    0 < shiftedSmoothProductMass a S := by
  rw [shiftedSmoothProductMass_eq_prod a S (fun i => smoothSamplingScale_pos (hS i))]
  exact Finset.prod_pos (fun i _ => shiftedSmoothSampleSum_pos (a i) (hS i))

namespace BooleanCubeKernel

end BooleanCubeKernel

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def centeredSpatialWidths {K I : Type*} (B σ : ℝ) (N : I → ℕ) : Option K × I → ℝ :=
  fun z => match z.1 with
    | none => (N z.2 : ℝ)/8
    | some _ => σ*(N z.2 : ℝ)/(8*(1+B))

theorem centeredSpatialWidths_pos {K I : Type*} {B σ : ℝ} (hB : 0 ≤ B) (hσ : 0 < σ)
    (N : I → ℕ) (hN : ∀ i, 0 < N i) (z : Option K × I) :
    0 < centeredSpatialWidths B σ N z := by
  have hn : (0 : ℝ) < N z.2 := by exact_mod_cast hN z.2
  rcases z with ⟨k,i⟩
  cases k <;> dsimp only [centeredSpatialWidths] <;> positivity

namespace BooleanCubeKernel

theorem centeredSpatialWidths_fit {K I : Type*} [Fintype K] {B σ : ℝ}
    (hB : 0 ≤ B) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (root : K → ℤ)
    (hroot : (∑ k, |(root k : ℝ)|) ≤ B) (N : I → ℕ) (i : I) :
    4 * physicalSiteWidth root (centeredSpatialWidths B σ N) i ≤ (N i : ℝ) := by
  have hn := Nat.cast_nonneg (α := ℝ) (N i)
  have hb : 1+B ≠ 0 := ne_of_gt (by linarith)
  have hv : 0 ≤ σ*(N i : ℝ)/(8*(1+B)) := by positivity
  have ht : B*(σ*(N i : ℝ)/(8*(1+B))) ≤ (N i : ℝ)/8 := by
    calc
      _ ≤ (1+B)*(σ*(N i : ℝ)/(8*(1+B))) :=
        mul_le_mul_of_nonneg_right (by linarith) hv
      _ = σ*(N i : ℝ)/8 := by field_simp
      _ ≤ (N i : ℝ)/8 := by
        exact div_le_div_of_nonneg_right (by nlinarith) (by norm_num)
  simp only [physicalSiteWidth, centeredSpatialWidths, ← Finset.sum_mul]
  have hs := mul_le_mul_of_nonneg_right hroot hv
  nlinarith

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def spatialSamplingBudget (P : ℝ) : ℝ := 4*P+128

theorem le_spatialSamplingBudget {P : ℝ} (hP : 0 ≤ P) : P ≤ spatialSamplingBudget P := by
  unfold spatialSamplingBudget
  linarith

noncomputable def spatialWidthFraction (P τ : ℝ) : ℝ := τ/(8*(1+Real.exp (2*P)))

theorem spatialWidthFraction_pos (P : ℝ) {τ : ℝ} (hτ : 0 < τ) :
    0 < spatialWidthFraction P τ := by
  unfold spatialWidthFraction
  positivity

theorem spatialWidthFraction_inv_le {P τ : ℝ} (hP : 0 ≤ P) (hτ : 0 < τ)
    (hτP : τ⁻¹ ≤ Real.exp P) : 1/spatialWidthFraction P τ ≤ Real.exp (spatialSamplingBudget P) := by
  have h1 : 1 ≤ Real.exp (2*P) := Real.one_le_exp_iff.mpr (by positivity)
  have h16 : (16 : ℝ) ≤ Real.exp 128 := by linarith [Real.add_one_le_exp (128 : ℝ)]
  calc
    _ = (8*(1+Real.exp (2*P)))*τ⁻¹ := by unfold spatialWidthFraction; field_simp
    _ ≤ (16*Real.exp (2*P))*Real.exp P :=
      mul_le_mul (by nlinarith) hτP (inv_nonneg.mpr hτ.le) (by positivity)
    _ = 16*Real.exp (3*P) := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    _ ≤ Real.exp 128 * Real.exp (3*P) := mul_le_mul_of_nonneg_right h16 (by positivity)
    _ = Real.exp (128+3*P) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by unfold spatialSamplingBudget; linarith)

theorem spatialWidthFraction_mul_le_width {K X : Type*} (P : ℝ) {τ : ℝ}
    (hτ1 : τ ≤ 1) (N : X → ℕ) (z : Option K × X) :
    spatialWidthFraction P τ * (N z.2 : ℝ) ≤
      centeredSpatialWidths (Real.exp (2*P)) τ N z := by
  have hfrac : spatialWidthFraction P τ ≤ 1/8 := by
    unfold spatialWidthFraction
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 8*(1+Real.exp (2*P)))).mpr
    nlinarith [Real.exp_pos (2*P)]
  rcases z with ⟨k,i⟩
  cases k with
  | none =>
    change spatialWidthFraction P τ * (N i : ℝ) ≤ (N i : ℝ)/8
    exact (mul_le_mul_of_nonneg_right hfrac (Nat.cast_nonneg _)).trans_eq (by ring)
  | some k =>
    dsimp only [spatialWidthFraction, centeredSpatialWidths]
    apply le_of_eq
    ring

theorem spatial_scale_of_exp_size {P τ H q : ℝ} (hP : 0 ≤ P) (hτ : 0 < τ)
    (hτP : τ⁻¹ ≤ Real.exp P) (hq0 : 0 ≤ q) (hq : q ≤ Real.exp P)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (hH : Real.exp (5*P+128) ≤ H) :
    64*(probabilityProfileLipschitz : ℝ)*q*(1+Real.exp (2*P)) ≤ τ*H := by
  have h1 : 1+Real.exp (2*P) ≤ 2*Real.exp (2*P) := by
    have := Real.one_le_exp_iff.mpr (show 0 ≤ 2*P by positivity)
    linarith
  have h128 : (128 : ℝ) ≤ Real.exp 128 := by linarith [Real.add_one_le_exp (128 : ℝ)]
  have hexp : Real.exp P*Real.exp P*Real.exp (2*P)*Real.exp P = Real.exp (5*P) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [mul_comm τ H]
  apply (div_le_iff₀ hτ).mp
  calc
    _ = 64*(probabilityProfileLipschitz : ℝ)*q*(1+Real.exp (2*P))*τ⁻¹ := div_eq_mul_inv _ _
    _ ≤ 64*Real.exp P*Real.exp P*(2*Real.exp (2*P))*Real.exp P := by
      gcongr
    _ = 128*Real.exp (5*P) := by rw [show
        64*Real.exp P*Real.exp P*(2*Real.exp (2*P))*Real.exp P =
          128*(Real.exp P*Real.exp P*Real.exp (2*P)*Real.exp P) by ring, hexp]
    _ ≤ Real.exp 128*Real.exp (5*P) := mul_le_mul_of_nonneg_right h128 (by positivity)
    _ = Real.exp (5*P+128) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ H := hH

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

noncomputable def trimmedSpatialWidths {K I : Type*} (B τ : ℝ) (N : I → ℕ) : Option K × I → ℝ :=
  fun z => τ * centeredSpatialWidths B 1 N z

theorem trimmedSpatialWidths_pos {K I : Type*} {B τ : ℝ} (hB : 0 ≤ B) (hτ : 0 < τ)
    (N : I → ℕ) (hN : ∀ i, 0 < N i) (z : Option K × I) :
    0 < trimmedSpatialWidths B τ N z :=
  mul_pos hτ (centeredSpatialWidths_pos hB (by norm_num) N hN z)

theorem spatialWidthFraction_le_trimmed_width {K I : Type*} (P : ℝ) {τ : ℝ} (hτ : 0 ≤ τ)
    (N : I → ℕ) (z : Option K × I) :
    spatialWidthFraction P τ * (N z.2 : ℝ) ≤ trimmedSpatialWidths (Real.exp (2*P)) τ N z := by
  have h := mul_le_mul_of_nonneg_left
    (spatialWidthFraction_mul_le_width (K := K) P (by norm_num : (1 : ℝ) ≤ 1) N z) hτ
  have he : spatialWidthFraction P τ = τ * spatialWidthFraction P 1 := by
    unfold spatialWidthFraction
    ring
  rw [he, mul_assoc]
  exact h

namespace BooleanCubeKernel

theorem trimmedSpatialWidths_fit {K I : Type*} [Fintype K] {B τ : ℝ}
    (hB : 0 ≤ B) (hτ : 0 ≤ τ) (root : K → ℤ)
    (hroot : (∑ k, |(root k : ℝ)|) ≤ B) (N : I → ℕ) (i : I) :
    physicalSiteWidth root (trimmedSpatialWidths B τ N) i ≤ τ * (N i : ℝ) / 4 := by
  have h := mul_le_mul_of_nonneg_left
    (centeredSpatialWidths_fit hB (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) ≤ 1)
      root hroot N i) hτ
  have he : physicalSiteWidth root (trimmedSpatialWidths B τ N) i =
      τ * physicalSiteWidth root (centeredSpatialWidths B 1 N) i := by
    simp only [physicalSiteWidth, trimmedSpatialWidths, mul_add, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he]
  nlinarith

end BooleanCubeKernel

noncomputable def spatialTrimMargin {I : Type*} (τ : ℝ) (N : I → ℕ) : I → ℕ :=
  fun i => ⌈τ * (N i : ℝ) / 4⌉₊

theorem spatialTrimMargin_fits {K I : Type*} [Fintype K] {B τ : ℝ}
    (hB : 0 ≤ B) (hτ : 0 ≤ τ) (root : K → ℤ)
    (hroot : (∑ k, |(root k : ℝ)|) ≤ B) (N : I → ℕ) (i : I) :
    BooleanCubeKernel.physicalSiteWidth root (trimmedSpatialWidths B τ N) i ≤
      (spatialTrimMargin τ N i : ℝ) :=
  (BooleanCubeKernel.trimmedSpatialWidths_fit hB hτ root hroot N i).trans (Nat.le_ceil _)

theorem spatialTrimMargin_bound {I : Type*} {τ : ℝ} (N : I → ℕ)
    (hsize : ∀ i, 4 ≤ τ * (N i : ℝ)) (i : I) :
    (spatialTrimMargin τ N i : ℝ) ≤ τ * (N i : ℝ) / 2 := by
  have h := Nat.ceil_lt_add_one (show 0 ≤ τ * (N i : ℝ) / 4 by linarith [hsize i])
  dsimp only [spatialTrimMargin]
  linarith [hsize i]

theorem spatialTrimMargin_proper {I : Type*} {τ : ℝ} (hτ : τ ≤ 1/2)
    (N : I → ℕ) (hN : ∀ i, 0 < N i) (hsize : ∀ i, 4 ≤ τ * (N i : ℝ)) (i : I) :
    2 * spatialTrimMargin τ N i < N i := by
  have hn : (0 : ℝ) < N i := by exact_mod_cast hN i
  have h := spatialTrimMargin_bound N hsize i
  have hi : (2 : ℝ) * (spatialTrimMargin τ N i : ℝ) < N i := by nlinarith
  exact_mod_cast hi

theorem spatialTrimMargin_error_bound {I : Type*} [Fintype I] {τ : ℝ}
    (N : I → ℕ) (hN : ∀ i, 0 < N i) (hsize : ∀ i, 4 ≤ τ * (N i : ℝ)) :
    2 * (∑ i, 2 * (spatialTrimMargin τ N i : ℝ) / N i) ≤ 2 * (Fintype.card I : ℝ) * τ := by
  have hi (i : I) : 2 * (spatialTrimMargin τ N i : ℝ) / N i ≤ τ := by
    apply (div_le_iff₀ (show (0 : ℝ) < N i by exact_mod_cast hN i)).mpr
    linarith [spatialTrimMargin_bound N hsize i]
  calc
    _ ≤ 2 * ∑ _i : I, τ := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hi i)) (by norm_num)
    _ = _ := by simp [mul_assoc]

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

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

theorem trimmedSpatialWidths_scale {K I : Type*} {B τ : ℝ} (hB : 0 ≤ B)
    (modulus : I → ℕ) (hmodulus : ∀ i, 0 < modulus i) (N : I → ℕ)
    (hsize : ∀ i, 64*(probabilityProfileLipschitz : ℝ)*(modulus i : ℝ)*(1+B) ≤ τ*(N i : ℝ))
    (z : Option K × I) :
    8*(probabilityProfileLipschitz : ℝ) ≤
      residueProfileWidth modulus (trimmedSpatialWidths B τ N) z := by
  rcases z with ⟨k,i⟩
  have hm : (0 : ℝ) < modulus i := by exact_mod_cast hmodulus i
  change 8*(probabilityProfileLipschitz : ℝ) ≤ trimmedSpatialWidths B τ N (k,i)/(modulus i : ℝ)
  apply (le_div_iff₀ hm).mpr
  cases k with
  | none =>
    change _ ≤ τ*((N i : ℝ)/8)
    have hl : 64*(probabilityProfileLipschitz : ℝ)*(modulus i : ℝ) ≤
        64*(probabilityProfileLipschitz : ℝ)*(modulus i : ℝ)*(1+B) := by
      apply le_mul_of_one_le_right (by positivity)
      linarith
    nlinarith [hsize i]
  | some k =>
    change _ ≤ τ*(1*(N i : ℝ)/(8*(1+B)))
    rw [one_mul, ← mul_div_assoc]
    apply (le_div_iff₀ (by positivity : (0 : ℝ)<8*(1+B))).mpr
    nlinarith [hsize i]

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators

noncomputable def unconditionedSpatialTrimFraction (d : ℕ) (σ : ℝ) : ℝ :=
  σ / (32 * (d + 1))

noncomputable def unconditionedSpatialWidthCutoff (B τ L : ℝ) : ℝ :=
  max (4 / τ) (8 * (1 + B) * max (8 * (probabilityProfileLipschitz : ℝ)) L / τ)

theorem unconditionedSpatialTrimFraction_bounds (d : ℕ) {σ : ℝ}
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    0 < unconditionedSpatialTrimFraction d σ ∧
      unconditionedSpatialTrimFraction d σ ≤ 1/2 ∧
      2 * (d : ℝ) * unconditionedSpatialTrimFraction d σ ≤ σ / 8 := by
  have hd : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  have hden : 0 < 32 * ((d : ℝ) + 1) := by positivity
  unfold unconditionedSpatialTrimFraction
  refine ⟨div_pos hσ hden, ?_, ?_⟩
  · apply (div_le_iff₀ hden).mpr
    nlinarith
  · rw [← mul_div_assoc]
    apply (div_le_iff₀ hden).mpr
    nlinarith

theorem unconditionedSpatialWidthCutoff_bounds {K X : Type*} [Fintype X]
    {B τ L σ : ℝ} (hB : 0 ≤ B) (hτ : 0 < τ) (hτhalf : τ ≤ 1/2)
    (hbudget : 2 * (Fintype.card X : ℝ) * τ ≤ σ / 8)
    (N : X → ℕ) (hN : ∀ i, unconditionedSpatialWidthCutoff B τ L ≤ (N i : ℝ)) :
    (∀ i, 0 < N i) ∧
    (∀ i, 4 ≤ τ * (N i : ℝ)) ∧
    (∀ z : Option K × X, 0 < trimmedSpatialWidths B τ N z) ∧
    (∀ z : Option K × X, 8 * (probabilityProfileLipschitz : ℝ) ≤
      residueProfileWidth (fun _ : X => 1) (trimmedSpatialWidths B τ N) z) ∧
    (∀ z : Option K × X, L ≤ trimmedSpatialWidths B τ N z) ∧
    (∀ i, 2 * spatialTrimMargin τ N i < N i) ∧
    2 * (∑ i, 2 * (spatialTrimMargin τ N i : ℝ) / N i) ≤ σ / 8 := by
  have hsize (i : X) : 4 ≤ τ * (N i : ℝ) := by
    have hh := (le_max_left _ _).trans (hN i)
    have hh' := (div_le_iff₀ hτ).mp hh
    linarith
  have hpos (i : X) : 0 < N i := by
    have hh : 0 < (N i : ℝ) := by nlinarith [hsize i]
    exact_mod_cast hh
  let M : ℝ := max (8 * (probabilityProfileLipschitz : ℝ)) L
  have hM : 0 ≤ M := (by positivity : (0 : ℝ) ≤ 8 * (probabilityProfileLipschitz : ℝ)).trans
    (le_max_left _ _)
  have hwide (i : X) : 8 * (1 + B) * M ≤ τ * (N i : ℝ) := by
    have hh := (le_max_right _ _).trans (hN i)
    have hh' := (div_le_iff₀ hτ).mp hh
    linarith
  have hwidth (z : Option K × X) : M ≤ trimmedSpatialWidths B τ N z := by
    rcases z with ⟨k, i⟩
    cases k with
    | none =>
      change M ≤ τ * ((N i : ℝ) / 8)
      have hh : 8 * M ≤ 8 * (1 + B) * M := by nlinarith
      nlinarith [hwide i]
    | some k =>
      change M ≤ τ * (1 * (N i : ℝ) / (8 * (1 + B)))
      rw [one_mul, ← mul_div_assoc]
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < 8 * (1 + B))).mpr
      nlinarith [hwide i]
  refine ⟨hpos, hsize, trimmedSpatialWidths_pos hB hτ N hpos, ?_, ?_,
    spatialTrimMargin_proper hτhalf N hpos hsize,
    (spatialTrimMargin_error_bound N hpos hsize).trans hbudget⟩
  · intro z
    change 8 * (probabilityProfileLipschitz : ℝ) ≤ trimmedSpatialWidths B τ N z / (1 : ℕ)
    simpa only [Nat.cast_one, div_one] using (le_max_left _ _).trans (hwidth z)
  · intro z
    exact (le_max_right _ _).trans (hwidth z)

theorem unconditionedSpatialWidthBudget {K X : Type*} [Fintype X]
    {B L σ : ℝ} (hB : 0 ≤ B) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (N : X → ℕ)
    (hN : ∀ i, unconditionedSpatialWidthCutoff B
      (unconditionedSpatialTrimFraction (Fintype.card X) σ) L ≤ (N i : ℝ)) :
    let τ := unconditionedSpatialTrimFraction (Fintype.card X) σ
    (∀ i, 0 < N i) ∧
    (∀ i, 4 ≤ τ * (N i : ℝ)) ∧
    (∀ z : Option K × X, 0 < trimmedSpatialWidths B τ N z) ∧
    (∀ z : Option K × X, 8 * (probabilityProfileLipschitz : ℝ) ≤
      residueProfileWidth (fun _ : X => 1) (trimmedSpatialWidths B τ N) z) ∧
    (∀ z : Option K × X, L ≤ trimmedSpatialWidths B τ N z) ∧
    (∀ i, 2 * spatialTrimMargin τ N i < N i) ∧
    2 * (∑ i, 2 * (spatialTrimMargin τ N i : ℝ) / N i) ≤ σ / 8 := by
  obtain ⟨hτ, hτhalf, hbudget⟩ := unconditionedSpatialTrimFraction_bounds (Fintype.card X) hσ hσ1
  exact unconditionedSpatialWidthCutoff_bounds hB hτ hτhalf hbudget N hN

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueLinearPointCap
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def integerArrayLinearForm {D : Type*} [Fintype D] (c z : D → ℤ) : ℤ := ∑ d, c d * z d

theorem integerArrayLinearForm_affine_join {D : Type*} [Fintype D] [DecidableEq D]
    (c a q : D → ℤ) (j : D) (tail : {d : D // d ≠ j} → ℤ) (x : ℤ) :
    integerArrayLinearForm c (fun d => a d + q d * coordinateJoin j tail x d) =
      c j * (a j + q j * x) + ∑ d : {d : D // d ≠ j}, c d.val * (a d.val + q d.val * tail d) := by
  rw [integerArrayLinearForm, Fintype.sum_eq_add_sum_subtype_ne _ j]
  simp only [coordinateJoin_pivot, coordinateJoin_other]

theorem integerArrayLinearForm_pivot_injective {D : Type*} [Fintype D] [DecidableEq D]
    (c a q : D → ℤ) (j : D) (hc : c j ≠ 0) (hq : q j ≠ 0)
    (tail : {d : D // d ≠ j} → ℤ) :
    Function.Injective (fun x => integerArrayLinearForm c
      (fun d => a d + q d * coordinateJoin j tail x d)) := by
  intro x y h
  simp only [integerArrayLinearForm_affine_join] at h
  exact mul_left_cancel₀ hq (add_left_cancel (mul_left_cancel₀ hc (add_right_cancel h)))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem residueSmoothPMF_linear_cap {K I : Type*} [Fintype K] [Fintype I]
    (c residue : K × I → ℤ) (modulus : I → ℕ) (hmodulus : ∀ i, 0 < modulus i)
    (W : K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue modulus) (residueProfileWidth modulus W))
    (j : K × I) (hc : c j ≠ 0)
    (hscale : 8*(probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth modulus W j) (y : ℤ) :
    ((residueSmoothPMF residue modulus hmodulus W hW hZ).map (integerArrayLinearForm c) y).toReal ≤
      2*(modulus j.2 : ℝ)/W j := by
  rw [residueSmoothPMF, PMF.map_comp, residueSmoothIndexPMF]
  have hq : (modulus j.2 : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hmodulus j.2))
  have h := shiftedSmoothProductPMF_coordinate_cap (residueProfileCenter residue modulus)
    (residueProfileWidth modulus W) (residueProfileWidth_pos modulus W hmodulus hW) hZ j
    (integerArrayLinearForm c ∘ residueLatticeArray residue modulus)
    (integerArrayLinearForm_pivot_injective c residue (fun d => (modulus d.2 : ℤ)) j hc hq)
    hscale y
  simpa only [residueProfileWidth, div_div_eq_mul_div] using h

theorem selectedResidueSmoothPMF_linear_cap {K I : Type*} [Fintype K] [Fintype I]
    (c : K × I → ℤ) (modulus : I → ℕ) (hmodulus : ∀ i, 0 < modulus i)
    (T : Finset (ColumnResiduePattern K I modulus)) (hT : T.Nonempty)
    (W : K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
    (hscale : ∀ z, 8*(probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth modulus W z)
    (j : K × I) (hc : c j ≠ 0) (y : ℤ) :
    ((selectedResidueSmoothPMF modulus T W hW hZ).map (integerArrayLinearForm c) y).toReal ≤
      2*(modulus j.2 : ℝ)/W j := by
  have hcell (r : T) : 0 < shiftedSmoothProductMass
      (residueProfileCenter (columnResidueRepresentative modulus r.val) modulus)
      (residueProfileWidth modulus W) := shiftedSmoothProductMass_pos_of_scales _ _ hscale
  obtain ⟨_, h⟩ := selectedResidueSmoothPMF_bound_of_cells (ε := 2*(modulus j.2 : ℝ)/W j)
    modulus hmodulus T hT W hW hcell
    (fun z => if integerArrayLinearForm c z = y then (1 : ℂ) else 0)
    (by
      intro r
      exact (pmf_point_indicator_norm _ (integerArrayLinearForm c) y).trans_le
        (residueSmoothPMF_linear_cap c (columnResidueRepresentative modulus r.val)
          modulus hmodulus W hW (hcell r) j hc (hscale j) y))
  exact (pmf_point_indicator_norm _ (integerArrayLinearForm c) y).symm.trans_le h

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.QuantitativeNoninjectivity
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def noninjectivityIndicator {J Y : Type*} (f : J → Y) : ℝ :=
  if Function.Injective f then 0 else 1

theorem noninjectivityIndicator_nonneg {J Y : Type*} (f : J → Y) :
    0 ≤ noninjectivityIndicator f := by
  unfold noninjectivityIndicator
  split_ifs <;> norm_num

theorem noninjectivityIndicator_le_pairs {J Y : Type*} [Fintype J] [DecidableEq J]
    [DecidableEq Y] (f : J → Y) :
    noninjectivityIndicator f ≤ ∑ j, ∑ k, if j = k then 0 else if f j = f k then (1 : ℝ) else 0 := by
  have hn (j k : J) : 0 ≤ (if j = k then 0 else if f j = f k then (1 : ℝ) else 0) := by
    split_ifs <;> norm_num
  by_cases hf : Function.Injective f
  · simp only [noninjectivityIndicator, if_pos hf]
    exact Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun k _ => hn j k))
  · have hpair : ∃ j k, j ≠ k ∧ f j = f k := by
      by_contra h
      apply hf
      intro j k he
      by_contra hne
      exact h ⟨j,k,hne,he⟩
    obtain ⟨j,k,hjk,he⟩ := hpair
    simp only [noninjectivityIndicator, if_neg hf]
    calc
      (1 : ℝ) = (if j = k then 0 else if f j = f k then 1 else 0) := by simp [hjk,he]
      _ ≤ ∑ l, if j = l then 0 else if f j = f l then (1 : ℝ) else 0 :=
        Finset.single_le_sum (fun l _ => hn j l) (Finset.mem_univ k)
      _ ≤ _ := Finset.single_le_sum
        (fun l _ => Finset.sum_nonneg (fun k _ => hn l k)) (Finset.mem_univ j)

namespace FiniteProbabilityWeights

theorem mean_fintype_sum {Ω J : Type*} [Fintype Ω] [Fintype J]
    (p : FiniteProbabilityWeights Ω) (f : J → Ω → ℝ) :
    p.mean (fun x => ∑ j, f j x) = ∑ j, p.mean (f j) := by
  simp only [mean, Finset.mul_sum]
  exact Finset.sum_comm

theorem noninjectivity_le {Ω J Y : Type*} [Fintype Ω] [Fintype J] [DecidableEq J]
    [DecidableEq Y] (p : FiniteProbabilityWeights Ω) (F : Ω → J → Y)
    {C : ℝ} (hC : 0 ≤ C)
    (hp : ∀ j k, j ≠ k → p.mean (fun x => if F x j = F x k then 1 else 0) ≤ C) :
    p.mean (fun x => noninjectivityIndicator (F x)) ≤ (Fintype.card J : ℝ)^2*C := by
  have hm := p.mean_mono (fun x => noninjectivityIndicator_le_pairs (F x))
  simp_rw [mean_fintype_sum] at hm
  refine hm.trans ?_
  calc
    _ ≤ ∑ _j : J, ∑ _k : J, C := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      by_cases he : j = k
      · simpa only [if_pos he, mean_const] using hC
      · simpa only [if_neg he] using hp j k he
    _ = _ := by simp [pow_two, mul_assoc]

theorem reweightPositive_noninjectivity_le {Ω J Y : Type*} [Fintype Ω] [Fintype J]
    [DecidableEq J] [DecidableEq Y] (p : FiniteProbabilityWeights Ω) (F : Ω → J → Y)
    (D : Ω → ℝ) (hD0 : ∀ x, 0 ≤ D x) (hD : 0 < p.mean D)
    {M C : ℝ} (hM : 0 ≤ M) (hcap : ∀ x, D x ≤ M) (hlower : 1/2 ≤ p.mean D)
    (hC : 0 ≤ C)
    (hp : ∀ j k, j ≠ k → p.mean (fun x => if F x j = F x k then 1 else 0) ≤ C) :
    (p.reweightPositive D hD0 hD).mean (fun x => noninjectivityIndicator (F x)) ≤
      2*M*((Fintype.card J : ℝ)^2*C) := by
  have hb : p.mean (fun x => D x * noninjectivityIndicator (F x)) ≤
      M * p.mean (fun x => noninjectivityIndicator (F x)) := by
    rw [← mean_const_mul]
    exact p.mean_mono (fun x => mul_le_mul_of_nonneg_right (hcap x) (noninjectivityIndicator_nonneg _))
  have ht := p.reweightPositive_test_le D hD0 hD (fun x => noninjectivityIndicator (F x))
    (fun x => noninjectivityIndicator_nonneg _) (a := 1/2) (ε := 0) (by norm_num) hlower
    (by simpa only [add_zero] using hb)
  have hpair := p.noninjectivity_le F hC hp
  have hmul := mul_le_mul_of_nonneg_left hpair (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hM)
  exact (ht.trans_eq (by ring)).trans hmul

end FiniteProbabilityWeights
end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

def jointIntegerPhysicalSite {K I : Type*} [Fintype K] (root : K → ℤ)
    (z : (I → ℤ) × (Option K × I → ℤ)) : I → ℤ :=
  z.1 + integerPhysicalSite root z.2

theorem jointIntegerPhysicalSite_cast {K I : Type*} [Fintype K]
    (root : K → ℤ) (z : (I → ℤ) × (Option K × I → ℤ)) :
    (fun i => (jointIntegerPhysicalSite root z i : ℝ)) =
      (fun i => (z.1 i : ℝ)) + physicalAffineSite root z.2 := by
  funext i
  simp only [jointIntegerPhysicalSite, Pi.add_apply, Int.cast_add,
    integerPhysicalSite_cast_apply]

theorem jointIntegerPhysicalSite_mem_box {K I : Type*}
    [Fintype K] [Fintype I] [DecidableEq I]
    (root : K → ℤ) (N R : I → ℕ) (hR : ∀ i, 2 * R i ≤ N i)
    (W : Option K × I → ℝ) (hwidth : ∀ i, physicalSiteWidth root W i ≤ (R i : ℝ))
    (z : trimmedIntegerBox N R × rectangularWeightIndices 0 W 1) :
    jointIntegerPhysicalSite root (z.1.val, z.2.val) ∈ integerBox N := by
  apply trimmedIntegerBox_add_mem N R hR z.1.property
  intro i
  have h := (integerPhysicalSite_abs_bound root W z.2.val
    (rectangularWeightIndices_zero_bound W z.2.property) i).trans (hwidth i)
  exact_mod_cast h

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

def rowDifferenceCoefficients {K I : Type*} [DecidableEq I]
    (r s : K → ℤ) (i : I) (z : Option K × I) : ℤ :=
  if z.2 = i then z.1.elim 0 (fun k => r k - s k) else 0

theorem rowDifferenceCoefficients_linear {K I : Type*} [Fintype K] [Fintype I] [DecidableEq I]
    (r s : K → ℤ) (i : I) (z : Option K × I → ℤ) :
    integerArrayLinearForm (rowDifferenceCoefficients r s i) z =
      integerPhysicalSite r z i - integerPhysicalSite s z i := by
  have he : integerArrayLinearForm (rowDifferenceCoefficients r s i) z =
      ∑ k, (r k - s k) * z (some k,i) := by
    simp [integerArrayLinearForm, rowDifferenceCoefficients, Fintype.sum_prod_type,
      Fintype.sum_option, ite_mul]
  rw [he]
  simp only [integerPhysicalSite, sub_mul, Finset.sum_sub_distrib]
  ring

theorem selectedResidue_site_collision_le {K I : Type*} [Fintype K] [Fintype I] [DecidableEq I]
    (r s : K → ℤ) (k : K) (hk : r k ≠ s k) (i : I)
    (modulus : I → ℕ) (hmodulus : ∀ i, 0 < modulus i)
    (T : Finset (ColumnResiduePattern (Option K) I modulus)) (hT : T.Nonempty)
    (W : Option K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
    (hscale : ∀ z, 8*(probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth modulus W z) :
    (selectedResidueFiniteLaw modulus T W hW hZ).mean
      (fun z => if integerPhysicalSite r z.val = integerPhysicalSite s z.val then 1 else 0) ≤
        2*(modulus i : ℝ)/W (some k,i) := by
  let c := rowDifferenceCoefficients r s i
  have hc : c (some k,i) ≠ 0 := by
    simpa [c, rowDifferenceCoefficients] using sub_ne_zero.mpr hk
  have hp := selectedResidueSmoothPMF_linear_cap c modulus hmodulus T hT W hW hZ hscale (some k,i) hc 0
  have he : (selectedResidueFiniteLaw modulus T W hW hZ).mean
      (fun z => if integerArrayLinearForm c z.val = 0 then 1 else 0) ≤
        2*(modulus i : ℝ)/W (some k,i) :=
    (selectedResidueFiniteLaw_mean modulus T W hW hZ
      (fun z => if integerArrayLinearForm c z = 0 then 1 else 0)).trans_le
      ((pmf_map_toReal_indicator _ (integerArrayLinearForm c) 0).symm.trans_le hp)
  refine le_trans ((selectedResidueFiniteLaw modulus T W hW hZ).mean_mono ?_) he
  intro z
  by_cases h : integerPhysicalSite r z.val = integerPhysicalSite s z.val
  · have hz : integerArrayLinearForm c z.val = 0 := by
      rw [rowDifferenceCoefficients_linear, congrFun h i, sub_self]
    simp only [if_pos h, if_pos hz, le_refl]
  · simp only [if_neg h]
    split_ifs <;> norm_num

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3

open scoped BigOperators Classical

namespace BooleanCubeKernel

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

theorem selectedResidue_distinct_collision_le {K I : Type*} [Fintype K] [Fintype I] [DecidableEq I]
    (r s : K → ℤ) (hrs : r ≠ s) (i : I)
    (modulus : I → ℕ) (hmodulus : ∀ i, 0 < modulus i)
    (T : Finset (ColumnResiduePattern (Option K) I modulus)) (hT : T.Nonempty)
    (W : Option K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
    (hscale : ∀ z, 8*(probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth modulus W z)
    {L : ℝ} (hL : 0 < L) (hwidth : ∀ k, L ≤ W (some k,i)) :
    (selectedResidueFiniteLaw modulus T W hW hZ).mean
      (fun z => if integerPhysicalSite r z.val = integerPhysicalSite s z.val then 1 else 0) ≤
        2*(modulus i : ℝ)/L := by
  have hdiff : ∃ k, r k ≠ s k := by
    by_contra h
    apply hrs
    funext k
    by_contra hk
    exact h ⟨k,hk⟩
  obtain ⟨k,hk⟩ := hdiff
  exact (selectedResidue_site_collision_le r s k hk i modulus hmodulus T hT W hW hZ hscale).trans
    (div_le_div_of_nonneg_left (by positivity) hL (hwidth k))

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

end Erdos3.BooleanCubeKernel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.JointSamplerProductivity
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

namespace FiniteProbabilityWeights

theorem productive_mass_lower_bound {Ω : Type*} [Fintype Ω]
    (p : FiniteProbabilityWeights Ω) (score : Ω → ℝ) (bad : Finset Ω)
    {a : ℝ} (ha : 0 ≤ a) (hscore : ∀ x, score x ≤ 1) :
    p.mean score - a - p.mass bad ≤
      p.mass (Finset.univ.filter (fun x => x ∉ bad ∧ a ≤ score x)) := by
  classical
  let productive := Finset.univ.filter (fun x => x ∉ bad ∧ a ≤ score x)
  have hpoint (x : Ω) : score x ≤ a + (if x ∈ productive then 1 else 0) +
      (if x ∈ bad then 1 else 0) := by
    by_cases hb : x ∈ bad
    · simp only [hb, ite_true]
      split_ifs <;> linarith [hscore x]
    · by_cases hs : a ≤ score x
      · have hp : x ∈ productive := by simp [productive, hb, hs]
        simp only [hb, hp, ite_true, ite_false]
        linarith [hscore x]
      · have hp : x ∉ productive := by simp [productive, hs]
        simp only [hb, hp, ite_false, add_zero]
        linarith
  have h := p.mean_mono hpoint
  rw [p.mean_add, p.mean_add, p.mean_const, p.mean_indicator, p.mean_indicator] at h
  linarith

end FiniteProbabilityWeights

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

theorem integral_productive_sampler_mass {C Ω : Type*}
    [MeasurableSpace C] [Fintype Ω]
    (μ : Measure C) [IsProbabilityMeasure μ]
    (law : C → FiniteProbabilityWeights Ω) (score : C → Ω → ℝ)
    (bad : C → Finset Ω) {σ : ℝ} (hσ : 0 < σ)
    (hscore : ∀ c z, score c z ≤ 1)
    (hiScore : Integrable (fun c => (law c).mean (score c)) μ)
    (hiBad : Integrable (fun c => (law c).mass (bad c)) μ)
    (hiProductive : Integrable (fun c => (law c).mass
      (Finset.univ.filter (fun z => z ∉ bad c ∧ σ / 2 ≤ score c z))) μ)
    (hmean : 7 * σ / 8 ≤ ∫ c, (law c).mean (score c) ∂μ)
    (hbad : (∫ c, (law c).mass (bad c) ∂μ) ≤ σ / 16) :
    σ / 4 ≤ ∫ c, (law c).mass
      (Finset.univ.filter (fun z => z ∉ bad c ∧ σ / 2 ≤ score c z)) ∂μ := by
  have h := integral_mono ((hiScore.sub (integrable_const (σ / 2))).sub hiBad)
    hiProductive (fun c => (law c).productive_mass_lower_bound (score c) (bad c)
      (by positivity : 0 ≤ σ / 2) (hscore c))
  simp only [Pi.sub_apply] at h
  rw [integral_sub (f := fun c => (law c).mean (score c) - σ / 2)
      (g := fun c => (law c).mass (bad c))
      (hiScore.sub (integrable_const (σ / 2))) hiBad,
    integral_sub hiScore (integrable_const (σ / 2)),
    integral_const, probReal_univ, one_smul] at h
  linarith

theorem integral_productive_injective_mass {C Ω R Y : Type*}
    [MeasurableSpace C] [Fintype Ω] [Fintype R]
    (μ : Measure C) [IsProbabilityMeasure μ]
    (law : C → FiniteProbabilityWeights Ω) (sites : FiniteProbabilityWeights R)
    (image : Ω → R → Y) (test : Y → ℝ)
    {σ η parent : ℝ} (hσ : 0 < σ) (hη : η ≤ σ / 8) (hparent : σ ≤ parent)
    (htest : ∀ y, test y ≤ 1)
    (hint : ∀ r, Integrable (fun c => (law c).mean (fun z => test (image z r))) μ)
    (hmarginal : ∀ r, parent - η ≤ ∫ c, (law c).mean (fun z => test (image z r)) ∂μ)
    (hiBad : Integrable (fun c => (law c).mean
      (fun z => noninjectivityIndicator (image z))) μ)
    (hiProductive : Integrable (fun c => (law c).mass (Finset.univ.filter (fun z =>
      Function.Injective (image z) ∧ σ / 2 ≤ sites.mean (fun r => test (image z r))))) μ)
    (hcollision : (∫ c, (law c).mean (fun z => noninjectivityIndicator (image z)) ∂μ) ≤ σ / 16) :
    σ / 4 ≤ ∫ c, (law c).mass (Finset.univ.filter (fun z =>
      Function.Injective (image z) ∧ σ / 2 ≤ sites.mean (fun r => test (image z r)))) ∂μ := by
  let score := fun z => sites.mean (fun r => test (image z r))
  let bad := Finset.univ.filter (fun z => ¬Function.Injective (image z))
  have hscore (z) : score z ≤ 1 := by
    calc
      _ ≤ sites.mean (fun _ => 1) := sites.mean_mono (fun r => htest _)
      _ = 1 := sites.mean_const 1
  have hbad (c) : (law c).mass bad =
      (law c).mean (fun z => noninjectivityIndicator (image z)) := by
    rw [← (law c).mean_indicator]
    congr 1
    funext z
    by_cases hz : Function.Injective (image z) <;> simp [bad, hz, noninjectivityIndicator]
  have hprod : (Finset.univ.filter (fun z => z ∉ bad ∧ σ / 2 ≤ score z)) =
      Finset.univ.filter (fun z => Function.Injective (image z) ∧
        σ / 2 ≤ sites.mean (fun r => test (image z r))) := by
    simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and, not_not, score]
  have he (c) : (law c).mean score =
      sites.mean (fun r => (law c).mean (fun z => test (image z r))) :=
    (law c).mean_comm sites (fun z r => test (image z r))
  have hi : Integrable (fun c => (law c).mean score) μ := by
    simp_rw [he]
    exact sites.mean_integrable μ _ hint
  have havg : 7 * σ / 8 ≤ ∫ c, (law c).mean score ∂μ := by
    simp_rw [he]
    rw [sites.integral_mean μ _ hint]
    calc
      _ ≤ parent - η := by linarith
      _ = sites.mean (fun _ => parent - η) := (sites.mean_const _).symm
      _ ≤ _ := sites.mean_mono hmarginal
  have hiBad' : Integrable (fun c => (law c).mass bad) μ := by
    simp_rw [hbad]
    exact hiBad
  have hiProd' : Integrable (fun c => (law c).mass
      (Finset.univ.filter (fun z => z ∉ bad ∧ σ / 2 ≤ score z))) μ := by
    simpa only [hprod] using hiProductive
  have hbad' : (∫ c, (law c).mass bad ∂μ) ≤ σ / 16 := by
    simpa only [hbad] using hcollision
  have h := integral_productive_sampler_mass μ law (fun _ => score) (fun _ => bad)
    hσ (fun _ => hscore) hi hiBad' hiProd' havg hbad'
  simpa only [hprod] using h

theorem integral_productive_injective_mass_of_complex_marginals {C Ω R Y : Type*}
    [MeasurableSpace C] [Fintype Ω] [Fintype R]
    (μ : Measure C) [IsProbabilityMeasure μ]
    (law : C → FiniteProbabilityWeights Ω) (sites : FiniteProbabilityWeights R)
    (image : Ω → R → Y) (test : Y → ℝ)
    {σ η parent : ℝ} (hσ : 0 < σ) (hη : η ≤ σ / 8) (hparent : σ ≤ parent)
    (htest : ∀ y, test y ≤ 1)
    (hint : ∀ r, Integrable
      (fun c => (law c).complexMean (fun z => (test (image z r) : ℂ))) μ)
    (hmarginal : ∀ r, ‖(∫ c, (law c).complexMean (fun z => (test (image z r) : ℂ)) ∂μ) -
      (parent : ℂ)‖ ≤ η)
    (hiBad : Integrable (fun c => (law c).mean
      (fun z => noninjectivityIndicator (image z))) μ)
    (hiProductive : Integrable (fun c => (law c).mass (Finset.univ.filter (fun z =>
      Function.Injective (image z) ∧ σ / 2 ≤ sites.mean (fun r => test (image z r))))) μ)
    (hcollision : (∫ c, (law c).mean (fun z => noninjectivityIndicator (image z)) ∂μ) ≤ σ / 16) :
    σ / 4 ≤ ∫ c, (law c).mass (Finset.univ.filter (fun z =>
      Function.Injective (image z) ∧ σ / 2 ≤ sites.mean (fun r => test (image z r)))) ∂μ := by
  apply integral_productive_injective_mass μ law sites image test hσ hη hparent htest
  · intro r
    have hi := (hint r).re
    change Integrable (fun c => ((law c).complexMean
      (fun z => (test (image z r) : ℂ))).re) μ at hi
    simpa only [FiniteProbabilityWeights.complexMean_ofReal, Complex.ofReal_re] using hi
  · intro r
    have h := hmarginal r
    simp only [FiniteProbabilityWeights.complexMean_ofReal, integral_complex_ofReal,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h
    linarith [(abs_le.mp h).1]
  · exact hiBad
  · exact hiProductive
  · exact hcollision

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.PhysicalCubeMatrix
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Matrix

def physicalCubeCoefficient {K α : Type*} (root : K → ℤ) (D : Matrix α K ℤ) :
    Matrix (Unit ⊕ α) (Option K) ℤ
  | .inl _, none => 1
  | .inl _, some k => root k
  | .inr _, none => 0
  | .inr i, some k => D i k

def physicalCubeOffset {X α : Type*} (base : X → ℤ) (x : X) : (Unit ⊕ α) → ℤ
  | .inl _ => base x
  | .inr _ => 0

def physicalCubeRootDifferences {K X α : Type*} [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (z : Option K × X → ℤ) : X → (Unit ⊕ α) → ℤ :=
  fun x i => physicalCubeOffset base x i + ∑ k, physicalCubeCoefficient root D i k * z (k, x)

theorem physicalCubeRootDifferences_root {K X α : Type*} [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (z : Option K × X → ℤ) (x : X) :
    physicalCubeRootDifferences root D base z x (.inl ()) =
      jointIntegerPhysicalSite root (base, z) x := by
  simp [physicalCubeRootDifferences, physicalCubeOffset, physicalCubeCoefficient,
    jointIntegerPhysicalSite, integerPhysicalSite]

theorem physicalCubeRootDifferences_direction {K X α : Type*} [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (z : Option K × X → ℤ) (x : X) (i : α) :
    physicalCubeRootDifferences root D base z x (.inr i) = ∑ k, D i k * z (some k, x) := by
  simp [physicalCubeRootDifferences, physicalCubeOffset, physicalCubeCoefficient]

theorem physicalCubeRootDifferences_vertex {K X α : Type*} [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (z : Option K × X → ℤ) (x : X) (t : Finset α) :
    physicalCubeRootDifferences root D base z x (.inl ()) +
        ∑ i ∈ t, physicalCubeRootDifferences root D base z x (.inr i) =
      jointIntegerPhysicalSite (integerAffineCube root D t) (base, z) x := by
  rw [physicalCubeRootDifferences_root]
  simp_rw [physicalCubeRootDifferences_direction]
  have hs : (∑ k, ∑ i ∈ t, D i k * z (some k, x)) =
      ∑ i ∈ t, ∑ k, D i k * z (some k, x) := Finset.sum_comm
  simp only [jointIntegerPhysicalSite, integerPhysicalSite, Pi.add_apply,
    integerAffineCube, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
  rw [hs]
  ring

end Erdos3.BooleanCubeKernel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalAmbientVolumeRatio
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Matrix

def centeredPhysicalCubeMap {K X α : Type*} [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (z : Option K × X → ℤ) : X → (Unit ⊕ α) → ℤ :=
  fun d => physicalCubeCoefficient root D *ᵥ (fun k => z (k, d))

noncomputable def centeredPhysicalCubeWindow {K X α : Type*}
    [Fintype K] [Fintype X] [Fintype α]
    (root : K → ℤ) (D : Matrix α K ℤ) (Q : Option K × X → ℝ) : Finset (X → (Unit ⊕ α) → ℤ) :=
  (rectangularWeightIndices 0 Q 1).image (centeredPhysicalCubeMap root D)

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

end Erdos3.BooleanCubeKernel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalRowsSiteReconstruction
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators

def physicalCubeVertexValue {I α : Type*} (v : I → (Unit ⊕ α) → ℤ) (s : Finset α) : I → ℤ :=
  fun i => v i (.inl ()) + ∑ a ∈ s, v i (.inr a)

theorem physicalCubeVertexValue_rootDifferences {I K α : Type*} [Fintype K]
    (root : K → ℤ) (difference : Matrix α K ℤ) (base : I → ℤ)
    (z : Option K × I → ℤ) (s : Finset α) :
    physicalCubeVertexValue (physicalCubeRootDifferences root difference base z) s =
      jointIntegerPhysicalSite (integerAffineCube root difference s) (base, z) := by
  funext i
  exact physicalCubeRootDifferences_vertex root difference base z i s

theorem integerSiteValue_affine_physical {I K : Type*} [Fintype K] {q : ℕ}
    (root : K → ℤ) (difference : Fin q → K → ℤ) (base : I → ℤ)
    (z : Option K × I → ℤ) (s : Finset (Fin q)) :
    (fun i => (base i : ℝ)) + integerSiteValue (affineSite root difference s)
        (fun k i => (z (k, i) : ℝ)) =
      fun i => (physicalCubeVertexValue (physicalCubeRootDifferences root (Matrix.of difference) base z) s i : ℝ) := by
  rw [physicalCubeVertexValue_rootDifferences]
  change (fun i => (base i : ℝ)) + physicalAffineSite (integerAffineCube root (Matrix.of difference) s) z = _
  exact (jointIntegerPhysicalSite_cast (integerAffineCube root (Matrix.of difference) s) (base, z)).symm

noncomputable def physicalCubeCoveredSample {I : Type*} {m q : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (D : ℕ)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hm : ∀ j d, coefficients (p j) d ∈ U j) (v : I → (Unit ⊕ Fin q) → ℤ) :
    ∀ j, SubspaceArrayTorus (Finset (Fin q)) (U j) := fun j =>
  QuotientAddGroup.mk' (subspaceArrayIntegerLattice (Finset (Fin q)) (U j))
    ((D : ℝ)⁻¹ • fun s => eval (fun i => (physicalCubeVertexValue v s i : ℝ))
      (restrictCoefficients (U j) (p j) (hm j)))

theorem affineCoveredSiteSample_physical {I K : Type*} [Fintype K] {m q : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    (root : K → ℤ) (difference : Fin q → K → ℤ) (D : ℕ)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hm : ∀ j d, coefficients (p j) d ∈ U j) (base : I → ℤ) (z : Option K × I → ℤ) :
    affineCoveredSiteSample U root difference D
        (fun j => translate (fun i => (base i : ℝ)) (p j))
        (fun j => coefficients_translate_mem (U j) (fun i => (base i : ℝ)) (p j) (hm j))
        (fun k i => (z (k, i) : ℝ)) =
      physicalCubeCoveredSample U D p hm (physicalCubeRootDifferences root (Matrix.of difference) base z) := by
  funext j
  rw [affineCoveredSiteSample_eq_values]
  dsimp only [physicalCubeCoveredSample]
  apply congrArg (QuotientAddGroup.mk' (subspaceArrayIntegerLattice (Finset (Fin q)) (U j)))
  apply congrArg (fun v : Finset (Fin q) → U j => (D : ℝ)⁻¹ • v)
  funext s
  apply Subtype.ext
  rw [eval_restrictCoefficients, eval_restrictCoefficients, eval_translate]
  apply congrArg (fun x : I → ℝ => eval x (p j))
  funext i
  have h := congrFun (integerSiteValue_affine_physical root difference base z s) i
  simpa only [Pi.add_apply, add_comm] using h

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators

noncomputable def physicalCubeSiteTest {I : Type*} {q : ℕ}
    (test : Finset (Fin q) → (I → ℝ) → ℂ) (v : I → (Unit ⊕ Fin q) → ℤ) : ℂ :=
  ∏ s, test s (fun i => (physicalCubeVertexValue v s i : ℝ))

theorem physicalCubeSiteTest_norm_le {I : Type*} {q : ℕ}
    (test : Finset (Fin q) → (I → ℝ) → ℂ) (htest : ∀ s x, ‖test s x‖ ≤ 1)
    (v : I → (Unit ⊕ Fin q) → ℤ) : ‖physicalCubeSiteTest test v‖ ≤ 1 := by
  rw [physicalCubeSiteTest, norm_prod]
  exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun s _ => htest s _)

theorem layeredSiteWeight_physicalCube {I K : Type*} [Fintype K] {q : ℕ}
    (root : K → ℤ) (difference : Fin q → K → ℤ) (base : I → ℤ)
    (test : Finset (Fin q) → (I → ℝ) → ℂ) (z : Option K × I → ℤ) :
    layeredSiteWeight 0 (fun s => affineSite root difference s)
        (fun s x => test s ((fun i => (base i : ℝ)) + x)) (fun k i => (z (k, i) : ℝ)) =
      physicalCubeSiteTest test (physicalCubeRootDifferences root (Matrix.of difference) base z) := by
  simp only [layeredSiteWeight, map_zero, AddCircle.coe_zero,
    CircleFourier.character_zero, one_mul, physicalCubeSiteTest]
  apply Finset.prod_congr rfl
  intro s _
  rw [integerSiteValue_affine_physical]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

noncomputable def starVertexSiteFactor {α V : Type*} [Fintype α]
    (factor : Unit ⊕ α → V → ℂ) (s : Finset α) (v : V) : ℂ :=
  ∏ i, if spatialStarVertex i = s then factor i v else 1

theorem starVertexSiteFactor_bound {α V : Type*} [Fintype α]
    (factor : Unit ⊕ α → V → ℂ) (hfactor : ∀ i v, ‖factor i v‖ ≤ 1)
    (s : Finset α) (v : V) : ‖starVertexSiteFactor factor s v‖ ≤ 1 := by
  rw [starVertexSiteFactor, norm_prod]
  apply Finset.prod_le_one (fun _ _ => norm_nonneg _)
  intro i _
  split_ifs
  · exact hfactor i v
  · simp

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial

theorem coefficientTorusFourierSum_sample {I K F : Type*} [Fintype K] [Fintype F] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (c : F → ℂ)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j) (z : Option K → I → ℝ) :
    coefficientTorusFourierSum U frequency c (affineSampleCoefficientTorus U p hm z) =
      affineCubeFourierSum frequency p c z := by
  unfold coefficientTorusFourierSum affineCubeFourierSum
  apply Finset.sum_congr rfl
  intro a _
  rw [coefficientTorusCharacter_sample U (frequency a) p hp hm z]

theorem coefficientCoverSample_sites {I K : Type*} [Fintype K] {m q : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    (root : K → ℤ) (difference : Fin q → K → ℤ) (D : ℕ)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j) (z : Option K → I → ℝ) :
    coefficientSiteTorusMap U (fun s k => affineSite root difference s (some k))
        (affineCoefficientCoverSample U p hm D z) =
      affineCoveredSiteSample U root difference D p hm z := by
  funext j
  rw [affineCoefficientCoverSample, coefficientSiteTorusMap_mk]
  change QuotientAddGroup.mk' (subspaceArrayIntegerLattice (Finset (Fin q)) (U j))
    (matrixModuleAction (fun s d =>
      (boundedSiteMatrix (j.val + 1) (fun s k => affineSite root difference s (some k)) s d : ℝ))
      ((D : ℝ)⁻¹ • fun d => coefficients
        (substitute (affineParameterSubstitution z) (restrictCoefficients (U j) (p j) (hm j))) d.val)) = _
  rw [map_smul, ← siteEvaluation_bounded_coefficients _ _
    (degreeLE_substitute_affine _ (affineParameterSubstitution_degree z) _
      (degreeLE_restrictCoefficients (U j) (p j) (hm j) (hp j)))]
  rfl

noncomputable def physicalCubeEuclideanSample {I : Type*} {m q : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (D : ℕ)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hm : ∀ j d, coefficients (p j) d ∈ U j) (v : I → (Unit ⊕ Fin q) → ℤ) :
    EuclideanJetLayers U (fun j : Fin m => BoundedBooleanJet (Fin q) (j.val + 1)) :=
  euclideanJetEquiv U (siteBooleanJetTorusMap U
    (fun j => (Subtype.val : BoundedBooleanJet (Fin q) (j.val + 1) → Finset (Fin q)))
    (physicalCubeCoveredSample U D p hm v))

theorem coefficientCoverSample_physicalJet {I K : Type*} [Fintype K] {m q : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (root : K → ℤ) (difference : Fin q → K → ℤ) (D : ℕ)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j) (base : I → ℤ) (z : Option K × I → ℤ) :
    euclideanCoefficientJetMap U root (Matrix.of difference)
        (fun j => (Subtype.val : BoundedBooleanJet (Fin q) (j.val + 1) → Finset (Fin q)))
        (affineCoefficientCoverSample U (fun j => translate (fun i => (base i : ℝ)) (p j))
          (fun j => coefficients_translate_mem (U j) (fun i => (base i : ℝ)) (p j) (hm j))
          D (fun k i => (z (k, i) : ℝ))) =
      physicalCubeEuclideanSample U D p hm (physicalCubeRootDifferences root (Matrix.of difference) base z) := by
  have hs := coefficientCoverSample_sites U root difference D
    (fun j => translate (fun i => (base i : ℝ)) (p j))
    (fun j => degreeLE_translate (1 : I → ℕ) (fun _ => by norm_num) _ (p j) (hp j))
    (fun j => coefficients_translate_mem (U j) (fun i => (base i : ℝ)) (p j) (hm j))
    (fun k i => (z (k, i) : ℝ))
  rw [affineCoveredSiteSample_physical] at hs
  exact congrArg (fun t : SiteTorus (Finset (Fin q)) U => euclideanJetEquiv U
    (siteBooleanJetTorusMap U
      (fun j => (Subtype.val : BoundedBooleanJet (Fin q) (j.val + 1) → Finset (Fin q))) t)) hs

noncomputable def physicalCubePositiveTest {I : Type*} {m q : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (D : ℕ) (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (f : EuclideanJetLayers U (fun j : Fin m => BoundedBooleanJet (Fin q) (j.val + 1)) → ℝ)
    (test : Finset (Fin q) → (I → ℝ) → ℂ) (v : I → (Unit ⊕ Fin q) → ℤ) : ℂ :=
  physicalCubeSiteTest test v * (f (physicalCubeEuclideanSample U D p hm v) : ℂ)

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial

noncomputable def physicalCubeRowSample {X : Type*} {m dim : ℕ}
    {J O : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, Fintype (O j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (d : ℕ)
    (rows : ∀ j, O j → Finset (Fin dim))
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (p j) e ∈ U j) (v : X → (Unit ⊕ Fin dim) → ℤ) :
    EuclideanJetLayers U O :=
  euclideanJetEquiv U (siteBooleanJetTorusMap U rows (physicalCubeCoveredSample U d p hm v))

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators Matrix

def standardPhysicalCubeOutput {X : Type*} {q : ℕ}
    (z : Option (Fin q) × X → ℤ) : X → (Unit ⊕ Fin q) → ℤ :=
  fun x => Sum.elim (fun _ => z (none,x)) (fun i => z (some i,x))

def standardPhysicalCubeFrame {X : Type*} {q : ℕ}
    (v : X → (Unit ⊕ Fin q) → ℤ) : Option (Fin q) × X → ℤ :=
  fun z => Option.elim' (v z.2 (.inl ())) (fun i => v z.2 (.inr i)) z.1

theorem standardPhysicalCubeOutput_frame {X : Type*} {q : ℕ}
    (v : X → (Unit ⊕ Fin q) → ℤ) :
    standardPhysicalCubeOutput (standardPhysicalCubeFrame v) = v := by
  funext x i
  rcases i with i | i
  · cases i; rfl
  · rfl

theorem standardPhysicalCubeFrame_injective {X : Type*} {q : ℕ} :
    Function.Injective (standardPhysicalCubeFrame (X := X) (q := q)) := by
  intro v w h
  have he := congrArg standardPhysicalCubeOutput h
  simpa only [standardPhysicalCubeOutput_frame] using he

theorem physicalCubeRootDifferences_standard {X : Type*} {q : ℕ}
    (z : Option (Fin q) × X → ℤ) :
    physicalCubeRootDifferences (fun _ : Fin q => 0) (1 : Matrix (Fin q) (Fin q) ℤ) 0 z =
      standardPhysicalCubeOutput z := by
  funext x i
  rcases i with i | i
  · cases i
    rw [physicalCubeRootDifferences_root]
    simp [jointIntegerPhysicalSite, integerPhysicalSite, standardPhysicalCubeOutput]
  · rw [physicalCubeRootDifferences_direction]
    simp [Matrix.one_apply, standardPhysicalCubeOutput]

noncomputable def standardPhysicalJetMap {m q : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ)) :
    CoefficientTorus (K := Fin q) U →+
      EuclideanJetLayers U (fun j : Fin m => BoundedBooleanJet (Fin q) (j.val + 1)) :=
  euclideanCoefficientJetMap U (fun _ => 0) (1 : Matrix (Fin q) (Fin q) ℤ)
    (fun j => (Subtype.val : BoundedBooleanJet (Fin q) (j.val + 1) → Finset (Fin q)))

theorem affineCoveredSiteSample_zero_base_physical {X K : Type*} [Fintype K] {m q : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    (root : K → ℤ) (difference : Fin q → K → ℤ) (d : ℕ)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (p j) e ∈ U j) (z : Option K × X → ℤ) :
    affineCoveredSiteSample U root difference d p hm (fun k x => (z (k,x) : ℝ)) =
      physicalCubeCoveredSample U d p hm (physicalCubeRootDifferences root (Matrix.of difference) 0 z) := by
  funext j
  rw [affineCoveredSiteSample_eq_values]
  dsimp only [physicalCubeCoveredSample]
  apply congrArg (QuotientAddGroup.mk' (subspaceArrayIntegerLattice (Finset (Fin q)) (U j)))
  apply congrArg (fun v : Finset (Fin q) → U j => (d : ℝ)⁻¹ • v)
  funext s
  apply congrArg (fun x => eval x (restrictCoefficients (U j) (p j) (hm j)))
  funext x
  have h := congrFun (integerSiteValue_affine_physical root difference (0 : X → ℤ) z s) x
  simpa only [Pi.zero_apply, Int.cast_zero, Pi.add_apply, zero_add] using h

theorem coefficientCoverSample_standardPhysicalJet {X : Type*} {m q : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (d : ℕ) (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j e, coefficients (p j) e ∈ U j) (z : Option (Fin q) × X → ℤ) :
    standardPhysicalJetMap U
      (affineCoefficientCoverSample U p hm d (fun k x => (z (k,x) : ℝ))) =
      physicalCubeEuclideanSample U d p hm (standardPhysicalCubeOutput z) := by
  let D : Fin q → Fin q → ℤ := fun i j => if i = j then 1 else 0
  have hD : Matrix.of D = (1 : Matrix (Fin q) (Fin q) ℤ) := by
    ext i j
    simp [D, Matrix.one_apply]
  have h := coefficientCoverSample_sites U (fun _ : Fin q => 0)
    D d p hp hm (fun k x => (z (k,x) : ℝ))
  have hs := affineCoveredSiteSample_zero_base_physical U (fun _ : Fin q => 0)
    D d p hm z
  rw [hs, hD, physicalCubeRootDifferences_standard] at h
  have hjet : euclideanCoefficientJetMap U (fun _ : Fin q => 0) (Matrix.of D)
      (fun j => (Subtype.val : BoundedBooleanJet (Fin q) (j.val + 1) → Finset (Fin q)))
      (affineCoefficientCoverSample U p hm d (fun k x => (z (k,x) : ℝ))) =
      physicalCubeEuclideanSample U d p hm (standardPhysicalCubeOutput z) :=
    congrArg (fun t : SiteTorus (Finset (Fin q)) U => euclideanJetEquiv U
    (siteBooleanJetTorusMap U
      (fun j => (Subtype.val : BoundedBooleanJet (Fin q) (j.val + 1) → Finset (Fin q))) t)) h
  rw [hD] at hjet
  exact hjet

theorem physicalCubeEuclideanSample_frame {X : Type*} {m q : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (d : ℕ) (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j e, coefficients (p j) e ∈ U j) (v : X → (Unit ⊕ Fin q) → ℤ) :
    physicalCubeEuclideanSample U d p hm v = standardPhysicalJetMap U
      (affineCoefficientCoverSample U p hm d (fun k x => (standardPhysicalCubeFrame v (k,x) : ℝ))) := by
  rw [coefficientCoverSample_standardPhysicalJet U d p hp hm, standardPhysicalCubeOutput_frame]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial

def standardPhysicalSite {q : ℕ} : Finset (Fin q) → Fin q → ℤ :=
  integerAffineCube (fun _ => 0) (1 : Matrix (Fin q) (Fin q) ℤ)

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory VectorPolynomial

variable {m q : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable [CompactSpace (CoefficientTorus (K := Fin q) U)]
variable [MeasurableSpace (CoefficientTorus (K := Fin q) U)]
variable [BorelSpace (CoefficientTorus (K := Fin q) U)]
variable (μ : Measure (CoefficientTorus (K := Fin q) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

theorem standardPhysicalJetMap_measurePreserving :
    MeasurePreserving (standardPhysicalJetMap (q := q) U) μ
      (Measure.pi (fun j => Measure.pi (fun _ : BoundedBooleanJet (Fin q) (j.val + 1) => ν j))) := by
  have hperiod : integerScalarLattice (Fin q) (1 : ℤ) ≤
      (1 : Matrix (Fin q) (Fin q) ℤ).mulVecLin.range := by
    intro v _
    exact ⟨v, by simp⟩
  exact euclideanCoefficientJetMap_measurePreserving U (fun _ => 0)
    (1 : Matrix (Fin q) (Fin q) ℤ) 1 one_ne_zero hperiod
    (fun j => (Subtype.val : BoundedBooleanJet (Fin q) (j.val + 1) → Finset (Fin q)))
    (fun _ => Subtype.val_injective) (fun _ s => s.property) μ ν

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators Classical

variable {X : Type*} {m q : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ)) (d : ℕ)
variable (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j e, coefficients (p j) e ∈ U j)

noncomputable def physicalSingleSiteValue (w : X → ℝ) : EuclideanJetLayers U (fun _ => Unit) :=
  fun j _ => (euclideanSubspaceTorusEquiv (U j)).symm
    (QuotientAddGroup.mk' (subspaceArrayIntegerLattice Unit (U j))
      (fun _ => (d : ℝ)⁻¹ • eval w (restrictCoefficients (U j) (p j) (hm j))))

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators Classical

variable {X : Type*} {m dim : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ)) (d : ℕ)
variable (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j e, coefficients (p j) e ∈ U j)

end Erdos3.BooleanCubeKernel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PhysicalResidueOffsetShift
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

def physicalCubeResidueCoordinates {K X α : Type*} [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (residue : Option K × X → ℤ) (modulus : X → ℕ) (z : Option K × X → ℤ) :
    X → (Unit ⊕ α) → ℤ :=
  fun x i => physicalCubeRootDifferences root D base residue x i +
    (modulus x : ℤ) * physicalCubeRootDifferences root D 0 z x i

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory
open scoped BigOperators Matrix

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Matrix

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

def physicalResidueReconstruction {K X α : Type*} [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (residue : Option K × X → ℤ) (q : X → ℕ) (v : X → (Unit ⊕ α) → ℤ) :
    X → (Unit ⊕ α) → ℤ :=
  fun d i => physicalCubeRootDifferences root D base residue d i + (q d : ℤ) * v d i

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Matrix

def physicalResidueOffsetShift {K X α : Type*} [Fintype K]
    (root root₀ : K → ℤ) (D D₀ : Matrix α K ℤ)
    (r : Option K × X → ℤ) (q : X → ℕ) : X → (Unit ⊕ α) → ℤ :=
  fun d => residueMatrixShift (physicalCubeCoefficient root D) (physicalCubeCoefficient root₀ D₀)
    (q d) (fun k => r (k, d))

end Erdos3.BooleanCubeKernel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedFixedScaleJointMarginalTransfer
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open MeasureTheory

theorem joint_normalization_integral_compare {X Y C : Type*} [Fintype X] [Fintype Y]
    [MeasurableSpace C] (p : FiniteProbabilityWeights X) (q : FiniteProbabilityWeights Y)
    (μ : Measure C) [IsProbabilityMeasure μ]
    (D : C → X × Y → ℝ) (hDm : ∀ z, Measurable (fun c => D c z))
    (hD0 : ∀ c z, 0 ≤ D c z)
    (hlocal : ∀ c x, 0 < q.mean (fun y => D c (x,y)))
    (hglobal : ∀ c, 0 < (p.prod q).mean (D c))
    (f : X × Y → ℂ) (hf : ∀ z, ‖f z‖ ≤ 1) {ε : ℝ}
    (hclose : ∀ c x, |q.mean (fun y => D c (x,y))-1| ≤ ε) :
    ‖(∫ c, (p.prod q).normalizedDensityTest (D c) f ∂μ) -
      p.complexMean (fun x => ∫ c, q.normalizedDensityTest
        (fun y => D c (x,y)) (fun y => f (x,y)) ∂μ)‖ ≤ 2*ε := by
  have hj := (p.prod q).normalizedDensityTest_integrable μ D hDm hD0 hglobal f hf
  have hl (x : X) := q.normalizedDensityTest_integrable μ (fun c y => D c (x,y))
    (fun y => hDm (x,y)) (fun c y => hD0 c (x,y)) (fun c => hlocal c x)
    (fun y => f (x,y)) (fun y => hf (x,y))
  have hli := p.complexMean_integrable μ
    (fun c x => q.normalizedDensityTest (fun y => D c (x,y)) (fun y => f (x,y))) hl
  rw [← p.integral_complexMean μ _ hl, ← integral_sub hj hli]
  have h := norm_integral_le_of_norm_le (integrable_const (2*ε) (μ := μ))
    (ae_of_all μ (fun c => p.joint_normalization_compare q (D c) (hD0 c)
      (hlocal c) (hglobal c) f hf (hclose c)))
  simpa only [integral_const, probReal_univ, one_smul] using h

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {B K I : Type*} [Fintype K] [Fintype I]
variable (A : Finset B) (hA : A.Nonempty)
variable (modulus : I → ℕ) (T : Finset (ColumnResiduePattern K I modulus))
variable (W : K × I → ℝ) (hW : ∀ z, 0 < W z)
variable (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)

theorem selectedJointFiniteLaw_integral_local_comparison {C : Type*} [MeasurableSpace C]
    (μ : Measure C) [IsProbabilityMeasure μ]
    (D : C → B → (K × I → ℤ) → ℝ) (hDm : ∀ a z, Measurable (fun c => D c a z))
    (hD0 : ∀ c a z, 0 ≤ D c a z)
    (hD : ∀ c, 0 < selectedJointDensityMass A modulus T W (D c))
    (hlocal : ∀ c a, 0 < selectedResidueDensityMass modulus T W (D c a))
    (f : B → (K × I → ℤ) → ℂ) (hf : ∀ a z, ‖f a z‖ ≤ 1) {ε : ℝ}
    (hclose : ∀ c a, |selectedResidueDensityMass modulus T W (D c a)-1| ≤ ε) :
    ‖(∫ c, (selectedJointFiniteLaw A hA modulus T W hW hZ (D c) (hD0 c) (hD c)).complexMean
        (fun z => f z.1.val z.2.val) ∂μ) -
      (𝔼 a ∈ A, ∫ c, ∑' z,
        ((selectedResidueDensityPMF modulus T W hW hZ (D c a) (hD0 c a) (hlocal c a) z).toReal : ℂ) *
          f a z ∂μ)‖ ≤ 2*ε := by
  let p := FiniteProbabilityWeights.uniformFinset A hA
  let q := selectedResidueFiniteLaw modulus T W hW hZ
  have h := p.joint_normalization_integral_compare q μ (fun c z => D c z.1.val z.2.val)
    (fun z => hDm z.1.val z.2.val) (fun c z => hD0 c z.1.val z.2.val)
    (fun c a => by
      change 0 < q.mean (fun y => D c a.val y.val)
      rw [selectedResidueFiniteLaw_densityMass modulus T W hW hZ (D c a.val)]
      exact hlocal c a.val)
    (fun c => by change 0 < (selectedJointReference A hA modulus T W hW hZ).mean _
                 rw [selectedJointReference_densityMass]; exact hD c)
    (fun z => f z.1.val z.2.val) (fun z => hf z.1.val z.2.val)
    (fun c a => by
      change |q.mean (fun y => D c a.val y.val)-1| ≤ ε
      rw [selectedResidueFiniteLaw_densityMass modulus T W hW hZ (D c a.val)]
      exact hclose c a.val)
  have he (c : C) (a : B) := selectedResidueDensityPMF_normalizedDensityTest modulus T W hW hZ
    (D c a) (hD0 c a) (hlocal c a) (f a)
  have hm := FiniteProbabilityWeights.uniformFinset_complexMean A hA
    (fun a => ∫ c, q.normalizedDensityTest (fun z => D c a z.val) (fun z => f a z.val) ∂μ)
  dsimp only [p] at h
  rw [hm] at h
  simpa only [selectedJointFiniteLaw_complexMean, he, selectedJointReference, q] using h

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel
open MeasureTheory
open scoped BigOperators Classical

theorem fixedScaleJointMarginalTransfer
    {K I C : Type*} [Fintype K] [Fintype I] [DecidableEq I]
    [MeasurableSpace C] (μ : Measure C) [IsProbabilityMeasure μ]
    (root : K → ℤ) (N margin : I → ℕ) (hmargin : ∀ i, 2 * margin i < N i)
    (stride : I → ℕ) (T : Finset (ColumnResiduePattern (Option K) I stride))
    (W : Option K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride T W z)
    (hfit : ∀ i, physicalSiteWidth root W i ≤ (margin i : ℝ))
    (D : C → (I → ℤ) → (Option K × I → ℤ) → ℝ)
    (hDm : ∀ a z, Measurable (fun c => D c a z))
    (hD0 : ∀ c a z, 0 ≤ D c a z)
    (hD : ∀ c, 0 < selectedJointDensityMass (trimmedIntegerBox N margin) stride T W (D c))
    (hlocal : ∀ c a, 0 < selectedResidueDensityMass stride T W (D c a))
    {ε η : ℝ}
    (hclose : ∀ c a, |selectedResidueDensityMass stride T W (D c a) - 1| ≤ ε)
    (hmix : ∀ a (ψ : (I → ℝ) → ℂ), (∀ v, ‖ψ v‖ ≤ 1) →
      ‖(∫ c, ∑' z, ((selectedResidueDensityPMF stride T W hW hZ (D c a)
          (hD0 c a) (hlocal c a) z).toReal : ℂ) * ψ (physicalAffineSite root z) ∂μ) -
        ∑' z, ((selectedResidueSmoothPMF stride T W hW hZ z).toReal : ℂ) *
          ψ (physicalAffineSite root z)‖ ≤ η) :
    ∀ φ : (I → ℝ) → ℂ, (∀ v, ‖φ v‖ ≤ 1) →
      let f := fun c =>
        (selectedJointFiniteLaw (trimmedIntegerBox N margin)
          (trimmedIntegerBox_nonempty N margin hmargin) stride T W hW hZ
          (D c) (hD0 c) (hD c)).complexMean
            (fun z => φ ((fun i => (z.1.val i : ℝ)) + physicalAffineSite root z.2.val))
      Integrable f μ ∧
        ‖(∫ c, f c ∂μ) - (𝔼 x ∈ integerBox N, φ (fun i => (x i : ℝ)))‖ ≤
          2 * ε + η + 2 * ∑ i, 2 * (margin i : ℝ) / N i := by
  intro φ hφ
  let Q := trimmedIntegerBox N margin
  have hQ : Q.Nonempty := trimmedIntegerBox_nonempty N margin hmargin
  constructor
  · have hi := (selectedJointReference Q hQ stride T W hW hZ).normalizedDensityTest_integrable μ
      (fun c z => D c z.1.val z.2.val)
      (fun z => hDm z.1.val z.2.val) (fun c z => hD0 c z.1.val z.2.val)
      (fun c => by
        rw [selectedJointReference_densityMass Q hQ stride T W hW hZ (D c)]
        exact hD c)
      (fun z => φ ((fun i => (z.1.val i : ℝ)) + physicalAffineSite root z.2.val))
      (fun z => hφ _)
    apply hi.congr
    filter_upwards [] with c
    exact (selectedJointFiniteLaw_complexMean Q hQ stride T W hW hZ
      (D c) (hD0 c) (hD c)
      (fun a z => φ ((fun i => (a i : ℝ)) + physicalAffineSite root z))).symm
  · have hjoint := selectedJointFiniteLaw_integral_local_comparison Q hQ stride T W hW hZ μ
      D hDm hD0 hD hlocal
      (fun a z => φ ((fun i => (a i : ℝ)) + physicalAffineSite root z))
      (fun _ _ => hφ _) hclose
    have hreference :
        ‖(𝔼 a ∈ Q, ∫ c, ∑' z,
          ((selectedResidueDensityPMF stride T W hW hZ (D c a)
            (hD0 c a) (hlocal c a) z).toReal : ℂ) *
            φ ((fun i => (a i : ℝ)) + physicalAffineSite root z) ∂μ) -
          (𝔼 x ∈ integerBox N, φ (fun i => (x i : ℝ)))‖ ≤
          η + 2 * ∑ i, 2 * (margin i : ℝ) / N i := by
      refine selectedResidue_trimmed_comparison_transfer root N margin hmargin stride T W hW hZ
        hfit (fun x => φ (fun i => (x i : ℝ))) (fun _ _ => hφ _) _ ?_
      intro a _
      have h := hmix a (fun v => φ ((fun i => (a i : ℝ)) + v)) (fun _ => hφ _)
      have hcast (z : Option K × I → ℤ) :
          (fun i => ((a + integerPhysicalSite root z) i : ℝ)) =
            (fun i => (a i : ℝ)) + physicalAffineSite root z := by
        funext i
        simp only [Pi.add_apply, Int.cast_add, integerPhysicalSite_cast_apply]
      simpa only [hcast] using h
    exact ((norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
      (add_le_add hjoint hreference)).trans_eq (by ring)

end Erdos3.BooleanCubeKernel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedSpatialProxyCap
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

variable {Ω R : Type*} [Fintype Ω] [DecidableEq Ω] [DecidableEq R]
variable (p : FiniteProbabilityWeights Ω) (label : Ω → R)

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open BooleanCubeKernel

noncomputable def narrowTrimmedSpatialWidths {G J X : Type*}
    (W τ ξ : ℝ) (N : X → ℕ) : Option (G ⊕ J) × X → ℝ :=
  fun z => match z.1 with
    | some (.inr _) => ξ * trimmedSpatialWidths W τ N z
    | _ => trimmedSpatialWidths W τ N z

theorem narrowTrimmedSpatialWidths_pos {G J X : Type*}
    {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ)
    (N : X → ℕ) (hN : ∀ x, 0 < N x) (z : Option (G ⊕ J) × X) :
    0 < narrowTrimmedSpatialWidths W τ ξ N z := by
  rcases z with ⟨_ | (g | j), x⟩
  · exact trimmedSpatialWidths_pos hW hτ N hN _
  · exact trimmedSpatialWidths_pos hW hτ N hN _
  · exact mul_pos hξ (trimmedSpatialWidths_pos hW hτ N hN _)

theorem narrowTrimmedSpatialWidths_le {G J X : Type*}
    {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ1 : ξ ≤ 1)
    (N : X → ℕ) (hN : ∀ x, 0 < N x) (z : Option (G ⊕ J) × X) :
    narrowTrimmedSpatialWidths W τ ξ N z ≤ trimmedSpatialWidths W τ N z := by
  rcases z with ⟨_ | (g | j), x⟩
  · exact le_rfl
  · exact le_rfl
  · exact mul_le_of_le_one_left (trimmedSpatialWidths_pos hW hτ N hN _).le hξ1

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

namespace BooleanCubeKernel

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

variable {G J X : Type*} [Fintype G] [Fintype J] [Fintype X] [DecidableEq X]
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ1 : ξ ≤ 1)
variable (N : X → ℕ) (hN : ∀ x, 0 < N x)
variable (hτ1 : τ ≤ 1 / 2) (hsize : ∀ x, 4 ≤ τ * (N x : ℝ))

variable {dim : ℕ} (root : G ⊕ J → ℤ) (dirs : Matrix (Fin dim) (G ⊕ J) ℤ)
variable (hsite : ∀ s : Finset (Fin dim), (∑ k, |(integerAffineCube root dirs s k : ℝ)|) ≤ W)

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (c : LayerSamplerVariables G I n B → ℤ)
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (hx : ∀ g, (integerScalarCubeWeights (Fin dim) S.value S.positive).weight (x g) ≠ 0)
variable (hy : (principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).weight y ≠ 0)

variable {X : Type*} [Fintype X] [DecidableEq X]
variable {W τ ξ : ℝ} (hbudget : allocatedPhysicalRootBudget B U b S c ≤ W)
variable (hτ : 0 < τ) (hξ1 : ξ ≤ 1) (N : X → ℕ) (hN : ∀ a, 0 < N a)
variable (hτ1 : τ ≤ 1 / 2) (hsize : ∀ a, 4 ≤ τ * (N a : ℝ))

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
variable (y y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))

local notation "vars" => LayerSamplerVariables G I n B
local notation "cols" => principalSpatialColumns (fun j => c (Sum.inr j)) id y
local notation "refcols" => principalSpatialColumns (fun j => c (Sum.inr j)) id y₀
local notation "ker" => (fun g => c (Sum.inl g) + (x g none : ℤ))
local notation "root" => allocatedPhysicalCubeRoot B U basis S c x y
local notation "dirs" => allocatedPhysicalCubeDirections B U basis S x y

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule
open scoped BigOperators Classical Matrix

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedReferenceJetWindow
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators

def translatePhysicalCube {X α : Type*} (base : X → ℤ)
    (v : X → (Unit ⊕ α) → ℤ) : X → (Unit ⊕ α) → ℤ :=
  fun x i => physicalCubeOffset base x i + v x i

theorem physicalCubeVertexValue_translate {X α : Type*} (base : X → ℤ)
    (v : X → (Unit ⊕ α) → ℤ) (s : Finset α) :
    physicalCubeVertexValue (translatePhysicalCube base v) s =
      fun x => base x + physicalCubeVertexValue v s x := by
  funext x
  simp only [physicalCubeVertexValue, translatePhysicalCube, physicalCubeOffset,
    zero_add, add_assoc]

theorem physicalResidueReconstruction_translate {K X α : Type*} [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (r : Option K × X → ℤ) (q : X → ℕ) (v : X → (Unit ⊕ α) → ℤ) :
    physicalResidueReconstruction root D base r q v =
      translatePhysicalCube base (physicalResidueReconstruction root D 0 r q v) := by
  funext x i
  cases i <;> simp [physicalResidueReconstruction, physicalCubeRootDifferences,
    translatePhysicalCube, physicalCubeOffset, add_assoc]

theorem physicalCubeCoveredSample_translate {X : Type*} {m q : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ)) (cover : ℕ)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (p j) e ∈ U j) (base : X → ℤ)
    (v : X → (Unit ⊕ Fin q) → ℤ) :
    physicalCubeCoveredSample U cover
        (fun j => translate (fun x => (base x : ℝ)) (p j))
        (fun j => coefficients_translate_mem (U j) (fun x => (base x : ℝ)) (p j) (hm j)) v =
      physicalCubeCoveredSample U cover p hm (translatePhysicalCube base v) := by
  funext j
  dsimp only [physicalCubeCoveredSample]
  apply congrArg (QuotientAddGroup.mk' (subspaceArrayIntegerLattice (Finset (Fin q)) (U j)))
  apply congrArg (fun w : Finset (Fin q) → U j => (cover : ℝ)⁻¹ • w)
  funext s
  apply Subtype.ext
  rw [eval_restrictCoefficients, eval_restrictCoefficients, eval_translate]
  apply congrArg (fun x : X → ℝ => eval x (p j))
  funext x
  rw [physicalCubeVertexValue_translate]
  simp only [Int.cast_add, add_comm]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial

theorem physicalCubeRowSample_translate {X : Type*} {m dim : ℕ}
    {J O : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, Fintype (O j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (d : ℕ)
    (rows : ∀ j, O j → Finset (Fin dim))
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (p j) e ∈ U j) (base : X → ℤ)
    (v : X → (Unit ⊕ Fin dim) → ℤ) :
    physicalCubeRowSample U d rows
        (fun j => translate (fun x => (base x : ℝ)) (p j))
        (fun j => coefficients_translate_mem (U j) (fun x => (base x : ℝ)) (p j) (hm j)) v =
      physicalCubeRowSample U d rows p hm (translatePhysicalCube base v) := by
  unfold physicalCubeRowSample
  rw [physicalCubeCoveredSample_translate]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators Classical

theorem physicalResidueReconstruction_injective {K X α : Type*} [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (r : Option K × X → ℤ) (q : X → ℕ) (hq : ∀ x, 0 < q x) :
    Function.Injective (physicalResidueReconstruction root D base r q) := by
  intro v w h
  funext x i
  have he := congrFun (congrFun h x) i
  have hn : (q x : ℤ) ≠ 0 := by exact_mod_cast (hq x).ne'
  exact mul_left_cancel₀ hn (add_left_cancel he)

theorem physicalResidueReconstruction_columnResidue {K X : Type*} [Fintype K] {q : ℕ}
    (root : K → ℤ) (D : Matrix (Fin q) K ℤ) (base : X → ℤ)
    (r : Option K × X → ℤ) (stride : X → ℕ) (v : X → (Unit ⊕ Fin q) → ℤ) :
    columnResiduePattern stride
        (standardPhysicalCubeFrame (physicalResidueReconstruction root D base r stride v)) =
      columnResiduePattern stride (standardPhysicalCubeFrame (physicalCubeRootDifferences root D base r)) := by
  funext z
  rcases z with ⟨k,x⟩
  cases k <;> simp [columnResiduePattern, standardPhysicalCubeFrame,
    physicalResidueReconstruction]

theorem spatialWindow_four_coordinate_bound {X α : Type*} [Fintype X] [Fintype α]
    (H : X → ℝ) (hH : ∀ x, 0 ≤ H x) {v : X → (Unit ⊕ α) → ℤ}
    (hv : v ∈ spatialWindow H 4) (x : X) (i : Unit ⊕ α) :
    |(v x i : ℝ)| ≤ 8 * H x := by
  have h := (mem_spatialWindow_iff H 4 v).mp hv
  have hr : |(v x (.inl ()) : ℝ)| ≤ H x * 4 := h x (.inl ())
  cases i with
  | inl i => cases i; nlinarith [hH x]
  | inr i =>
    have hd : |(v x (.inl ()) : ℝ) + (v x (.inr i) : ℝ)| ≤ H x * 4 := by
      simpa only [spatialStar, Sum.elim_inr, Int.cast_add] using h x (.inr i)
    rcases abs_le.mp hr with ⟨hr₁,hr₂⟩
    rcases abs_le.mp hd with ⟨hd₁,hd₂⟩
    apply abs_le.mpr
    constructor <;> linarith

theorem physicalCube_zero_residue_bound {K X α : Type*} [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (stride : X → ℕ)
    (r : Option K × X → ℤ) (hr : ∀ k x, |(r (k,x) : ℝ)| ≤ stride x)
    (H : X → ℝ)
    (hrows : ∀ x i, (∑ k, |(physicalCubeCoefficient root D i k : ℝ)|) ≤ H x)
    (x : X) (i : Unit ⊕ α) :
    |(physicalCubeRootDifferences root D 0 r x i : ℝ)| ≤ (stride x : ℝ) * H x := by
  have hz : physicalCubeOffset (0 : X → ℤ) x i = 0 := by cases i <;> rfl
  simp only [physicalCubeRootDifferences, hz, zero_add, Int.cast_sum, Int.cast_mul]
  calc
    _ ≤ ∑ k, |(physicalCubeCoefficient root D i k : ℝ) * (r (k,x) : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k, |(physicalCubeCoefficient root D i k : ℝ)| * |(r (k,x) : ℝ)| := by
      simp only [abs_mul]
    _ ≤ ∑ k, |(physicalCubeCoefficient root D i k : ℝ)| * (stride x : ℝ) := by
      exact Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (hr k x) (abs_nonneg _))
    _ = (∑ k, |(physicalCubeCoefficient root D i k : ℝ)|) * (stride x : ℝ) :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ H x * (stride x : ℝ) := mul_le_mul_of_nonneg_right (hrows x i) (Nat.cast_nonneg _)
    _ = _ := mul_comm _ _

noncomputable def referenceJetEnvelopeWidths {X : Type*} {q : ℕ}
    (stride : X → ℕ) (H : X → ℝ) : Option (Fin q) × X → ℝ :=
  fun z => 20 * (stride z.2 : ℝ) * H z.2

theorem referenceJetEnvelopeWidths_pos {X : Type*} {q : ℕ}
    (stride : X → ℕ) (hs : ∀ x, 0 < stride x) (H : X → ℝ) (hH : ∀ x, 0 < H x)
    (z : Option (Fin q) × X) : 0 < referenceJetEnvelopeWidths stride H z := by
  exact mul_pos (mul_pos (by norm_num) (Nat.cast_pos.mpr (hs z.2))) (hH z.2)

theorem referenceJetEnvelopeWidths_residue {X : Type*} {q : ℕ}
    (stride : X → ℕ) (hs : ∀ x, 0 < stride x) (H : X → ℝ) (z : Option (Fin q) × X) :
    residueProfileWidth stride (referenceJetEnvelopeWidths stride H) z = 20 * H z.2 := by
  have hn : (stride z.2 : ℝ) ≠ 0 := (Nat.cast_pos.mpr (hs z.2)).ne'
  dsimp only [residueProfileWidth, referenceJetEnvelopeWidths]
  field_simp

theorem physicalResidueReconstruction_envelope {K X : Type*} [Fintype K] [Fintype X] {q : ℕ}
    (root : K → ℤ) (D : Matrix (Fin q) K ℤ) (stride : X → ℕ) (hs : ∀ x, 0 < stride x)
    (r : Option K × X → ℤ) (H : X → ℝ) (hH : ∀ x, 0 < H x)
    (hoffset : ∀ x i, |(physicalCubeRootDifferences root D 0 r x i : ℝ)| ≤ (stride x : ℝ) * H x)
    {v : X → (Unit ⊕ Fin q) → ℤ} (hv : v ∈ spatialWindow H 4)
    (z : Option (Fin q) × X) :
    |(standardPhysicalCubeFrame (physicalResidueReconstruction root D 0 r stride v) z : ℝ) /
      referenceJetEnvelopeWidths stride H z| ≤ 1 / 2 := by
  have hcoord (i : Unit ⊕ Fin q) :
      |(physicalResidueReconstruction root D 0 r stride v z.2 i : ℝ)| ≤
        9 * (stride z.2 : ℝ) * H z.2 := by
    simp only [physicalResidueReconstruction, Int.cast_add, Int.cast_mul, Int.cast_natCast]
    apply (abs_add_le _ _).trans
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (stride z.2) : (0 : ℝ) ≤ stride z.2)]
    have h := mul_le_mul_of_nonneg_left
      (spatialWindow_four_coordinate_bound H (fun x => (hH x).le) hv z.2 i)
      (Nat.cast_nonneg (stride z.2) : (0 : ℝ) ≤ stride z.2)
    linarith [hoffset z.2 i]
  have hf : |(standardPhysicalCubeFrame (physicalResidueReconstruction root D 0 r stride v) z : ℝ)| ≤
      9 * (stride z.2 : ℝ) * H z.2 := by
    rcases z with ⟨k,x⟩
    cases k with
    | none => exact hcoord (.inl ())
    | some k => exact hcoord (.inr k)
  rw [abs_div, abs_of_pos (referenceJetEnvelopeWidths_pos stride hs H hH z),
    div_le_iff₀ (referenceJetEnvelopeWidths_pos stride hs H hH z)]
  dsimp only [referenceJetEnvelopeWidths]
  nlinarith [mul_pos (Nat.cast_pos.mpr (hs z.2) : (0 : ℝ) < stride z.2) (hH z.2)]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

end Erdos3.BooleanCubeKernel

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} (c : LayerSamplerVariables G I n B → ℤ)
variable (x : G → IntegerScalarCubeBox α S.value)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PhysicalSpatialResidueSupport
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def affineResidueIntervalSiteWeight (b r H : ℝ) (q : ℕ)
    (offset : ℤ) {m : ℕ} (a : ZMod m) (k : Fin (intervalSiteCount b r)) (u : ℤ) : ℝ :=
  residueSiteIndicator (m := q * m)
      ((offset + (q : ℤ) * (a.val : ℤ) : ℤ) : ZMod (q * m)) u *
    intervalSiteWeight b r k (((u : ℝ) - offset) / ((q : ℝ) * H))

noncomputable def affineVectorResidueSiteWeight {X : Type*} [Fintype X]
    (b r : ℝ) (H : X → ℝ) (q : X → ℕ) (offset : X → ℤ)
    {m : ℕ} (a : X → ZMod m) (k : X → Fin (intervalSiteCount b r)) (u : X → ℤ) : ℂ :=
  ∏ x, (affineResidueIntervalSiteWeight b r (H x) (q x) (offset x) (a x) (k x) (u x) : ℂ)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem affineVectorResidueSiteWeight_factorization {X : Type*} [Fintype X]
    (b r : ℝ) (H : X → ℝ) (q : X → ℕ) (offset : X → ℤ)
    {m : ℕ} (a : X → ZMod m) (k : X → Fin (intervalSiteCount b r)) (u : X → ℤ) :
    affineVectorResidueSiteWeight b r H q offset a k u =
      (∏ x, (residueSiteIndicator (m := q x * m)
        ((offset x + (q x : ℤ) * ((a x).val : ℤ) : ℤ) : ZMod (q x * m)) (u x) : ℂ)) *
      vectorIntervalSiteWeight b r k (fun x => ((u x : ℝ) - offset x) / ((q x : ℝ) * H x)) := by
  simp only [affineVectorResidueSiteWeight, affineResidueIntervalSiteWeight,
    vectorIntervalSiteWeight, Complex.ofReal_mul, Finset.prod_mul_distrib]

theorem vectorIntervalSiteWeight_affine_lipschitz {X : Type*} [Fintype X]
    (b : ℝ) {r : ℝ≥0} (hr : 0 < r) (k : X → Fin (intervalSiteCount b r))
    (slope shift : X → ℝ) {L : ℝ≥0} (hslope : ∀ x, |slope x| ≤ L) :
    LipschitzWith ((Fintype.card X * ((2 * intervalSiteCount b r + 1) / r)) * L)
      (fun y : X → ℝ => vectorIntervalSiteWeight b r k (fun x => slope x * y x + shift x)) := by
  have haffine : LipschitzWith L (fun y : X → ℝ => fun x => slope x * y x + shift x) := by
    apply LipschitzWith.of_dist_le_mul
    intro y z
    apply (dist_pi_le_iff (mul_nonneg L.coe_nonneg dist_nonneg)).mpr
    intro x
    calc
      dist (slope x * y x + shift x) (slope x * z x + shift x) =
          |slope x| * dist (y x) (z x) := by
        simp only [Real.dist_eq]
        rw [show slope x * y x + shift x - (slope x * z x + shift x) =
          slope x * (y x - z x) by ring, abs_mul]
      _ ≤ (L : ℝ) * dist y z :=
        mul_le_mul (hslope x) (dist_le_pi_dist y z x) dist_nonneg L.coe_nonneg
  exact (vectorIntervalSiteWeight_lipschitz b hr k).comp haffine

theorem affineVectorInterval_normalized_lipschitz {X : Type*} [Fintype X]
    (b : ℝ) {r : ℝ≥0} (hr : 0 < r) (k : X → Fin (intervalSiteCount b r))
    (H N : X → ℝ) (q : X → ℕ) (offset : X → ℤ)
    {L : ℝ≥0} (hscale : ∀ x, |N x / ((q x : ℝ) * H x)| ≤ L) :
    LipschitzWith ((Fintype.card X * ((2 * intervalSiteCount b r + 1) / r)) * L)
      (fun y : X → ℝ => vectorIntervalSiteWeight b r k
        (fun x => (N x * y x - offset x) / ((q x : ℝ) * H x))) := by
  have h := vectorIntervalSiteWeight_affine_lipschitz b hr k
    (fun x => N x / ((q x : ℝ) * H x))
    (fun x => -(offset x : ℝ) / ((q x : ℝ) * H x)) hscale
  convert h using 1
  funext y
  congr 1
  funext x
  ring

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

noncomputable def physicalResidueStarFactor {K X α : Type*} [Fintype K] [Fintype X]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (residue : Option K × X → ℤ) (q : X → ℕ) (b r : ℝ) (H : X → ℝ)
    {m : ℕ} (t : X → SpatialSiteLabel α m b r) (i : Unit ⊕ α) (u : X → ℤ) : ℂ :=
  affineVectorResidueSiteWeight b r H q
    (physicalCubeVertexValue (physicalCubeRootDifferences root D base residue) (spatialStarVertex i))
    (fun x => (t x).1 i) (fun x => (t x).2 i) u

noncomputable def physicalResidueSpatialSiteFactor {K X α : Type*}
    [Fintype K] [Fintype X] [Fintype α]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (residue : Option K × X → ℤ) (q : X → ℕ) (b r : ℝ) (H : X → ℝ)
    {m : ℕ} (t : X → SpatialSiteLabel α m b r) (s : Finset α) (u : X → ℤ) : ℂ :=
  starVertexSiteFactor (physicalResidueStarFactor root D base residue q b r H t) s u

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators NNReal

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

def physicalResidueQuotient {K X α : Type*} [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (r : Option K × X → ℤ) (q : X → ℕ) (u : X → (Unit ⊕ α) → ℤ) :
    X → (Unit ⊕ α) → ℤ :=
  fun x i => (u x i - physicalCubeRootDifferences root D base r x i) / (q x : ℤ)

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

end Erdos3.BooleanCubeKernel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PhysicalNormalizedSpatialFactor
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical NNReal

variable {K X α : Type*} [Fintype K] [Fintype X] [Fintype α]
variable (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
variable (residue : Option K × X → ℤ) (q : X → ℕ)
variable (b : ℝ) (r : ℝ≥0) (H N : X → ℝ) {m : ℕ}
variable (t : X → SpatialSiteLabel α m b r) (s : Finset α)

local notation "offset" => (fun i : Unit ⊕ α =>
  physicalCubeVertexValue (physicalCubeRootDifferences root D base residue) (spatialStarVertex i))

noncomputable def physicalResidueSpatialMask (u : X → ℤ) : ℂ :=
  starVertexSiteFactor (fun i u => ∏ x,
    (residueSiteIndicator (m := q x * m)
      ((offset i x + (q x : ℤ) * (((t x).1 i).val : ℤ) : ℤ) : ZMod (q x * m)) (u x) : ℂ)) s u

noncomputable def physicalResidueSpatialSmooth (y : X → ℝ) : ℂ :=
  starVertexSiteFactor (fun i y => vectorIntervalSiteWeight b r (fun x => (t x).2 i)
    (fun x => (N x * y x - offset i x) / ((q x : ℝ) * H x))) s y

theorem physicalResidueSpatialSiteFactor_normalized (hN : ∀ x, N x ≠ 0) (u : X → ℤ) :
    physicalResidueSpatialSiteFactor root D base residue q b r H t s u =
      physicalResidueSpatialMask root D base residue q b r t s u *
        physicalResidueSpatialSmooth root D base residue q b r H N t s (fun x => (u x : ℝ) / N x) := by
  unfold physicalResidueSpatialSiteFactor physicalResidueSpatialMask physicalResidueSpatialSmooth
  unfold starVertexSiteFactor
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : spatialStarVertex i = s
  · simp only [hi, ite_true, physicalResidueStarFactor]
    rw [affineVectorResidueSiteWeight_factorization]
    congr 1
    apply congrArg (vectorIntervalSiteWeight b r (fun x => (t x).2 i))
    funext x
    congr 1
    field_simp [hN x]
  · simp only [hi, ite_false, mul_one]

theorem physicalResidueSpatialSmooth_bounds (hr : 0 < r) {L : ℝ≥0}
    (hscale : ∀ x, |N x / ((q x : ℝ) * H x)| ≤ L) :
    (∀ y, ‖physicalResidueSpatialSmooth root D base residue q b r H N t s y‖ ≤ 1) ∧
      LipschitzWith (Fintype.card (Unit ⊕ α) *
        ((Fintype.card X * ((2 * intervalSiteCount b r + 1) / r)) * L))
        (physicalResidueSpatialSmooth root D base residue q b r H N t s) := by
  let f := fun (i : Unit ⊕ α) (y : X → ℝ) =>
    if spatialStarVertex i = s then vectorIntervalSiteWeight b r (fun x => (t x).2 i)
      (fun x => (N x * y x - offset i x) / ((q x : ℝ) * H x)) else 1
  have hn (i : Unit ⊕ α) (y : X → ℝ) : ‖f i y‖ ≤ (1 : ℝ≥0) := by
    dsimp only [f]
    split_ifs
    · exact vectorIntervalSiteWeight_bound b (show (0 : ℝ) < r from hr) _ _
    · simp
  have hl (i : Unit ⊕ α) :
      LipschitzWith ((Fintype.card X * ((2 * intervalSiteCount b r + 1) / r)) * L) (f i) := by
    by_cases hi : spatialStarVertex i = s
    · simpa only [f, hi, ite_true] using
        affineVectorInterval_normalized_lipschitz b hr (fun x => (t x).2 i) H N q (offset i) hscale
    · simpa only [f, hi, ite_false] using
        (LipschitzWith.const (α := X → ℝ) (1 : ℂ)).weaken (show 0 ≤ _ from zero_le)
  have hp := bounded_lipschitz_fintype_prod f (B := 1) (le_refl _) hl hn
  refine ⟨?_, ?_⟩
  · intro y
    simpa only [physicalResidueSpatialSmooth, starVertexSiteFactor, f, one_pow, NNReal.coe_one] using hp.1 y
  · apply LipschitzWith.of_dist_le_mul
    intro y z
    simpa only [physicalResidueSpatialSmooth, starVertexSiteFactor, f, one_pow, mul_one] using hp.2.dist_le_mul y z

theorem physicalResidueSpatialSmooth_pre_lipschitz (hr : 0 < r) {L : ℝ≥0}
    (hscale : ∀ x, |N x / ((q x : ℝ) * H x)| ≤ L)
    {P EX ES EL : ℝ} (hP : 0 ≤ P) (hb : 0 ≤ b)
    (hbox : b ≤ Real.exp P) (hrinv : 1 / (r : ℝ) ≤ Real.exp P)
    (hX : (Fintype.card X : ℝ) ≤ Real.exp EX)
    (hS : (Fintype.card (Unit ⊕ α) : ℝ) ≤ Real.exp ES) (hL : (L : ℝ) ≤ Real.exp EL) :
    LipschitzWith ⟨Real.exp (ES + EX + (3 * P + 6) + EL), Real.exp_nonneg _⟩
      (physicalResidueSpatialSmooth root D base residue q b r H N t s) := by
  apply (physicalResidueSpatialSmooth_bounds root D base residue q b r H N t s hr hscale).2.weaken
  apply NNReal.coe_le_coe.mp
  change (Fintype.card (Unit ⊕ α) : ℝ) *
      ((Fintype.card X : ℝ) * ((2 * (intervalSiteCount b r : ℝ) + 1) / (r : ℝ)) * L) ≤ _
  have hi := intervalSiteLipschitz_le_exp hb (show (0 : ℝ) < r from hr) hP hbox hrinv
  have hxi := mul_le_mul hX hi (by positivity) (Real.exp_pos EX).le
  have hxl := mul_le_mul hxi hL L.coe_nonneg (by positivity)
  apply (mul_le_mul hS hxl (by positivity) (Real.exp_pos ES).le).trans_eq
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

theorem trimmedSpatialRootScale_normalized_ratio {X : Type*}
    (N q : X → ℕ) {τ : ℝ} (hτ : 0 < τ) (hN : ∀ x, 0 < N x) (hq : ∀ x, 0 < q x) (x : X) :
    (N x : ℝ) / ((q x : ℝ) * trimmedSpatialRootScale τ N q x) = 8 / τ := by
  have hn : (N x : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hN x).ne'
  have hq' : (q x : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hq x).ne'
  unfold trimmedSpatialRootScale
  field_simp [hn, hq', hτ.ne']

end Erdos3.BooleanCubeKernel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.StandardJetFourier
namespace OAI

section

namespace Erdos3

open Module Submodule
open scoped Classical

namespace VectorPolynomial

variable {m : ℕ} {O J : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

noncomputable def coveredJetAmbientTorus (d : ℕ) (y : EuclideanJetLayers U O) :
    JetAmbientIndex O J → UnitAddCircle := fun a =>
  subspaceAmbientTorus (U a.1) (euclideanSubspaceTorusEquiv (U a.1)
    (quotientIntegerCover (latticeSection (standardEuclideanLattice (J a.1))
      (euclideanSubspace (U a.1))).toAddSubgroup d (y a.1 a.2.1))) a.2.2

omit [∀ j, Fintype (O j)] in
theorem coveredJetAmbientTorus_continuous (d : ℕ) :
    Continuous (coveredJetAmbientTorus (O := O) U d) := by
  apply continuous_pi
  intro a
  exact (continuous_apply a.2.2).comp ((subspaceAmbientTorus_continuous (U a.1)).comp
    ((euclideanSubspaceTorusEquiv_continuous (U a.1)).comp
      ((quotientIntegerCover_continuous _ d).comp
        ((continuous_apply a.2.1).comp (continuous_apply a.1)))))

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {α K : Type*} [Fintype α] [DecidableEq α] [Fintype K] {m : ℕ}
variable {O J : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (root : K → ℤ) (D : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)

omit [∀ j, Fintype (O j)] in
theorem coveredJetAmbientTorus_coefficient (d : ℕ) (x : CoefficientTorus (K := K) U)
    (j : Fin m) (o : O j) (i : J j) :
    coveredJetAmbientTorus U d (euclideanCoefficientJetMap U root D rows x) ⟨j, o, i⟩ =
      ∑ e : BoundedCoefficientExponent K (j.val + 1),
        ((d : ℤ) * boundedCoefficientJetMatrix root D (j.val + 1) (rows j) o e) •
          coefficientAmbientTorus U x ⟨⟨j, e⟩, i⟩ := by
  change subspaceAmbientTorus (U j) (euclideanSubspaceTorusEquiv (U j)
    (d • euclideanCoefficientJetMap U root D rows x j o)) i = _
  rw [euclideanCoefficientJetMap_apply, map_nsmul, map_sum, map_nsmul, map_sum]
  simp only [map_zsmul, euclideanCoefficientEquiv_apply, AddEquiv.apply_symm_apply,
    Pi.smul_apply, Finset.sum_apply]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro e _
  change d • (boundedCoefficientJetMatrix root D (j.val + 1) (rows j) o e •
    coefficientAmbientTorus U x ⟨⟨j, e⟩, i⟩) = _
  rw [← natCast_zsmul, ← mul_smul]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "single" => (fun _ : Fin m => Unit)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators Classical Matrix

theorem standardPhysicalSite_apply {q : ℕ} (s : Finset (Fin q)) (i : Fin q) :
    standardPhysicalSite s i = if i ∈ s then 1 else 0 := by
  simp [standardPhysicalSite, integerAffineCube, Matrix.one_apply]

theorem boundedSiteMatrix_standard {q h : ℕ} (s : Finset (Fin q))
    (e : BoundedCoefficientExponent (Fin q) h) :
    boundedSiteMatrix h standardPhysicalSite s e = if e.val.support ⊆ s then 1 else 0 := by
  change (∏ i ∈ e.val.support, standardPhysicalSite s i ^ e.val i) = _
  simp only [standardPhysicalSite_apply]
  by_cases hs : e.val.support ⊆ s
  · rw [if_pos hs]
    exact Finset.prod_eq_one (fun i hi => by rw [if_pos (hs hi), one_pow])
  · rw [if_neg hs]
    obtain ⟨i, hi, his⟩ := Finset.not_subset.mp hs
    exact Finset.prod_eq_zero hi (by rw [if_neg his, zero_pow (Finsupp.mem_support_iff.mp hi)])

theorem boundedCoefficientJetMatrix_standard {q h : ℕ} {O : Type*}
    (rows : O → Finset (Fin q)) (o : O) (e : BoundedCoefficientExponent (Fin q) h) :
    boundedCoefficientJetMatrix (fun _ => 0) (1 : Matrix (Fin q) (Fin q) ℤ) h rows o e =
      if rows o = e.val.support then 1 else 0 := by
  rw [← booleanJetExtractionMatrix_mul_boundedSite]
  change (booleanJetExtractionMatrix rows *ᵥ (fun s => boundedSiteMatrix h standardPhysicalSite s e)) o = _
  rw [booleanJetExtractionMatrix_mulVec]
  simp only [boundedSiteMatrix_standard]
  exact booleanCoefficient_monomial e.val.support (rows o)

end Erdos3.BooleanCubeKernel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PhysicalSupportedCubes
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

def physicalCubeParametersEquiv (X : Type*) (dim : ℕ) :
    (X → (Unit ⊕ Fin dim) → ℤ) ≃ (Fin dim → X → ℤ) × (X → ℤ) where
  toFun v := (fun i x => v x (.inr i), fun x => v x (.inl ()))
  invFun p := fun x => Sum.elim (fun _ => p.2 x) (fun i => p.1 i x)
  left_inv v := by
    funext x i
    cases i with
    | inl i => cases i; rfl
    | inr i => rfl
  right_inv p := rfl

theorem physicalCubeParametersEquiv_vertex {X : Type*} (dim : ℕ)
    (v : X → (Unit ⊕ Fin dim) → ℤ) (ω : Fin dim → Bool) :
    physicalCubeVertexValue v (Finset.univ.filter (fun i => ω i)) =
      (physicalCubeParametersEquiv X dim v).2 +
        cubeShift (physicalCubeParametersEquiv X dim v).1 ω := by
  funext x
  change v x (.inl ()) + ∑ i ∈ Finset.univ.filter (fun i => ω i), v x (.inr i) =
    v x (.inl ()) + (∑ i, if ω i then (fun x => v x (.inr i)) else 0) x
  simp only [Finset.sum_filter, Finset.sum_apply]
  apply congrArg (fun z : ℤ => v x (.inl ()) + z)
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> rfl

theorem physicalCubeParametersEquiv_support_iff {X : Type*} (dim : ℕ)
    (Q : Set (X → ℤ)) (v : X → (Unit ⊕ Fin dim) → ℤ) :
    (∀ s : Finset (Fin dim), physicalCubeVertexValue v s ∈ Q) ↔
      ∀ ω : Fin dim → Bool, (physicalCubeParametersEquiv X dim v).2 +
        cubeShift (physicalCubeParametersEquiv X dim v).1 ω ∈ Q := by
  classical
  constructor
  · intro hv ω
    rw [← physicalCubeParametersEquiv_vertex]
    exact hv _
  · intro hv s
    have h := hv (fun i => decide (i ∈ s))
    rw [← physicalCubeParametersEquiv_vertex] at h
    simpa using h

def physicalSupportedCubeEquiv (X : Type*) (dim : ℕ) (Q : Set (X → ℤ)) :
    {v : X → (Unit ⊕ Fin dim) → ℤ // ∀ s, physicalCubeVertexValue v s ∈ Q} ≃
      SupportedCube dim Q where
  toFun v := ⟨physicalCubeParametersEquiv X dim v.val,
    (physicalCubeParametersEquiv_support_iff dim Q v.val).mp v.property⟩
  invFun p := ⟨(physicalCubeParametersEquiv X dim).symm p.val,
    (physicalCubeParametersEquiv_support_iff dim Q _).mpr (by
      simpa only [Equiv.apply_symm_apply] using p.property)⟩
  left_inv v := by apply Subtype.ext; exact Equiv.symm_apply_apply _ _
  right_inv p := by apply Subtype.ext; exact Equiv.apply_symm_apply _ _

noncomputable def physicalIntegerBoxCubes {X : Type*} [Fintype X] [DecidableEq X]
    (N : X → ℕ) (dim : ℕ) : Finset (X → (Unit ⊕ Fin dim) → ℤ) :=
  Finset.univ.image (fun p : SupportedCube dim (integerBox N : Set (X → ℤ)) =>
    (physicalCubeParametersEquiv X dim).symm p.val)

end Erdos3.BooleanCubeKernel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RoundedAffineLifts
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

def jointIntegerFrame {K I : Type*}
    (z : (I → ℤ) × (Option K × I → ℤ)) : Option K → I → ℤ :=
  fun k i => match k with
    | none => z.1 i + z.2 (none,i)
    | some k => z.2 (some k,i)

theorem integerAffineMap_jointIntegerFrame {K I : Type*} [Fintype K]
    (z : (I → ℤ) × (Option K × I → ℤ)) (root : K → ℤ) :
    integerAffineMap (fun i k => jointIntegerFrame z (some k) i) (jointIntegerFrame z none) root =
      jointIntegerPhysicalSite root z := by
  funext i
  simp only [integerAffineMap, jointIntegerFrame, jointIntegerPhysicalSite,
    integerPhysicalSite, Pi.add_apply]
  rw [add_assoc]
  congr 2
  apply Finset.sum_congr rfl
  intro k _
  exact mul_comm _ _

end Erdos3.BooleanCubeKernel

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule

variable {m : ℕ} {G V : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (p : ∀ j, VectorPolynomial V ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (p j) d ∈ U j) (center : ∀ j, U j)

noncomputable def allocatedAffineDensity
    (frame : Option (LayerSamplerVariables G I n B) → V → ℝ) : ℝ :=
  allocatedCoefficientDensity B U b hb o hR hσ S (centeredAffineCoefficientTorus U p hm center frame)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory

variable {m : ℕ} {G V : Type*} [Fintype G] [Fintype V]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (p : ∀ j, VectorPolynomial V ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (p j) d ∈ U j) (center : ∀ j, U j)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

variable (modulus : V → ℕ)
variable (Γ : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) V modulus))
variable (width : Option (LayerSamplerVariables G I n B) × V → ℝ) (hwidth : ∀ z, 0 < width z)
variable (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus Γ width x)

variable (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hsmall : ∀ j, C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
variable (hp : ∀ j, DegreeLE (1 : V → ℕ) (j.val + 1) (p j))

include hσ1 C hC hchart hsmall hp

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel

variable {m : ℕ} {G V : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (p : ∀ j, VectorPolynomial V ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (p j) d ∈ U j) (center : ∀ j, U j)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel

variable {K V : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*}

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedFixedDensityProjection
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem trimmedSpatialWidths_antitone_budget {K X : Type*} {W W' τ : ℝ}
    (hW : 0 ≤ W) (hWW' : W ≤ W') (hτ : 0 ≤ τ) (N : X → ℕ)
    (z : Option K × X) :
    trimmedSpatialWidths W' τ N z ≤ trimmedSpatialWidths W τ N z := by
  rcases z with ⟨k, i⟩
  cases k with
  | none => exact le_rfl
  | some k =>
    dsimp only [trimmedSpatialWidths, centeredSpatialWidths]
    gcongr

theorem spatialWidthFraction_le_allocated_width {K X : Type*} {P W τ : ℝ}
    (hP : 0 ≤ P) (hW : 0 ≤ W) (hWP : W ≤ Real.exp P) (hτ : 0 ≤ τ)
    (N : X → ℕ) (z : Option K × X) :
    spatialWidthFraction P τ * (N z.2 : ℝ) ≤ trimmedSpatialWidths W τ N z := by
  exact (spatialWidthFraction_le_trimmed_width P hτ N z).trans
    (trimmedSpatialWidths_antitone_budget hW
      (hWP.trans (Real.exp_le_exp.mpr (by linarith))) hτ N z)

namespace VectorPolynomial

open BooleanCubeKernel

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable (c : LayerSamplerVariables G I n B → ℤ)

theorem allocatedPhysicalCube_site_le_exp {q : ℕ}
    (x : G → IntegerScalarCubeBox (Fin q) S.value)
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin q)
      (allocatedPrincipalSides B U basis S))
    {P : ℝ} (hroot : allocatedPhysicalRootBudget B U basis S c ≤ Real.exp P)
    (hL : (S.value : ℝ) ≤ Real.exp P) (s : Finset (Fin q)) (k : LayerSamplerVariables G I n B) :
    |((affineSite (allocatedPhysicalCubeRoot B U basis S c x y)
      (allocatedPhysicalCubeDirections B U basis S x y) s (some k) : ℤ) : ℝ)| ≤
      Real.exp (P + (q + 2 : ℕ)) := by
  have hs : (s.card : ℝ) ≤ q := by
    exact_mod_cast (show s.card ≤ q from by simpa only [Fintype.card_fin] using s.card_le_univ)
  have hd (i) : |(allocatedPhysicalCubeDirections B U basis S x y i k : ℝ)| ≤ Real.exp P :=
    (allocatedPhysicalCube_directions_bound B U basis S x y i k).trans hL
  have hr : |(allocatedPhysicalCubeRoot B U basis S c x y k : ℝ)| ≤ Real.exp P :=
    (allocatedPhysicalCube_root_budget B U basis S c x y k).trans hroot
  have hsum : |∑ i ∈ s, (allocatedPhysicalCubeDirections B U basis S x y i k : ℝ)| ≤
      (q : ℝ) * Real.exp P := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _i ∈ s, Real.exp P := Finset.sum_le_sum (fun i _ => hd i)
      _ = (s.card : ℝ) * Real.exp P := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hs (Real.exp_nonneg P)
  calc
    _ ≤ Real.exp P + (q : ℝ) * Real.exp P := by
      simp only [affineSite, Int.cast_add, Int.cast_sum]
      exact (abs_add_le _ _).trans (add_le_add hr hsum)
    _ ≤ Real.exp ((q : ℝ) + 2) * Real.exp P := by
      have hq : (q : ℝ) + 1 ≤ Real.exp ((q : ℝ) + 2) := by
        linarith [Real.add_one_le_exp ((q : ℝ) + 2)]
      nlinarith [Real.exp_pos P]
    _ = _ := by rw [← Real.exp_add]; congr 1; push_cast; ring

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Polynomial
open scoped BigOperators

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.JointFrameCoefficientCoverSample
namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators

theorem substitute_translate_joint_frame {K X V : Type*} [Fintype K]
    [AddCommGroup V] [Module ℝ V] (p : VectorPolynomial X ℝ V)
    (a : X → ℤ) (z : Option K × X → ℤ) :
    substitute (affineParameterSubstitution (fun k v => (z (k,v) : ℝ)))
      (translate (fun v => (a v : ℝ)) p) =
    substitute (affineParameterSubstitution
      (fun k v => (jointIntegerFrame (a,z) k v : ℝ))) p := by
  change substitute _ (substitute (fun v => MvPolynomial.X v + MvPolynomial.C (a v : ℝ)) p) = _
  rw [substitute_comp]
  apply congrArg (fun f : X → MvPolynomial K ℝ => substitute f p)
  funext v
  simp only [map_add, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
    affineParameterSubstitution, rowPolynomial, jointIntegerFrame, Int.cast_add, map_add,
    MvPolynomial.algebraMap_eq]
  ring

theorem affineSampleCoefficientArray_joint_frame {K X : Type*} [Fintype K]
    {m : ℕ} {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (a : X → ℤ) (z : Option K × X → ℤ) :
    affineSampleCoefficientArray U (fun j => translate (fun v => (a v : ℝ)) (p j))
      (fun j => coefficients_translate_mem (U j) (fun v => (a v : ℝ)) (p j) (hm j))
      (fun k v => (z (k,v) : ℝ)) =
    affineSampleCoefficientArray U p hm (fun k v => (jointIntegerFrame (a,z) k v : ℝ)) := by
  funext s
  apply Subtype.ext
  simp only [affineSampleCoefficientArray_val, substitute_translate_joint_frame]

theorem affineSampleCoefficientTorus_joint_frame {K X : Type*} [Fintype K]
    {m : ℕ} {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (a : X → ℤ) (z : Option K × X → ℤ) :
    affineSampleCoefficientTorus U (fun j => translate (fun v => (a v : ℝ)) (p j))
      (fun j => coefficients_translate_mem (U j) (fun v => (a v : ℝ)) (p j) (hm j))
      (fun k v => (z (k,v) : ℝ)) =
    affineSampleCoefficientTorus U p hm (fun k v => (jointIntegerFrame (a,z) k v : ℝ)) :=
  congrArg (QuotientAddGroup.mk' (coefficientIntegerLattice U))
    (affineSampleCoefficientArray_joint_frame U p hm a z)

variable {m : ℕ} {G X : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (R σ : Fin m → ℝ) (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (L₀ : ℕ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedReferenceJetMass
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory VectorPolynomial
open scoped BigOperators Classical

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory VectorPolynomial
open scoped BigOperators Classical

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

theorem physicalWindow_sum_le_sampled_mass {X : Type*} [Fintype X] {q : ℕ}
    (stride : X → ℕ) (hs : ∀ x, 0 < stride x)
    (residue : ColumnResiduePattern (Option (Fin q)) X stride)
    (V : Option (Fin q) × X → ℝ) (hV : ∀ z, 0 < V z)
    (hscale : ∀ z, 8 * (probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth stride V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride {residue} V z)
    (f : (X → (Unit ⊕ Fin q) → ℤ) → ℝ) (hf : ∀ v, 0 ≤ f v)
    (window : Finset (X → (Unit ⊕ Fin q) → ℤ))
    (hresidue : ∀ v ∈ window, columnResiduePattern stride (standardPhysicalCubeFrame v) = residue)
    (hinner : ∀ v ∈ window, ∀ i, |(standardPhysicalCubeFrame v i : ℝ) / V i| ≤ 1 / 2) :
    (∑ v ∈ window, f v) ≤
      ((3 / 2 : ℝ) ^ Fintype.card (Option (Fin q) × X) *
        (∏ i, residueProfileWidth stride V i) /
        (smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin q) × X)) *
          selectedResidueDensityMass stride {residue} V (fun z => f (standardPhysicalCubeOutput z)) := by
  let frames := window.image standardPhysicalCubeFrame
  have hr : ∀ z ∈ frames, columnResiduePattern stride z = residue := by
    intro z hz
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
    exact hresidue v hv
  have hi : ∀ z ∈ frames, ∀ i, |(z i : ℝ) / V i| ≤ 1 / 2 := by
    intro z hz
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
    exact hinner v hv
  have h := selectedResidueDensityMass_singleton_window_bound stride hs residue V hV hscale hZ
    (fun z => f (standardPhysicalCubeOutput z)) (fun z => hf _) frames hr hi
  have he : (∑ z ∈ frames, f (standardPhysicalCubeOutput z)) = ∑ v ∈ window, f v := by
    dsimp only [frames]
    rw [Finset.sum_image]
    · simp only [standardPhysicalCubeOutput_frame]
    · intro v _ w _ he
      exact standardPhysicalCubeFrame_injective he
  rwa [he] at h

theorem physicalReconstruction_sum_le_sampled_mass {X K : Type*} [Fintype X] [Fintype K] {q : ℕ}
    (stride : X → ℕ) (hs : ∀ x, 0 < stride x)
    (root : K → ℤ) (D : Matrix (Fin q) K ℤ)
    (residue : ColumnResiduePattern (Option K) X stride)
    (H : X → ℝ) (hH : ∀ x, 0 < H x)
    (hrows : ∀ x i, (∑ k, |(physicalCubeCoefficient root D i k : ℝ)|) ≤ H x)
    (hscale : ∀ x, 8 * (probabilityProfileLipschitz : ℝ) ≤ 20 * H x)
    (f : (X → (Unit ⊕ Fin q) → ℤ) → ℝ) (hf : ∀ v, 0 ≤ f v) :
    let r := boundedColumnResidueRepresentative stride residue
    let target := columnResiduePattern stride
      (standardPhysicalCubeFrame (physicalCubeRootDifferences root D 0 r))
    let V := referenceJetEnvelopeWidths (q := q) stride H
    0 < ∑' z, selectedResidueSmoothWeight stride {target} V z →
    (∑ v ∈ spatialWindow H 4, f (physicalResidueReconstruction root D 0 r stride v)) ≤
      ((3 / 2 : ℝ) ^ Fintype.card (Option (Fin q) × X) *
        (∏ i, residueProfileWidth stride V i) /
        (smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin q) × X)) *
          selectedResidueDensityMass stride {target} V (fun z => f (standardPhysicalCubeOutput z)) := by
  intro r target V hZ
  let window := (spatialWindow H 4).image (physicalResidueReconstruction root D 0 r stride)
  have hr : ∀ k x, |(r (k,x) : ℝ)| ≤ stride x := by
    intro k x
    have h := boundedColumnResidueRepresentative_bounds stride hs residue (k,x)
    rw [abs_of_nonneg (by exact_mod_cast h.1 : (0 : ℝ) ≤ r (k,x))]
    exact_mod_cast h.2.le
  have hoffset := physicalCube_zero_residue_bound root D stride r hr H hrows
  have hres : ∀ v ∈ window, columnResiduePattern stride (standardPhysicalCubeFrame v) = target := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    exact physicalResidueReconstruction_columnResidue root D 0 r stride w
  have hin : ∀ v ∈ window, ∀ i, |(standardPhysicalCubeFrame v i : ℝ) / V i| ≤ 1 / 2 := by
    intro v hv i
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    exact physicalResidueReconstruction_envelope root D stride hs r H hH hoffset hw i
  have hsc : ∀ z, 8 * (probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth stride V z := by
    intro z
    change _ ≤ residueProfileWidth stride (referenceJetEnvelopeWidths stride H) z
    rw [referenceJetEnvelopeWidths_residue stride hs H]
    exact hscale z.2
  have h := physicalWindow_sum_le_sampled_mass stride hs target V
    (referenceJetEnvelopeWidths_pos stride hs H hH) hsc hZ f hf window hres hin
  have he : (∑ v ∈ window, f v) =
      ∑ v ∈ spatialWindow H 4, f (physicalResidueReconstruction root D 0 r stride v) := by
    dsimp only [window]
    exact Finset.sum_image (fun v _ w _ he => physicalResidueReconstruction_injective root D 0 r stride hs he)
  rwa [he] at h

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory VectorPolynomial
open scoped BigOperators Classical

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

theorem referenceJetEnvelope_volume {X : Type*} [Fintype X] {q : ℕ}
    (stride : X → ℕ) (hs : ∀ x, 0 < stride x) (H : X → ℝ) :
    ((3 / 2 : ℝ) ^ Fintype.card (Option (Fin q) × X) *
      (∏ i, residueProfileWidth stride (referenceJetEnvelopeWidths (q := q) stride H) i) /
      (smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin q) × X)) =
    (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin q) × X) *
      (∏ x, ∏ _i : Unit ⊕ Fin q, H x) := by
  have hprod : (∏ i, residueProfileWidth stride (referenceJetEnvelopeWidths (q := q) stride H) i) =
      20 ^ Fintype.card (Option (Fin q) × X) * (∏ i : Option (Fin q) × X, H i.2) := by
    simp_rw [referenceJetEnvelopeWidths_residue stride hs H]
    rw [Finset.prod_mul_distrib]
    simp only [Finset.prod_const, Finset.card_univ]
  have hcoord : (∏ i : Option (Fin q) × X, H i.2) = ∏ x, ∏ _i : Unit ⊕ Fin q, H x := by
    rw [Fintype.prod_prod_type, Finset.prod_comm]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_option,
      Fintype.card_fin, Fintype.card_sum, Fintype.card_unique, Nat.add_comm]
  rw [hprod, hcoord, ← mul_assoc, ← mul_pow]
  norm_num only [show (3 / 2 : ℝ) * 20 = 30 by norm_num]
  rw [mul_div_right_comm, ← div_pow]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

noncomputable def coarseReferenceMassConstant (q : ℕ) (X : Type*) [Fintype X]
    (W L : ℝ) : ℝ :=
  4 * (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin q) × X) *
    (((1 + W) / L) ^ q) ^ Fintype.card X

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory VectorPolynomial
open scoped BigOperators Classical

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory Polynomial
open scoped BigOperators Classical NNReal

end Erdos3.VectorPolynomial

end

end OAI

end


