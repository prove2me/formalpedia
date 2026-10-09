-- Prove2me | Definitions.Def_OAIErdos3B108
-- name    : OAIErdos3B108
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-09T00:42:51.996506+00:00
-- url     : https://prove2.me/theorems/9a5891fd-a48b-460f-ace6-6593157a11ba
-- title:
--   OpenAI Erdős-3 split, definitions bundle 109 of 132
-- statement:
--   Definitions bundle 109 of 132 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B107`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 109 available.
--
--   Modules: `OAI.Erdos3.BooleanCubeKernel.affineCubeFourierProjection`, `OAI.Erdos3.BooleanCubeKernel.affineCubeFourierSum`, `OAI.Erdos3.BooleanCubeKernel.affineCubeModeFactors`, `OAI.Erdos3.BooleanCubeKernel.affineCubeModeFactors_bounded`, `OAI.Erdos3.BooleanCubeKernel.affineCubeModeFactors_iff_bounded`, `OAI.Erdos3.BooleanCubeKernel.affine_cube_residue_removal_at_error`, `OAI.Erdos3.BooleanCubeKernel.coefficientResidualAverage_continuous`, `OAI.Erdos3.BooleanCubeKernel.coefficientResidual_section_integrable`, `OAI.Erdos3.BooleanCubeKernel.coefficientTorusFourierProjection_approx_residualAverage`, `OAI.Erdos3.BooleanCubeKernel.coefficientTorusFourierSum_residualAverage`, `OAI.Erdos3.BooleanCubeKernel.exists_affine_cube_ambient_residue_removal`, `OAI.Erdos3.BooleanCubeKernel.exists_affine_cube_congruence_removal`, `OAI.Erdos3.BooleanCubeKernel.exists_affine_cube_fourier_projection`, `OAI.Erdos3.BooleanCubeKernel.exists_affine_cube_residue_uniform_removal`, `OAI.Erdos3.BooleanCubeKernel.exists_cube_residue_threshold_exp_budget`, `OAI.Erdos3.BooleanCubeKernel.layeredSiteWeight_oneSite`, `OAI.Erdos3.BooleanCubeKernel.not_affineCubeModeFactors_iff`, `OAI.Erdos3.RationalFilteredNilmanifold.FixedPositiveNiltestRealization`, `OAI.Erdos3.RationalFilteredNilmanifold.SingleRefilteredRecoveryFamily`, `OAI.Erdos3.VectorPolynomial.affineCoefficientCoverSample`, `OAI.Erdos3.VectorPolynomial.affineCoefficientCoverSample_eq_scaled`, `OAI.Erdos3.VectorPolynomial.affineCoefficientCoverSample_projection`, `OAI.Erdos3.VectorPolynomial.affineSampleCoefficientArray_smul`, `OAI.Erdos3.VectorPolynomial.affine_coefficient_amplitude_residue_removal_at_error`, `OAI.Erdos3.VectorPolynomial.affine_coefficient_residue_removal_at_error`, `OAI.Erdos3.VectorPolynomial.allocatedBufferedPhysicalChartRadius`, `OAI.Erdos3.VectorPolynomial.allocatedBufferedPhysicalChartRadius_inv_le_exp`, `OAI.Erdos3.VectorPolynomial.allocatedBufferedPhysicalChartRadius_inv_le_exp_uniform`, `OAI.Erdos3.VectorPolynomial.allocatedBufferedPhysicalChartRadius_le_original`, `OAI.Erdos3.VectorPolynomial.allocatedBufferedPhysicalChartRadius_le_supported`, `OAI.Erdos3.VectorPolynomial.allocatedBufferedPhysicalChartRadius_pos`, `OAI.Erdos3.VectorPolynomial.allocatedFullSiteRadius`, `OAI.Erdos3.VectorPolynomial.allocatedFullSiteRadius_le_exp`, `OAI.Erdos3.VectorPolynomial.allocatedFullSiteRadius_one_le`, `OAI.Erdos3.VectorPolynomial.allocatedFullSiteRadius_pos`, `OAI.Erdos3.VectorPolynomial.allocatedIdealCoverRadius`, `OAI.Erdos3.VectorPolynomial.allocatedIdealCoverRadius_inv_le_exp`, `OAI.Erdos3.VectorPolynomial.allocatedIdealCoverRadius_pos`, `OAI.Erdos3.VectorPolynomial.allocatedIdealCoverSupport`, `OAI.Erdos3.VectorPolynomial.allocatedIdealCoverSupport_ideal`, `OAI.Erdos3.VectorPolynomial.allocatedIdealCoverSupport_inactive`, `OAI.Erdos3.VectorPolynomial.allocatedIdealCoverSupport_le_exp`, `OAI.Erdos3.VectorPolynomial.allocatedIdealCoverSupport_nonneg`, `OAI.Erdos3.VectorPolynomial.allocatedSiteChartRadius_inv_le_exp`, `OAI.Erdos3.VectorPolynomial.allocatedSiteChartRadius_le_original`, `OAI.Erdos3.VectorPolynomial.allocatedSiteCoefficientRadius`, `OAI.Erdos3.VectorPolynomial.allocatedSiteCoefficientRadius_nonneg`, `OAI.Erdos3.VectorPolynomial.allocatedSiteJetSize_le_allowance`, `OAI.Erdos3.VectorPolynomial.allocatedSiteRootAllowance`, `OAI.Erdos3.VectorPolynomial.allocatedSiteRootAllowance_le_exp`, `OAI.Erdos3.VectorPolynomial.allocatedSiteRootAllowance_one_le`, `OAI.Erdos3.VectorPolynomial.boundedExponentMap`, `OAI.Erdos3.VectorPolynomial.boundedSiteMatrix_mapDomain`, `OAI.Erdos3.VectorPolynomial.coefficientProductDensity`, `OAI.Erdos3.VectorPolynomial.coefficientProductDensity_nonneg`, `OAI.Erdos3.VectorPolynomial.coefficientProductDensity_probability`, `OAI.Erdos3.VectorPolynomial.coefficientTorus_compact_of_lattice`, `OAI.Erdos3.VectorPolynomial.exists_affine_coefficient_ambient_residue_removal`, `OAI.Erdos3.VectorPolynomial.exists_affine_coefficient_amplitude_ambient_residue_removal`, `OAI.Erdos3.VectorPolynomial.exists_affine_coefficient_amplitude_congruence_removal`, `OAI.Erdos3.VectorPolynomial.exists_affine_coefficient_amplitude_fourier_normalization`, `OAI.Erdos3.VectorPolynomial.exists_affine_coefficient_amplitude_residue_uniform_removal`, `OAI.Erdos3.VectorPolynomial.exists_affine_coefficient_congruence_removal`, `OAI.Erdos3.VectorPolynomial.exists_affine_coefficient_cover_haar_approximation`, `OAI.Erdos3.VectorPolynomial.exists_affine_coefficient_cover_tilted_family_comparison`, `OAI.Erdos3.VectorPolynomial.exists_affine_coefficient_density_mass`, `OAI.Erdos3.VectorPolynomial.exists_affine_coefficient_fourier_normalization`, `OAI.Erdos3.VectorPolynomial.exists_affine_coefficient_haar_approximation`, `OAI.Erdos3.VectorPolynomial.exists_affine_coefficient_haar_comparison`, `OAI.Erdos3.VectorPolynomial.exists_affine_coefficient_residue_uniform_removal`, `OAI.Erdos3.VectorPolynomial.forecastInactiveSlicedSiteNumerics`, `OAI.Erdos3.VectorPolynomial.forecastSlicedEarlyDiagonalBudget`, `OAI.Erdos3.VectorPolynomial.forecastSlicedEarlyPolynomial`, `OAI.Erdos3.VectorPolynomial.forecastSlicedEarlyPolynomial_eval`, `OAI.Erdos3.VectorPolynomial.selectedResidueSmoothPMF_weighted_coefficient_density`, `OAI.Erdos3.VectorPolynomial.siteImage_density_euclideanJet`, `OAI.Erdos3.VectorPolynomial.slicedFixedUniformAccuracyLog`, `OAI.Erdos3.VectorPolynomial.slicedFixedUniformSiteLog`, `OAI.Erdos3.VectorPolynomial.slicedFixedUniformSiteLog_mono`, `OAI.Erdos3.VectorPolynomial.slicedFixedUniformSiteLog_nonneg`, `OAI.Erdos3.VectorPolynomial.slicedFixedUniformSitePolynomial`, `OAI.Erdos3.VectorPolynomial.slicedFixedUniformSitePolynomial_eval`, `OAI.Erdos3.VectorPolynomial.slicedFixedZeroGeometryLog`, `OAI.Erdos3.VectorPolynomial.slicedFixedZeroGeometryLog_eval₂`, `OAI.Erdos3.VectorPolynomial.slicedFixedZeroGeometryLog_mono`, `OAI.Erdos3.VectorPolynomial.slicedFixedZeroGeometryLog_nonneg`, `OAI.Erdos3.boundedSiteMatrix_fixed_kernel_factor`, `OAI.Erdos3.exists_fourier_uniform_budget`, `OAI.Erdos3.exists_integer_cover_threshold`, `OAI.Erdos3.exists_matrix_factor_of_common_reconstruction`, `OAI.Erdos3.exists_mode_residue_threshold_exp_budget`, `OAI.Erdos3.exists_slicedGridSiteLog_uniform_budget`, `OAI.Erdos3.forecastSlicedEarlyLogs_le_diagonal_of_dimensions`, `OAI.Erdos3.fourierModeError`, `OAI.Erdos3.fourierModeError_cost_le`, `OAI.Erdos3.fourierModeError_inv_le_exp`, `OAI.Erdos3.fourierModeError_pos`, `OAI.Erdos3.integerBooleanSitesFromRows`, `OAI.Erdos3.modeResidueSideThreshold`, `OAI.Erdos3.modeResidueSideThreshold_bounds`, `OAI.Erdos3.modeResidueWidth_mesh`, `OAI.Erdos3.selectedResidueSmoothPMF_weighted_fourier_normalization`, `OAI.Erdos3.selectedResidueSmoothWeight_pos_of_threshold`, `OAI.Erdos3.slicedGridSiteLog_eval`, `OAI.Erdos3.slicedGridSiteLog_mono`, `OAI.Erdos3.uniformProductAccuracyLog_eval₂`, `OAI.Erdos3.uniformProductAccuracyLog_mono`, `_private.Polynomial.ForecastSlicedEarlyUnrestrictedPolynomialBudget.0.OAI.Erdos3.majorArcBiasLog_mono_budget`, `_private.Polynomial.ForecastSlicedEarlyUnrestrictedPolynomialBudget.0.OAI.Erdos3.majorArcCoverLog_mono_budget`, `_private.Polynomial.ForecastSlicedEarlyUnrestrictedPolynomialBudget.0.OAI.Erdos3.majorArcErrorLog_mono_budget`, `_private.Polynomial.ForecastSlicedEarlyUnrestrictedPolynomialBudget.0.OAI.Erdos3.majorArcLengthLog_mono_budget`, `_private.Polynomial.ForecastSlicedEarlyUnrestrictedPolynomialBudget.0.OAI.Erdos3.majorArcLocalizationLog_mono_budget`, `_private.Polynomial.ForecastSlicedEarlyUnrestrictedPolynomialBudget.0.OAI.Erdos3.majorArcSpectrumLog_mono_budget`, `_private.Polynomial.ForecastSlicedEarlyUnrestrictedPolynomialBudget.0.OAI.Erdos3.positiveModerateAccuracyLog_mono_budget`, `_private.Polynomial.ForecastSlicedEarlyUnrestrictedPolynomialBudget.0.OAI.Erdos3.positiveModerateCoverLog_mono_budget`, `_private.Polynomial.ForecastSlicedEarlyUnrestrictedPolynomialBudget.0.OAI.Erdos3.positiveModerateLengthLog_mono_budget`, `_private.Polynomial.ForecastSlicedEarlyUnrestrictedPolynomialBudget.0.OAI.Erdos3.positiveModerateSpectrumLog_mono_budget`, `_private.Polynomial.ForecastSlicedEarlyUnrestrictedPolynomialBudget.0.OAI.Erdos3.positiveRetainedBiasLog_mono_budget`, `_private.Polynomial.ForecastSlicedEarlyUnrestrictedPolynomialBudget.0.OAI.Erdos3.positiveRetainedComplexityLog_mono_budget`, `_private.Polynomial.ForecastSlicedEarlyUnrestrictedPolynomialBudget.0.OAI.Erdos3.positiveRetainedDenominatorLog_mono_budget`, `_private.Polynomial.ForecastSlicedEarlyUnrestrictedPolynomialBudget.0.OAI.Erdos3.positiveRetainedFrequencyLog_mono_budget`, `_private.Polynomial.ForecastSlicedEarlyUnrestrictedPolynomialBudget.0.OAI.Erdos3.positiveSpectrumCardLog_mono_budget`, `_private.Polynomial.ForecastSlicedEarlyUnrestrictedPolynomialBudget.0.OAI.Erdos3.uniformBlockAccuracyLog_mono_budget`, `_private.Polynomial.ForecastSlicedEarlyUnrestrictedPolynomialBudget.0.OAI.Erdos3.uniformRetainedBiasLog_mono_budget`, `_private.Polynomial.ForecastSlicedEarlyUnrestrictedPolynomialBudget.0.OAI.Erdos3.uniformRetainedDenominatorLog_mono_budget`, `_private.Polynomial.ForecastSlicedEarlyUnrestrictedPolynomialBudget.0.OAI.Erdos3.uniformRetainedFrequencyLog_mono_budget`, `_private.Polynomial.ForecastSlicedEarlyUnrestrictedPolynomialBudget.0.OAI.Erdos3.uniformSpectrumCardLog_mono_budget`, `_private.Polynomial.ForecastSlicedEarlyUnrestrictedPolynomialBudget.0.OAI.Erdos3.uniformSpectrumSizeLog_mono_budget`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B034
import Definitions.Def_OAIErdos3B036

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FixedKernelSiteImage
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

theorem exists_matrix_factor_of_common_reconstruction {S J K I : Type*}
    [Fintype S] [Fintype J] [Fintype K] [Fintype I]
    (E₀ : Matrix S K ℝ) (E : Matrix S I ℝ) (B : Matrix S J ℝ) (T : Matrix J S ℝ)
    (h₀ : B * T * E₀ = E₀) (hE : B * T * E = E)
    (hs : Function.Surjective (Matrix.mulVec (T * E₀))) :
    ∃ R : Matrix K I ℝ, E₀ * R = E := by
  choose v hv using fun i : I => hs (fun j => (T * E) j i)
  let R : Matrix K I ℝ := fun k i => v i k
  have hr : (T * E₀) * R = T * E := by
    ext j i
    exact congrFun (hv i) j
  refine ⟨R, ?_⟩
  calc
    E₀ * R = (B * (T * E₀)) * R := by rw [← Matrix.mul_assoc, h₀]
    _ = B * ((T * E₀) * R) := Matrix.mul_assoc _ _ _
    _ = B * (T * E) := by rw [hr]
    _ = E := by rw [← Matrix.mul_assoc, hE]

theorem boundedSiteMatrix_fixed_kernel_factor {α K I : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] [Fintype I]
    (root₀ : K → ℤ) (D₀ : Matrix α K ℤ) (a : ℤ) (ha : a ≠ 0)
    (hperiod : integerScalarLattice α a ≤ D₀.mulVecLin.range)
    (h : ℕ) (root : I → ℤ) (D : Matrix α I ℤ) :
    ∃ R : Matrix (VectorPolynomial.BoundedCoefficientExponent K h)
        (VectorPolynomial.BoundedCoefficientExponent I h) ℝ,
      Matrix.of (fun s d => (VectorPolynomial.boundedSiteMatrix h (integerAffineCube root₀ D₀) s d : ℝ)) * R =
        Matrix.of (fun s d => (VectorPolynomial.boundedSiteMatrix h (integerAffineCube root D) s d : ℝ)) := by
  classical
  let B := boundedBooleanReconstructionMatrix α h
  let T := booleanJetExtractionMatrix (Subtype.val : BoundedBooleanJet α h → Finset α)
  let E₀ := VectorPolynomial.boundedSiteMatrix h (integerAffineCube root₀ D₀)
  let E := VectorPolynomial.boundedSiteMatrix h (integerAffineCube root D)
  let B' := Matrix.of (fun s j => (B s j : ℝ))
  let T' := Matrix.of (fun j s => (T j s : ℝ))
  let E₀' := Matrix.of (fun s d => (E₀ s d : ℝ))
  let E' := Matrix.of (fun s d => (E s d : ℝ))
  have h₀ : B' * T' * E₀' = E₀' := by
    ext s d
    have hz := congrArg (fun z : ℤ => (z : ℝ))
      (congrFun (congrFun (boundedBooleanReconstruction_siteMatrix root₀ D₀ h) s) d)
    simpa only [B', T', E₀', B, T, E₀, Matrix.mul_apply, Matrix.of_apply,
      Int.cast_sum, Int.cast_mul] using hz
  have hE : B' * T' * E' = E' := by
    ext s d
    have hz := congrArg (fun z : ℤ => (z : ℝ))
      (congrFun (congrFun (boundedBooleanReconstruction_siteMatrix root D h) s) d)
    simpa only [B', T', E', B, T, E, Matrix.mul_apply, Matrix.of_apply,
      Int.cast_sum, Int.cast_mul] using hz
  have hjet : T' * E₀' = Matrix.of (fun j d => (boundedCoefficientJetMatrix root₀ D₀ h
      (Subtype.val : BoundedBooleanJet α h → Finset α) j d : ℝ)) := by
    ext j d
    have hz := congrArg (fun z : ℤ => (z : ℝ))
      (congrFun (congrFun (booleanJetExtractionMatrix_mul_boundedSite root₀ D₀ h
        (Subtype.val : BoundedBooleanJet α h → Finset α)) j) d)
    simpa only [T', E₀', T, E₀, Matrix.mul_apply, Matrix.of_apply, Int.cast_sum, Int.cast_mul] using hz
  apply exists_matrix_factor_of_common_reconstruction E₀' E' B' T' h₀ hE
  rw [hjet]
  intro v
  obtain ⟨x, hx⟩ := matrixModuleAction_surjective_of_period (W := ℝ)
    (boundedCoefficientJetMatrix root₀ D₀ h (Subtype.val : BoundedBooleanJet α h → Finset α))
    (a ^ h) (pow_ne_zero _ ha)
    (boundedCoefficientJetMatrix_period root₀ D₀ a hperiod h
      (Subtype.val : BoundedBooleanJet α h → Finset α) Subtype.val_injective (fun j => j.property)) v
  refine ⟨x, ?_⟩
  ext j
  exact congrFun hx j

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.FixedKernelPolynomialCover
namespace OAI

section

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix

noncomputable def boundedExponentMap {K I : Type*} (e : K → I) (h : ℕ)
    (d : BoundedCoefficientExponent K h) : BoundedCoefficientExponent I h :=
  ⟨d.val.mapDomain e, by rw [Finsupp.degree_mapDomain]; exact d.property⟩

theorem boundedSiteMatrix_mapDomain {K I S : Type*} (h : ℕ) (site : S → I → ℤ) (e : K → I) :
    (boundedSiteMatrix h site).submatrix id (boundedExponentMap e h) =
      boundedSiteMatrix h (fun s k => site s (e k)) := by
  ext s d
  change (d.val.mapDomain e).prod (fun i n => site s i ^ n) = d.val.prod (fun k n => site s (e k) ^ n)
  exact Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RetainedAffineCommonCover
namespace OAI

section

namespace Erdos3

noncomputable def modeResidueSideThreshold (m d : ℕ) (D S ρ ε : ℝ) : ℝ :=
  modeRemovalSideThreshold m d D S ρ ε + S / (ρ * modeRemovalMesh d)

theorem modeResidueSideThreshold_bounds (m d : ℕ) {D S ρ ε : ℝ}
    (hD : 0 ≤ D) (hS : 0 ≤ S) (hρ : 0 < ρ) (hε : 0 < ε) :
    modeRemovalSideThreshold m d D S ρ ε ≤ modeResidueSideThreshold m d D S ρ ε ∧
      S / modeRemovalMesh d ≤ ρ * modeResidueSideThreshold m d D S ρ ε := by
  have hδ := modeRemovalMesh_pos d
  have hb := (modeRemovalSideThreshold_bounds m d hD hS hρ hε).1
  constructor
  · exact le_add_of_nonneg_right (by positivity)
  · have hle : S / (ρ * modeRemovalMesh d) ≤ modeResidueSideThreshold m d D S ρ ε :=
      le_add_of_nonneg_left hb.le
    have he : ρ * (S / (ρ * modeRemovalMesh d)) = S / modeRemovalMesh d := by
      field_simp
    rw [← he]
    exact mul_le_mul_of_nonneg_left hle hρ.le

theorem modeResidueWidth_mesh (m d : ℕ) {D S ρ ε H V : ℝ} {M : ℕ}
    (hD : 0 ≤ D) (hS : 0 ≤ S) (hρ : 0 < ρ) (hε : 0 < ε)
    (hM : 0 < M) (hMS : (M : ℝ) ≤ S)
    (hH : modeResidueSideThreshold m d D S ρ ε ≤ H)
    (hV : 0 < V) (hwidth : ρ * H ≤ V) :
    1 ≤ V / M ∧ 1 / (V / M) ≤ modeRemovalMesh d := by
  have hm : (0 : ℝ) < M := by exact_mod_cast hM
  have hδ := modeRemovalMesh_pos d
  have hu : (M : ℝ) / modeRemovalMesh d ≤ V :=
    (div_le_div_of_nonneg_right hMS hδ.le).trans
      (((modeResidueSideThreshold_bounds m d hD hS hρ hε).2.trans
        (mul_le_mul_of_nonneg_left hH hρ.le)).trans hwidth)
  apply modeRemovalMesh_of_width d (div_pos hV hm)
  apply (le_div_iff₀ hm).mpr
  calc
    (1 / modeRemovalMesh d) * M = (M : ℝ) / modeRemovalMesh d := by ring
    _ ≤ V := hu

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem selectedResidueSmoothWeight_pos_of_threshold {K I : Type*} [Fintype K] [Fintype I]
    (m : ℕ) {D S ρ ε : ℝ} (hD : 0 ≤ D) (hS : 0 ≤ S) (hρ : 0 < ρ) (hε : 0 < ε)
    (modulus : I → ℕ) (hmodulus : ∀ j, 0 < modulus j) (hbound : ∀ j, (modulus j : ℝ) ≤ S)
    (H : I → ℝ)
    (hsize : ∀ j, modeResidueSideThreshold m (Fintype.card (K × I)) D S ρ ε ≤ H j)
    (G : Finset (ColumnResiduePattern K I modulus)) (hG : G.Nonempty)
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z) (hwidth : ∀ z, ρ * H z.2 ≤ V z) :
    0 < ∑' x, selectedResidueSmoothWeight modulus G V x := by
  let d := Fintype.card (K × I)
  have hv z : 1 ≤ residueProfileWidth modulus V z ∧
      1 / residueProfileWidth modulus V z ≤ modeRemovalMesh d :=
    modeResidueWidth_mesh m d hD hS hρ hε (hmodulus z.2) (hbound z.2)
      (hsize z.2) (hV z) (hwidth z)
  apply selectedResidueSmoothWeight_mass_pos modulus G hG V hV
  intro r
  rw [← residueSmoothWeight_mass _ modulus hmodulus V hV]
  have hlower := shiftedSmoothProductMass_lower
    (residueProfileCenter (columnResidueRepresentative modulus r.val) modulus)
    (residueProfileWidth modulus V) (residueProfileWidth_pos modulus V hmodulus hV)
    (modeRemovalMesh_pos d).le (modeRemovalMesh_le_one d) (fun z => (hv z).2) (modeRemovalMesh_small d)
  exact (div_pos (Finset.prod_pos (fun z _ => residueProfileWidth_pos modulus V hmodulus hV z))
    (by norm_num)).trans_le hlower

end Erdos3

end

section

namespace Erdos3

open Polynomial

theorem exists_mode_residue_threshold_exp_budget (m : ℕ) :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ (n d : ℕ) (P F D S ρ ε : ℝ),
      0 ≤ P → (n : ℝ) ≤ P → (d : ℝ) ≤ P →
      0 ≤ F → F ≤ Real.exp P → 0 ≤ D → D ≤ Real.exp P →
      0 ≤ S → S ≤ Real.exp P → 0 < ρ → 1 / ρ ≤ Real.exp P →
      0 < ε → 1 / ε ≤ Real.exp P →
      modeResidueSideThreshold m d D S ρ ε ≤ Real.exp ((P + K) ^ K) ∧
      modeRemovalRankThreshold m n d F D S ρ ε ≤ Real.exp ((P + K) ^ K) := by
  obtain ⟨K₀, _, hbase⟩ := exists_mode_threshold_exp_budget m
  obtain ⟨K, hK, hpoly⟩ := exists_natPolynomial_eval_budget
    ((X + C K₀) ^ K₀ + (2 * X + modeProfileLogPolynomial + 3) + 1)
  refine ⟨K, hK, ?_⟩
  intro n d P F D S ρ ε hP hn hd hF hFP hD hDP hS hSP hρ hρP hε hεP
  obtain ⟨hs, hr⟩ := hbase n d P F D S ρ ε hP hn hd hF hFP hD hDP hS hSP hρ hρP hε hεP
  have hprof := modeProfileLog_nonneg hP
  have hδ := modeRemovalMesh_pos d
  have he : S / (ρ * modeRemovalMesh d) ≤ Real.exp (2 * P + modeProfileLog P + 3) := by
    calc
      _ = S * (1 / ρ) * (1 / modeRemovalMesh d) := by ring
      _ ≤ Real.exp P * Real.exp P * Real.exp (modeProfileLog P + 3) := by
        gcongr
        exact modeRemovalMesh_inv_le_exp d hP hd
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hp : (P + K₀) ^ K₀ + (2 * P + modeProfileLog P + 3) + 1 ≤ (P + K) ^ K := by
    simpa [Polynomial.eval₂_pow, modeProfileLogPolynomial_eval] using hpoly P hP
  have hb0 : 0 ≤ (P + K₀) ^ K₀ := by positivity
  constructor
  · exact (add_le_exp_add_one hb0 (by linarith) hs he).trans (Real.exp_le_exp.mpr hp)
  · exact hr.trans (Real.exp_le_exp.mpr (by linarith))

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open Polynomial

theorem exists_cube_residue_threshold_exp_budget (m q : ℕ) :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ (n d : ℕ) (P F L S ρ ε : ℝ),
      0 ≤ P → (n : ℝ) ≤ P → (d : ℝ) ≤ P →
      0 ≤ F → F ≤ Real.exp P → 0 ≤ L → L ≤ Real.exp P →
      0 ≤ S → S ≤ Real.exp P → 0 < ρ → 1 / ρ ≤ Real.exp P →
      0 < ε → 1 / ε ≤ Real.exp P →
      modeResidueSideThreshold m d (cubeModePolynomialBudget q L) S ρ ε ≤ Real.exp ((P + K) ^ K) ∧
      modeRemovalRankThreshold m n d F (cubeModePolynomialBudget q L) S ρ ε ≤ Real.exp ((P + K) ^ K) := by
  obtain ⟨K₀, _, hbase⟩ := exists_cube_mode_threshold_exp_budget m q
  obtain ⟨K, hK, hpoly⟩ := exists_natPolynomial_eval_budget
    ((X + C K₀) ^ K₀ + (2 * X + modeProfileLogPolynomial + 3) + 1)
  refine ⟨K, hK, ?_⟩
  intro n d P F L S ρ ε hP hn hd hF hFP hL hLP hS hSP hρ hρP hε hεP
  obtain ⟨hs, hr⟩ := hbase n d P F L S ρ ε hP hn hd hF hFP hL hLP hS hSP hρ hρP hε hεP
  have hprof := modeProfileLog_nonneg hP
  have hδ := modeRemovalMesh_pos d
  have he : S / (ρ * modeRemovalMesh d) ≤ Real.exp (2 * P + modeProfileLog P + 3) := by
    calc
      _ = S * (1 / ρ) * (1 / modeRemovalMesh d) := by ring
      _ ≤ Real.exp P * Real.exp P * Real.exp (modeProfileLog P + 3) := by
        gcongr
        exact modeRemovalMesh_inv_le_exp d hP hd
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hp : (P + K₀) ^ K₀ + (2 * P + modeProfileLog P + 3) + 1 ≤ (P + K) ^ K := by
    simpa [Polynomial.eval₂_pow, modeProfileLogPolynomial_eval] using hpoly P hP
  have hb0 : 0 ≤ (P + K₀) ^ K₀ := by positivity
  constructor
  · exact (add_le_exp_add_one hb0 (by linarith) hs he).trans (Real.exp_le_exp.mpr hp)
  · exact hr.trans (Real.exp_le_exp.mpr (by linarith))

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators

theorem affine_cube_residue_removal_at_error {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K] {m q : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (difference : Fin q → K → ℤ)
    (hlin : LinearIndependent ℝ (fun i k => (difference i k : ℝ)))
    {L C : ℝ} (hL : 0 ≤ L) (hC : 0 ≤ C)
    (hsite : ∀ (s : Finset (Fin q)) k, |((affineSite root difference s (some k) : ℤ) : ℝ)| ≤ L)
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (hbound : ∀ j d, d.degree ≤ j.val + 1 → ∀ a, |(frequency j d a : ℝ)| ≤ C)
    (hbad : ∃ i, ¬∃ M : (Finset (Fin q) → U i) →ₗ[ℝ] ℝ,
      ∀ P, Homogeneous (i.val + 1) P →
        affineModeLift (coefficientFunctional (fun d a => (frequency i d a : ℝ))) (map (U i).subtype P) =
          M (VectorPolynomial.siteEvaluation
            (fun s => affineSite (fun k => (root k : ℝ)) (fun r k => (difference r k : ℝ)) s) P))
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : I → ℕ) (hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (hS : 0 ≤ S) (hρ : 0 < ρ) (hε : 0 < ε)
    (hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ)
    (hsize : ∀ k, modeResidueSideThreshold m (Fintype.card (Option K × I))
      (cubeModePolynomialBudget q L) S ρ ε ≤ H k)
    (hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (hR : modeRemovalRankThreshold m (Fintype.card I) (Fintype.card (Option K × I))
      C (cubeModePolynomialBudget q L) S ρ ε ≤ R)
    (Q : MvPolynomial (Option K × I) ℝ) (hQ : Q.totalDegree ≤ 0)
    (test : Finset (Fin q) → (I → ℝ) → ℂ) (htest : ∀ t v, ‖test t v‖ ≤ 1)
    (residue : Option K × I → ℤ)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hwidth : ∀ z, ρ * H z.2 ≤ V z) :
    ∃ hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue stride)
        (residueProfileWidth stride V),
    ‖∑' z : Option K × I → ℤ, ((residueSmoothIndexPMF residue stride hs V hV hZ z).toReal : ℂ) *
      layeredModeTestedPhase
        (fun j => affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ))))
        p Q (fun s => affineSite root difference s) test (fun k j => (residueLatticeArray residue stride z (k, j) : ℝ))‖ ≤ ε := by
  classical
  let d := Fintype.card (Option K × I)
  let D := cubeModePolynomialBudget q L
  let T := modeRemovalShrink m d D ρ ε
  let B := finiteLayerBiasBudget m (modeRemovalBias m ε)
  have hD : 0 ≤ D := (cubeModePolynomialBudget_pos q hL).le
  have hT : 0 < T := lt_of_lt_of_le zero_lt_one (modeRemovalShrink_one_le m d hD hρ hε)
  have hB : 1 ≤ B := finiteLayerBiasBudget_one_le m (modeRemovalBias_pos m hε)
  have hside := modeRemovalSideThreshold_bounds m d hD hS hρ hε
  have hsizeBase k : modeRemovalSideThreshold m d D S ρ ε ≤ H k :=
    (modeResidueSideThreshold_bounds m d hD hS hρ hε).1.trans (hsize k)
  have hH k : 0 < H k := hside.1.trans_le (hsizeBase k)
  have hsize' k : (stride k : ℝ) * T * (B + 1) ≤ H k := by
    calc
      _ ≤ S * T * (B + 1) := by gcongr; exact hstride k
      _ ≤ H k := hside.2.1.trans (hsizeBase k)
  have hv z : 1 ≤ residueProfileWidth stride V z ∧
      1 / residueProfileWidth stride V z ≤ modeRemovalMesh d :=
    modeResidueWidth_mesh m d hD hS hρ hε (hs z.2) (hstride z.2) (hsize z.2) (hV z) (hwidth z)
  have hmass := shiftedSmoothProductMass_lower (residueProfileCenter residue stride)
    (residueProfileWidth stride V) (residueProfileWidth_pos stride V hs hV)
    (modeRemovalMesh_pos d).le (modeRemovalMesh_le_one d) (fun z => (hv z).2) (modeRemovalMesh_small d)
  have hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue stride)
      (residueProfileWidth stride V) :=
    (div_pos (Finset.prod_pos (fun z _ => residueProfileWidth_pos stride V hs hV z)) (by norm_num)).trans_le hmass
  refine ⟨hZ, ?_⟩
  have hout := affine_cube_residue_removal_of_widths U root difference hlin hL hC hsite frequency hbound hbad
    p hp hm stride hs (modeRemovalBias_pos m hε) hT hS hstride H hH hsize' hrank hR
    Q hQ test htest residue V hV hZ (fun z => (hv z).1) (modeRemovalMesh_pos d).le (modeRemovalMesh_le_one d)
    (fun z => (hv z).2) (modeRemovalMesh_small d) hρ (modeRemovalRadius_pos d hε).le hwidth
    (modeRemovalShrink_move m d hρ hε) (modeRemovalBeta_pos hε).le (fun i => modeRemovalBias_le i hε)
  exact hout.trans (modeRemovalError_bound d hε)

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

theorem affine_coefficient_amplitude_residue_removal_at_error {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    {C : ℝ} (hC : 0 ≤ C)
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (hbound : ∀ j d, d.degree ≤ j.val + 1 → ∀ a, |(frequency j d a : ℝ)| ≤ C)
    (hbad : ∃ i : Fin m, ∃ P, Homogeneous (i.val + 1) P ∧
      affineModeLift (coefficientFunctional (fun d a => (frequency i d a : ℝ)))
        (map (U i).subtype P) ≠ 0)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : I → ℕ) (hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (hS : 0 ≤ S) (hρ : 0 < ρ) (hε : 0 < ε)
    (hstride : ∀ k, (stride k : ℝ) ≤ S)
    (F : (Option K × I → ℝ) → ℂ) (hF : ∀ x, ‖F x‖ ≤ 1)
    {Lip : ℝ≥0} (hLip : LipschitzWith Lip F)
    (H : I → ℝ)
    (hsize : ∀ k, modeResidueSideThreshold m (Fintype.card (Option K × I))
      1 S ρ (modeAmplitudeAccuracy Lip ε) ≤ H k)
    (hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (hR : modeRemovalRankThreshold m (Fintype.card I) (Fintype.card (Option K × I))
      C 1 S ρ (modeAmplitudeAccuracy Lip ε) ≤ R)
    (residue : Option K × I → ℤ)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hwidth : ∀ z, ρ * H z.2 ≤ V z) :
    ∃ hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue stride)
        (residueProfileWidth stride V),
    ‖∑' z : Option K × I → ℤ, ((residueSmoothIndexPMF residue stride hs V hV hZ z).toReal : ℂ) *
      (F (fun t => (residueLatticeArray residue stride z t : ℝ) / V t) *
      layeredCoefficientCharacter
        (fun j => affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ))))
        p (fun k j => (residueLatticeArray residue stride z (k, j) : ℝ)))‖ ≤ ε := by
  classical
  let ε₀ := modeAmplitudeAccuracy (Lip : ℝ) ε
  have hε₀ : 0 < ε₀ := modeAmplitudeAccuracy_pos Lip.coe_nonneg hε
  let d := Fintype.card (Option K × I)
  let D : ℝ := 1
  let T := modeRemovalShrink m d D ρ ε₀
  let B := finiteLayerBiasBudget m (modeRemovalBias m ε₀)
  have hD : 0 ≤ D := zero_le_one
  have hT : 0 < T := lt_of_lt_of_le zero_lt_one (modeRemovalShrink_one_le m d hD hρ hε₀)
  have hB : 1 ≤ B := finiteLayerBiasBudget_one_le m (modeRemovalBias_pos m hε₀)
  have hside := modeRemovalSideThreshold_bounds m d hD hS hρ hε₀
  have hsizeBase k : modeRemovalSideThreshold m d D S ρ ε₀ ≤ H k :=
    (modeResidueSideThreshold_bounds m d hD hS hρ hε₀).1.trans (hsize k)
  have hH k : 0 < H k := hside.1.trans_le (hsizeBase k)
  have hsize' k : (stride k : ℝ) * T * (B + 1) ≤ H k := by
    calc
      _ ≤ S * T * (B + 1) := by gcongr; exact hstride k
      _ ≤ H k := hside.2.1.trans (hsizeBase k)
  have hv z : 1 ≤ residueProfileWidth stride V z ∧
      1 / residueProfileWidth stride V z ≤ modeRemovalMesh d :=
    modeResidueWidth_mesh m d hD hS hρ hε₀ (hs z.2) (hstride z.2) (hsize z.2) (hV z) (hwidth z)
  have hmass := shiftedSmoothProductMass_lower (residueProfileCenter residue stride)
    (residueProfileWidth stride V) (residueProfileWidth_pos stride V hs hV)
    (modeRemovalMesh_pos d).le (modeRemovalMesh_le_one d) (fun z => (hv z).2) (modeRemovalMesh_small d)
  have hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue stride)
      (residueProfileWidth stride V) :=
    (div_pos (Finset.prod_pos (fun z _ => residueProfileWidth_pos stride V hs hV z)) (by norm_num)).trans_le hmass
  refine ⟨hZ, ?_⟩
  have hout := affine_coefficient_residue_removal_of_widths_lipschitz_amplitude U hC frequency hbound hbad
    p hp hm stride hs (modeRemovalBias_pos m hε₀) hT hS hstride H hH hsize' hrank hR
    residue V hV hZ (fun z => (hv z).1) (modeRemovalMesh_pos d).le (modeRemovalMesh_le_one d)
    (fun z => (hv z).2) (modeRemovalMesh_small d) hρ (modeRemovalRadius_pos d hε₀).le hwidth
    (modeRemovalShrink_move m d hρ hε₀) (modeRemovalBeta_pos hε₀).le (fun i => modeRemovalBias_le i hε₀) F hF hLip
  exact hout.trans (modeAmplitudeError_bound d Lip.coe_nonneg hε)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators

theorem exists_affine_cube_residue_uniform_removal (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option K × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (difference : Fin q → K → ℤ)
    (_hlin : LinearIndependent ℝ (fun i k => (difference i k : ℝ)))
    {L C : ℝ} (_hL : 0 ≤ L) (_hC : 0 ≤ C) (_hLP : L ≤ Real.exp P) (_hCP : C ≤ Real.exp P)
    (_hsite : ∀ (s : Finset (Fin q)) k, |((affineSite root difference s (some k) : ℤ) : ℝ)| ≤ L)
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (_hbound : ∀ j d, d.degree ≤ j.val + 1 → ∀ a, |(frequency j d a : ℝ)| ≤ C)
    (_hbad : ∃ i, ¬∃ M : (Finset (Fin q) → U i) →ₗ[ℝ] ℝ,
      ∀ P, Homogeneous (i.val + 1) P →
        affineModeLift (coefficientFunctional (fun d a => (frequency i d a : ℝ))) (map (U i).subtype P) =
          M (VectorPolynomial.siteEvaluation
            (fun s => affineSite (fun k => (root k : ℝ)) (fun r k => (difference r k : ℝ)) s) P))
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hεP : 1 / ε ≤ Real.exp P)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ)
    (_hsize : ∀ k, Real.exp ((P + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((P + A) ^ A) ≤ R)
    (Q : MvPolynomial (Option K × I) ℝ) (_hQ : Q.totalDegree ≤ 0)
    (test : Finset (Fin q) → (I → ℝ) → ℂ) (_htest : ∀ t v, ‖test t v‖ ≤ 1)
    (residue : Option K × I → ℤ)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z)
    (_hwidth : ∀ z, ρ * H z.2 ≤ V z),
    ∃ hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue stride)
        (residueProfileWidth stride V),
    ‖∑' z : Option K × I → ℤ, ((residueSmoothIndexPMF residue stride _hs V hV hZ z).toReal : ℂ) *
      layeredModeTestedPhase
        (fun j => affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ))))
        p Q (fun s => affineSite root difference s) test (fun k j => (residueLatticeArray residue stride z (k, j) : ℝ))‖ ≤ ε := by
  obtain ⟨A, hA, hbudget⟩ := exists_cube_residue_threshold_exp_budget m q
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ P hP hn hd U root difference hlin L C hL hC hLP hCP
    hsite frequency hbound hbad p hp hm stride hs R S ρ ε hS hSP hρ hε hρP hεP
    hstride H hsize hrank hR Q hQ test htest residue V hV hwidth
  obtain ⟨hside, hrankBudget⟩ := hbudget (Fintype.card I) (Fintype.card (Option K × I))
    P C L S ρ ε hP hn hd hC hCP hL hLP hS hSP hρ hρP hε hεP
  exact affine_cube_residue_removal_at_error U root difference hlin hL hC hsite frequency hbound hbad
    p hp hm stride hs hS hρ hε hstride H (fun k => hside.trans (hsize k)) hrank
    (hrankBudget.trans hR) Q hQ test htest residue V hV hwidth

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators

theorem exists_affine_cube_ambient_residue_removal (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option K × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (difference : Fin q → K → ℤ)
    (_hlin : LinearIndependent ℝ (fun i k => (difference i k : ℝ)))
    {L C : ℝ} (_hL : 0 ≤ L) (_hC : 0 ≤ C) (_hLP : L ≤ Real.exp P) (_hCP : C ≤ Real.exp P)
    (_hsite : ∀ (s : Finset (Fin q)) k, |((affineSite root difference s (some k) : ℤ) : ℝ)| ≤ L)
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (_hbound : ∀ j d, d.degree ≤ j.val + 1 → ∀ a, |(frequency j d a : ℝ)| ≤ C)
    (_hbad : ∃ i, ¬∃ M : (Finset (Fin q) → U i) →ₗ[ℝ] ℝ,
      ∀ P, Homogeneous (i.val + 1) P →
        affineModeLift (coefficientFunctional (fun d a => (frequency i d a : ℝ))) (map (U i).subtype P) =
          M (VectorPolynomial.siteEvaluation
            (fun s => affineSite (fun k => (root k : ℝ)) (fun r k => (difference r k : ℝ)) s) P))
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hεP : 1 / ε ≤ Real.exp P)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ)
    (_hsize : ∀ k, Real.exp ((P + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((P + A) ^ A) ≤ R)
    (Q : MvPolynomial (Option K × I) ℝ) (_hQ : Q.totalDegree ≤ 0)
    (test : Finset (Fin q) → (I → ℝ) → ℂ) (_htest : ∀ t v, ‖test t v‖ ≤ 1)
    (residue : Option K × I → ℤ)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z)
    (_hwidth : ∀ z, ρ * H z.2 ≤ V z),
    ∃ hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue stride)
        (residueProfileWidth stride V),
    ‖∑' z : Option K × I → ℤ, ((residueSmoothPMF residue stride _hs V hV hZ z).toReal : ℂ) *
      layeredModeTestedPhase
        (fun j => affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ))))
        p Q (fun s => affineSite root difference s) test (fun k j => (z (k, j) : ℝ))‖ ≤ ε := by
  obtain ⟨A, hA, hremove⟩ := exists_affine_cube_residue_uniform_removal m q
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ P hP hn hd U root difference hlin L C hL hC hLP hCP
    hsite frequency hbound hbad p hp hm stride hs R S ρ ε hS hSP hρ hε hρP hεP
    hstride H hsize hrank hR Q hQ test htest residue V hV hwidth
  obtain ⟨hZ, hrem⟩ := hremove hP hn hd U root difference hlin hL hC hLP hCP
    hsite frequency hbound hbad p hp hm stride hs hS hSP hρ hε hρP hεP
    hstride H hsize hrank hR Q hQ test htest residue V hV hwidth
  refine ⟨hZ, ?_⟩
  rw [residueSmoothPMF_expectation]
  exact hrem

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators

theorem exists_affine_cube_congruence_removal (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option K × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (difference : Fin q → K → ℤ)
    (_hlin : LinearIndependent ℝ (fun i k => (difference i k : ℝ)))
    {L C : ℝ} (_hL : 0 ≤ L) (_hC : 0 ≤ C) (_hLP : L ≤ Real.exp P) (_hCP : C ≤ Real.exp P)
    (_hsite : ∀ (s : Finset (Fin q)) k, |((affineSite root difference s (some k) : ℤ) : ℝ)| ≤ L)
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (_hbound : ∀ j d, d.degree ≤ j.val + 1 → ∀ a, |(frequency j d a : ℝ)| ≤ C)
    (_hbad : ∃ i, ¬∃ M : (Finset (Fin q) → U i) →ₗ[ℝ] ℝ,
      ∀ P, Homogeneous (i.val + 1) P →
        affineModeLift (coefficientFunctional (fun d a => (frequency i d a : ℝ))) (map (U i).subtype P) =
          M (VectorPolynomial.siteEvaluation
            (fun s => affineSite (fun k => (root k : ℝ)) (fun r k => (difference r k : ℝ)) s) P))
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hεP : 1 / ε ≤ Real.exp P)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ)
    (_hsize : ∀ k, Real.exp ((P + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((P + A) ^ A) ≤ R)
    (Q : MvPolynomial (Option K × I) ℝ) (_hQ : Q.totalDegree ≤ 0)
    (test : Finset (Fin q) → (I → ℝ) → ℂ) (_htest : ∀ t v, ‖test t v‖ ≤ 1)
    (G : Finset (ColumnResiduePattern (Option K) I stride)) (_hG : G.Nonempty)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z)
    (_hwidth : ∀ z, ρ * H z.2 ≤ V z),
    ∃ hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x,
    ‖∑' z : Option K × I → ℤ, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) *
      layeredModeTestedPhase
        (fun j => affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ))))
        p Q (fun s => affineSite root difference s) test (fun k j => (z (k, j) : ℝ))‖ ≤ ε := by
  obtain ⟨A, hA, hremove⟩ := exists_affine_cube_ambient_residue_removal m q
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ P hP hn hd U root difference hlin L C hL hC hLP hCP
    hsite frequency hbound hbad p hp hm stride hs R S ρ ε hS hSP hρ hε hρP hεP
    hstride H hsize hrank hR Q hQ test htest G hG V hV hwidth
  have hh (r : G) := hremove hP hn hd U root difference hlin hL hC hLP hCP
    hsite frequency hbound hbad p hp hm stride hs hS hSP hρ hε hρP hεP
    hstride H hsize hrank hR Q hQ test htest (columnResidueRepresentative stride r.val) V hV hwidth
  choose hZ hrem using hh
  exact selectedResidueSmoothPMF_bound_of_cells stride hs G hG V hV hZ _ hrem

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial

def affineCubeModeFactors {K : Type*} [Fintype K] {m q : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (difference : Fin q → K → ℤ)
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ) : Prop :=
  ∀ j, ∃ M : (Finset (Fin q) → U j) →ₗ[ℝ] ℝ,
    ∀ P, Homogeneous (j.val + 1) P →
      affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ)))
        (map (U j).subtype P) = M (VectorPolynomial.siteEvaluation
          (fun s => affineSite (fun k => (root k : ℝ)) (fun r k => (difference r k : ℝ)) s) P)

theorem not_affineCubeModeFactors_iff {K : Type*} [Fintype K] {m q : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (difference : Fin q → K → ℤ)
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ) :
    ¬affineCubeModeFactors U root difference frequency ↔
      ∃ j, ¬∃ M : (Finset (Fin q) → U j) →ₗ[ℝ] ℝ,
        ∀ P, Homogeneous (j.val + 1) P →
          affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ)))
            (map (U j).subtype P) = M (VectorPolynomial.siteEvaluation
              (fun s => affineSite (fun k => (root k : ℝ)) (fun r k => (difference r k : ℝ)) s) P) := by
  classical
  simp only [affineCubeModeFactors, not_forall]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial

theorem affineCubeModeFactors_bounded {K : Type*} [Fintype K] {m q : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (difference : Fin q → K → ℤ)
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (hf : affineCubeModeFactors U root difference frequency) (j : Fin m) :
    ∃ M : (Finset (Fin q) → U j) →ₗ[ℝ] ℝ,
      ∀ p : VectorPolynomial K ℝ (U j), DegreeLE (1 : K → ℕ) (j.val + 1) p →
        coefficientFunctional (fun d a => (frequency j d a : ℝ)) (map (U j).subtype p) =
          M (VectorPolynomial.siteEvaluation (fun s k => ((affineSite root difference s (some k) : ℤ) : ℝ)) p) := by
  obtain ⟨M, hM⟩ := hf j
  refine ⟨M, homogeneous_factorization_to_bounded_site (U j) (j.val + 1)
    (fun s k => ((affineSite root difference s (some k) : ℤ) : ℝ))
    (fun d a => (frequency j d a : ℝ)) M ?_⟩
  have hsite : (fun s (k : Option K) => k.elim (1 : ℝ)
      (fun t => ((affineSite root difference s (some t) : ℤ) : ℝ))) =
      (fun s => affineSite (fun k => (root k : ℝ)) (fun i k => (difference i k : ℝ)) s) := by
    funext s k
    cases k <;> simp [affineSite, Int.cast_sum]
  simpa only [hsite] using hM

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial Polynomial
open scoped BigOperators Classical

end Erdos3.BooleanCubeKernel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineCoefficientAmplitudeCongruenceRemoval
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

theorem exists_affine_coefficient_amplitude_residue_uniform_removal (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option K × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    {C : ℝ} (_hC : 0 ≤ C) (_hCP : C ≤ Real.exp P)
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (_hbound : ∀ j d, d.degree ≤ j.val + 1 → ∀ a, |(frequency j d a : ℝ)| ≤ C)
    (_hbad : ∃ i : Fin m, ∃ P, Homogeneous (i.val + 1) P ∧
      affineModeLift (coefficientFunctional (fun d a => (frequency i d a : ℝ)))
        (map (U i).subtype P) ≠ 0)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hεP : 1 / ε ≤ Real.exp P)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ)
    (_hsize : ∀ k, Real.exp ((P + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((P + A) ^ A) ≤ R)
    (residue : Option K × I → ℤ)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z)
    (_hwidth : ∀ z, ρ * H z.2 ≤ V z)
    (F : (Option K × I → ℝ) → ℂ) (_hF : ∀ x, ‖F x‖ ≤ 1)
    {Lip : ℝ≥0} (_hLip : LipschitzWith Lip F) (_hLipP : (Lip : ℝ) ≤ Real.exp P),
    ∃ hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue stride)
        (residueProfileWidth stride V),
    ‖∑' z : Option K × I → ℤ, ((residueSmoothIndexPMF residue stride _hs V hV hZ z).toReal : ℂ) *
      (F (fun t => (residueLatticeArray residue stride z t : ℝ) / V t) *
      layeredCoefficientCharacter
        (fun j => affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ))))
        p (fun k j => (residueLatticeArray residue stride z (k, j) : ℝ)))‖ ≤ ε := by
  obtain ⟨A₀, _, hbudget⟩ := exists_mode_residue_threshold_exp_budget m
  obtain ⟨A, hA, habsorb⟩ := exists_natPolynomial_eval_budget
    ((2 * Polynomial.X + 2 + Polynomial.C A₀) ^ A₀)
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ P hP hn hd U C hC hCP frequency hbound hbad p hp hm stride hs R S ρ ε hS hSP hρ hε hρP hεP
    hstride H hsize hrank hR residue V hV hwidth F hF Lip hLip hLipP
  let P' := 2 * P + 2
  have hPP : P ≤ P' := by dsimp [P']; linarith
  have hP' : 0 ≤ P' := hP.trans hPP
  have hExp := Real.exp_le_exp.mpr hPP
  have hacc := modeAmplitudeAccuracy_pos Lip.coe_nonneg hε
  have haccexp : 1 / modeAmplitudeAccuracy Lip ε ≤ Real.exp P' :=
    modeAmplitudeAccuracy_inv_le_exp hP Lip.coe_nonneg hLipP hε hεP
  have hcut : (P' + A₀) ^ A₀ ≤ (P + A) ^ A := by
    simpa [P', Polynomial.eval₂_pow] using habsorb P hP
  obtain ⟨hside, hrankBudget⟩ := hbudget (Fintype.card I) (Fintype.card (Option K × I))
    P' C 1 S ρ (modeAmplitudeAccuracy Lip ε) hP' (hn.trans hPP) (hd.trans hPP)
    hC (hCP.trans hExp) zero_le_one (Real.one_le_exp hP') hS (hSP.trans hExp)
    hρ (hρP.trans hExp) hacc haccexp
  exact affine_coefficient_amplitude_residue_removal_at_error U hC frequency hbound hbad
    p hp hm stride hs hS hρ hε hstride F hF hLip H
    (fun k => hside.trans ((Real.exp_le_exp.mpr hcut).trans (hsize k))) hrank
    (hrankBudget.trans ((Real.exp_le_exp.mpr hcut).trans hR)) residue V hV hwidth

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

theorem exists_affine_coefficient_amplitude_ambient_residue_removal (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option K × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    {C : ℝ} (_hC : 0 ≤ C) (_hCP : C ≤ Real.exp P)
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (_hbound : ∀ j d, d.degree ≤ j.val + 1 → ∀ a, |(frequency j d a : ℝ)| ≤ C)
    (_hbad : ∃ i : Fin m, ∃ P, Homogeneous (i.val + 1) P ∧
      affineModeLift (coefficientFunctional (fun d a => (frequency i d a : ℝ)))
        (map (U i).subtype P) ≠ 0)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hεP : 1 / ε ≤ Real.exp P)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ)
    (_hsize : ∀ k, Real.exp ((P + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((P + A) ^ A) ≤ R)
    (residue : Option K × I → ℤ)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z)
    (_hwidth : ∀ z, ρ * H z.2 ≤ V z)
    (F : (Option K × I → ℝ) → ℂ) (_hF : ∀ x, ‖F x‖ ≤ 1)
    {Lip : ℝ≥0} (_hLip : LipschitzWith Lip F) (_hLipP : (Lip : ℝ) ≤ Real.exp P),
    ∃ hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue stride)
        (residueProfileWidth stride V),
    ‖∑' z : Option K × I → ℤ, ((residueSmoothPMF residue stride _hs V hV hZ z).toReal : ℂ) *
      (F (fun t => (z t : ℝ) / V t) *
      layeredCoefficientCharacter
        (fun j => affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ))))
        p (fun k j => (z (k, j) : ℝ)))‖ ≤ ε := by
  obtain ⟨A, hA, hremove⟩ := exists_affine_coefficient_amplitude_residue_uniform_removal m
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ P hP hn hd U C hC hCP frequency hbound hbad p hp hm stride hs R S ρ ε hS hSP hρ hε hρP hεP
    hstride H hsize hrank hR residue V hV hwidth F hF Lip hLip hLipP
  obtain ⟨hZ, hrem⟩ := hremove hP hn hd U hC hCP frequency hbound hbad p hp hm stride hs hS hSP hρ hε hρP hεP
    hstride H hsize hrank hR residue V hV hwidth F hF hLip hLipP
  refine ⟨hZ, ?_⟩
  rw [residueSmoothPMF_expectation]
  exact hrem

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

theorem exists_affine_coefficient_amplitude_congruence_removal (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option K × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    {C : ℝ} (_hC : 0 ≤ C) (_hCP : C ≤ Real.exp P)
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (_hbound : ∀ j d, d.degree ≤ j.val + 1 → ∀ a, |(frequency j d a : ℝ)| ≤ C)
    (_hbad : ∃ i : Fin m, ∃ P, Homogeneous (i.val + 1) P ∧
      affineModeLift (coefficientFunctional (fun d a => (frequency i d a : ℝ)))
        (map (U i).subtype P) ≠ 0)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hεP : 1 / ε ≤ Real.exp P)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ)
    (_hsize : ∀ k, Real.exp ((P + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((P + A) ^ A) ≤ R)
    (G : Finset (ColumnResiduePattern (Option K) I stride)) (_hG : G.Nonempty)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z)
    (_hwidth : ∀ z, ρ * H z.2 ≤ V z)
    (F : (Option K × I → ℝ) → ℂ) (_hF : ∀ x, ‖F x‖ ≤ 1)
    {Lip : ℝ≥0} (_hLip : LipschitzWith Lip F) (_hLipP : (Lip : ℝ) ≤ Real.exp P),
    ∃ hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x,
    ‖∑' z : Option K × I → ℤ, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) *
      (F (fun t => (z t : ℝ) / V t) *
      layeredCoefficientCharacter
        (fun j => affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ))))
        p (fun k j => (z (k, j) : ℝ)))‖ ≤ ε := by
  obtain ⟨A, hA, hremove⟩ := exists_affine_coefficient_amplitude_ambient_residue_removal m
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ P hP hn hd U C hC hCP frequency hbound hbad p hp hm stride hs R S ρ ε hS hSP hρ hε hρP hεP
    hstride H hsize hrank hR G hG V hV hwidth F hF Lip hLip hLipP
  have hh (r : G) := hremove hP hn hd U hC hCP frequency hbound hbad p hp hm stride hs hS hSP hρ hε hρP hεP
    hstride H hsize hrank hR (columnResidueRepresentative stride r.val) V hV hwidth F hF hLip hLipP
  choose hZ hrem using hh
  exact selectedResidueSmoothPMF_bound_of_cells stride hs G hG V hV hZ _ hrem

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineCoefficientCongruenceRemoval
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem affine_coefficient_residue_removal_at_error {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    {C : ℝ} (hC : 0 ≤ C)
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (hbound : ∀ j d, d.degree ≤ j.val + 1 → ∀ a, |(frequency j d a : ℝ)| ≤ C)
    (hbad : ∃ i : Fin m, ∃ P, Homogeneous (i.val + 1) P ∧
      affineModeLift (coefficientFunctional (fun d a => (frequency i d a : ℝ)))
        (map (U i).subtype P) ≠ 0)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : I → ℕ) (hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (hS : 0 ≤ S) (hρ : 0 < ρ) (hε : 0 < ε)
    (hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ)
    (hsize : ∀ k, modeResidueSideThreshold m (Fintype.card (Option K × I))
      1 S ρ ε ≤ H k)
    (hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (hR : modeRemovalRankThreshold m (Fintype.card I) (Fintype.card (Option K × I))
      C 1 S ρ ε ≤ R)
    (residue : Option K × I → ℤ)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hwidth : ∀ z, ρ * H z.2 ≤ V z) :
    ∃ hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue stride)
        (residueProfileWidth stride V),
    ‖∑' z : Option K × I → ℤ, ((residueSmoothIndexPMF residue stride hs V hV hZ z).toReal : ℂ) *
      layeredCoefficientCharacter
        (fun j => affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ))))
        p (fun k j => (residueLatticeArray residue stride z (k, j) : ℝ))‖ ≤ ε := by
  classical
  let d := Fintype.card (Option K × I)
  let D : ℝ := 1
  let T := modeRemovalShrink m d D ρ ε
  let B := finiteLayerBiasBudget m (modeRemovalBias m ε)
  have hD : 0 ≤ D := zero_le_one
  have hT : 0 < T := lt_of_lt_of_le zero_lt_one (modeRemovalShrink_one_le m d hD hρ hε)
  have hB : 1 ≤ B := finiteLayerBiasBudget_one_le m (modeRemovalBias_pos m hε)
  have hside := modeRemovalSideThreshold_bounds m d hD hS hρ hε
  have hsizeBase k : modeRemovalSideThreshold m d D S ρ ε ≤ H k :=
    (modeResidueSideThreshold_bounds m d hD hS hρ hε).1.trans (hsize k)
  have hH k : 0 < H k := hside.1.trans_le (hsizeBase k)
  have hsize' k : (stride k : ℝ) * T * (B + 1) ≤ H k := by
    calc
      _ ≤ S * T * (B + 1) := by gcongr; exact hstride k
      _ ≤ H k := hside.2.1.trans (hsizeBase k)
  have hv z : 1 ≤ residueProfileWidth stride V z ∧
      1 / residueProfileWidth stride V z ≤ modeRemovalMesh d :=
    modeResidueWidth_mesh m d hD hS hρ hε (hs z.2) (hstride z.2) (hsize z.2) (hV z) (hwidth z)
  have hmass := shiftedSmoothProductMass_lower (residueProfileCenter residue stride)
    (residueProfileWidth stride V) (residueProfileWidth_pos stride V hs hV)
    (modeRemovalMesh_pos d).le (modeRemovalMesh_le_one d) (fun z => (hv z).2) (modeRemovalMesh_small d)
  have hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue stride)
      (residueProfileWidth stride V) :=
    (div_pos (Finset.prod_pos (fun z _ => residueProfileWidth_pos stride V hs hV z)) (by norm_num)).trans_le hmass
  refine ⟨hZ, ?_⟩
  have hout := affine_coefficient_residue_removal_of_widths U hC frequency hbound hbad
    p hp hm stride hs (modeRemovalBias_pos m hε) hT hS hstride H hH hsize' hrank hR
    residue V hV hZ (fun z => (hv z).1) (modeRemovalMesh_pos d).le (modeRemovalMesh_le_one d)
    (fun z => (hv z).2) (modeRemovalMesh_small d) hρ (modeRemovalRadius_pos d hε).le hwidth
    (modeRemovalShrink_move m d hρ hε) (modeRemovalBeta_pos hε).le (fun i => modeRemovalBias_le i hε)
  exact hout.trans (modeRemovalError_bound d hε)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem exists_affine_coefficient_residue_uniform_removal (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option K × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    {C : ℝ} (_hC : 0 ≤ C) (_hCP : C ≤ Real.exp P)
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (_hbound : ∀ j d, d.degree ≤ j.val + 1 → ∀ a, |(frequency j d a : ℝ)| ≤ C)
    (_hbad : ∃ i : Fin m, ∃ P, Homogeneous (i.val + 1) P ∧
      affineModeLift (coefficientFunctional (fun d a => (frequency i d a : ℝ)))
        (map (U i).subtype P) ≠ 0)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hεP : 1 / ε ≤ Real.exp P)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ)
    (_hsize : ∀ k, Real.exp ((P + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((P + A) ^ A) ≤ R)
    (residue : Option K × I → ℤ)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z)
    (_hwidth : ∀ z, ρ * H z.2 ≤ V z),
    ∃ hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue stride)
        (residueProfileWidth stride V),
    ‖∑' z : Option K × I → ℤ, ((residueSmoothIndexPMF residue stride _hs V hV hZ z).toReal : ℂ) *
      layeredCoefficientCharacter
        (fun j => affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ))))
        p (fun k j => (residueLatticeArray residue stride z (k, j) : ℝ))‖ ≤ ε := by
  obtain ⟨A, hA, hbudget⟩ := exists_mode_residue_threshold_exp_budget m
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ P hP hn hd U C hC hCP frequency hbound hbad p hp hm stride hs R S ρ ε hS hSP hρ hε hρP hεP
    hstride H hsize hrank hR residue V hV hwidth
  obtain ⟨hside, hrankBudget⟩ := hbudget (Fintype.card I) (Fintype.card (Option K × I))
    P C 1 S ρ ε hP hn hd hC hCP zero_le_one (Real.one_le_exp hP) hS hSP hρ hρP hε hεP
  exact affine_coefficient_residue_removal_at_error U hC frequency hbound hbad
    p hp hm stride hs hS hρ hε hstride H (fun k => hside.trans (hsize k)) hrank
    (hrankBudget.trans hR) residue V hV hwidth

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem exists_affine_coefficient_ambient_residue_removal (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option K × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    {C : ℝ} (_hC : 0 ≤ C) (_hCP : C ≤ Real.exp P)
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (_hbound : ∀ j d, d.degree ≤ j.val + 1 → ∀ a, |(frequency j d a : ℝ)| ≤ C)
    (_hbad : ∃ i : Fin m, ∃ P, Homogeneous (i.val + 1) P ∧
      affineModeLift (coefficientFunctional (fun d a => (frequency i d a : ℝ)))
        (map (U i).subtype P) ≠ 0)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hεP : 1 / ε ≤ Real.exp P)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ)
    (_hsize : ∀ k, Real.exp ((P + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((P + A) ^ A) ≤ R)
    (residue : Option K × I → ℤ)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z)
    (_hwidth : ∀ z, ρ * H z.2 ≤ V z),
    ∃ hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue stride)
        (residueProfileWidth stride V),
    ‖∑' z : Option K × I → ℤ, ((residueSmoothPMF residue stride _hs V hV hZ z).toReal : ℂ) *
      layeredCoefficientCharacter
        (fun j => affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ))))
        p (fun k j => (z (k, j) : ℝ))‖ ≤ ε := by
  obtain ⟨A, hA, hremove⟩ := exists_affine_coefficient_residue_uniform_removal m
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ P hP hn hd U C hC hCP frequency hbound hbad p hp hm stride hs R S ρ ε hS hSP hρ hε hρP hεP
    hstride H hsize hrank hR residue V hV hwidth
  obtain ⟨hZ, hrem⟩ := hremove hP hn hd U hC hCP frequency hbound hbad p hp hm stride hs hS hSP hρ hε hρP hεP
    hstride H hsize hrank hR residue V hV hwidth
  refine ⟨hZ, ?_⟩
  rw [residueSmoothPMF_expectation]
  exact hrem

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem exists_affine_coefficient_congruence_removal (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option K × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    {C : ℝ} (_hC : 0 ≤ C) (_hCP : C ≤ Real.exp P)
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (_hbound : ∀ j d, d.degree ≤ j.val + 1 → ∀ a, |(frequency j d a : ℝ)| ≤ C)
    (_hbad : ∃ i : Fin m, ∃ P, Homogeneous (i.val + 1) P ∧
      affineModeLift (coefficientFunctional (fun d a => (frequency i d a : ℝ)))
        (map (U i).subtype P) ≠ 0)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hεP : 1 / ε ≤ Real.exp P)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ)
    (_hsize : ∀ k, Real.exp ((P + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((P + A) ^ A) ≤ R)
    (G : Finset (ColumnResiduePattern (Option K) I stride)) (_hG : G.Nonempty)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z)
    (_hwidth : ∀ z, ρ * H z.2 ≤ V z),
    ∃ hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x,
    ‖∑' z : Option K × I → ℤ, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) *
      layeredCoefficientCharacter
        (fun j => affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ))))
        p (fun k j => (z (k, j) : ℝ))‖ ≤ ε := by
  obtain ⟨A, hA, hremove⟩ := exists_affine_coefficient_ambient_residue_removal m
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ P hP hn hd U C hC hCP frequency hbound hbad p hp hm stride hs R S ρ ε hS hSP hρ hε hρP hεP
    hstride H hsize hrank hR G hG V hV hwidth
  have hh (r : G) := hremove hP hn hd U hC hCP frequency hbound hbad p hp hm stride hs hS hSP hρ hε hρP hεP
    hstride H hsize hrank hR (columnResidueRepresentative stride r.val) V hV hwidth
  choose hZ hrem using hh
  exact selectedResidueSmoothPMF_bound_of_cells stride hs G hG V hV hZ _ hrem

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.AnchoredCoefficientFourierNormalization
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem selectedResidueSmoothPMF_weighted_fourier_normalization {K I J : Type*}
    [Fintype K] [Fintype I] [Fintype J]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (w : (K × I → ℤ) → ℂ) (c : J → ℂ) (u : J → (K × I → ℤ) → ℂ)
    (keep : J → Prop) [DecidablePred keep] {C τ : ℝ}
    (hc : (∑ j, ‖c j‖) ≤ C) (hτ : 0 ≤ τ)
    (hkeep : ∀ j, keep j → ∀ x, u j x = 1)
    (hdiscard : ∀ j, ¬keep j →
      ‖∑' x, ((selectedResidueSmoothPMF modulus G V hV hZ x).toReal : ℂ) *
        (w x * u j x)‖ ≤ τ) :
    ‖(∑' x, ((selectedResidueSmoothPMF modulus G V hV hZ x).toReal : ℂ) *
        (w x * ∑ j, c j * u j x)) -
      (∑' x, ((selectedResidueSmoothPMF modulus G V hV hZ x).toReal : ℂ) * w x) *
        (∑ j, if keep j then c j else 0)‖ ≤ C * τ := by
  have hproject := selectedResidueSmoothPMF_discard_error modulus G V hV hZ
    w c u keep hc hτ hdiscard
  have heq (x : K × I → ℤ) :
      (∑ j, if keep j then c j * u j x else 0) =
        ∑ j, if keep j then c j else 0 := by
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : keep j
    · simp only [hj, ite_true, hkeep j hj x, mul_one]
    · simp only [hj, ite_false]
  simp_rw [heq, ← mul_assoc] at hproject
  rw [tsum_mul_right] at hproject
  simpa only [mul_assoc] using hproject

end Erdos3

end

section

namespace Erdos3

open Polynomial

noncomputable def fourierModeError (B ε : ℝ) : ℝ := ε / (B + 1)

theorem fourierModeError_pos {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) :
    0 < fourierModeError B ε := div_pos hε (by linarith)

theorem fourierModeError_cost_le {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) :
    B * fourierModeError B ε ≤ ε := by
  have h := mul_le_mul_of_nonneg_right (show B ≤ B + 1 by linarith) (fourierModeError_pos hB hε).le
  have he : (B + 1) * fourierModeError B ε = ε := by
    unfold fourierModeError
    field_simp
  exact h.trans_eq he

theorem fourierModeError_inv_le_exp {P B ε : ℝ} (hP : 0 ≤ P) (_hB : 0 ≤ B)
    (hBP : B ≤ Real.exp P) (hε : 0 < ε) (hεP : 1 / ε ≤ Real.exp P) :
    1 / fourierModeError B ε ≤ Real.exp (2 * P + 2) := by
  have hb : B + 1 ≤ Real.exp (P + 1) := by
    simpa only [add_comm B 1] using one_add_le_exp_succ hP hBP
  rw [fourierModeError, one_div, inv_div]
  calc
    _ = (B + 1) * (1 / ε) := by ring
    _ ≤ Real.exp (P + 1) * Real.exp P :=
      mul_le_mul hb hεP (by positivity) (Real.exp_nonneg _)
    _ = Real.exp (2 * P + 1) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

theorem exists_fourier_uniform_budget (A B : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ P : ℝ, 0 ≤ P →
      Real.exp ((2 * P + 2 + A) ^ A) ≤ Real.exp ((P + C) ^ C) ∧
      Real.exp ((2 * P + 2 + B) ^ B) ≤ Real.exp ((P + C) ^ C) := by
  obtain ⟨C, hC, hp⟩ := exists_natPolynomial_eval_budget
    (((2 * X + 2 + Polynomial.C A) ^ A) + ((2 * X + 2 + Polynomial.C B) ^ B))
  refine ⟨C, hC, ?_⟩
  intro P hP
  have hh : (2 * P + 2 + A) ^ A + (2 * P + 2 + B) ^ B ≤ (P + C) ^ C := by
    simpa [Polynomial.eval₂_pow] using hp P hP
  have ha : 0 ≤ (2 * P + 2 + A) ^ A := by positivity
  have hb : 0 ≤ (2 * P + 2 + B) ^ B := by positivity
  exact ⟨Real.exp_le_exp.mpr (by linarith), Real.exp_le_exp.mpr (by linarith)⟩

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

theorem exists_affine_coefficient_amplitude_fourier_normalization (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] {F : Type*} [Fintype F]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option K × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    {C : ℝ} (_hC : 0 ≤ C) (_hCP : C ≤ Real.exp P)
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ)
    (_hbound : ∀ a j d, d.degree ≤ j.val + 1 → ∀ t, |(frequency a j d t : ℝ)| ≤ C)
    (c : F → ℂ) {B : ℝ} (_hB : 0 ≤ B) (_hBP : B ≤ Real.exp P)
    (_hcoefficients : (∑ a, ‖c a‖) ≤ B)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hεP : 1 / ε ≤ Real.exp P)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ) (_hsize : ∀ k, Real.exp ((P + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((P + A) ^ A) ≤ R)
    (G : Finset (ColumnResiduePattern (Option K) I stride)) (_hG : G.Nonempty)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z) (_hwidth : ∀ z, ρ * H z.2 ≤ V z)
    (amplitude : (Option K × I → ℝ) → ℂ) (_hamp : ∀ x, ‖amplitude x‖ ≤ 1)
    {Lip : ℝ≥0} (_hLip : LipschitzWith Lip amplitude) (_hLipP : (Lip : ℝ) ≤ Real.exp P),
    ∃ hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x,
    ‖(∑' z : Option K × I → ℤ, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) *
        (amplitude (fun t => (z t : ℝ) / V t) * ∑ a, c a * layeredCoefficientCharacter
          (fun j => affineModeLift (coefficientFunctional (fun d t => (frequency a j d t : ℝ))))
          p (fun k j => (z (k, j) : ℝ)))) -
      (∑' z : Option K × I → ℤ, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) *
        amplitude (fun t => (z t : ℝ) / V t)) *
      (∑ a, if affineCoefficientModeTrivial U (frequency a) then c a else 0)‖ ≤ ε := by
  classical
  obtain ⟨A₀, _, hremove⟩ := exists_affine_coefficient_amplitude_congruence_removal m
  obtain ⟨A₁, _, hthreshold⟩ := exists_mode_residue_threshold_exp_budget m
  obtain ⟨A, hA, hbudget⟩ := exists_fourier_uniform_budget A₀ A₁
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ F _ P hP hn hd U C hC hCP frequency hbound c B hB hBP hcoefficients
    p hp hm stride hs R S ρ ε hS hSP hρ hε hρP hεP hstride H hsize hrank hR G hG V hV hwidth amplitude hamp Lip hLip hLipP
  let P' := 2 * P + 2
  let δ := fourierModeError B ε
  have hPP : P ≤ P' := by dsimp [P']; linarith
  have hEP : Real.exp P ≤ Real.exp P' := Real.exp_le_exp.mpr hPP
  have hδ : 0 < δ := fourierModeError_pos hB hε
  have hδP : 1 / δ ≤ Real.exp P' := fourierModeError_inv_le_exp hP hB hBP hε hεP
  obtain ⟨hb₀, hb₁⟩ := hbudget P hP
  obtain ⟨hside, _⟩ := hthreshold (Fintype.card I) (Fintype.card (Option K × I))
    P' C 1 S ρ δ (hP.trans hPP) (hn.trans hPP) (hd.trans hPP) hC (hCP.trans hEP)
    zero_le_one (Real.one_le_exp (hP.trans hPP)) hS (hSP.trans hEP) hρ (hρP.trans hEP) hδ hδP
  have hZ := selectedResidueSmoothWeight_pos_of_threshold m zero_le_one
    hS hρ hδ stride hs hstride H (fun j => hside.trans (hb₁.trans (hsize j))) G hG V hV hwidth
  refine ⟨hZ, ?_⟩
  have hdiscard (a : F) (hbad : ¬affineCoefficientModeTrivial U (frequency a)) :
      ‖∑' z : Option K × I → ℤ, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) *
        (amplitude (fun t => (z t : ℝ) / V t) * layeredCoefficientCharacter
          (fun j => affineModeLift (coefficientFunctional (fun d t => (frequency a j d t : ℝ))))
          p (fun k j => (z (k, j) : ℝ)))‖ ≤ δ := by
    obtain ⟨_, hr⟩ := hremove (hP.trans hPP) (hn.trans hPP) (hd.trans hPP)
      U hC (hCP.trans hEP) (frequency a) (hbound a)
      ((not_affineCoefficientModeTrivial_iff U (frequency a)).mp hbad)
      p hp hm stride hs hS (hSP.trans hEP) hρ hδ (hρP.trans hEP) hδP hstride
      H (fun j => hb₀.trans (hsize j)) hrank (hb₀.trans hR) G hG V hV hwidth
      amplitude hamp hLip (hLipP.trans hEP)
    exact hr
  have hproj := selectedResidueSmoothPMF_weighted_fourier_normalization stride G V hV hZ
    (fun z => amplitude (fun t => (z t : ℝ) / V t)) c
    (fun a z => layeredCoefficientCharacter
      (fun j => affineModeLift (coefficientFunctional (fun d t => (frequency a j d t : ℝ))))
      p (fun k j => (z (k, j) : ℝ)))
    (fun a => affineCoefficientModeTrivial U (frequency a)) hcoefficients hδ.le
    (fun a ha z => layeredCoefficientCharacter_eq_one_of_trivial U (frequency a) ha p hp hm
      (fun k j => (z (k, j) : ℝ))) hdiscard
  exact hproj.trans (fourierModeError_cost_le hB hε)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

theorem exists_affine_coefficient_fourier_normalization (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] {F : Type*} [Fintype F]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option K × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    {C : ℝ} (_hC : 0 ≤ C) (_hCP : C ≤ Real.exp P)
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ)
    (_hbound : ∀ a j d, d.degree ≤ j.val + 1 → ∀ t, |(frequency a j d t : ℝ)| ≤ C)
    (c : F → ℂ) {B : ℝ} (_hB : 0 ≤ B) (_hBP : B ≤ Real.exp P)
    (_hcoefficients : (∑ a, ‖c a‖) ≤ B)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hεP : 1 / ε ≤ Real.exp P)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ) (_hsize : ∀ k, Real.exp ((P + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((P + A) ^ A) ≤ R)
    (G : Finset (ColumnResiduePattern (Option K) I stride)) (_hG : G.Nonempty)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z) (_hwidth : ∀ z, ρ * H z.2 ≤ V z),
    ∃ hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x,
    ‖(∑' z : Option K × I → ℤ, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) *
        (∑ a, c a * layeredCoefficientCharacter
          (fun j => affineModeLift (coefficientFunctional (fun d t => (frequency a j d t : ℝ))))
          p (fun k j => (z (k, j) : ℝ)))) -
      (∑ a, if affineCoefficientModeTrivial U (frequency a) then c a else 0)‖ ≤ ε := by
  classical
  obtain ⟨A₀, _, hremove⟩ := exists_affine_coefficient_congruence_removal m
  obtain ⟨A₁, _, hthreshold⟩ := exists_mode_residue_threshold_exp_budget m
  obtain ⟨A, hA, hbudget⟩ := exists_fourier_uniform_budget A₀ A₁
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ F _ P hP hn hd U C hC hCP frequency hbound c B hB hBP hcoefficients
    p hp hm stride hs R S ρ ε hS hSP hρ hε hρP hεP hstride H hsize hrank hR G hG V hV hwidth
  let P' := 2 * P + 2
  let δ := fourierModeError B ε
  have hPP : P ≤ P' := by dsimp [P']; linarith
  have hEP : Real.exp P ≤ Real.exp P' := Real.exp_le_exp.mpr hPP
  have hδ : 0 < δ := fourierModeError_pos hB hε
  have hδP : 1 / δ ≤ Real.exp P' := fourierModeError_inv_le_exp hP hB hBP hε hεP
  obtain ⟨hb₀, hb₁⟩ := hbudget P hP
  obtain ⟨hside, _⟩ := hthreshold (Fintype.card I) (Fintype.card (Option K × I))
    P' C 1 S ρ δ (hP.trans hPP) (hn.trans hPP) (hd.trans hPP) hC (hCP.trans hEP)
    zero_le_one (Real.one_le_exp (hP.trans hPP)) hS (hSP.trans hEP) hρ (hρP.trans hEP) hδ hδP
  have hZ := selectedResidueSmoothWeight_pos_of_threshold m zero_le_one
    hS hρ hδ stride hs hstride H (fun j => hside.trans (hb₁.trans (hsize j))) G hG V hV hwidth
  refine ⟨hZ, ?_⟩
  have hdiscard (a : F) (hbad : ¬affineCoefficientModeTrivial U (frequency a)) :
      ‖∑' z : Option K × I → ℤ, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) *
        ((1 : ℂ) * layeredCoefficientCharacter
          (fun j => affineModeLift (coefficientFunctional (fun d t => (frequency a j d t : ℝ))))
          p (fun k j => (z (k, j) : ℝ)))‖ ≤ δ := by
    obtain ⟨_, hr⟩ := hremove (hP.trans hPP) (hn.trans hPP) (hd.trans hPP)
      U hC (hCP.trans hEP) (frequency a) (hbound a)
      ((not_affineCoefficientModeTrivial_iff U (frequency a)).mp hbad)
      p hp hm stride hs hS (hSP.trans hEP) hρ hδ (hρP.trans hEP) hδP hstride
      H (fun j => hb₀.trans (hsize j)) hrank (hb₀.trans hR) G hG V hV hwidth
    simpa only [one_mul] using hr
  have hproj := selectedResidueSmoothPMF_discard_error stride G V hV hZ (fun _ => 1) c
    (fun a z => layeredCoefficientCharacter
      (fun j => affineModeLift (coefficientFunctional (fun d t => (frequency a j d t : ℝ))))
      p (fun k j => (z (k, j) : ℝ)))
    (fun a => affineCoefficientModeTrivial U (frequency a)) hcoefficients hδ.le hdiscard
  have hkeep (b : Option K → I → ℝ) :
      (∑ a, if affineCoefficientModeTrivial U (frequency a) then
        c a * layeredCoefficientCharacter
          (fun j => affineModeLift (coefficientFunctional (fun d t => (frequency a j d t : ℝ)))) p b
        else 0) = ∑ a, if affineCoefficientModeTrivial U (frequency a) then c a else 0 := by
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : affineCoefficientModeTrivial U (frequency a)
    · simp only [ha, ite_true, layeredCoefficientCharacter_eq_one_of_trivial U (frequency a) ha p hp hm b,
        mul_one]
    · simp only [ha, ite_false]
  simp only [one_mul, hkeep, selectedResidueSmoothPMF_const] at hproj
  exact hproj.trans (fourierModeError_cost_le hB hε)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineCoefficientCoverTilt
namespace OAI

section

namespace Erdos3

open Polynomial

theorem exists_integer_cover_threshold (A₀ : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ P : ℝ, 0 ≤ P →
      Real.exp ((P + A₀) ^ A₀) ≤ Real.exp ((P + A) ^ A) ∧
      Real.exp P * Real.exp ((P + A₀) ^ A₀) ≤ Real.exp ((P + A) ^ A) := by
  obtain ⟨A, hA, hpoly⟩ := exists_natPolynomial_eval_budget (X + (X + C A₀) ^ A₀ + 1)
  refine ⟨A, hA, ?_⟩
  intro P hP
  have he : P + (P + A₀) ^ A₀ + 1 ≤ (P + A) ^ A := by
    simpa [Polynomial.eval₂_pow] using hpoly P hP
  constructor
  · apply Real.exp_le_exp.mpr
    linarith
  · rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

theorem affineSampleCoefficientArray_smul {I K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ)) (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (r : ℝ) (b : Option K → I → ℝ) :
    affineSampleCoefficientArray U (fun j => r • p j)
      (fun j => coefficients_smul_mem (U j) (p j) (hm j) r) b =
      r • affineSampleCoefficientArray U p hm b := by
  funext s
  apply Subtype.ext
  change (affineSampleCoefficientArray U (fun j => r • p j) _ b s).val =
    r • (affineSampleCoefficientArray U p hm b s).val
  rw [affineSampleCoefficientArray_val, affineSampleCoefficientArray_val]
  simp only [map_smul, Finsupp.smul_apply]

noncomputable def affineCoefficientCoverSample {I K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ)) (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (q : ℕ) (b : Option K → I → ℝ) : CoefficientTorus (K := K) U :=
  QuotientAddGroup.mk' (coefficientIntegerLattice U) ((q : ℝ)⁻¹ • affineSampleCoefficientArray U p hm b)

theorem affineCoefficientCoverSample_eq_scaled {I K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ)) (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (q : ℕ) (b : Option K → I → ℝ) :
    affineCoefficientCoverSample U p hm q b =
      affineSampleCoefficientTorus U (fun j => (q : ℝ)⁻¹ • p j)
        (fun j => coefficients_smul_mem (U j) (p j) (hm j) (q : ℝ)⁻¹) b := by
  rw [affineSampleCoefficientTorus, affineSampleCoefficientArray_smul]
  rfl

theorem affineCoefficientCoverSample_projection {I K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ)) (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (q : ℕ) (hq : 0 < q) (b : Option K → I → ℝ) :
    quotientIntegerCover (coefficientIntegerLattice U) q (affineCoefficientCoverSample U p hm q b) =
      affineSampleCoefficientTorus U p hm b := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [affineCoefficientCoverSample, quotientIntegerCover_mk,
    smul_smul, mul_inv_cancel₀ hq0, one_smul]
  rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

theorem exists_affine_coefficient_haar_comparison (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] {F : Type*} [Fintype F]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option K × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    {C : ℝ} (_hC : 0 ≤ C) (_hCP : C ≤ Real.exp P)
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ)
    (_hbound : ∀ a j d, d.degree ≤ j.val + 1 → ∀ t, |(frequency a j d t : ℝ)| ≤ C)
    (c : F → ℂ) {B : ℝ} (_hB : 0 ≤ B) (_hBP : B ≤ Real.exp P)
    (_hcoefficients : (∑ a, ‖c a‖) ≤ B)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hεP : 1 / ε ≤ Real.exp P)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ) (_hsize : ∀ k, Real.exp ((P + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((P + A) ^ A) ≤ R)
    (G : Finset (ColumnResiduePattern (Option K) I stride)) (_hG : G.Nonempty)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z) (_hwidth : ∀ z, ρ * H z.2 ≤ V z),
    ∃ hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x,
    ‖(∑' z : Option K × I → ℤ, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) *
        coefficientTorusFourierSum U frequency c
          (affineSampleCoefficientTorus U p _hm (fun k j => (z (k, j) : ℝ)))) -
      (∫ x, coefficientTorusFourierSum U frequency c x ∂μ)‖ ≤ ε := by
  obtain ⟨A, hA, hnormalization⟩ := exists_affine_coefficient_fourier_normalization m
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ F _ P hP hn hd U _ _ μ _ _ C hC hCP frequency hbound c B hB hBP hcoefficients
    p hp hm stride hs R S ρ ε hS hSP hρ hε hρP hεP hstride H hsize hrank hR G hG V hV hwidth
  obtain ⟨hZ, hnorm⟩ := hnormalization hP hn hd U hC hCP frequency hbound c hB hBP hcoefficients
    p hp hm stride hs hS hSP hρ hε hρP hεP hstride H hsize hrank hR G hG V hV hwidth
  refine ⟨hZ, ?_⟩
  rw [coefficientTorusFourierSum_integral]
  simpa only [coefficientTorusFourierSum, coefficientTorusCharacter_sample U _ p hp hm] using hnorm

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

theorem exists_affine_coefficient_haar_approximation (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] {F : Type*} [Fintype F]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option K × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    {C : ℝ} (_hC : 0 ≤ C) (_hCP : C ≤ Real.exp P)
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ)
    (_hbound : ∀ a j d, d.degree ≤ j.val + 1 → ∀ t, |(frequency a j d t : ℝ)| ≤ C)
    (c : F → ℂ) {B : ℝ} (_hB : 0 ≤ B) (_hBP : B ≤ Real.exp P)
    (_hcoefficients : (∑ a, ‖c a‖) ≤ B)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hεP : 1 / ε ≤ Real.exp P)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ) (_hsize : ∀ k, Real.exp ((P + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((P + A) ^ A) ≤ R)
    (G : Finset (ColumnResiduePattern (Option K) I stride)) (_hG : G.Nonempty)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z) (_hwidth : ∀ z, ρ * H z.2 ≤ V z)
    (f : CoefficientTorus (K := K) U → ℂ) (_hf : Integrable f μ)
    {η : ℝ} (_hη : 0 ≤ η)
    (_happrox : ∀ x, ‖f x - coefficientTorusFourierSum U frequency c x‖ ≤ η),
    ∃ hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x,
    ‖(∑' z : Option K × I → ℤ, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) *
        f (affineSampleCoefficientTorus U p _hm (fun k j => (z (k, j) : ℝ)))) -
      (∫ x, f x ∂μ)‖ ≤ 2 * η + ε := by
  obtain ⟨A, hA, hcomparison⟩ := exists_affine_coefficient_haar_comparison m
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ F _ P hP hn hd U _ _ μ _ _ C hC hCP frequency hbound c B hB hBP hcoefficients
    p hp hm stride hs R S ρ ε hS hSP hρ hε hρP hεP hstride H hsize hrank hR G hG V hV hwidth f hf η hη happrox
  obtain ⟨hZ, hcomp⟩ := hcomparison hP hn hd U μ hC hCP frequency hbound c hB hBP hcoefficients
    p hp hm stride hs hS hSP hρ hε hρP hεP hstride H hsize hrank hR G hG V hV hwidth
  refine ⟨hZ, ?_⟩
  let g := coefficientTorusFourierSum U frequency c
  let sample (z : Option K × I → ℤ) := affineSampleCoefficientTorus U p hm (fun k j => (z (k, j) : ℝ))
  let E (a : CoefficientTorus (K := K) U → ℂ) :=
    ∑' z, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) * a (sample z)
  have hfirst := selectedResidueSmoothPMF_approximation stride G V hV hZ
    (fun _ => 1) (fun z => f (sample z)) (fun z => g (sample z)) hη
    (fun _ _ => by simp) (fun z _ => happrox (sample z))
  simp only [one_mul] at hfirst
  have hlast := probability_integral_approximation μ g f
    (coefficientTorusFourierSum_integrable U frequency c μ) hf
    (fun x => by simpa only [norm_sub_rev] using happrox x)
  have htri := norm_sub_le_norm_sub_add_norm_sub (E f) (E g) (∫ x, f x ∂μ)
  have htri' := norm_sub_le_norm_sub_add_norm_sub (E g) (∫ x, g x ∂μ) (∫ x, f x ∂μ)
  change ‖E f - E g‖ ≤ η at hfirst
  change ‖E g - ∫ x, g x ∂μ‖ ≤ ε at hcomp
  change ‖E f - ∫ x, f x ∂μ‖ ≤ 2 * η + ε
  linarith

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

theorem exists_affine_coefficient_cover_haar_approximation (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] {F : Type*} [Fintype F]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option K × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    {C : ℝ} (_hC : 0 ≤ C) (_hCP : C ≤ Real.exp P)
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ)
    (_hbound : ∀ a j d, d.degree ≤ j.val + 1 → ∀ t, |(frequency a j d t : ℝ)| ≤ C)
    (c : F → ℂ) {B : ℝ} (_hB : 0 ≤ B) (_hBP : B ≤ Real.exp P)
    (_hcoefficients : (∑ a, ‖c a‖) ≤ B)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    (q : ℕ) (_hq : 0 < q) (_hqP : (q : ℝ) ≤ Real.exp P)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hεP : 1 / ε ≤ Real.exp P)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ) (_hsize : ∀ k, Real.exp ((P + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((P + A) ^ A) ≤ R)
    (G : Finset (ColumnResiduePattern (Option K) I stride)) (_hG : G.Nonempty)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z) (_hwidth : ∀ z, ρ * H z.2 ≤ V z)
    (f : CoefficientTorus (K := K) U → ℂ) (_hf : Integrable f μ)
    {η : ℝ} (_hη : 0 ≤ η)
    (_happrox : ∀ x, ‖f x - coefficientTorusFourierSum U frequency c x‖ ≤ η),
    ∃ hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x,
    ‖(∑' z : Option K × I → ℤ, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) *
        f (affineCoefficientCoverSample U p _hm q (fun k j => (z (k, j) : ℝ)))) -
      (∫ x, f x ∂μ)‖ ≤ 2 * η + ε := by
  obtain ⟨A₀, _, hcomparison⟩ := exists_affine_coefficient_haar_approximation m
  obtain ⟨A, hA, hbudget⟩ := exists_integer_cover_threshold A₀
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ F _ P hP hn hd U _ _ μ _ _ C hC hCP frequency hbound c B hB hBP hcoefficients
    p hp hm q hq hqP stride hs R S ρ ε hS hSP hρ hε hρP hεP hstride H hsize hrank hR G hG V hV hwidth f hf η hη happrox
  have hb := hbudget P hP
  have hR0 : 0 ≤ R := (Real.exp_pos _).le.trans hR
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hscaledR : Real.exp ((P + A₀) ^ A₀) ≤ R / q := by
    apply (le_div_iff₀ hq0).mpr
    calc
      _ ≤ Real.exp P * Real.exp ((P + A₀) ^ A₀) := by
        simpa only [mul_comm] using mul_le_mul_of_nonneg_right hqP (Real.exp_pos ((P + A₀) ^ A₀)).le
      _ ≤ Real.exp ((P + A) ^ A) := hb.2
      _ ≤ R := hR
  obtain ⟨hZ, he⟩ := hcomparison hP hn hd U μ hC hCP frequency hbound c hB hBP hcoefficients
    (fun j => (q : ℝ)⁻¹ • p j) (fun j => (hp j).smul (q : ℝ)⁻¹)
    (fun j => coefficients_smul_mem (U j) (p j) (hm j) (q : ℝ)⁻¹)
    stride hs hS hSP hρ hε hρP hεP hstride H (fun k => hb.1.trans (hsize k))
    (fun j => (hrank j).div_nat hR0 q hq) hscaledR G hG V hV hwidth f hf hη happrox
  refine ⟨hZ, ?_⟩
  simpa only [affineCoefficientCoverSample_eq_scaled] using he

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

theorem exists_affine_coefficient_density_mass (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] {F : Type*} [Fintype F]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option K × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    {C : ℝ} (_hC : 0 ≤ C) (_hCP : C ≤ Real.exp P)
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ)
    (_hbound : ∀ a j d, d.degree ≤ j.val + 1 → ∀ t, |(frequency a j d t : ℝ)| ≤ C)
    (c : F → ℂ) {B : ℝ} (_hB : 0 ≤ B) (_hBP : B ≤ Real.exp P)
    (_hcoefficients : (∑ a, ‖c a‖) ≤ B)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hεP : 1 / ε ≤ Real.exp P)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ) (_hsize : ∀ k, Real.exp ((P + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((P + A) ^ A) ≤ R)
    (G : Finset (ColumnResiduePattern (Option K) I stride)) (_hG : G.Nonempty)
    (V : Option K × I → ℝ) (_hV : ∀ z, 0 < V z) (_hwidth : ∀ z, ρ * H z.2 ≤ V z)
    (D : CoefficientTorus (K := K) U → ℝ) (_hD : Integrable D μ)
    (_hDmass : (∫ x, D x ∂μ) = 1)
    {η : ℝ} (_hη : 0 ≤ η)
    (_happrox : ∀ x, ‖(D x : ℂ) - coefficientTorusFourierSum U frequency c x‖ ≤ η),
    ∃ _hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x,
    |selectedResidueDensityMass stride G V
      (fun z => D (affineSampleCoefficientTorus U p _hm (fun k j => (z (k, j) : ℝ)))) - 1| ≤
      2 * η + ε := by
  obtain ⟨A, hA, hcomparison⟩ := exists_affine_coefficient_haar_approximation m
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ F _ P hP hn hd U _ _ μ _ _ C hC hCP frequency hbound c B hB hBP hcoefficients
    p hp hm stride hs R S ρ ε hS hSP hρ hε hρP hεP hstride H hsize hrank hR G hG V hV hwidth D hD hDmass η hη happrox
  obtain ⟨hZ, he⟩ := hcomparison hP hn hd U μ hC hCP frequency hbound c hB hBP hcoefficients
    p hp hm stride hs hS hSP hρ hε hρP hεP hstride H hsize hrank hR G hG V hV hwidth
    (fun x => (D x : ℂ)) hD.ofReal hη happrox
  refine ⟨hZ, ?_⟩
  rw [integral_complex_ofReal, hDmass, Complex.ofReal_one] at he
  rw [← selectedResidueDensityMass_complex stride G V hV hZ
    (fun z => D (affineSampleCoefficientTorus U p hm (fun k j => (z (k, j) : ℝ)))),
    ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at he
  exact he

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

theorem exists_affine_coefficient_cover_tilted_family_comparison (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (F : Bool → Type*) [∀ b, Fintype (F b)]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option K × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    {C : ℝ} (_hC : 0 ≤ C) (_hCP : C ≤ Real.exp P)
    (frequency : ∀ b, F b → ∀ j, (K →₀ ℕ) → J j → ℤ)
    (_hbound : ∀ b a j d, d.degree ≤ j.val + 1 → ∀ t, |(frequency b a j d t : ℝ)| ≤ C)
    (c : ∀ b, F b → ℂ) {B : ℝ} (_hB : 0 ≤ B) (_hBP : B ≤ Real.exp P)
    (_hcoefficients : ∀ b, (∑ a, ‖c b a‖) ≤ B)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    (cover : ℕ) (_hcover : 0 < cover) (_hcoverP : (cover : ℝ) ≤ Real.exp P)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hεP : 1 / ε ≤ Real.exp P)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ) (_hsize : ∀ k, Real.exp ((P + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((P + A) ^ A) ≤ R)
    (G : Finset (ColumnResiduePattern (Option K) I stride)) (_hG : G.Nonempty)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z) (_hwidth : ∀ z, ρ * H z.2 ≤ V z)
    (D : CoefficientTorus (K := K) U → ℝ) (_hD : Integrable D μ)
    (_hDmass : (∫ x, D x ∂μ) = 1) (_hD0 : ∀ x, 0 ≤ D x)
    (f : CoefficientTorus (K := K) U → ℂ) (_hf : AEStronglyMeasurable f μ)
    (_hfbound : ∀ x, ‖f x‖ ≤ 1)
    {η : ℝ} (_hη : 0 ≤ η)
    (_happrox : ∀ b x,
      ‖(D x : ℂ) * (if b then f x else 1) - coefficientTorusFourierSum U (frequency b) (c b) x‖ ≤ η)
    (_hsmall : 2 * η + ε ≤ 1 / 2),
    ∃ hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x,
    ∃ hDpos : 0 < selectedResidueDensityMass stride G V
      (fun z => D (affineCoefficientCoverSample U p _hm cover (fun k j => (z (k, j) : ℝ)))),
    |selectedResidueDensityMass stride G V
      (fun z => D (affineCoefficientCoverSample U p _hm cover (fun k j => (z (k, j) : ℝ)))) - 1| ≤ 2 * η + ε ∧
    (1 / 2 ≤ selectedResidueDensityMass stride G V
      (fun z => D (affineCoefficientCoverSample U p _hm cover (fun k j => (z (k, j) : ℝ))))) ∧
    (selectedResidueDensityMass stride G V
      (fun z => D (affineCoefficientCoverSample U p _hm cover (fun k j => (z (k, j) : ℝ)))) ≤ 3 / 2) ∧
    ‖(∑' z, ((selectedResidueDensityPMF stride G V hV hZ
        (fun z => D (affineCoefficientCoverSample U p _hm cover (fun k j => (z (k, j) : ℝ))))
        (fun _z => _hD0 _) hDpos z).toReal : ℂ) *
          f (affineCoefficientCoverSample U p _hm cover (fun k j => (z (k, j) : ℝ)))) -
      (∫ x, (D x : ℂ) * f x ∂μ)‖ ≤ 4 * (2 * η + ε) := by
  obtain ⟨A, hA, hcomparison⟩ := exists_affine_coefficient_cover_haar_approximation m
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ F _ P hP hn hd U _ _ μ _ _ C hC hCP frequency hbound c B hB hBP hcoefficients
    p hp hm cover hcover hcoverP stride hs R S ρ ε hS hSP hρ hε hρP hεP hstride H hsize hrank hR G hG V hV hwidth
    D hD hDmass hD0 f hf hfbound η hη happrox hsmall
  let sample (z : Option K × I → ℤ) := affineCoefficientCoverSample U p hm cover (fun k j => (z (k, j) : ℝ))
  obtain ⟨hZ, he0⟩ := hcomparison hP hn hd U μ hC hCP (frequency false) (hbound false)
    (c false) hB hBP (hcoefficients false) p hp hm cover hcover hcoverP stride hs hS hSP hρ hε hρP hεP hstride
    H hsize hrank hR G hG V hV hwidth (fun x => (D x : ℂ)) hD.ofReal hη
    (fun x => by simpa using happrox false x)
  have hmass : |selectedResidueDensityMass stride G V (fun z => D (sample z)) - 1| ≤ 2 * η + ε := by
    rw [integral_complex_ofReal, hDmass, Complex.ofReal_one] at he0
    rw [← selectedResidueDensityMass_complex stride G V hV hZ (fun z => D (sample z)),
      ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at he0
    exact he0
  have hlower : 1 / 2 ≤ selectedResidueDensityMass stride G V (fun z => D (sample z)) := by
    have := (abs_le.mp hmass).1
    linarith
  have hupper : selectedResidueDensityMass stride G V (fun z => D (sample z)) ≤ 3 / 2 := by
    have := (abs_le.mp hmass).2
    linarith
  have hDpos : 0 < selectedResidueDensityMass stride G V (fun z => D (sample z)) := by linarith
  refine ⟨hZ, hDpos, hmass, hlower, hupper, ?_⟩
  obtain ⟨hZ', he1⟩ := hcomparison hP hn hd U μ hC hCP (frequency true) (hbound true)
    (c true) hB hBP (hcoefficients true) p hp hm cover hcover hcoverP stride hs hS hSP hρ hε hρP hεP hstride
    H hsize hrank hR G hG V hV hwidth (fun x => (D x : ℂ) * f x)
    (density_mul_integrable μ D hD f hf hfbound) hη
    (fun x => by simpa using happrox true x)
  have he := selectedResidueDensityPMF_error stride G V hV hZ
    (fun z => D (sample z)) (fun z => hD0 _) hDpos (fun z => f (sample z))
    hlower he1 hmass (norm_density_integral_le_one μ D hD hD0 hDmass f hfbound)
  convert he using 1; ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.SectionRetainedFourier
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators Classical

noncomputable def affineCubeFourierSum {I K F : Type*} [Fintype K] [Fintype F] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ)) (c : F → ℂ) (b : Option K → I → ℝ) : ℂ :=
  ∑ a, c a * layeredCoefficientCharacter
    (fun j => affineModeLift (coefficientFunctional (fun d t => (frequency a j d t : ℝ)))) p b

noncomputable def affineCubeFourierProjection {I K F : Type*} [Fintype K] [Fintype F] {m q : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (difference : Fin q → K → ℤ)
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ)) (c : F → ℂ) (b : Option K → I → ℝ) : ℂ :=
  ∑ a, if affineCubeModeFactors U root difference (frequency a) then
    c a * layeredCoefficientCharacter
      (fun j => affineModeLift (coefficientFunctional (fun d t => (frequency a j d t : ℝ)))) p b else 0

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators

theorem exists_affine_cube_fourier_projection (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {F : Type*} [Fintype F]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option K × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (difference : Fin q → K → ℤ)
    (_hlin : LinearIndependent ℝ (fun i k => (difference i k : ℝ)))
    {L C : ℝ} (_hL : 0 ≤ L) (_hC : 0 ≤ C) (_hLP : L ≤ Real.exp P) (_hCP : C ≤ Real.exp P)
    (_hsite : ∀ (s : Finset (Fin q)) k, |((affineSite root difference s (some k) : ℤ) : ℝ)| ≤ L)
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ)
    (_hbound : ∀ a j d, d.degree ≤ j.val + 1 → ∀ t, |(frequency a j d t : ℝ)| ≤ C)
    (c : F → ℂ) {B : ℝ} (_hB : 0 ≤ B) (_hBP : B ≤ Real.exp P)
    (_hcoefficients : (∑ a, ‖c a‖) ≤ B)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hεP : 1 / ε ≤ Real.exp P)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ)
    (_hsize : ∀ k, Real.exp ((P + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((P + A) ^ A) ≤ R)
    (Q : MvPolynomial (Option K × I) ℝ) (_hQ : Q.totalDegree ≤ 0)
    (test : Finset (Fin q) → (I → ℝ) → ℂ) (_htest : ∀ t v, ‖test t v‖ ≤ 1)
    (G : Finset (ColumnResiduePattern (Option K) I stride)) (_hG : G.Nonempty)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z)
    (_hwidth : ∀ z, ρ * H z.2 ≤ V z),
    ∃ hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x,
    ‖(∑' z : Option K × I → ℤ, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) *
        (layeredSiteWeight Q (fun s => affineSite root difference s) test (fun k j => (z (k, j) : ℝ)) *
          affineCubeFourierSum frequency p c (fun k j => (z (k, j) : ℝ)))) -
      (∑' z : Option K × I → ℤ, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) *
        (layeredSiteWeight Q (fun s => affineSite root difference s) test (fun k j => (z (k, j) : ℝ)) *
          affineCubeFourierProjection U root difference frequency p c (fun k j => (z (k, j) : ℝ))))‖ ≤ ε := by
  obtain ⟨A₀, _, hremove⟩ := exists_affine_cube_congruence_removal m q
  obtain ⟨A₁, _, hthreshold⟩ := exists_cube_residue_threshold_exp_budget m q
  obtain ⟨A, hA, hbudget⟩ := exists_fourier_uniform_budget A₀ A₁
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ F _ P hP hn hd U root difference hlin L C hL hC hLP hCP
    hsite frequency hbound c B hB hBP hcoefficients p hp hm stride hs R S ρ ε hS hSP hρ hε hρP hεP
    hstride H hsize hrank hR Q hQ test htest G hG V hV hwidth
  classical
  let P' := 2 * P + 2
  let δ := fourierModeError B ε
  have hPP : P ≤ P' := by dsimp [P']; linarith
  have hEP : Real.exp P ≤ Real.exp P' := Real.exp_le_exp.mpr hPP
  have hδ : 0 < δ := fourierModeError_pos hB hε
  have hδP : 1 / δ ≤ Real.exp P' := fourierModeError_inv_le_exp hP hB hBP hε hεP
  obtain ⟨hb₀, hb₁⟩ := hbudget P hP
  obtain ⟨hside, _⟩ := hthreshold (Fintype.card I) (Fintype.card (Option K × I))
    P' C L S ρ δ (hP.trans hPP) (hn.trans hPP) (hd.trans hPP) hC (hCP.trans hEP)
    hL (hLP.trans hEP) hS (hSP.trans hEP) hρ (hρP.trans hEP) hδ hδP
  have hZ := selectedResidueSmoothWeight_pos_of_threshold m (cubeModePolynomialBudget_pos q hL).le
    hS hρ hδ stride hs hstride H (fun j => hside.trans (hb₁.trans (hsize j))) G hG V hV hwidth
  refine ⟨hZ, ?_⟩
  apply le_trans ?_ (fourierModeError_cost_le hB hε)
  unfold affineCubeFourierSum affineCubeFourierProjection
  apply selectedResidueSmoothPMF_discard_error stride G V hV hZ
    (fun z => layeredSiteWeight Q (fun s => affineSite root difference s) test (fun k j => (z (k, j) : ℝ)))
    c (fun a z => layeredCoefficientCharacter
      (fun j => affineModeLift (coefficientFunctional (fun d t => (frequency a j d t : ℝ))))
      p (fun k j => (z (k, j) : ℝ)))
    (fun a => affineCubeModeFactors U root difference (frequency a)) hcoefficients hδ.le
  intro a hbad
  obtain ⟨_, hr⟩ := hremove (hP.trans hPP) (hn.trans hPP) (hd.trans hPP)
    U root difference hlin hL hC (hLP.trans hEP) (hCP.trans hEP) hsite (frequency a) (hbound a)
    ((not_affineCubeModeFactors_iff U root difference (frequency a)).mp hbad)
    p hp hm stride hs hS (hSP.trans hEP) hρ hδ (hρP.trans hEP) hδP hstride
    H (fun j => hb₀.trans (hsize j)) hrank (hb₀.trans hR) Q hQ test htest G hG V hV hwidth
  simpa only [layeredModeTestedPhase_eq_weight_mul] using hr

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators Classical

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators Classical

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators Matrix Classical

end Erdos3.BooleanCubeKernel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineCubePositiveComparison
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped Classical

theorem affineCubeModeFactors_iff_bounded {K : Type*} [Fintype K] {m q : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (difference : Fin q → K → ℤ)
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ) :
    affineCubeModeFactors U root difference frequency ↔
      ∀ j, ∃ M : (Finset (Fin q) → U j) →ₗ[ℝ] ℝ,
        ∀ p : VectorPolynomial K ℝ (U j), DegreeLE (1 : K → ℕ) (j.val + 1) p →
          coefficientFunctional (fun d a => (frequency j d a : ℝ)) (map (U j).subtype p) =
            M (VectorPolynomial.siteEvaluation (fun s k => ((affineSite root difference s (some k) : ℤ) : ℝ)) p) := by
  constructor
  · exact affineCubeModeFactors_bounded U root difference frequency
  · intro h j
    obtain ⟨M, hM⟩ := h j
    refine ⟨M, ?_⟩
    let L := (coefficientFunctional (fun d a => (frequency j d a : ℝ))).comp (map (U j).subtype)
    have hh := (homogeneous_site_factorization_iff (j.val + 1)
      (fun s k => ((affineSite root difference s (some k) : ℤ) : ℝ)) L M).mpr hM
    change ∀ p, Homogeneous (j.val + 1) p → affineModeLift L p = _ at hh
    have he : (fun s (k : Option K) => k.elim (1 : ℝ)
        (fun k => ((affineSite root difference s (some k) : ℤ) : ℝ))) =
        (fun s => affineSite (fun k => (root k : ℝ)) (fun i k => (difference i k : ℝ)) s) := by
      funext s k
      cases k <;> simp [affineSite, Int.cast_sum]
    simpa only [L, affineModeLift_comp_map, LinearMap.comp_apply, he] using hh

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory VectorPolynomial
open scoped BigOperators Classical

variable {K : Type*} [Fintype K] {m q : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
  (U : ∀ j, Submodule ℝ (J j → ℝ))
  (R : CoefficientArray (K := K) U →ₗ[ℝ] CoefficientArray (K := K) U)
  (hR : ∀ x ∈ coefficientIntegerLattice U, R x ∈ coefficientIntegerLattice U)
  [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]

theorem coefficientResidual_section_integrable
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (μ : Measure (CoefficientTorus (K := K) U)) [IsFiniteMeasure μ]
    (f : CoefficientTorus (K := K) U → W) (hf : Continuous f)
    {B : ℝ} (hB : ∀ x, ‖f x‖ ≤ B) (x : CoefficientTorus (K := K) U) :
    Integrable (fun y => f (x + linearQuotientEndomorphism (coefficientIntegerLattice U) R hR y)) μ := by
  have hc := linearQuotientEndomorphism_continuous (coefficientIntegerLattice U) R hR
    R.continuous_of_finiteDimensional
  exact Integrable.of_bound (hf.comp (continuous_const.add hc)).aestronglyMeasurable B
    (ae_of_all μ (fun _ => hB _))

theorem coefficientResidualAverage_continuous
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (μ : Measure (CoefficientTorus (K := K) U)) [IsFiniteMeasure μ]
    (f : CoefficientTorus (K := K) U → W) (hf : Continuous f)
    {B : ℝ} (hB : ∀ x, ‖f x‖ ≤ B) :
    Continuous (linearQuotientAverage (coefficientIntegerLattice U) R hR μ f) := by
  apply continuous_of_dominated
    (fun x => (coefficientResidual_section_integrable U R hR μ f hf hB x).aestronglyMeasurable)
    (fun _ => ae_of_all μ (fun _ => hB _)) (integrable_const B)
  exact ae_of_all μ (fun _ => hf.comp (continuous_id.add continuous_const))

theorem coefficientTorusFourierSum_residualAverage {F : Type*} [Fintype F]
    (root : K → ℤ) (difference : Fin q → K → ℤ)
    (hfactor : ∀ frequency : ∀ j, (K →₀ ℕ) → J j → ℤ,
      (coefficientArrayFunctional U frequency).comp R = 0 ↔ affineCubeModeFactors U root difference frequency)
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (c : F → ℂ)
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (x : CoefficientTorus (K := K) U) :
    linearQuotientAverage (coefficientIntegerLattice U) R hR μ (coefficientTorusFourierSum U frequency c) x =
      ∑ a, if affineCubeModeFactors U root difference (frequency a) then
        c a * coefficientTorusCharacter U (frequency a) x else 0 := by
  have hi (a : F) := coefficientResidual_section_integrable U R hR μ
    (coefficientTorusCharacter U (frequency a))
    (quotientLinearCharacter_continuous _ _ _ (coefficientArrayFunctional U (frequency a)).continuous_of_finiteDimensional)
    (fun x => (quotientLinearCharacter_norm _ _ _ x).le) x
  change (∫ y, ∑ a, c a * coefficientTorusCharacter U (frequency a)
    (x + linearQuotientEndomorphism (coefficientIntegerLattice U) R hR y) ∂μ) = _
  rw [integral_finsetSum _ (fun a _ => (hi a).const_mul (c a))]
  simp only [integral_const_mul]
  change (∑ a, c a * linearQuotientAverage (coefficientIntegerLattice U) R hR μ
    (quotientLinearCharacter (coefficientIntegerLattice U) (coefficientArrayFunctional U (frequency a))
      (coefficientArrayFunctional_integral U (frequency a))) x) = _
  simp only [linearQuotientAverage_character, hfactor, mul_ite, mul_zero]
  rfl

theorem coefficientTorusFourierProjection_approx_residualAverage {F : Type*} [Fintype F]
    (root : K → ℤ) (difference : Fin q → K → ℤ)
    (hfactor : ∀ frequency : ∀ j, (K →₀ ℕ) → J j → ℤ,
      (coefficientArrayFunctional U frequency).comp R = 0 ↔ affineCubeModeFactors U root difference frequency)
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (c : F → ℂ)
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (D : CoefficientTorus (K := K) U → ℝ) {η : ℝ}
    (happrox : ∀ x, ‖coefficientTorusFourierSum U frequency c x - (D x : ℂ)‖ ≤ η)
    (x : CoefficientTorus (K := K) U)
    (hD : Integrable (fun y => D (x + linearQuotientEndomorphism (coefficientIntegerLattice U) R hR y)) μ) :
    ‖(∑ a, if affineCubeModeFactors U root difference (frequency a) then
        c a * coefficientTorusCharacter U (frequency a) x else 0) -
      ((linearQuotientAverage (coefficientIntegerLattice U) R hR μ D x : ℝ) : ℂ)‖ ≤ η := by
  rw [← coefficientTorusFourierSum_residualAverage U R hR root difference hfactor frequency c μ x]
  have hi : Integrable (fun y => coefficientTorusFourierSum U frequency c
      (x + linearQuotientEndomorphism (coefficientIntegerLattice U) R hR y)) μ := by
    apply integrable_finsetSum
    intro a _
    apply Integrable.const_mul
    exact coefficientResidual_section_integrable U R hR μ (coefficientTorusCharacter U (frequency a))
      (quotientLinearCharacter_continuous _ _ _ (coefficientArrayFunctional U (frequency a)).continuous_of_finiteDimensional)
      (fun x => (quotientLinearCharacter_norm _ _ _ x).le) x
  have he := linearQuotientAverage_approx (coefficientIntegerLattice U) R hR μ
    (coefficientTorusFourierSum U frequency c) (fun x => (D x : ℂ)) happrox x hi hD.ofReal
  simpa only [linearQuotientAverage, integral_complex_ofReal] using he

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

open MeasureTheory VectorPolynomial
open scoped BigOperators Classical

end Erdos3.BooleanCubeKernel

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

theorem coefficientProductDensity_probability {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    [∀ s : CoefficientSlot K m, MeasurableSpace (SubspaceArrayTorus Unit (U s.1))]
    [∀ s : CoefficientSlot K m, BorelSpace (SubspaceArrayTorus Unit (U s.1))]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ s : CoefficientSlot K m, Measure (SubspaceArrayTorus Unit (U s.1)))
    [∀ s, (ν s).IsAddLeftInvariant] [∀ s, IsProbabilityMeasure (ν s)]
    (f : ∀ s : CoefficientSlot K m, SubspaceArrayTorus Unit (U s.1) → ℝ)
    (hf : ∀ s, Integrable (f s) (ν s)) (hf0 : ∀ s x, 0 ≤ f s x)
    (hmass : ∀ s, (∫ x, f s x ∂ν s) = 1) :
    Integrable (coefficientProductDensity U f) μ ∧
      (∀ x, 0 ≤ coefficientProductDensity U f x) ∧
      (∫ x, coefficientProductDensity U f x ∂μ) = 1 := by
  let g : CoefficientCoordinateTori (K := K) U → ℝ := fun y => ∏ s, f s (y s)
  have hg : Integrable g (Measure.pi ν) := Integrable.fintype_prod_dep hf
  have hp := coefficientCoordinateTorus_measurePreserving U μ ν
  refine ⟨hp.integrable_comp_of_integrable hg, coefficientProductDensity_nonneg U f hf0, ?_⟩
  have hg' : AEStronglyMeasurable g (Measure.map (coefficientCoordinateTorus U) μ) := by
    simpa only [hp.map_eq] using hg.aestronglyMeasurable
  calc
    (∫ x, coefficientProductDensity U f x ∂μ) = ∫ y, g y ∂Measure.pi ν := by
      simpa only [hp.map_eq, g, coefficientProductDensity] using
        (integral_map hp.measurable.aemeasurable hg').symm
    _ = ∏ s, ∫ x, f s x ∂ν s := integral_fintype_prod_eq_prod f
    _ = 1 := by simp only [hmass, Finset.prod_const_one]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.OneSiteWeightIdentity
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial

theorem layeredSiteWeight_oneSite {I K : Type*} [Fintype K]
    (root : K → ℤ) (difference : Fin 0 → K → ℤ) (φ : (I → ℝ) → ℂ)
    (b : Option K → I → ℝ) :
    layeredSiteWeight 0 (fun s => affineSite root difference s) (fun _ => φ) b =
      φ (integerSiteValue (affineSite root difference ∅) b) := by
  simp only [layeredSiteWeight, map_zero, AddCircle.coe_zero,
    CircleFourier.character_zero, one_mul]
  exact Fintype.prod_subsingleton
    (fun s : Finset (Fin 0) => φ (integerSiteValue (affineSite root difference s) b))
    (∅ : Finset (Fin 0))

end Erdos3.BooleanCubeKernel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerBooleanSiteReconstruction
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def integerBooleanSitesFromRows (rows : Finset (Finset α))
    (z : rows → ℤ) : Finset α → ℤ :=
  booleanReconstructionMatrix α *ᵥ (fun t => if ht : t ∈ rows then z ⟨t, ht⟩ else 0)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.EuclideanJetDensity
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical

theorem siteImage_density_euclideanJet {α K : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] {m : ℕ} {J : Fin m → Type*}
    [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (SiteTorus (Finset α) U)] [BorelSpace (SiteTorus (Finset α) U)]
    (root : K → ℤ) (D : Matrix α K ℤ) (a : ℤ) (ha : a ≠ 0)
    (hperiod : integerScalarLattice α a ≤ D.mulVecLin.range)
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (ρ : Measure (CoefficientTorus (K := K) U)) :
    let E := coefficientSiteTorusMap U (integerAffineCube root D)
    let π := Set.rangeFactorization E
    let e := euclideanSiteImageHomeomorph U root D a ha hperiod
    let ξ := Measure.pi (fun j => Measure.pi (fun _ : BoundedBooleanJet α (j.val + 1) => ν j))
    ∀ g : Set.range E → ℝ, Continuous g → ∀ {B : ℝ},
      (∀ y, g y ∈ Set.Icc (0 : ℝ) B) → (∫ y, g y ∂μ.map π) = 1 →
      ρ.map π = realDensityMeasure (μ.map π) g →
      let f := fun z => g (e.symm z)
      Continuous f ∧ (∀ z, f z ∈ Set.Icc (0 : ℝ) B) ∧
        Integrable f ξ ∧ (∫ z, f z ∂ξ) = 1 ∧ (∀ y, f (e y) = g y) ∧
        ρ.map (euclideanCoefficientJetMap U root D
          (fun j => (Subtype.val : BoundedBooleanJet α (j.val + 1) → Finset α))) =
          realDensityMeasure ξ f := by
  intro E π e ξ g hgc B hcap hmass hlaw f
  let eM := e.toMeasurableEquiv
  have hhaar : (μ.map π).map eM = ξ := euclideanSiteImageHomeomorph_haar U root D a ha hperiod μ ν
  have hfc : Continuous f := hgc.comp e.symm.continuous
  have hfb (z) : f z ∈ Set.Icc (0 : ℝ) B := hcap (e.symm z)
  let : ∀ j, IsProbabilityMeasure (Measure.pi (fun _ : BoundedBooleanJet α (j.val + 1) => ν j)) :=
    fun _ => Measure.pi.instIsProbabilityMeasure _
  let : IsProbabilityMeasure ξ := Measure.pi.instIsProbabilityMeasure _
  have hfi : Integrable f ξ := Integrable.of_bound hfc.aestronglyMeasurable B
    (ae_of_all _ (fun z => by rw [Real.norm_of_nonneg (hfb z).1]; exact (hfb z).2))
  have hfvalue (y) : f (e y) = g y := congrArg g (e.symm_apply_apply y)
  have hfmass : (∫ z, f z ∂ξ) = 1 := by
    rw [← hhaar, integral_map_equiv]
    change (∫ y, g (e.symm (e y)) ∂μ.map π) = 1
    simpa only [Homeomorph.symm_apply_apply] using hmass
  refine ⟨hfc, hfb, hfi, hfmass, hfvalue, ?_⟩
  have hπ : Measurable π := (coefficientSiteTorusMap_continuous U _).rangeFactorization.measurable
  calc
    _ = (ρ.map π).map eM := (Measure.map_map eM.measurable hπ).symm
    _ = realDensityMeasure ξ f := by
      rw [hlaw, realDensityMeasure_map_equiv, hhaar]
      rfl

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CoefficientLatticeCompact
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module

theorem coefficientTorus_compact_of_lattice {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [∀ j, IsZLattice ℝ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))] :
    CompactSpace (CoefficientTorus (K := K) U) := by
  classical
  let Λ := fun j => latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))
  let : ∀ j, Module.Finite ℤ (Λ j) := fun j => ZLattice.module_finite ℝ (Λ j)
  let b := fun j => Module.Free.chooseBasis ℤ (Λ j)
  let e := fun j => (euclideanSubspaceArrayEquiv (U j)).toLinearEquiv.trans
    (LinearEquiv.piUnique ℝ (fun _ : Unit => U j))
  apply coefficientTorus_compact_of_basis U
    (fun j => ((b j).ofZLatticeBasis ℝ (Λ j)).map (e j))
  intro j i a
  have hi := (euclideanSubspaceArrayEquiv_mem_lattice (U j)
    ((b j i : Λ j) : euclideanSubspace (U j))).mpr (b j i).property
  simpa only [Basis.map_apply, Basis.ofZLatticeBasis_apply, e,
    LinearEquiv.trans_apply, LinearEquiv.piUnique_apply, Equiv.piUnique,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv] using hi default a

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedFullSiteRadius
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

noncomputable def allocatedSiteRootAllowance (α : Type*) [Fintype α] (m : ℕ) : ℝ :=
  1 + (2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (m + 1) + idealSiteEnvelopeRadius α m

theorem allocatedSiteRootAllowance_one_le (α : Type*) [Fintype α] (m : ℕ) :
    1 ≤ allocatedSiteRootAllowance α m := by
  have h := (idealSiteEnvelopeRadius_pos α m).le
  unfold allocatedSiteRootAllowance
  have hp : 0 ≤ (2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (m + 1) := by positivity
  linarith

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

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (α : Type*) [Fintype α]

theorem allocatedSiteChartRadius_le_original (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (j : Fin m) :
    allocatedPhysicalChartRadius (G := G) B α C (allocatedSiteRootAllowance α m) j ≤
      allocatedPhysicalChartRadius (G := G) B α C 1 j := by
  have hH := allocatedSiteRootAllowance_one_le α m
  have hCj := hC j
  unfold allocatedPhysicalChartRadius
  apply one_div_le_one_div_of_le (by positivity)
  gcongr

theorem allocatedSiteChartRadius_inv_le_exp (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    {P : ℝ} (hP : 0 ≤ P)
    (hallow : ((2 * m : ℕ) + 5) * (Fintype.card α : ℝ) + 5 ≤ P)
    (hCP : ∀ j, C j ≤ Real.exp P)
    (hNP : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Real.exp P)
    (hIP : ∀ j, (Fintype.card (I j) : ℝ) ≤ Real.exp P) (j : Fin m) :
    (allocatedPhysicalChartRadius (G := G) B α C (allocatedSiteRootAllowance α m) j)⁻¹ ≤
      Real.exp (3 * (P + 1) + Fintype.card α + 2 +
        (j.val + 1 : ℕ) * (P + Fintype.card α + 1)) :=
  allocatedPhysicalChartRadius_inv_le_exp B α C hC (allocatedSiteRootAllowance_one_le α m) hP
    ((allocatedSiteRootAllowance_le_exp α m).trans (Real.exp_le_exp.mpr hallow)) hCP hNP hIP j

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (α : Type*) [Fintype α]

theorem allocatedSiteJetSize_le_allowance (j : Fin m) :
    allocatedSiteJetSize (G := G) B α j ≤
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
        allocatedSiteRootAllowance α m := by
  let N : ℝ := Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1))
  have hN : 1 ≤ N := by
    change (1 : ℝ) ≤ Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1))
    exact_mod_cast Nat.succ_le_of_lt (Fintype.card_pos_iff.mpr
      ⟨constantCoefficientSlot (LayerSamplerVariables G I n B) (j.val + 1)⟩)
  have hpow : ((Fintype.card α : ℝ) + 1) ^ (j.val + 1) ≤
      ((Fintype.card α : ℝ) + 1) ^ (m + 1) :=
    pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card α)])
      (Nat.succ_le_succ (Nat.le_of_lt j.isLt))
  have he := (idealSiteEnvelopeRadius_pos α m).le
  have hm := mul_le_mul_of_nonneg_left hpow
    (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Fintype.card α))
  unfold allocatedSiteJetSize allocatedSiteRootAllowance
  change N * _ + _ ≤ N * _
  nlinarith [mul_le_mul_of_nonneg_left hm (zero_le_one.trans hN),
    mul_le_mul_of_nonneg_right hN he]

noncomputable def allocatedFullSiteRadius : ℝ≥0 :=
  ⟨1 + (2 : ℝ) ^ Fintype.card α * ∑ j : Fin m, allocatedSiteJetSize (G := G) B α j,
    add_nonneg zero_le_one (mul_nonneg (pow_nonneg (by norm_num) _)
      (Finset.sum_nonneg (fun j _ => allocatedSiteJetSize_nonneg B α j)))⟩

theorem allocatedFullSiteRadius_one_le : 1 ≤ allocatedFullSiteRadius (G := G) B α := by
  change (1 : ℝ) ≤ 1 + (2 : ℝ) ^ Fintype.card α * ∑ j : Fin m, allocatedSiteJetSize (G := G) B α j
  exact le_add_of_nonneg_right (mul_nonneg (pow_nonneg (by norm_num) _)
    (Finset.sum_nonneg (fun j _ => allocatedSiteJetSize_nonneg B α j)))

theorem allocatedFullSiteRadius_pos : 0 < allocatedFullSiteRadius (G := G) B α :=
  zero_lt_one.trans_le (allocatedFullSiteRadius_one_le B α)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedFullSiteRadiusBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (α : Type*) [Fintype α]

theorem allocatedFullSiteRadius_le_exp {P : ℝ} (hP : 0 ≤ P)
    (hm : (m : ℝ) ≤ Real.exp P) (hq : (Fintype.card α : ℝ) ≤ P)
    (hH : allocatedSiteRootAllowance α m ≤ Real.exp P)
    (hN : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Real.exp P) :
    (allocatedFullSiteRadius (G := G) B α : ℝ) ≤ Real.exp (4 * P + 1) := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hp : (2 : ℝ) ^ Fintype.card α ≤ Real.exp P := by
    calc
      _ ≤ (Real.exp 1) ^ Fintype.card α := pow_le_pow_left₀ (by norm_num) htwo _
      _ = Real.exp (Fintype.card α : ℝ) := by rw [← Real.exp_nat_mul]; simp only [mul_one]
      _ ≤ _ := Real.exp_le_exp.mpr hq
  have hj (j : Fin m) : allocatedSiteJetSize (G := G) B α j ≤ Real.exp (2 * P) := by
    calc
      _ ≤ _ := allocatedSiteJetSize_le_allowance B α j
      _ ≤ Real.exp P * Real.exp P := mul_le_mul (hN j) hH
        (zero_le_one.trans (allocatedSiteRootAllowance_one_le α m)) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hs : (∑ j : Fin m, allocatedSiteJetSize (G := G) B α j) ≤ Real.exp (3 * P) := by
    calc
      _ ≤ ∑ _j : Fin m, Real.exp (2 * P) := Finset.sum_le_sum (fun j _ => hj j)
      _ = (m : ℝ) * Real.exp (2 * P) := by simp
      _ ≤ Real.exp P * Real.exp (2 * P) := mul_le_mul_of_nonneg_right hm (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hmultip : (2 : ℝ) ^ Fintype.card α * ∑ j : Fin m, allocatedSiteJetSize (G := G) B α j ≤
      Real.exp (4 * P) := by
    calc
      _ ≤ Real.exp P * Real.exp (3 * P) := mul_le_mul hp hs
        (Finset.sum_nonneg (fun j _ => allocatedSiteJetSize_nonneg B α j)) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hunit : 1 ≤ Real.exp (4 * P) := Real.one_le_exp_iff.mpr (by positivity)
  change 1 + _ ≤ _
  calc
    _ ≤ Real.exp (4 * P) + Real.exp (4 * P) := add_le_add hunit hmultip
    _ = 2 * Real.exp (4 * P) := by ring
    _ ≤ Real.exp 1 * Real.exp (4 * P) := mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedPhysicalLongIdealCap
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} {I : Fin m → Type*} {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] (rowSets : Fin m → Finset (Finset α))

noncomputable def allocatedSiteCoefficientRadius (a : Σ j : Fin m, Fin (n j)) : ℝ :=
  max (allocatedNaturalSupportRadius (G := G) B α a.1 a.2)
    ((2 : ℝ) ^ (a.1.val + 1) *
      (allocatedNaturalSiteRadius (G := G) B a.1 a.2 (rowSets a.1) + 1 / 4))

theorem allocatedSiteCoefficientRadius_nonneg (a : Σ j : Fin m, Fin (n j)) :
    0 ≤ allocatedSiteCoefficientRadius (G := G) B rowSets a :=
  (allocatedNaturalSupportRadius_nonneg (G := G) B α a.1 a.2).trans (le_max_left _ _)

variable [Fintype G] [∀ j, Fintype (I j)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})

end Erdos3.VectorPolynomial

end

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

noncomputable def allocatedIdealCoverRadius (C : Fin m → ℝ) (j : Fin m) : ℝ :=
  finiteRowChartRadius (rowSets j).card (Fintype.card (I j)) (C j)
    (allocatedIdealCoverSupport (G := G) B rowSets j)

theorem allocatedIdealCoverRadius_pos (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) (j : Fin m) :
    0 < allocatedIdealCoverRadius (G := G) B rowSets C j :=
  finiteRowChartRadius_pos _ _ (hC j) (allocatedIdealCoverSupport_nonneg B rowSets j)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] (rowSets : Fin m → Finset (Finset α))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rowTypes" => (fun j => {t : Finset α // t ∈ rowSets j})
local notation "output" => (Σ a : {a // ¬grid a}, rowTypes (Sigma.fst (Subtype.val a)))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rowTypes" => (fun j => {t : Finset α // t ∈ rowSets j})
local notation "output" => (Σ a : {a // ¬grid a}, rowTypes (Sigma.fst (Subtype.val a)))

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

theorem allocatedIdealCoverRadius_inv_le_exp {P : ℝ} (hP : 0 ≤ P)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) (j : Fin m)
    (hA : (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
      ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)) ≤ Real.exp P)
    (hI : partitionedIdealRadius α m + 1 ≤ Real.exp P)
    (hn : (n j : ℝ) ≤ Real.exp P)
    (hW : ∀ i : Fin (n j), allocatedSiteCoefficientRadius (G := G) B rowSets ⟨j, i⟩ + 1 ≤ Real.exp P)
    (hr : ((rowSets j).card : ℝ) ≤ Real.exp P)
    (hd : (Fintype.card (I j) : ℝ) ≤ Real.exp P) (hCP : C j ≤ Real.exp P) :
    (allocatedIdealCoverRadius (G := G) B rowSets C j)⁻¹ ≤ Real.exp (8 * P + 14) := by
  have hp : Real.exp P ≤ Real.exp (2 * P + 2) := Real.exp_le_exp.mpr (by linarith)
  have h := finiteRowChartRadius_inv_le_exp (rowSets j).card (Fintype.card (I j))
    (hC j) (allocatedIdealCoverSupport_nonneg B rowSets j) (by positivity : 0 ≤ 2 * P + 2)
    (hr.trans hp) (hd.trans hp) (hCP.trans hp)
    (allocatedIdealCoverSupport_le_exp B rowSets hP j hA hI hn hW)
  have he : 4 * (2 * P + 2) + 6 = 8 * P + 14 := by ring
  simpa only [allocatedIdealCoverRadius, he] using h

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedSupportedBufferedPhysicalFactorization
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (α : Type*) [Fintype α]

noncomputable def allocatedBufferedPhysicalChartRadius (C : Fin m → ℝ) (j : Fin m) : ℝ :=
  min (allocatedPhysicalChartRadius (G := G) B α C (allocatedSiteRootAllowance α m) j)
    (1 / (8 * (C j + 1) * ((Fintype.card (I j) : ℝ) + 1) * (allocatedFullSiteRadius (G := G) B α : ℝ)))

theorem allocatedBufferedPhysicalChartRadius_pos (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) (j : Fin m) :
    0 < allocatedBufferedPhysicalChartRadius (G := G) B α C j := by
  have hCj := hC j
  have hr : (0 : ℝ) < allocatedFullSiteRadius (G := G) B α := allocatedFullSiteRadius_pos B α
  exact lt_min (allocatedPhysicalChartRadius_pos B α C hC
    (allocatedSiteRootAllowance_one_le α m) j) (by positivity)

theorem allocatedBufferedPhysicalChartRadius_le_supported (C : Fin m → ℝ) (j : Fin m) :
    allocatedBufferedPhysicalChartRadius (G := G) B α C j ≤
      allocatedPhysicalChartRadius (G := G) B α C (allocatedSiteRootAllowance α m) j := min_le_left _ _

theorem allocatedBufferedPhysicalChartRadius_le_original (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) (j : Fin m) :
    allocatedBufferedPhysicalChartRadius (G := G) B α C j ≤ allocatedPhysicalChartRadius (G := G) B α C 1 j :=
  (allocatedBufferedPhysicalChartRadius_le_supported B α C j).trans (allocatedSiteChartRadius_le_original B α C hC j)

theorem allocatedBufferedPhysicalChartRadius_inv_le_exp
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) {P : ℝ} (hP : 0 ≤ P)
    (hm : (m : ℝ) ≤ Real.exp P) (hq : (Fintype.card α : ℝ) ≤ P)
    (hallow : ((2 * m : ℕ) + 5) * (Fintype.card α : ℝ) + 5 ≤ P)
    (hCP : ∀ j, C j ≤ Real.exp P)
    (hNP : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Real.exp P)
    (hIP : ∀ j, (Fintype.card (I j) : ℝ) ≤ Real.exp P) (j : Fin m) :
    (allocatedBufferedPhysicalChartRadius (G := G) B α C j)⁻¹ ≤
      Real.exp (3 * (P + 1) + Fintype.card α + 2 +
        (j.val + 1 : ℕ) * (P + Fintype.card α + 1) + (6 * P + 6)) := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hunit : 1 ≤ Real.exp P := Real.one_le_exp_iff.mpr hP
  have hadd {a : ℝ} (ha : a ≤ Real.exp P) : a + 1 ≤ Real.exp (P + 1) := by
    calc
      _ ≤ 2 * Real.exp P := by linarith
      _ ≤ Real.exp 1 * Real.exp P := mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have h8 : (8 : ℝ) ≤ Real.exp 3 := by
    calc
      _ = (2 : ℝ) ^ 3 := by norm_num
      _ ≤ (Real.exp 1) ^ 3 := pow_le_pow_left₀ (by norm_num) htwo 3
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have hr := allocatedFullSiteRadius_le_exp B α hP hm hq
    ((allocatedSiteRootAllowance_le_exp α m).trans (Real.exp_le_exp.mpr hallow)) hNP
  have hCj := hC j
  have hCp := hadd (hCP j)
  have hIp := hadd (hIP j)
  have hden : 8 * (C j + 1) * ((Fintype.card (I j) : ℝ) + 1) * (allocatedFullSiteRadius (G := G) B α : ℝ) ≤
      Real.exp (6 * P + 6) := by
    calc
      _ ≤ Real.exp 3 * Real.exp (P + 1) * Real.exp (P + 1) * Real.exp (4 * P + 1) := by gcongr
      _ = _ := by simp only [← Real.exp_add]; congr 1; ring
  have hold := allocatedSiteChartRadius_inv_le_exp B α C hC hP hallow hCP hNP hIP j
  unfold allocatedBufferedPhysicalChartRadius
  by_cases h : allocatedPhysicalChartRadius (G := G) B α C (allocatedSiteRootAllowance α m) j ≤
      1 / (8 * (C j + 1) * ((Fintype.card (I j) : ℝ) + 1) * (allocatedFullSiteRadius (G := G) B α : ℝ))
  · rw [min_eq_left h]
    exact hold.trans (Real.exp_le_exp.mpr (le_add_of_nonneg_right (by positivity)))
  · rw [min_eq_right (le_of_not_ge h), one_div, inv_inv]
    exact hden.trans (Real.exp_le_exp.mpr (le_add_of_nonneg_left (by positivity)))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "jets" => (fun j : Fin m => BoundedBooleanJet α ((j : ℕ) + 1))
local notation "rows" => (fun j => (Subtype.val : jets j → Finset α))
local notation "quarter" => (fun j (_ : jets j) => standardLatticeClosedQuarterBox (J j))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.BooleanCubeKernel

open Module Submodule _root_.Set _root_.OAI.Set VectorPolynomial
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ} (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin dim) ((j : ℕ) + 1))
local notation "rows" => (fun j => (Subtype.val : jets j → Finset (Fin dim)))
local notation "quarter" => (fun j (_ : jets j) => standardLatticeClosedQuarterBox (J j))

end Erdos3.BooleanCubeKernel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedUnitSiteEarlyBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (α : Type*) [Fintype α]

theorem allocatedBufferedPhysicalChartRadius_inv_le_exp_uniform
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) {P : ℝ} (hP : 0 ≤ P)
    (hm : (m : ℝ) ≤ Real.exp P) (hq : (Fintype.card α : ℝ) ≤ P)
    (hallow : ((2 * m : ℕ) + 5) * (Fintype.card α : ℝ) + 5 ≤ P)
    (hCP : ∀ j, C j ≤ Real.exp P)
    (hNP : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Real.exp P)
    (hIP : ∀ j, (Fintype.card (I j) : ℝ) ≤ Real.exp P) (j : Fin m) :
    (allocatedBufferedPhysicalChartRadius (G := G) B α C j)⁻¹ ≤
      Real.exp (((m : ℝ) + 10) * (P + Fintype.card α + 2)) := by
  apply (allocatedBufferedPhysicalChartRadius_inv_le_exp B α C hC hP hm hq hallow hCP hNP hIP j).trans
  apply Real.exp_le_exp.mpr
  have hj : ((j.val + 1 : ℕ) : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt j.isLt
  have hfactor : 0 ≤ P + (Fintype.card α : ℝ) + 1 := by positivity
  have hmul := mul_le_mul_of_nonneg_right hj hfactor
  have hq0 : (0 : ℝ) ≤ Fintype.card α := Nat.cast_nonneg _
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  nlinarith

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ControlledSingleRefilteredReconstruction
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d e n : ℕ}
  (D : RationalFilteredNilmanifold L (s + 1) d)
  (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
  (E : RationalFilteredNilmanifold (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) e)
  (Q : RationalFilteredNilmanifold
    ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n)
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

noncomputable def SingleRefilteredRecoveryFamily (p : ℝ) (q k : ℕ) (cost : ℝ) : Prop :=
  let H := D.filtration.gradedRefiltrationSubalgebra W
  let N := H ⧸ E.filtration.layerIdeal (s + 1)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] N)
  let := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] N)
  let := realification_moduleTopology_t2 Q.basis
  let T := Q.raiseStep (Nat.le_succ s)
  ∃ Λ : Subgroup T.filtration.Group, Λ ≤ T.lattice ∧
    (Λ.subgroupOf T.lattice).Characteristic ∧ (Λ.subgroupOf T.lattice).Normal ∧
    (Λ.subgroupOf T.lattice).FiniteIndex ∧ (Λ.relIndex T.lattice : ℝ) ≤ Real.exp cost ∧
    ∃ (B : ℕ) (hB : 0 < B)
      (hin : scaledIntegerGrid B ⊆ bchSubgroupCoordinates Q.basis Λ)
      (hout : bchSubgroupCoordinates Q.basis Λ ⊆ denominatorGrid B),
      let V := Q.loweredCover (Nat.le_succ s) Λ B hB hin hout
      V.filtration = Q.filtration ∧ V.lattice ≤ Q.lattice ∧
      V.GeometryComplexityLE cost ∧
      ∀ l r : D.RealGroup,
        (∀ i, |(D.basis.baseChange ℝ).repr l.coord i| ≤ Real.exp ((p + 2) ^ k)) →
        (D.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid q →
        ∀ (S : D.Space → ℂ) (ℓ : ℝ≥0), (ℓ : ℝ) ≤ Real.exp p →
          (let := D.metricSpace; LipschitzWith ℓ S) →
          (∀ x, (S x).im = 0 ∧ 0 ≤ (S x).re ∧ (S x).re ≤ 1) →
          (∀ z : D.RealGroup, z.coord ∈ D.filtration.realGradedRefiltrationLayer W (s + 1) →
            ∀ x, S (z • x) = S x) →
          ∃ (v : V.Space → ℂ) (K : ℝ≥0),
            (K : ℝ) ≤ Real.exp cost ∧ (let := V.metricSpace; LipschitzWith K v) ∧
            (∀ x, (v x).im = 0 ∧ 0 ≤ (v x).re ∧ (v x).re ≤ 1) ∧ (∀ x, ‖v x‖ ≤ 1) ∧
            ∀ x : E.RealGroup,
              v (QuotientGroup.mk (realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
                (hM := V.filtration.lowerCentralSeries_eq_bot)
                (lieQuotientMap (E.filtration.layerIdeal (s + 1))) x)) =
              S (QuotientGroup.mk (l * realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
                (hM := D.filtration.lowerCentralSeries_eq_bot) H.incl x * r))

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct NNReal

def FixedPositiveNiltestRealization {σ K : Type*} [LieRing K] [LieAlgebra ℚ K]
    [TopologicalSpace (ℝ ⊗[ℚ] K)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] K)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] K)] [T2Space (ℝ ⊗[ℚ] K)] {t d : ℕ}
    (V : RationalFilteredNilmanifold K t d) {w : σ → ℕ}
    (g : V.filtration.realification.PolynomialOrbit w) (cost : ℝ) (f : (σ → ℤ) → ℂ) : Prop :=
  ∃ U : V.Niltest w, U.orbit = g ∧ U.UnitIntervalValued ∧ U.ComplexityLE cost ∧
    ∀ x, U.eval x = f x

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct BigOperators

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastInactiveSlicedFixedScalarCapBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option Empty → ZMod q)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hcell : 0 < (principalTupleWeights (α := Empty) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

variable (Hchild : ℕ)

local notation "height" => basisAxisScale (basis j) i
local notation "degree" => Fin.val j + 1
local notation "denom" => inactiveDenominator
  (principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i)))
local notation "side" => inactiveSideLength degree height denom
local notation "cost" => (denom : ℝ) * 2 ^ degree
local notation "radius" => blockJetScaleBound (Fintype.card Empty) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 1
local notation "torus" => blockTorusFactor (Fintype.card Empty) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 1

def slicedFixedZeroGeometryLog {A : Type*} [Semiring A]
    (D v w vq vchild : A) : A :=
  slicedGridGeometryLog D v w (vq + w + 1) +
    (2 * (D + v + 8) + D * (vchild + 1) + 4)

theorem slicedFixedZeroGeometryLog_nonneg {D v w vq vchild : ℝ}
    (hD : 0 ≤ D) (hv : 0 ≤ v) (hw : 0 ≤ w) (hvq : 0 ≤ vq) (hvc : 0 ≤ vchild) :
    0 ≤ slicedFixedZeroGeometryLog D v w vq vchild := by
  unfold slicedFixedZeroGeometryLog slicedGridGeometryLog
  positivity

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option Empty → ZMod q)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hcell : 0 < (principalTupleWeights (α := Empty) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

local notation "height" => basisAxisScale (basis j) i
local notation "degree" => Fin.val j + 1
local notation "denom" => inactiveDenominator
  (principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i)))
local notation "side" => inactiveSideLength degree height denom
local notation "cost" => (denom : ℝ) * 2 ^ degree
local notation "radius" => blockJetScaleBound (Fintype.card Empty) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 1
local notation "torus" => blockTorusFactor (Fintype.card Empty) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 1

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastInactiveSlicedCappedContinuousSource
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {A : Type*} [Fintype A]

noncomputable def forecastInactiveSlicedSiteNumerics
    (selected : A → Σ j : Fin m, Fin (n j)) (q Hchild : ℕ)
    (δ P Cactual δout Q Nt Vt Ct Ht : ℝ) (Lt : ℝ≥0) : Prop :=
    let degree := fun a => (selected a).1.val + 1
    let denom := fun a => inactiveDenominator (principalProfileSize (R (selected a).1)
      (Finset.card (layerIntegerPrincipalSlots (G := G) B (selected a).1 (selected a).2)))
    let torus := fun a => blockTorusFactor (Fintype.card Empty) (degree a)
      (Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩)) 1
    let V := fun a => (torus a : ℝ) * ((denom a : ℝ) * 2 ^ degree a) / δ ^ degree a
    let cap := fun a => uniformSpectrumAbsoluteCap (selected a).1.val 1 (degree a) P (V a) (V a)
    let cutoff := fun a => max (allocatedSlicedGridHeightCutoff (G := G) B (R := R)
      (selected a).1 (selected a).2 (Nat.ceil ((q : ℝ) / δ)))
      (denom a * 2 ^ degree a * Hchild ^ degree a + 2 * denom a)
    let R0 := fun a => (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (degree a)) : ℝ) *
      R (selected a).1
    let ε := uniformProductAccuracy (Fintype.card A) Cactual δout / 2
    let ζ := fun a => uniformBlockRetainedBias (selected a).1.val 1 (degree a) P (V a) (V a) ε
    let freq := fun a => Real.toNNReal (uniformScaledRetainedFrequencyBound (selected a).1.val 1 P (V a) (ζ a))
    (∀ a, max (cutoff a : ℝ) (cap a) ≤ Cactual) ∧
    (∀ a, R0 a + 1 / 4 ≤ Real.exp Q) ∧
    (∀ a, (ε / (cap a + 1))⁻¹ ≤ Real.exp Q) ∧
    (∀ a, (CircleFourier.characterLipConstant * freq a + 4 : ℝ≥0) ≤ Real.exp Q) ∧
    (∀ a, (cutoff a : ℝ) ≤ Real.exp Q) ∧
    (∀ a, (2 * (cutoff a : ℝ≥0) ^ 2 * (cutoff a : ℝ≥0) : ℝ≥0) ≤ Real.exp Q) ∧
    ε⁻¹ ≤ Real.exp Q ∧
    (∀ a, max ((uniformSpectrumSizeConstant (selected a).1.val 1 (degree a) P (V a) (V a) /
      ε ^ max (majorArcSpectrumExponent (selected a).1.val 1)
        (majorArcLengthExponent (selected a).1.val * degree a)) * Real.exp (4 * Q + 8))
      (Real.exp (4 * Q + 8)) ≤ Nt) ∧
    (∀ a, max (uniformScaledRetainedDenominatorBound (selected a).1.val 1 (degree a) P
      (V a) (V a) (ζ a)) 1 ≤ Vt) ∧
    (∀ a, max (cap a * Real.exp (4 * Q + 8 + Q)) (Real.exp (4 * Q + 8 + Q)) ≤ Ct) ∧
    (⟨Real.exp (1 + 6 * Q + 12), Real.exp_nonneg _⟩ + 4 : ℝ≥0) ≤ Lt ∧
    (∀ a, R0 a + 1 / 4 ≤ Ht)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable {A : Type*} [Fintype A]

variable {Vact Out : Type*} [Fintype Vact] [DecidableEq Vact] [Fintype Out] [DecidableEq Out]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal

def slicedFixedUniformSiteLog (m : ℕ) (p E : ℝ) : ℝ :=
  p + E + 1 + ∑ j : Fin m, slicedGridSiteLog j.val 1 (j.val + 1) (j.val + 1) 1 p E

theorem slicedFixedUniformSiteLog_nonneg (m : ℕ) {p E : ℝ} (hp : 0 ≤ p) (hE : 0 ≤ E) :
    0 ≤ slicedFixedUniformSiteLog m p E := by
  unfold slicedFixedUniformSiteLog
  have hs : 0 ≤ ∑ j : Fin m, slicedGridSiteLog j.val 1 (j.val + 1) (j.val + 1) 1 p E :=
    Finset.sum_nonneg (fun j _ => (slicedGridSiteLog_bounds j.val 1 (j.val + 1) (j.val + 1)
      (by norm_num : (0 : ℝ) ≤ 1) hp hE).1)
  positivity

def slicedFixedUniformAccuracyLog (m : ℕ) (D p E : ℝ) : ℝ :=
  uniformProductAccuracyLog D (slicedFixedUniformSiteLog m p 0) E + 1

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {R : Fin m → ℝ} {A : Type*} [Fintype A]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable {A : Type*} [Fintype A]

variable {Vact Out : Type*} [Fintype Vact] [DecidableEq Vact] [Fintype Out] [DecidableEq Out]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {R : Fin m → ℝ} {A : Type*} [Fintype A]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable {A : Type*} [Fintype A]

variable {Vact Out : Type*} [Fintype Vact] [DecidableEq Vact] [Fintype Out] [DecidableEq Out]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable {A : Type*} [Fintype A]

variable {Vact Out : Type*} [Fintype Vact] [DecidableEq Vact] [Fintype Out] [DecidableEq Out]

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

@[gcongr] theorem majorArcBiasLog_mono_budget (n : ℕ) {p p₂ : ℝ}
    (hp : p ≤ p₂) :
    majorArcBiasLog n p ≤ majorArcBiasLog n p₂ := by
  unfold majorArcBiasLog
  gcongr

@[gcongr] theorem majorArcLocalizationLog_mono_budget (n : ℕ) {p p₂ : ℝ}
    (hp : p ≤ p₂) :
    majorArcLocalizationLog n p ≤ majorArcLocalizationLog n p₂ := by
  unfold majorArcLocalizationLog
  gcongr

@[gcongr] theorem majorArcLengthLog_mono_budget (n : ℕ) {p p₂ : ℝ}
    (hp : p ≤ p₂) :
    majorArcLengthLog n p ≤ majorArcLengthLog n p₂ := by
  unfold majorArcLengthLog
  gcongr

@[gcongr] theorem majorArcErrorLog_mono_budget (n : ℕ) {p p₂ : ℝ}
    (hp : p ≤ p₂) :
    majorArcErrorLog n p ≤ majorArcErrorLog n p₂ := by
  unfold majorArcErrorLog
  gcongr

@[gcongr] theorem majorArcCoverLog_mono_budget (n j : ℕ) {p v p₂ v₂ : ℝ}
    (hp : p ≤ p₂) (hv : v ≤ v₂) :
    majorArcCoverLog n j p v ≤ majorArcCoverLog n j p₂ v₂ := by
  unfold majorArcCoverLog
  gcongr

@[gcongr] theorem positiveModerateLengthLog_mono_budget (n : ℕ) {p p₂ : ℝ}
    (hp : p ≤ p₂) :
    positiveModerateLengthLog n p ≤ positiveModerateLengthLog n p₂ := by
  unfold positiveModerateLengthLog
  gcongr

@[gcongr] theorem positiveModerateCoverLog_mono_budget (n j : ℕ) {p v p₂ v₂ : ℝ}
    (hp : p ≤ p₂) (hv : v ≤ v₂) :
    positiveModerateCoverLog n j p v ≤ positiveModerateCoverLog n j p₂ v₂ := by
  unfold positiveModerateCoverLog
  gcongr

@[gcongr] theorem positiveModerateSpectrumLog_mono_budget (n j : ℕ) {p v p₂ v₂ : ℝ}
    (hp : p ≤ p₂) (hv : v ≤ v₂) :
    positiveModerateSpectrumLog n j p v ≤ positiveModerateSpectrumLog n j p₂ v₂ := by
  unfold positiveModerateSpectrumLog
  gcongr

@[gcongr] theorem positiveModerateAccuracyLog_mono_budget (n j t : ℕ) {p v w p₂ v₂ w₂ : ℝ}
    (hp : p ≤ p₂) (hv : v ≤ v₂) (hw : w ≤ w₂) :
    positiveModerateAccuracyLog n j t p v w ≤ positiveModerateAccuracyLog n j t p₂ v₂ w₂ := by
  unfold positiveModerateAccuracyLog
  gcongr

@[gcongr] theorem positiveRetainedBiasLog_mono_budget (n j t : ℕ) {p v w E p₂ v₂ w₂ E₂ : ℝ}
    (hp : p ≤ p₂) (hv : v ≤ v₂) (hw : w ≤ w₂) (hE : E ≤ E₂) :
    positiveRetainedBiasLog n j t p v w E ≤ positiveRetainedBiasLog n j t p₂ v₂ w₂ E₂ := by
  unfold positiveRetainedBiasLog
  gcongr

@[gcongr] theorem positiveSpectrumCardLog_mono_budget (n j t : ℕ) {p v w E p₂ v₂ w₂ E₂ : ℝ}
    (hp : p ≤ p₂) (hv : v ≤ v₂) (hw : w ≤ w₂) (hE : E ≤ E₂) :
    positiveSpectrumCardLog n j t p v w E ≤ positiveSpectrumCardLog n j t p₂ v₂ w₂ E₂ := by
  unfold positiveSpectrumCardLog
  gcongr

@[gcongr] theorem positiveRetainedFrequencyLog_mono_budget (n j t : ℕ) {p v w E p₂ v₂ w₂ E₂ : ℝ}
    (hp : p ≤ p₂) (hv : v ≤ v₂) (hw : w ≤ w₂) (hE : E ≤ E₂) :
    positiveRetainedFrequencyLog n j t p v w E ≤ positiveRetainedFrequencyLog n j t p₂ v₂ w₂ E₂ := by
  unfold positiveRetainedFrequencyLog
  gcongr

@[gcongr] theorem positiveRetainedDenominatorLog_mono_budget (n j t : ℕ) {p v w E p₂ v₂ w₂ E₂ : ℝ}
    (hp : p ≤ p₂) (hv : v ≤ v₂) (hw : w ≤ w₂) (hE : E ≤ E₂) :
    positiveRetainedDenominatorLog n j t p v w E ≤ positiveRetainedDenominatorLog n j t p₂ v₂ w₂ E₂ := by
  unfold positiveRetainedDenominatorLog
  gcongr

@[gcongr] theorem positiveRetainedComplexityLog_mono_budget (n j t : ℕ) {p v w E p₂ v₂ w₂ E₂ : ℝ}
    (hp : p ≤ p₂) (hv : v ≤ v₂) (hw : w ≤ w₂) (hE : E ≤ E₂) :
    positiveRetainedComplexityLog n j t p v w E ≤ positiveRetainedComplexityLog n j t p₂ v₂ w₂ E₂ := by
  unfold positiveRetainedComplexityLog
  gcongr

@[gcongr] theorem majorArcSpectrumLog_mono_budget (n j : ℕ) {p v p₂ v₂ : ℝ}
    (hp : p ≤ p₂) (hv : v ≤ v₂) :
    majorArcSpectrumLog n j p v ≤ majorArcSpectrumLog n j p₂ v₂ := by
  unfold majorArcSpectrumLog
  gcongr

@[gcongr] theorem uniformBlockAccuracyLog_mono_budget (n j t : ℕ) {p v w p₂ v₂ w₂ : ℝ}
    (hp : p ≤ p₂) (hv : v ≤ v₂) (hw : w ≤ w₂) :
    uniformBlockAccuracyLog n j t p v w ≤ uniformBlockAccuracyLog n j t p₂ v₂ w₂ := by
  unfold uniformBlockAccuracyLog
  gcongr

@[gcongr] theorem uniformSpectrumSizeLog_mono_budget (n j t : ℕ) {p v w p₂ v₂ w₂ : ℝ}
    (hp : p ≤ p₂) (hv : v ≤ v₂) (hw : w ≤ w₂) :
    uniformSpectrumSizeLog n j t p v w ≤ uniformSpectrumSizeLog n j t p₂ v₂ w₂ := by
  unfold uniformSpectrumSizeLog
  gcongr

@[gcongr] theorem uniformRetainedBiasLog_mono_budget (n j t : ℕ) {p v w E p₂ v₂ w₂ E₂ : ℝ}
    (hp : p ≤ p₂) (hv : v ≤ v₂) (hw : w ≤ w₂) (hE : E ≤ E₂) :
    uniformRetainedBiasLog n j t p v w E ≤ uniformRetainedBiasLog n j t p₂ v₂ w₂ E₂ := by
  unfold uniformRetainedBiasLog
  gcongr

@[gcongr] theorem uniformSpectrumCardLog_mono_budget (n j t : ℕ) {p v w E p₂ v₂ w₂ E₂ : ℝ}
    (hp : p ≤ p₂) (hv : v ≤ v₂) (hw : w ≤ w₂) (hE : E ≤ E₂) :
    uniformSpectrumCardLog n j t p v w E ≤ uniformSpectrumCardLog n j t p₂ v₂ w₂ E₂ := by
  unfold uniformSpectrumCardLog
  gcongr

@[gcongr] theorem uniformRetainedFrequencyLog_mono_budget (n j t : ℕ) {p v w E p₂ v₂ w₂ E₂ : ℝ}
    (hp : p ≤ p₂) (hv : v ≤ v₂) (hw : w ≤ w₂) (hE : E ≤ E₂) :
    uniformRetainedFrequencyLog n j t p v w E ≤ uniformRetainedFrequencyLog n j t p₂ v₂ w₂ E₂ := by
  unfold uniformRetainedFrequencyLog
  gcongr

@[gcongr] theorem uniformRetainedDenominatorLog_mono_budget (n j t : ℕ) {p v w E p₂ v₂ w₂ E₂ : ℝ}
    (hp : p ≤ p₂) (hv : v ≤ v₂) (hw : w ≤ w₂) (hE : E ≤ E₂) :
    uniformRetainedDenominatorLog n j t p v w E ≤ uniformRetainedDenominatorLog n j t p₂ v₂ w₂ E₂ := by
  unfold uniformRetainedDenominatorLog
  gcongr

theorem slicedGridSiteLog_mono (n d ta ti : ℕ) {D p E D' p' E' : ℝ}
    (hD : 0 ≤ D) (hp : 0 ≤ p) (_hE : 0 ≤ E)
    (hDD : D ≤ D') (hpp : p ≤ p') (hEE : E ≤ E') :
    slicedGridSiteLog n d ta ti D p E ≤ slicedGridSiteLog n d ta ti D' p' E' := by
  unfold slicedGridSiteLog
  gcongr
  linarith

theorem slicedGridSiteLog_eval (n d ta ti : ℕ) (D p E : Polynomial ℕ) (x : ℝ) :
    (slicedGridSiteLog n d ta ti D p E).eval₂ (Nat.castRingHom ℝ) x =
      slicedGridSiteLog n d ta ti (D.eval₂ (Nat.castRingHom ℝ) x)
        (p.eval₂ (Nat.castRingHom ℝ) x) (E.eval₂ (Nat.castRingHom ℝ) x) := by
  simp [slicedGridSiteLog, positiveRetainedComplexityLog, positiveRetainedDenominatorLog, positiveSpectrumCardLog, positiveRetainedFrequencyLog, positiveRetainedBiasLog, positiveModerateAccuracyLog, positiveModerateSpectrumLog, positiveModerateCoverLog, positiveModerateLengthLog, uniformSpectrumCardLog, uniformRetainedFrequencyLog, uniformRetainedDenominatorLog, uniformRetainedBiasLog, uniformSpectrumSizeLog, uniformBlockAccuracyLog, majorArcSpectrumLog, majorArcCoverLog, majorArcErrorLog, majorArcLengthLog, majorArcLocalizationLog, majorArcBiasLog, Polynomial.eval₂_pow]

theorem exists_slicedGridSiteLog_uniform_budget (m dim : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {D p E : ℝ}, 0 ≤ D → 0 ≤ p → 0 ≤ E → ∀ j : Fin m,
      slicedGridSiteLog j.val (boundedBooleanJetRows (Fin dim) (j.val + 1)).card
        ((layerTailDegree m + 1) * (boundedBooleanJetRows (Fin dim) (j.val + 1)).card)
        ((j.val + 1) * (boundedBooleanJetRows (Fin dim) (j.val + 1)).card) D p E ≤
        (D + p + E + A) ^ A := by
  classical
  let Lj := fun (j : Fin m) (D p E : Polynomial ℕ) => slicedGridSiteLog j.val
    (boundedBooleanJetRows (Fin dim) (j.val + 1)).card
    ((layerTailDegree m + 1) * (boundedBooleanJetRows (Fin dim) (j.val + 1)).card)
    ((j.val + 1) * (boundedBooleanJetRows (Fin dim) (j.val + 1)).card) D p E
  let poly := ∑ j : Fin m, Lj j Polynomial.X Polynomial.X Polynomial.X
  obtain ⟨A, hA, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨A, hA, ?_⟩
  intro D p E hD hp hE j
  let R := D + p + E
  have hR : 0 ≤ R := by dsimp [R]; positivity
  apply (slicedGridSiteLog_mono _ _ _ _ hD hp hE
    (by dsimp [R]; linarith : D ≤ R) (by dsimp [R]; linarith : p ≤ R)
    (by dsimp [R]; linarith : E ≤ R)).trans
  apply le_trans ?_ (hbound R hR)
  have heval (j : Fin m) : (Lj j Polynomial.X Polynomial.X Polynomial.X).eval₂ (Nat.castRingHom ℝ) R =
      slicedGridSiteLog j.val (boundedBooleanJetRows (Fin dim) (j.val + 1)).card
        ((layerTailDegree m + 1) * (boundedBooleanJetRows (Fin dim) (j.val + 1)).card)
        ((j.val + 1) * (boundedBooleanJetRows (Fin dim) (j.val + 1)).card) R R R := by
    simp only [Lj, slicedGridSiteLog_eval, Polynomial.eval₂_X]
  simp only [poly, Polynomial.eval₂_finsetSum, heval]
  apply Finset.single_le_sum ?_ (Finset.mem_univ j)
  intro i _
  exact (slicedGridSiteLog_bounds _ _ _ _ hR hR hR).1

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

theorem slicedFixedZeroGeometryLog_mono
    {D v w vq vchild D' v' w' vq' vchild' : ℝ}
    (hD0 : 0 ≤ D) (hv0 : 0 ≤ v) (hw0 : 0 ≤ w)
    (hvq0 : 0 ≤ vq) (hvc0 : 0 ≤ vchild)
    (hD : D ≤ D') (hv : v ≤ v') (hw : w ≤ w')
    (hvq : vq ≤ vq') (hvc : vchild ≤ vchild') :
    slicedFixedZeroGeometryLog D v w vq vchild ≤
      slicedFixedZeroGeometryLog D' v' w' vq' vchild' := by
  have hD'0 : 0 ≤ D' := hD0.trans hD
  unfold slicedFixedZeroGeometryLog slicedGridGeometryLog
  gcongr

theorem slicedFixedZeroGeometryLog_eval₂
    (D v w vq vchild : Polynomial ℕ) (x : ℝ) :
    (slicedFixedZeroGeometryLog D v w vq vchild).eval₂ (Nat.castRingHom ℝ) x =
      slicedFixedZeroGeometryLog (D.eval₂ (Nat.castRingHom ℝ) x)
        (v.eval₂ (Nat.castRingHom ℝ) x) (w.eval₂ (Nat.castRingHom ℝ) x)
        (vq.eval₂ (Nat.castRingHom ℝ) x) (vchild.eval₂ (Nat.castRingHom ℝ) x) := by
  simp [slicedFixedZeroGeometryLog, slicedGridGeometryLog, Polynomial.eval₂_pow]

end Erdos3.VectorPolynomial

namespace Erdos3

theorem uniformProductAccuracyLog_mono {D T E D' T' E' : ℝ}
    (hD0 : 0 ≤ D) (hT0 : 0 ≤ T)
    (hD : D ≤ D') (hT : T ≤ T') (hE : E ≤ E') :
    uniformProductAccuracyLog D T E ≤ uniformProductAccuracyLog D' T' E' := by
  have hD'0 : 0 ≤ D' := hD0.trans hD
  unfold uniformProductAccuracyLog
  gcongr

theorem uniformProductAccuracyLog_eval₂ (D T E : Polynomial ℕ) (x : ℝ) :
    (uniformProductAccuracyLog D T E).eval₂ (Nat.castRingHom ℝ) x =
      uniformProductAccuracyLog (D.eval₂ (Nat.castRingHom ℝ) x)
        (T.eval₂ (Nat.castRingHom ℝ) x) (E.eval₂ (Nat.castRingHom ℝ) x) := by
  simp [uniformProductAccuracyLog]

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

noncomputable def slicedFixedUniformSitePolynomial (m : ℕ) (p E : Polynomial ℕ) : Polynomial ℕ :=
  p + E + 1 + ∑ j : Fin m, slicedGridSiteLog j.val 1 (j.val + 1) (j.val + 1) 1 p E

theorem slicedFixedUniformSitePolynomial_eval (m : ℕ) (p E : Polynomial ℕ) (x : ℝ) :
    (slicedFixedUniformSitePolynomial m p E).eval₂ (Nat.castRingHom ℝ) x =
      slicedFixedUniformSiteLog m (p.eval₂ (Nat.castRingHom ℝ) x) (E.eval₂ (Nat.castRingHom ℝ) x) := by
  simp only [slicedFixedUniformSitePolynomial, slicedFixedUniformSiteLog,
    Polynomial.eval₂_add, Polynomial.eval₂_one, Polynomial.eval₂_finsetSum, slicedGridSiteLog_eval]

theorem slicedFixedUniformSiteLog_mono (m : ℕ) {p E p' E' : ℝ}
    (hp : 0 ≤ p) (hE : 0 ≤ E) (hpp : p ≤ p') (hEE : E ≤ E') :
    slicedFixedUniformSiteLog m p E ≤ slicedFixedUniformSiteLog m p' E' := by
  unfold slicedFixedUniformSiteLog
  apply add_le_add (add_le_add (add_le_add hpp hEE) le_rfl)
  apply Finset.sum_le_sum
  intro j _
  exact slicedGridSiteLog_mono _ _ _ _ zero_le_one hp hE le_rfl hpp hEE

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

def forecastSlicedEarlyDiagonalBudget (m : ℕ) (r : ℝ) : ℝ :=
  let pTailAll := r + slicedFixedZeroGeometryLog r r r 0 r
  let tailLog := slicedFixedUniformSiteLog m pTailAll 0
  let Pin := r * tailLog
  let Pdec := (r + r) * (r + 2) * modularRankChargeFactor m
  let V := Pin + Pdec + (r + r) + 3
  let Esite := r + r + 1 + r * V
  let pAll := (r + V) + slicedFixedZeroGeometryLog r r r V r
  let Eprod := slicedFixedUniformAccuracyLog m r pAll Esite
  let Q := slicedFixedUniformSiteLog m pAll Eprod
  let O := siteExponentialOutputLog 1 Q
  let Pperiod := V + r * O
  let Pfactor := r + r + O + 1 + r
  let Pnative := Pperiod + Pfactor + r + r + 1
  let Pmass := r + r * V + r * O + 1
  let Pcap := r + Pin + Pdec + 1
  Pnative + Pmass + Pcap

noncomputable def forecastSlicedEarlyPolynomial (m : ℕ) : Polynomial ℕ :=
  let r : Polynomial ℕ := Polynomial.X
  let pTailAll := r + slicedFixedZeroGeometryLog r r r 0 r
  let tailLog := slicedFixedUniformSitePolynomial m pTailAll 0
  let Pin := r * tailLog
  let Pdec := (r + r) * (r + 2) * Polynomial.C (modularRankChargeFactor m)
  let V := Pin + Pdec + (r + r) + 3
  let Esite := r + r + 1 + r * V
  let pAll := (r + V) + slicedFixedZeroGeometryLog r r r V r
  let Eprod := uniformProductAccuracyLog r (slicedFixedUniformSitePolynomial m pAll 0) Esite + 1
  let Q := slicedFixedUniformSitePolynomial m pAll Eprod
  let O := siteExponentialOutputLog 1 Q
  let Pperiod := V + r * O
  let Pfactor := r + r + O + 1 + r
  let Pnative := Pperiod + Pfactor + r + r + 1
  let Pmass := r + r * V + r * O + 1
  let Pcap := r + Pin + Pdec + 1
  Pnative + Pmass + Pcap

theorem forecastSlicedEarlyPolynomial_eval (m : ℕ) (r : ℝ) :
    (forecastSlicedEarlyPolynomial m).eval₂ (Nat.castRingHom ℝ) r =
      forecastSlicedEarlyDiagonalBudget m r := by
  have hcast (k : ℕ) : (Nat.castRingHom ℝ) k = (k : ℝ) := rfl
  simp only [forecastSlicedEarlyPolynomial, forecastSlicedEarlyDiagonalBudget,
    Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_X,
    Polynomial.eval₂_C, Polynomial.eval₂_zero, Polynomial.eval₂_one, Polynomial.eval₂_ofNat,
    slicedFixedZeroGeometryLog_eval₂, slicedFixedUniformSitePolynomial_eval,
    uniformProductAccuracyLog_eval₂, slicedFixedUniformAccuracyLog,
    siteExponentialOutputLog, hcast, Polynomial.eval₂_natCast]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open VectorPolynomial

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial

theorem forecastSlicedEarlyLogs_le_diagonal_of_dimensions (m Dmod d : ℕ) {r : ℝ} (hr : 0 ≤ r)
    {D ptail v w vchild Psm Plip Pbad Ppres E Pspatial Pcoord Pcut : ℝ}
    (hD : 0 ≤ D ∧ D ≤ r)
    (htail : 0 ≤ ptail ∧ ptail ≤ r)
    (hv : 0 ≤ v ∧ v ≤ r)
    (hw : 0 ≤ w ∧ w ≤ r)
    (hchild : 0 ≤ vchild ∧ vchild ≤ r)
    (hsm : 0 ≤ Psm ∧ Psm ≤ r)
    (hlip : 0 ≤ Plip ∧ Plip ≤ r)
    (hbad : 0 ≤ Pbad ∧ Pbad ≤ r)
    (hpres : 0 ≤ Ppres ∧ Ppres ≤ r)
    (hE : 0 ≤ E ∧ E ≤ r)
    (hspatial : 0 ≤ Pspatial ∧ Pspatial ≤ r)
    (hcoord : 0 ≤ Pcoord ∧ Pcoord ≤ r)
    (hcut : 0 ≤ Pcut ∧ Pcut ≤ r)
    (hDmod : (Dmod : ℝ) ≤ r) (hd : (d : ℝ) ≤ r) :
    let pTailAll := ptail + VectorPolynomial.slicedFixedZeroGeometryLog D v w 0 vchild
    let tailLog := VectorPolynomial.slicedFixedUniformSiteLog m pTailAll 0
    let Pin := D * tailLog
    let Pdec := (Pbad + Ppres) * ((Dmod + 2 : ℕ) : ℝ) * modularRankChargeFactor m
    let V := Pin + Pdec + (E + Psm) + 3
    let Esite := E + Psm + 1 + d * V
    let psite := ptail + V
    let pAll := psite + VectorPolynomial.slicedFixedZeroGeometryLog D v w V vchild
    let Eprod := VectorPolynomial.slicedFixedUniformAccuracyLog m D pAll Esite
    let Q := VectorPolynomial.slicedFixedUniformSiteLog m pAll Eprod
    let O := siteExponentialOutputLog 1 Q
    let Pperiod := V + D * O
    let Pfactor := Plip + D + O + 1 + Pspatial
    let Pnative := Pperiod + Pfactor + Pcoord + Pcut + 1
    let Pmass := Psm + d * V + D * O + 1
    let Pcap := Psm + Pin + Pdec + 1
    0 ≤ Pnative ∧ 0 ≤ Pmass ∧ 0 ≤ Pcap ∧
      Pnative + Pmass + Pcap ≤ forecastSlicedEarlyDiagonalBudget m r := by
  intro pTailAll tailLog Pin Pdec V Esite psite pAll Eprod Q O Pperiod Pfactor Pnative Pmass Pcap
  have hDNonneg := hD.1
  have htailNonneg := htail.1
  have hvNonneg := hv.1
  have hwNonneg := hw.1
  have hchildNonneg := hchild.1
  have hsmNonneg := hsm.1
  have hlipNonneg := hlip.1
  have hbadNonneg := hbad.1
  have hpresNonneg := hpres.1
  have hENonneg := hE.1
  have hspatialNonneg := hspatial.1
  have hcoordNonneg := hcoord.1
  have hcutNonneg := hcut.1
  let rTail := r + slicedFixedZeroGeometryLog r r r 0 r
  let rLog := slicedFixedUniformSiteLog m rTail 0
  let rIn := r * rLog
  let rDec := (r + r) * (r + 2) * modularRankChargeFactor m
  let rV := rIn + rDec + (r + r) + 3
  let rEsite := r + r + 1 + r * rV
  let rAll := (r + rV) + slicedFixedZeroGeometryLog r r r rV r
  let rProd := slicedFixedUniformAccuracyLog m r rAll rEsite
  let rQ := slicedFixedUniformSiteLog m rAll rProd
  let rO := siteExponentialOutputLog 1 rQ
  let rPeriod := rV + r * rO
  let rFactor := r + r + rO + 1 + r
  let rNative := rPeriod + rFactor + r + r + 1
  let rMass := r + r * rV + r * rO + 1
  let rCap := r + rIn + rDec + 1
  have htail0 : 0 ≤ pTailAll := add_nonneg htail.1
    (slicedFixedZeroGeometryLog_nonneg hD.1 hv.1 hw.1 (le_refl 0) hchild.1)
  have hlog0 : 0 ≤ tailLog := slicedFixedUniformSiteLog_nonneg m htail0 (le_refl 0)
  have hin0 : 0 ≤ Pin := mul_nonneg hD.1 hlog0
  have hdec0 : 0 ≤ Pdec := by dsimp only [Pdec]; positivity
  have hV0 : 0 ≤ V := by dsimp only [V]; positivity
  have hEs0 : 0 ≤ Esite := by dsimp only [Esite]; positivity
  have hsite0 : 0 ≤ psite := add_nonneg htail.1 hV0
  have hAll0 : 0 ≤ pAll := add_nonneg hsite0
    (slicedFixedZeroGeometryLog_nonneg hD.1 hv.1 hw.1 hV0 hchild.1)
  have hcap0 : 0 ≤ slicedFixedUniformSiteLog m pAll 0 := slicedFixedUniformSiteLog_nonneg m hAll0 (le_refl 0)
  have hprod0 : 0 ≤ Eprod := add_nonneg
    (uniformProductAccuracyLog_nonneg hD.1 hcap0 hEs0) zero_le_one
  have hQ0 : 0 ≤ Q := slicedFixedUniformSiteLog_nonneg m hAll0 hprod0
  have hO0 : 0 ≤ O := siteExponentialOutputLog_nonneg 1 hQ0
  have hperiod0 : 0 ≤ Pperiod := add_nonneg hV0 (mul_nonneg hD.1 hO0)
  have hfactor0 : 0 ≤ Pfactor := by dsimp only [Pfactor]; positivity
  have hnative0 : 0 ≤ Pnative := by dsimp only [Pnative]; positivity
  have hmass0 : 0 ≤ Pmass := by dsimp only [Pmass]; positivity
  have hcapFin0 : 0 ≤ Pcap := by dsimp only [Pcap]; positivity
  have htailR : pTailAll ≤ rTail := add_le_add htail.2
    (slicedFixedZeroGeometryLog_mono hD.1 hv.1 hw.1 (le_refl 0) hchild.1
      hD.2 hv.2 hw.2 le_rfl hchild.2)
  have hlogR : tailLog ≤ rLog := slicedFixedUniformSiteLog_mono m htail0 (le_refl 0) htailR le_rfl
  have hinR : Pin ≤ rIn := mul_le_mul hD.2 hlogR hlog0 hr
  have hdecR : Pdec ≤ rDec := by
    dsimp only [Pdec, rDec]
    simp only [Nat.cast_add, Nat.cast_ofNat]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (add_le_add hbad.2 hpres.2) (add_le_add hDmod le_rfl)
        (by positivity) (by positivity)) (Nat.cast_nonneg _)
  have hVR : V ≤ rV := add_le_add
    (add_le_add (add_le_add hinR hdecR) (add_le_add hE.2 hsm.2)) le_rfl
  have hrV : 0 ≤ rV := hV0.trans hVR
  have hEsR : Esite ≤ rEsite := add_le_add
    (add_le_add (add_le_add hE.2 hsm.2) le_rfl)
    (mul_le_mul hd hVR hV0 hr)
  have hAllR : pAll ≤ rAll := add_le_add (add_le_add htail.2 hVR)
    (slicedFixedZeroGeometryLog_mono hD.1 hv.1 hw.1 hV0 hchild.1
      hD.2 hv.2 hw.2 hVR hchild.2)
  have hprodR : Eprod ≤ rProd := add_le_add
    (uniformProductAccuracyLog_mono hD.1 hcap0 hD.2
      (slicedFixedUniformSiteLog_mono m hAll0 (le_refl 0) hAllR le_rfl) hEsR) le_rfl
  have hQR : Q ≤ rQ := slicedFixedUniformSiteLog_mono m hAll0 hprod0 hAllR hprodR
  have hOR : O ≤ rO := by
    dsimp only [O, rO, siteExponentialOutputLog]
    gcongr
  have hrO : 0 ≤ rO := hO0.trans hOR
  have hperiodR : Pperiod ≤ rPeriod := add_le_add hVR (mul_le_mul hD.2 hOR hO0 hr)
  have hfactorR : Pfactor ≤ rFactor := add_le_add
    (add_le_add (add_le_add (add_le_add hlip.2 hD.2) hOR) le_rfl) hspatial.2
  have hnativeR : Pnative ≤ rNative := add_le_add
    (add_le_add (add_le_add (add_le_add hperiodR hfactorR) hcoord.2) hcut.2) le_rfl
  have hmassR : Pmass ≤ rMass := add_le_add
    (add_le_add (add_le_add hsm.2 (mul_le_mul hd hVR hV0 hr))
      (mul_le_mul hD.2 hOR hO0 hr)) le_rfl
  have hcapR : Pcap ≤ rCap := add_le_add (add_le_add (add_le_add hsm.2 hinR) hdecR) le_rfl
  refine ⟨hnative0, hmass0, hcapFin0, ?_⟩
  change Pnative + Pmass + Pcap ≤ rNative + rMass + rCap
  exact add_le_add (add_le_add hnativeR hmassR) hcapR

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


