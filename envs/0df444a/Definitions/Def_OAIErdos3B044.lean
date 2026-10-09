-- Prove2me | Definitions.Def_OAIErdos3B044
-- name    : OAIErdos3B044
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-09T04:31:59.808663+00:00
-- url     : https://prove2.me/theorems/f1290baa-4add-4523-8ec9-9d60fa960e82
-- title:
--   OpenAI Erdős-3 split, definitions bundle 45 of 132
-- statement:
--   Definitions bundle 45 of 132 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B043`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 45 available.
--
--   Modules: `OAI.Erdos3.VectorPolynomial.CoefficientSamplerArrays`, `OAI.Erdos3.VectorPolynomial.boundedSiteMatrix_height`, `OAI.Erdos3.VectorPolynomial.boundedSiteMatrix_natAbs_le`, `OAI.Erdos3.VectorPolynomial.canonicalCoefficientDensity`, `OAI.Erdos3.VectorPolynomial.canonicalCoefficientDensity_recover_unique`, `OAI.Erdos3.VectorPolynomial.canonicalCoefficientSample`, `OAI.Erdos3.VectorPolynomial.canonicalCoefficientSample_integer_remainder`, `OAI.Erdos3.VectorPolynomial.coefficientArrayFunctional_endomorphism_zero_iff`, `OAI.Erdos3.VectorPolynomial.coefficientArrayFunctional_layerInsertion`, `OAI.Erdos3.VectorPolynomial.coefficientEvaluationArray`, `OAI.Erdos3.VectorPolynomial.coefficientEvaluationArray_constant`, `OAI.Erdos3.VectorPolynomial.coefficientEvaluationArray_layerInsertion`, `OAI.Erdos3.VectorPolynomial.coefficientEvaluationArray_preserves_lattice`, `OAI.Erdos3.VectorPolynomial.coefficientLayerEndomorphism`, `OAI.Erdos3.VectorPolynomial.coefficientLayerEndomorphism_insertion`, `OAI.Erdos3.VectorPolynomial.coefficientLayerEndomorphism_preserves_lattice`, `OAI.Erdos3.VectorPolynomial.coefficientLayerInsertion`, `OAI.Erdos3.VectorPolynomial.coefficientLayerInsertion_ne`, `OAI.Erdos3.VectorPolynomial.coefficientLayerInsertion_same`, `OAI.Erdos3.VectorPolynomial.coefficientRowPolynomial`, `OAI.Erdos3.VectorPolynomial.coefficientRowPolynomial_affine_eval`, `OAI.Erdos3.VectorPolynomial.coefficientRowPolynomial_constant`, `OAI.Erdos3.VectorPolynomial.coefficientRowPolynomial_eval`, `OAI.Erdos3.VectorPolynomial.coefficientRowPolynomial_sub`, `OAI.Erdos3.VectorPolynomial.coefficientSiteResidual`, `OAI.Erdos3.VectorPolynomial.coefficientSiteResidual_cover_on_kernel`, `OAI.Erdos3.VectorPolynomial.coefficientSiteResidual_preserves_lattice`, `OAI.Erdos3.VectorPolynomial.coefficientSiteResidual_site_zero`, `OAI.Erdos3.VectorPolynomial.coefficientSiteResidual_zero_iff`, `OAI.Erdos3.VectorPolynomial.constantCoefficientArray`, `OAI.Erdos3.VectorPolynomial.constantCoefficientArray_preserves_lattice`, `OAI.Erdos3.VectorPolynomial.emptyCoefficientExponent_eq`, `OAI.Erdos3.VectorPolynomial.euclideanCoefficientEquiv_mk`, `OAI.Erdos3.affineProbabilityProfile_abs_le`, `OAI.Erdos3.basisAxisScale_cast_pos`, `OAI.Erdos3.basisAxisScale_le_of_rational_kernel`, `OAI.Erdos3.canonicalArrayDensity`, `OAI.Erdos3.canonicalArrayDensity_recover`, `OAI.Erdos3.canonicalArrayDensity_recover_unique`, `OAI.Erdos3.canonicalMixedDensity`, `OAI.Erdos3.canonicalMixedDensity_apply`, `OAI.Erdos3.canonicalMixedDensity_recover`, `OAI.Erdos3.earlyConstantDensityCap`, `OAI.Erdos3.earlyConstantDensityCap_exp_bound`, `OAI.Erdos3.earlyConstantDensityCap_nonneg`, `OAI.Erdos3.earlyFiberCapLog`, `OAI.Erdos3.earlyFiberCap_exp_bound`, `OAI.Erdos3.euclideanFromCoordinates_lipschitz`, `OAI.Erdos3.exists_bounded_integral_span_of_rational_range`, `OAI.Erdos3.exists_lattice_basis_covolume_factor`, `OAI.Erdos3.exists_lattice_covolume_identity`, `OAI.Erdos3.exists_lattice_index_covolume_factor`, `OAI.Erdos3.exists_lattice_split_basis`, `OAI.Erdos3.exists_normalized_projected_chart`, `OAI.Erdos3.exists_projected_basis_with_axis_budgets`, `OAI.Erdos3.exists_quantitative_projected_chart`, `OAI.Erdos3.exists_rational_matrix_height`, `OAI.Erdos3.exists_scaled_lattice_covolume_identity`, `OAI.Erdos3.exists_short_projected_integer_basis`, `OAI.Erdos3.jointRationalSpaceLattice_full`, `OAI.Erdos3.ker_basis_inner_eq_orthogonal`, `OAI.Erdos3.kernel_eq_span_integer_inter_of_basis`, `OAI.Erdos3.kernel_eq_span_lattice_inter`, `OAI.Erdos3.latticeConstantMass`, `OAI.Erdos3.latticeImageProjection`, `OAI.Erdos3.latticeImageProjection_surjective`, `OAI.Erdos3.latticeKernel`, `OAI.Erdos3.latticeKernelEquiv`, `OAI.Erdos3.latticeKernel_discrete`, `OAI.Erdos3.latticeKernel_full`, `OAI.Erdos3.latticeSection_orthogonal_full`, `OAI.Erdos3.latticeSheetQuotient_eq_of_lift`, `OAI.Erdos3.mixedAmbientInterpolation`, `OAI.Erdos3.mixedAmbientInterpolation_bounds`, `OAI.Erdos3.mixedAmbientInterpolation_grid`, `OAI.Erdos3.mixedArrayInChart`, `OAI.Erdos3.mixedArrayQuotient`, `OAI.Erdos3.mixedArrayQuotient_injOn_chart`, `OAI.Erdos3.mixedArrayQuotient_measurable`, `OAI.Erdos3.mixedArraySupported`, `OAI.Erdos3.mixedArraySupported_iff_rows`, `OAI.Erdos3.mixedCoefficientDensity_width_cap`, `OAI.Erdos3.mixedCoefficient_small_support`, `OAI.Erdos3.mixedDensityCovolumeRatio`, `OAI.Erdos3.mixedDensityCovolumeRatio_pos`, `OAI.Erdos3.mixedLiftCoefficient`, `OAI.Erdos3.mixedLiftCoefficient_eq`, `OAI.Erdos3.mixedLiftPolynomial`, `OAI.Erdos3.mixedLiftPolynomial_coeff`, `OAI.Erdos3.mixedLiftPolynomial_coefficient_bound`, `OAI.Erdos3.mixedLiftPolynomial_degree`, `OAI.Erdos3.mixedLiftPolynomial_eval`, `OAI.Erdos3.mixedPolynomialPoint_sum`, `OAI.Erdos3.mixedRealCoordinates`, `OAI.Erdos3.mixedRealCoordinates_integer`, `OAI.Erdos3.mixedRealCoordinates_lipschitz`, `OAI.Erdos3.mixedRealCoordinates_norm_le`, `OAI.Erdos3.mixedRealCoordinates_point`, `OAI.Erdos3.mixedRealPoint`, `OAI.Erdos3.mixedRealPoint_integer`, `OAI.Erdos3.mixedRealPoint_norm_le`, `OAI.Erdos3.mixedRealPoint_scaled_coordinate_bound`, `OAI.Erdos3.normalizedChartReference`, `OAI.Erdos3.normalizedChartRegion`, `OAI.Erdos3.normalizedLatticePoint`, `OAI.Erdos3.normalizedLatticePointHom`, `OAI.Erdos3.normalizedLatticePoint_eq_sheet`, `OAI.Erdos3.normalizedLatticePoint_sub_mem_of_mk_eq`, `OAI.Erdos3.normalizedLatticeQuotient`, `OAI.Erdos3.normalizedLatticeQuotient_injOn`, `OAI.Erdos3.normalizedLatticeQuotient_linear_lift`, `OAI.Erdos3.normalizedLatticeQuotient_measurable`, `OAI.Erdos3.normalizedMixedPoint_small`, `OAI.Erdos3.normalizedQuotientDensity`, `OAI.Erdos3.normalizedQuotientDensity_apply`, `OAI.Erdos3.normalizedQuotientDensity_recover`, `OAI.Erdos3.orthonormalMixedChartHom`, `OAI.Erdos3.projectedAxisDefectBudget`, `OAI.Erdos3.projectedAxisDefectBudget_le_exp`, `OAI.Erdos3.projectedAxisDefectBudget_pos`, `OAI.Erdos3.projectedAxisNormBudget`, `OAI.Erdos3.projectedAxisNormBudget_add_one_le_exp`, `OAI.Erdos3.projectedAxisNormBudget_le_exp`, `OAI.Erdos3.projectedAxisNormBudget_pos`, `OAI.Erdos3.projectedChart_defectBudget_le_exp`, `OAI.Erdos3.projectedChart_forwardBudget_le_exp`, `OAI.Erdos3.projectedChart_inverseBudget_le_exp`, `OAI.Erdos3.projectedChart_volumeBudget_le_exp`, `OAI.Erdos3.projectedIntegerGenerator`, `OAI.Erdos3.projectedIntegerGenerator_mem`, `OAI.Erdos3.projectedIntegerGenerator_norm_le`, `OAI.Erdos3.projectedIntegerGenerator_span`, `OAI.Erdos3.projectedIntegerLattice`, `OAI.Erdos3.projectedIntegerLattice_covolume`, `OAI.Erdos3.projectedIntegerLattice_discrete`, `OAI.Erdos3.projectedIntegerLattice_full`, `OAI.Erdos3.projectedIntegerLattice_norm_inv_le_of_rational_kernel`, `OAI.Erdos3.rationalKernelAxisBound`, `OAI.Erdos3.rationalRangeLattice_full`, `OAI.Erdos3.rational_vector_mem_span_integer_points`, `OAI.Erdos3.real_rational_kernel_eq_span_integer`, `OAI.Erdos3.restrictedChartDensity_recover`, `OAI.Erdos3.scaledAbs_le_of_bound`, `OAI.Erdos3.scaledProfile_div_bound`, `OAI.Erdos3.standardEuclideanLattice_covolume`, `OAI.Erdos3.standardLatticeCoordinates`, `OAI.Erdos3.standardLatticeCoordinates_residue`, `OAI.Erdos3.standardLatticeIntegerLift`, `OAI.Erdos3.standardLatticeIntegerLift_projection`, `OAI.Erdos3.standardLatticeIntegerLift_sheet`, `OAI.Erdos3.translatedQuotientChart`, `OAI.Erdos3.translatedQuotientChart_embedding`, `OAI.Erdos3.translatedQuotientChart_haar_image`, `OAI.Erdos3.translatedQuotientChart_image`, `OAI.Erdos3.translatedQuotientChart_map_restrict`, `OAI.Erdos3.translatedQuotientChart_measurable`, `OAI.Erdos3.translatedQuotientChart_measurable_image`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B120

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ScaledLatticeCovolume
namespace OAI

section

namespace Erdos3

open scoped Matrix

theorem rational_vector_mem_span_integer_points {κ : Type*} [Fintype κ]
    (U : Submodule ℝ (κ → ℝ)) (q : κ → ℚ) (hq : (fun i => (q i : ℝ)) ∈ U) :
    (fun i => (q i : ℝ)) ∈ Submodule.span ℝ
      {x : κ → ℝ | x ∈ realIntegerGrid ∧ x ∈ U} := by
  classical
  let D := arrayDenominator q
  let z := clearedArray q
  have hD : (D : ℝ) ≠ 0 := by exact_mod_cast (arrayDenominator_pos q).ne'
  have he : (fun i => (z i : ℝ)) = (D : ℝ) • (fun i => (q i : ℝ)) := by
    funext i
    change (clearedArray q i : ℝ) = (arrayDenominator q : ℝ) * (q i : ℝ)
    exact_mod_cast clearedArray_cast q i
  have hz : (fun i => (z i : ℝ)) ∈ U := by rw [he]; exact U.smul_mem _ hq
  have hs : (fun i => (z i : ℝ)) ∈ Submodule.span ℝ
      {x : κ → ℝ | x ∈ realIntegerGrid ∧ x ∈ U} := Submodule.subset_span ⟨⟨z, rfl⟩, hz⟩
  have hinv := (Submodule.span ℝ {x : κ → ℝ | x ∈ realIntegerGrid ∧ x ∈ U}).smul_mem
    (D : ℝ)⁻¹ hs
  simpa only [he, smul_smul, inv_mul_cancel₀ hD, one_smul] using hinv

theorem exists_rational_matrix_height {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℚ) : ∃ H : ℕ, 1 ≤ H ∧ ∀ i j, RationalHeightLE (A i j) H := by
  classical
  let H := max 1 (Finset.univ.sup fun ij : ι × κ => max (A ij.1 ij.2).num.natAbs (A ij.1 ij.2).den)
  refine ⟨H, le_max_left _ _, ?_⟩
  intro i j
  have hmax : max (A i j).num.natAbs (A i j).den ≤ H :=
    (Finset.le_sup (f := fun ij : ι × κ => max (A ij.1 ij.2).num.natAbs (A ij.1 ij.2).den)
      (Finset.mem_univ (i, j))).trans (le_max_right _ _)
  exact ⟨(le_max_left _ _).trans hmax, (le_max_right _ _).trans hmax⟩

theorem real_rational_kernel_eq_span_integer {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℚ) :
    LinearMap.ker (Matrix.mulVecLin (fun i j => (A i j : ℝ))) =
      Submodule.span ℝ {x : κ → ℝ | x ∈ realIntegerGrid ∧
        x ∈ LinearMap.ker (Matrix.mulVecLin (fun i j => (A i j : ℝ)))} := by
  classical
  obtain ⟨H, hH, hA⟩ := exists_rational_matrix_height A
  obtain ⟨S, hS, _⟩ := exists_bounded_rational_image_section A hH hA
  let Ar : Matrix ι κ ℝ := fun i j => (A i j : ℝ)
  let Sr : Matrix κ ι ℝ := fun i j => (S i j : ℝ)
  let P : Matrix κ κ ℚ := 1 - S * A
  let Pr : Matrix κ κ ℝ := fun i j => (P i j : ℝ)
  have hSr : Ar * Sr * Ar = Ar := real_matrix_image_section A S hS
  have hPr : Pr = (1 : Matrix κ κ ℝ) - Sr * Ar := by
    ext i j
    change (P i j : ℝ) = (if i = j then 1 else 0) - ∑ k, (S i k : ℝ) * (A k j : ℝ)
    by_cases hij : i = j <;> simp [P, Matrix.sub_apply, Matrix.mul_apply, hij]
  have hzero : Ar * (1 - Sr * Ar) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hSr, sub_self]
  have hrange : LinearMap.range ((1 - Sr * Ar).mulVecLin) = LinearMap.ker Ar.mulVecLin := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      change Ar *ᵥ ((1 - Sr * Ar) *ᵥ y) = 0
      rw [Matrix.mulVec_mulVec, hzero, Matrix.zero_mulVec]
    · intro hx
      change Ar *ᵥ x = 0 at hx
      refine ⟨x, ?_⟩
      change (1 - Sr * Ar) *ᵥ x = x
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
        hx, Matrix.mulVec_zero, sub_zero]
  have hspan : Submodule.span ℝ (Set.range Pr.col) = LinearMap.ker Ar.mulVecLin := by
    rw [← Matrix.range_mulVecLin, hPr]
    exact hrange
  apply le_antisymm
  · change LinearMap.ker Ar.mulVecLin ≤ _
    calc
      LinearMap.ker Ar.mulVecLin = Submodule.span ℝ (Set.range Pr.col) := hspan.symm
      _ ≤ _ := by
        apply Submodule.span_le.mpr
        rintro x ⟨j, rfl⟩
        apply rational_vector_mem_span_integer_points _ (P.col j)
        exact hspan ▸ (Submodule.subset_span ⟨j, rfl⟩)
  · exact Submodule.span_le.mpr (fun _ hx => hx.2)

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix

theorem kernel_eq_span_integer_inter_of_basis
    {E ι κ : Type*} [AddCommGroup E] [Module ℝ E] [Fintype ι] [Fintype κ]
    (b : Basis κ ℝ E) (Λ : Submodule ℤ E) (hb : Submodule.span ℤ (Set.range b) = Λ)
    (π : E →ₗ[ℝ] (ι → ℝ)) (hπ : ∀ j, π (b j) ∈ realIntegerGrid) :
    LinearMap.ker π = Submodule.span ℝ {x : E | x ∈ Λ ∧ π x = 0} := by
  classical
  choose z hz using hπ
  let A : Matrix ι κ ℚ := fun i j => (z j i : ℚ)
  let Ar : Matrix ι κ ℝ := fun i j => (A i j : ℝ)
  let f : (κ → ℝ) →ₗ[ℝ] E := b.equivFun.symm.toLinearMap
  have hA (y : κ → ℝ) : π (b.equivFun.symm y) = Ar *ᵥ y := by
    funext i
    rw [b.equivFun_symm_apply, map_sum]
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
    apply Finset.sum_congr rfl
    intro j _
    have hj : (z j i : ℝ) = π (b j) i := congrFun (hz j) i
    rw [← hj]
    simp only [Ar, A, Rat.cast_intCast, mul_comm]
  have hmap : (LinearMap.ker Ar.mulVecLin).map f ≤
      Submodule.span ℝ {x : E | x ∈ Λ ∧ π x = 0} := by
    change (LinearMap.ker (Matrix.mulVecLin (fun i j => (A i j : ℝ)))).map f ≤ _
    rw [real_rational_kernel_eq_span_integer, Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro x ⟨y, ⟨⟨a, ha⟩, hy⟩, rfl⟩
    apply Submodule.subset_span
    constructor
    · rw [← hb, b.mem_span_iff_repr_mem ℤ]
      intro j
      refine ⟨a j, ?_⟩
      change (a j : ℝ) = b.equivFun (b.equivFun.symm y) j
      rw [LinearEquiv.apply_symm_apply]
      exact congrFun ha j
    · change π (b.equivFun.symm y) = 0
      rw [hA]
      exact hy
  apply le_antisymm
  · intro x hx
    apply hmap
    refine ⟨b.equivFun x, ?_, b.equivFun.symm_apply_apply x⟩
    change Ar *ᵥ b.equivFun x = 0
    rw [← hA, LinearEquiv.symm_apply_apply]
    exact hx
  · apply Submodule.span_le.mpr
    intro x hx
    exact hx.2

end Erdos3

end

section

namespace Erdos3

open Module

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι]
  (Λ : Submodule ℤ E) (π : E →ₗ[ℝ] (ι → ℝ))

noncomputable def latticeKernel : Submodule ℤ (LinearMap.ker π) :=
  ZLattice.comap ℝ Λ (LinearMap.ker π).subtype

instance latticeKernel_discrete [DiscreteTopology Λ] : DiscreteTopology (latticeKernel Λ π) :=
  ZLattice.comap_discreteTopology ℝ Λ continuous_subtype_val Subtype.val_injective

theorem kernel_eq_span_lattice_inter [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (hπ : ∀ x ∈ Λ, π x ∈ realIntegerGrid) :
    LinearMap.ker π = Submodule.span ℝ {x : E | x ∈ Λ ∧ π x = 0} := by
  let b := (Free.chooseBasis ℤ Λ).ofZLatticeBasis ℝ Λ
  exact kernel_eq_span_integer_inter_of_basis b Λ
    ((Free.chooseBasis ℤ Λ).ofZLatticeBasis_span ℝ)
    π (fun j => hπ _ (by
      simpa only [b, Basis.ofZLatticeBasis_apply] using ((Free.chooseBasis ℤ Λ) j).property))

theorem latticeKernel_full [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (hπ : ∀ x ∈ Λ, π x ∈ realIntegerGrid) : IsZLattice ℝ (latticeKernel Λ π) := by
  constructor
  apply (Submodule.map_injective_of_injective (LinearMap.ker π).injective_subtype)
  rw [Submodule.map_top, Submodule.range_subtype, Submodule.map_span]
  refine Eq.trans ?_ (kernel_eq_span_lattice_inter Λ π hπ).symm
  apply congrArg (Submodule.span ℝ)
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hy, y.property⟩
  · rintro ⟨hx, hzero⟩
    exact ⟨⟨x, hzero⟩, hx, rfl⟩

end Erdos3

end

section

namespace Erdos3

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (Λ : Submodule ℤ E) (π : E →ₗ[ℝ] (ι → ℝ))

def latticeImageProjection : Λ →ₗ[ℤ] latticeImage Λ π :=
  ((π.restrictScalars ℤ).comp Λ.subtype).codRestrict (latticeImage Λ π)
    (fun x => ⟨x.val, x.property, rfl⟩)

theorem latticeImageProjection_surjective : Function.Surjective (latticeImageProjection Λ π) := by
  rintro ⟨y, x, hx, hxy⟩
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

noncomputable def latticeKernelEquiv :
    latticeKernel Λ π ≃ₗ[ℤ] LinearMap.ker (latticeImageProjection Λ π) where
  toFun x := ⟨⟨x.val.val, x.property⟩, Subtype.ext x.val.property⟩
  invFun x := ⟨⟨x.val.val, congrArg Subtype.val
    (show latticeImageProjection Λ π x.val = 0 from x.property)⟩, x.val.property⟩
  left_inv _x := rfl
  right_inv _x := rfl
  map_add' _x _y := rfl
  map_smul' _a _x := rfl

end Erdos3

end

section

namespace Erdos3

open Module

theorem exists_lattice_split_basis
    {E ι α β : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Λ : Submodule ℤ E) (π : E →ₗ[ℝ] (ι → ℝ))
    (bK : Basis α ℤ (latticeKernel Λ π)) (bI : Basis β ℤ (latticeImage Λ π)) :
    ∃ b : Basis (α ⊕ β) ℤ Λ,
      (∀ i, (b (Sum.inl i) : E) = (bK i).val.val) ∧
      (∀ j, π (b (Sum.inr j) : E) = (bI j).val) := by
  let : Free ℤ (latticeImage Λ π) := Free.of_basis bI
  obtain ⟨b, hbK, hbI⟩ := exists_basis_of_surjection (latticeImageProjection Λ π)
    (latticeImageProjection_surjective Λ π) (bK.map (latticeKernelEquiv Λ π)) bI
  refine ⟨b, ?_, ?_⟩
  · intro i
    rw [hbK]
    rfl
  · intro j
    exact congrArg Subtype.val (hbI j)

end Erdos3

end

section

namespace Erdos3

open Module

theorem exists_lattice_basis_covolume_factor
    {E ι α β : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [Fintype ι] [Fintype α] [Fintype β] [DecidableEq β]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (π : E →ₗ[ℝ] (ι → ℝ)) [IsZLattice ℝ (latticeKernel Λ π)]
    (bK : Basis α ℤ (latticeKernel Λ π)) (bI : Basis β ℤ (latticeImage Λ π)) :
    ∃ b : Basis (α ⊕ β) ℤ Λ,
      (∀ i, (b (Sum.inl i) : E) = (bK i).val.val) ∧
      (∀ j, π (b (Sum.inr j) : E) = (bI j).val) ∧
      ZLattice.covolume Λ ^ 2 = ZLattice.covolume (latticeKernel Λ π) ^ 2 *
        (Matrix.gram ℝ (fun j : β => (b (Sum.inr j) : E) -
          (LinearMap.ker π).starProjection (b (Sum.inr j) : E))).det := by
  classical
  obtain ⟨b, hbK, hbI⟩ := exists_lattice_split_basis Λ π bK bI
  refine ⟨b, hbK, hbI, ?_⟩
  let bR := b.ofZLatticeBasis ℝ Λ
  let bKR := bK.ofZLatticeBasis ℝ (latticeKernel Λ π)
  have hval (i : α) : bR (Sum.inl i) = (bKR i : E) := by
    simpa only [bR, bKR, Basis.ofZLatticeBasis_apply] using hbK i
  have hspan : Submodule.span ℝ (Set.range (fun i : α => bR (Sum.inl i))) =
      LinearMap.ker π := by
    rw [show (fun i : α => bR (Sum.inl i)) = (fun i : α => (bKR i : E)) from funext hval]
    change Submodule.span ℝ (Set.range ((LinearMap.ker π).subtype ∘ bKR)) = _
    rw [Set.range_comp, ← Submodule.map_span, bKR.span_eq,
      Submodule.map_top, Submodule.range_subtype]
  have hkernelGram : (Matrix.gram ℝ (fun i : α => bR (Sum.inl i))).det =
      ZLattice.covolume (latticeKernel Λ π) ^ 2 := by
    have he : Matrix.gram ℝ (fun i : α => bR (Sum.inl i)) = Matrix.gram ℝ bKR := by
      ext i j
      simp only [Matrix.gram_apply, hval]
      rfl
    rw [he]
    exact (lattice_covolume_sq_eq_gram (latticeKernel Λ π) bK).symm
  have hblock := gram_det_orthogonal_block bR
  dsimp only at hblock
  rw [hspan, hkernelGram] at hblock
  rw [lattice_covolume_sq_eq_gram Λ b]
  simpa only [bR, Basis.ofZLatticeBasis_apply] using hblock

end Erdos3

end

section

namespace Erdos3

open Module

theorem exists_lattice_index_covolume_factor
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [Fintype ι] [DecidableEq ι]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (π : E →ₗ[ℝ] (ι → ℝ))
    (hinteger : ∀ x ∈ Λ, π x ∈ realIntegerGrid) (hsurj : Function.Surjective π) :
    ∃ L : (ι → ℝ) →ₗ[ℝ] E,
      (∀ y, π (L y) = y) ∧
      (∀ x, L (π x) = x - (LinearMap.ker π).starProjection x) ∧
      ZLattice.covolume Λ ^ 2 =
        ZLattice.covolume (latticeKernel Λ π) ^ 2 *
        ((latticeImage Λ π).toAddSubgroup.relIndex integerCoordinateLattice.toAddSubgroup : ℝ) ^ 2 *
        (Matrix.gram ℝ (fun i : ι => L (Pi.basisFun ℝ ι i))).det := by
  classical
  let H := latticeImage Λ π
  let K := latticeKernel Λ π
  let : DiscreteTopology H := latticeImage_discrete Λ π hinteger
  let : IsZLattice ℝ H := latticeImage_full Λ π hsurj
  let : IsZLattice ℝ K := latticeKernel_full Λ π hinteger
  let bK := Free.chooseBasis ℤ K
  let bI := IsZLattice.basis H
  let B := bI.ofZLatticeBasis ℝ H
  obtain ⟨L, hright, hsection⟩ := exists_orthogonal_section π hsurj
  have hL : Function.Injective L := by
    intro x y hxy
    have h := congrArg π hxy
    simpa only [hright] using h
  obtain ⟨b, _, hbI, hcov⟩ := exists_lattice_basis_covolume_factor Λ π bK bI
  have hw (j : ι) : (b (Sum.inr j) : E) -
      (LinearMap.ker π).starProjection (b (Sum.inr j) : E) = L (B j) := by
    rw [← hsection]
    apply congrArg L
    simpa only [B, Basis.ofZLatticeBasis_apply] using hbI j
  have hcov' : ZLattice.covolume Λ ^ 2 = ZLattice.covolume K ^ 2 *
      (Matrix.gram ℝ (fun j : ι => L (B j))).det := by
    simpa only [hw] using hcov
  have hgram := gram_det_injective_map_basis L hL (Pi.basisFun ℝ ι) B
  have hB : (B : ι → (ι → ℝ)) = fun j => (bI j).val := by
    funext j
    exact bI.ofZLatticeBasis_apply ℝ H j
  have hdet : |(Pi.basisFun ℝ ι).det B| =
      ((latticeImage Λ π).toAddSubgroup.relIndex integerCoordinateLattice.toAddSubgroup : ℝ) := by
    rw [Pi.basisFun_det_apply, hB]
    exact (ZLattice.covolume_eq_det H bI).symm.trans
      (integer_lattice_covolume_eq_index H (latticeImage_le_integer Λ π hinteger))
  have hsq := congrArg (fun t : ℝ => t ^ 2) hdet
  rw [sq_abs] at hsq
  refine ⟨L, hright, hsection, ?_⟩
  rw [hgram, hsq] at hcov'
  simpa only [mul_assoc] using hcov'

end Erdos3

end

section

namespace Erdos3

theorem exists_lattice_covolume_identity
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [Fintype ι] [DecidableEq ι]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (π : E →ₗ[ℝ] (ι → ℝ))
    (hinteger : ∀ x ∈ Λ, π x ∈ realIntegerGrid) (hsurj : Function.Surjective π) :
    ∃ L : (ι → ℝ) →ₗ[ℝ] E,
      (∀ y, π (L y) = y) ∧
      (∀ x, L (π x) = x - (LinearMap.ker π).starProjection x) ∧
      ZLattice.covolume Λ = ZLattice.covolume (latticeKernel Λ π) *
        ((latticeImage Λ π).toAddSubgroup.relIndex integerCoordinateLattice.toAddSubgroup : ℝ) *
        Real.sqrt (Matrix.gram ℝ (fun i : ι => L (Pi.basisFun ℝ ι i))).det := by
  let : IsZLattice ℝ (latticeKernel Λ π) := latticeKernel_full Λ π hinteger
  obtain ⟨L, hright, hsection, hsq⟩ := exists_lattice_index_covolume_factor Λ π hinteger hsurj
  refine ⟨L, hright, hsection, ?_⟩
  have h := congrArg Real.sqrt hsq
  rw [Real.sqrt_sq (ZLattice.covolume_pos Λ MeasureTheory.volume).le] at h
  rw [Real.sqrt_mul (mul_nonneg (sq_nonneg _) (sq_nonneg _)),
    Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq (ZLattice.covolume_pos (latticeKernel Λ π) MeasureTheory.volume).le,
    Real.sqrt_sq (Nat.cast_nonneg _)] at h
  exact h

end Erdos3

end

section

namespace Erdos3

theorem exists_scaled_lattice_covolume_identity
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [Fintype ι] [DecidableEq ι]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (π : E →ₗ[ℝ] (ι → ℝ))
    (hinteger : ∀ x ∈ Λ, π x ∈ realIntegerGrid) (hsurj : Function.Surjective π)
    (T : ι → ℝ) (hT : ∀ i, 0 < T i) :
    ∃ G : (ι → ℝ) →ₗ[ℝ] E,
      (∀ y, π (G y) = fun i => T i * y i) ∧
      (∀ x, G (fun i => π x i / T i) = x - (LinearMap.ker π).starProjection x) ∧
      ZLattice.covolume Λ = ZLattice.covolume (latticeKernel Λ π) *
        (((latticeImage Λ π).toAddSubgroup.relIndex integerCoordinateLattice.toAddSubgroup : ℝ) /
          ∏ i, T i) *
        Real.sqrt (Matrix.gram ℝ (fun i : ι => G (Pi.basisFun ℝ ι i))).det := by
  obtain ⟨L, hright, hsection, hcov⟩ := exists_lattice_covolume_identity Λ π hinteger hsurj
  let D := coordinateScaleEquiv T (fun i => (hT i).ne')
  let G := L.comp D.toLinearMap
  have hL : Function.Injective L := by
    intro x y hxy
    have h := congrArg π hxy
    simpa only [hright] using h
  have hscale := scaled_section_gram_sqrt L hL T hT
  have hprod : 0 < ∏ i, T i := Finset.prod_pos (fun i _ => hT i)
  have hroot : Real.sqrt (Matrix.gram ℝ (fun i : ι => L (Pi.basisFun ℝ ι i))).det =
      Real.sqrt (Matrix.gram ℝ (fun i : ι => G (Pi.basisFun ℝ ι i))).det / ∏ i, T i := by
    apply (eq_div_iff hprod.ne').mpr
    dsimp only [G, D, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hscale]
    ring
  refine ⟨G, ?_, ?_, ?_⟩
  · intro y
    exact hright (D y)
  · intro x
    change L (D (D.symm (π x))) = x - (LinearMap.ker π).starProjection x
    rw [LinearEquiv.apply_symm_apply]
    exact hsection x
  · rw [hroot] at hcov
    rw [hcov]
    ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.IntegralOrthogonalSection
namespace OAI

section

namespace Erdos3

open Module Submodule
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem ker_basis_inner_eq_orthogonal {I : Type*} [Fintype I]
    (W : Submodule ℝ E) (b : Basis I ℝ W) :
    LinearMap.ker (LinearMap.pi (fun i => innerₗ E (b i).val)) = Wᗮ := by
  have hspan : span ℝ (Set.range (fun i => (b i : E))) = W := by
    change span ℝ (Set.range (W.subtype ∘ b)) = W
    rw [Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_top,
      Submodule.range_subtype]
  ext x
  constructor
  · intro hx
    have hz : (LinearMap.pi (fun i => innerₗ E (b i).val)) x = 0 := hx
    have hW : W ≤ LinearMap.ker (innerₗ E x) := by
      rw [← hspan]
      apply span_le.mpr
      rintro _ ⟨i, rfl⟩
      change inner ℝ x (b i : E) = 0
      rw [real_inner_comm]
      exact congrFun hz i
    exact (W.mem_orthogonal' x).mpr (fun y hy => hW hy)
  · intro hx
    apply LinearMap.mem_ker.mpr
    ext i
    exact Submodule.inner_right_of_mem_orthogonal (b i).property hx

theorem latticeSection_orthogonal_full (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hintegral : Λ ≤ euclideanDualLattice Λ)
    (W : Submodule ℝ E) [IsZLattice ℝ (latticeSection Λ W)] :
    IsZLattice ℝ (latticeSection Λ Wᗮ) := by
  let B := Free.chooseBasis ℤ (latticeSection Λ W)
  let b := B.ofZLatticeBasis ℝ (latticeSection Λ W)
  let π : E →ₗ[ℝ] (Free.ChooseBasisIndex ℤ (latticeSection Λ W) → ℝ) :=
    LinearMap.pi (fun i => innerₗ E (b i).val)
  have hπ : ∀ x ∈ Λ, π x ∈ realIntegerGrid := by
    intro x hx
    have h : ∀ i, ∃ n : ℤ, (n : ℝ) = π x i := by
      intro i
      have hi : (b i : E) ∈ Λ := by
        have hi₀ : (B i).val.val ∈ Λ := (B i).property
        simpa only [b, Basis.ofZLatticeBasis_apply] using hi₀
      obtain ⟨n, hn⟩ := (mem_euclideanDualLattice Λ (b i).val).mp (hintegral hi) x hx
      exact ⟨n, hn.symm⟩
    choose z hz using h
    exact ⟨z, funext hz⟩
  have hk : LinearMap.ker π = Wᗮ := ker_basis_inner_eq_orthogonal W b
  have hfull := latticeKernel_full Λ π hπ
  have hsection : IsZLattice ℝ (latticeSection Λ (LinearMap.ker π)) := hfull
  exact (congrArg (fun V : Submodule ℝ E => IsZLattice ℝ (latticeSection Λ V)) hk).mp hsection

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.StandardLatticeCoordinates
namespace OAI

section

namespace Erdos3

open Module Submodule

variable {J : Type*} [Fintype J]

noncomputable def projectedIntegerLattice (W : Submodule ℝ (EuclideanSpace ℝ J)) :
    Submodule ℤ Wᗮ := orthogonalLatticeImage (standardEuclideanLattice J) Wᗮ

noncomputable def projectedIntegerGenerator (W : Submodule ℝ (EuclideanSpace ℝ J)) (i : J) : Wᗮ :=
  Wᗮ.orthogonalProjectionOnto (EuclideanSpace.basisFun J ℝ i)

theorem projectedIntegerGenerator_mem (W : Submodule ℝ (EuclideanSpace ℝ J)) (i : J) :
    projectedIntegerGenerator W i ∈ projectedIntegerLattice W := by
  refine ⟨EuclideanSpace.basisFun J ℝ i, ?_, rfl⟩
  exact subset_span (Set.mem_range_self i)

theorem projectedIntegerGenerator_norm_le (W : Submodule ℝ (EuclideanSpace ℝ J)) (i : J) :
    ‖projectedIntegerGenerator W i‖ ≤ 1 := by
  have h := Wᗮ.norm_orthogonalProjectionOnto_apply_le (EuclideanSpace.basisFun J ℝ i)
  simpa only [projectedIntegerGenerator, OrthonormalBasis.norm_eq_one] using h

theorem projectedIntegerGenerator_span (W : Submodule ℝ (EuclideanSpace ℝ J)) :
    span ℝ (Set.range (projectedIntegerGenerator W)) = ⊤ := by
  change span ℝ (Set.range (Wᗮ.orthogonalProjectionOnto.toLinearMap ∘
    (EuclideanSpace.basisFun J ℝ).toBasis)) = ⊤
  rw [Set.range_comp, ← Submodule.map_span, Basis.span_eq, Submodule.map_top]
  apply LinearMap.range_eq_top.mpr
  intro w
  refine ⟨w.val, ?_⟩
  apply Subtype.ext
  exact Wᗮ.starProjection_eq_self_iff.mpr w.property

instance projectedIntegerLattice_discrete (W : Submodule ℝ (EuclideanSpace ℝ J))
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice J) W)] :
    DiscreteTopology (projectedIntegerLattice W) := by
  let : IsZLattice ℝ (latticeSection (standardEuclideanLattice J) Wᗮ) :=
    latticeSection_orthogonal_full (standardEuclideanLattice J)
      (by rw [standardEuclideanLattice_self_dual]) W
  let : IsZLattice ℝ (latticeSection (euclideanDualLattice (standardEuclideanLattice J)) Wᗮ) := by
    constructor
    change span ℝ {x : Wᗮ | x.val ∈ euclideanDualLattice (standardEuclideanLattice J)} = ⊤
    rw [standardEuclideanLattice_self_dual]
    exact IsZLattice.span_top (K := ℝ) (L := latticeSection (standardEuclideanLattice J) Wᗮ)
  exact orthogonalLatticeImage_discrete (standardEuclideanLattice J) Wᗮ

instance projectedIntegerLattice_full (W : Submodule ℝ (EuclideanSpace ℝ J))
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice J) W)] :
    IsZLattice ℝ (projectedIntegerLattice W) := by
  let : DiscreteTopology (orthogonalLatticeImage (standardEuclideanLattice J) Wᗮ) :=
    projectedIntegerLattice_discrete W
  exact orthogonalLatticeImage_full (standardEuclideanLattice J) Wᗮ

end Erdos3

end

section

namespace Erdos3

open Module Submodule MeasureTheory

theorem standardEuclideanLattice_covolume (J : Type*) [Fintype J] :
    ZLattice.covolume (standardEuclideanLattice J) = 1 := by
  classical
  let b := EuclideanSpace.basisFun J ℝ
  have hg : Matrix.gram ℝ b.toBasis = 1 :=
    Matrix.gram_eq_one_iff_orthonormal.mpr b.orthonormal
  have hs := zspan_covolume_sq_eq_det_gram_fintype b.toBasis
  rw [hg, Matrix.det_one] at hs
  have hp := ZLattice.covolume_pos (standardEuclideanLattice J) volume
  change ZLattice.covolume (standardEuclideanLattice J) ^ 2 = 1 at hs
  nlinarith

theorem projectedIntegerLattice_covolume {J : Type*} [Fintype J]
    (W : Submodule ℝ (EuclideanSpace ℝ J))
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice J) W)] :
    ZLattice.covolume (latticeSection (standardEuclideanLattice J) W) *
      ZLattice.covolume (projectedIntegerLattice W) = 1 := by
  have hW : Wᗮᗮ = W := W.orthogonal_orthogonal
  let : DiscreteTopology (orthogonalLatticeImage (standardEuclideanLattice J) Wᗮ) :=
    projectedIntegerLattice_discrete W
  let : IsZLattice ℝ (orthogonalLatticeImage (standardEuclideanLattice J) Wᗮ) :=
    projectedIntegerLattice_full W
  let : IsZLattice ℝ (latticeSection (standardEuclideanLattice J) Wᗮᗮ) :=
    (congrArg (fun V : Submodule ℝ (EuclideanSpace ℝ J) =>
      IsZLattice ℝ (latticeSection (standardEuclideanLattice J) V)) hW).mpr inferInstance
  have h := orthogonalLattice_covolume (standardEuclideanLattice J) Wᗮ
  have hc := congrArg (fun V : Submodule ℝ (EuclideanSpace ℝ J) =>
    ZLattice.covolume (latticeSection (standardEuclideanLattice J) V)) hW
  rw [hc, standardEuclideanLattice_covolume] at h
  exact h.symm

end Erdos3

end

section

namespace Erdos3

open Module Submodule
open scoped Matrix NNReal

variable {J R I : Type*} [Fintype J] [Fintype R]

noncomputable def rationalKernelAxisBound (Q : Matrix R J ℚ) (H : ℕ) : ℝ :=
  (matrixDenominator Q : ℝ) * (((Fintype.card J : ℝ) + 1) * ((H : ℝ) + 1))

theorem projectedIntegerLattice_norm_inv_le_of_rational_kernel
    (Q : Matrix R J ℚ) (W : Submodule ℝ (J → ℝ))
    (hW : LinearMap.ker (Matrix.mulVecLin (fun r j => (Q r j : ℝ))) = W)
    {H : ℕ} (hQ : ∀ r j, RationalHeightLE (Q r j) H)
    {z : (euclideanSubspace W)ᗮ}
    (hz : z ∈ projectedIntegerLattice (euclideanSubspace W)) (hne : z ≠ 0) :
    ‖z‖⁻¹ ≤ rationalKernelAxisBound Q H := by
  classical
  obtain ⟨x, hx, hxz⟩ := hz
  change (euclideanSubspace W)ᗮ.orthogonalProjectionOnto x = z at hxz
  let y : EuclideanSpace ℝ J := x - z.val
  have hy : y ∈ euclideanSubspace W := by
    have h := (euclideanSubspace W)ᗮ.sub_starProjection_mem_orthogonal x
    rw [Submodule.orthogonal_orthogonal] at h
    simpa only [Submodule.starProjection_apply, hxz] using h
  have hQy : (fun r j => (Q r j : ℝ)) *ᵥ WithLp.ofLp y = 0 := by
    change WithLp.ofLp y ∈ W at hy
    rw [← hW] at hy
    exact hy
  have hxgrid : WithLp.ofLp x ∈ realDenominatorGrid 1 := by
    choose a ha using (mem_standardEuclideanLattice J x).mp hx
    refine ⟨a, ?_⟩
    ext j
    simpa only [Pi.smul_apply, Nat.cast_one, one_smul] using ha j
  have hQx : (fun r j => (Q r j : ℝ)) *ᵥ WithLp.ofLp x ≠ 0 := by
    intro hzero
    have hxW : x ∈ euclideanSubspace W := by
      change WithLp.ofLp x ∈ W
      rw [← hW]
      exact hzero
    have hproj : (euclideanSubspace W)ᗮ.orthogonalProjectionOnto x = 0 :=
      Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr
        ((euclideanSubspace W).le_orthogonal_orthogonal hxW)
    exact hne (hxz.symm.trans hproj)
  have hsep : 1 ≤ rationalKernelAxisBound Q H *
      dist (WithLp.ofLp x) (WithLp.ofLp y) := by
    by_contra! hsmall
    apply hQx
    apply rational_matrix_kernel_separation Q (H : ℝ≥0)
      (fun r j => (hQ r j).abs_real_le) 1 (by decide)
      (WithLp.ofLp x) (WithLp.ofLp y) hxgrid hQy
    simpa only [Nat.mul_one, rationalKernelAxisBound, NNReal.coe_natCast] using hsmall
  have hdist : dist (WithLp.ofLp x) (WithLp.ofLp y) ≤ ‖z‖ := by
    rw [dist_eq_norm]
    have he : WithLp.ofLp x - WithLp.ofLp y = WithLp.ofLp z.val := by
      ext j
      change x j - (x j - z.val j) = z.val j
      ring
    rw [he]
    exact (pi_norm_le_iff_of_nonneg (norm_nonneg z)).mpr
      (fun j => PiLp.norm_apply_le z.val j)
  have hbound : 1 ≤ rationalKernelAxisBound Q H * ‖z‖ :=
    hsep.trans (mul_le_mul_of_nonneg_left hdist (by
      unfold rationalKernelAxisBound
      positivity))
  exact (inv_le_iff_one_le_mul₀ (norm_pos_iff.mpr hne)).mpr hbound

theorem basisAxisScale_le_of_rational_kernel
    (Q : Matrix R J ℚ) (W : Submodule ℝ (J → ℝ))
    (hW : LinearMap.ker (Matrix.mulVecLin (fun r j => (Q r j : ℝ))) = W)
    {H : ℕ} (hQ : ∀ r j, RationalHeightLE (Q r j) H)
    (b : Basis I ℝ (euclideanSubspace W)ᗮ)
    (hb : span ℤ (Set.range b) = projectedIntegerLattice (euclideanSubspace W))
    (i : I) :
    basisAxisScale b i ≤ ⌈rationalKernelAxisBound Q H⌉₊ := by
  apply Nat.ceil_mono
  apply projectedIntegerLattice_norm_inv_le_of_rational_kernel Q W hW hQ
  · rw [← hb]
    exact subset_span (Set.mem_range_self i)
  · exact b.ne_zero i

end Erdos3

end

section

namespace Erdos3

open Module Submodule
open scoped BigOperators Matrix

theorem exists_bounded_integral_span_of_rational_range
    {J C : Type*} [Fintype J] [Fintype C]
    (B : Matrix J C ℚ) (W : Submodule ℝ (J → ℝ))
    (hW : LinearMap.range (Matrix.of (fun i j => (B i j : ℝ))).mulVecLin = W)
    {H : ℕ} (hB : ∀ i j, RationalHeightLE (B i j) H) :
    ∃ v : C → euclideanSubspace W,
      span ℝ (Set.range v) = ⊤ ∧
      (∀ j, v j ∈ latticeSection (standardEuclideanLattice J) (euclideanSubspace W)) ∧
      ∀ j, ‖v j‖ ≤ (Fintype.card J : ℝ) * H ^ (Fintype.card J * Fintype.card C) := by
  classical
  obtain ⟨D, hD, _, z, hz, hzH⟩ :=
    exists_bounded_integer_array (fun ij : J × C => B ij.1 ij.2) (fun ij => hB ij.1 ij.2)
  have hDr : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have hzr (i : J) (j : C) : (z (i, j) : ℝ) = (D : ℝ) * (B i j : ℝ) := by
    exact_mod_cast hz (i, j)
  have hcol (j : C) : (fun i => (B i j : ℝ)) ∈ W := by
    rw [← hW, Matrix.range_mulVecLin]
    exact subset_span ⟨j, rfl⟩
  have hmem (j : C) : WithLp.toLp 2 (fun i => (z (i, j) : ℝ)) ∈ euclideanSubspace W := by
    change (fun i => (z (i, j) : ℝ)) ∈ W
    have he : (fun i => (z (i, j) : ℝ)) = (D : ℝ) • (fun i => (B i j : ℝ)) :=
      funext (fun i => hzr i j)
    rw [he]
    exact W.smul_mem (D : ℝ) (hcol j)
  let v : C → euclideanSubspace W := fun j => ⟨WithLp.toLp 2 (fun i => (z (i, j) : ℝ)), hmem j⟩
  refine ⟨v, ?_, ?_, ?_⟩
  · apply top_unique
    intro x _
    have hx : WithLp.ofLp x.val ∈ W := x.property
    obtain ⟨y, hy⟩ := hW.ge hx
    have heq : x = ∑ j, (y j / D) • v j := by
      apply Subtype.ext
      ext i
      have hi := congrFun hy i
      change (∑ j, (B i j : ℝ) * y j) = x.val i at hi
      simp only [v, Submodule.coe_sum, Submodule.coe_smul, WithLp.ofLp_sum,
        WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [← hi]
      apply Finset.sum_congr rfl
      intro j _
      rw [hzr]
      field_simp
    rw [heq]
    exact sum_mem (fun j _ => smul_mem _ _ (subset_span ⟨j, rfl⟩))
  · intro j
    change (v j).val ∈ standardEuclideanLattice J
    exact (mem_standardEuclideanLattice J _).mpr (fun i => ⟨z (i, j), rfl⟩)
  · intro j
    calc
      ‖v j‖ ≤ ∑ i, |(z (i, j) : ℝ)| := euclidean_norm_le_sum_abs (v j).val
      _ ≤ ∑ _ : J, (H : ℝ) ^ (Fintype.card J * Fintype.card C) := by
        apply Finset.sum_le_sum
        intro i _
        have hb := hzH (i, j)
        rw [Fintype.card_prod] at hb
        have hr : |z (i, j)| ≤ (H ^ (Fintype.card J * Fintype.card C) : ℕ) := by
          simpa only [Int.natCast_natAbs] using (Int.ofNat_le.mpr hb)
        exact_mod_cast hr
      _ = _ := by simp

theorem rationalRangeLattice_full
    {J C : Type*} [Fintype J] [Fintype C]
    (B : Matrix J C ℚ) (W : Submodule ℝ (J → ℝ))
    (hW : LinearMap.range (Matrix.of (fun i j => (B i j : ℝ))).mulVecLin = W)
    {H : ℕ} (hB : ∀ i j, RationalHeightLE (B i j) H) :
    IsZLattice ℝ (latticeSection (standardEuclideanLattice J) (euclideanSubspace W)) := by
  obtain ⟨v, hv, hmem, _⟩ := exists_bounded_integral_span_of_rational_range B W hW hB
  constructor
  apply top_unique
  rw [← hv]
  apply span_mono
  rintro _ ⟨j, rfl⟩
  exact hmem j

theorem jointRationalSpaceLattice_full
    {J C V : Type*} [Fintype J] [Fintype C] [Fintype V]
    (B : Matrix J C ℚ) (A : Matrix V J ℚ) {H R : ℕ}
    (hH : 1 ≤ H) (hR : 1 ≤ R)
    (hB : ∀ i j, RationalHeightLE (B i j) H) (hA : ∀ v j, RationalHeightLE (A v j) R) :
    IsZLattice ℝ (latticeSection (standardEuclideanLattice J)
      (euclideanSubspace (VectorPolynomial.jointRationalSpace B A))) := by
  obtain ⟨P, hP, hW⟩ := VectorPolynomial.exists_jointRationalSpace_generators B A hH hR hB hA
  exact rationalRangeLattice_full P _ hW hP

end Erdos3

end

section

namespace Erdos3

open Module Submodule BohrLattice.MinkowskiSecondBox
open scoped BigOperators

theorem exists_short_projected_integer_basis {J : Type*} [Fintype J]
    (W : Submodule ℝ (EuclideanSpace ℝ J))
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice J) W)] :
    let n := finrank ℝ Wᗮ
    ∃ b : Basis (Fin n) ℝ Wᗮ,
      span ℤ (Set.range b) = projectedIntegerLattice W ∧
      (∏ i, ‖b i‖) ≤ (n : ℝ) ^ n * minkowskiSecondConstant n *
        ZLattice.covolume (projectedIntegerLattice W) ∧
      ∀ i, ‖b i‖ ≤ (n : ℝ) * n.factorial * minkowskiSecondConstant n := by
  simpa only [mul_one] using exists_short_euclidean_lattice_basis
    (projectedIntegerLattice W) (stdOrthonormalBasis ℝ Wᗮ) (projectedIntegerGenerator W)
    (projectedIntegerGenerator_span W) (projectedIntegerGenerator_mem W)
    (projectedIntegerGenerator_norm_le W)

end Erdos3

end

section

namespace Erdos3

open Module Submodule
open scoped Matrix

variable {D I J : Type*} [Fintype D] [Fintype I] [Fintype J]

noncomputable def standardLatticeIntegerLift (W : Submodule ℝ (EuclideanSpace ℝ D))
    (bP : Basis J ℝ Wᗮ) (hP : span ℤ (Set.range bP) = projectedIntegerLattice W) :
    (J → ℤ) →ₗ[ℤ] standardEuclideanLattice D :=
  latticeIntegerLift (standardEuclideanLattice D) W
    (integerBasisOfReal (projectedIntegerLattice W) bP hP)

theorem standardLatticeIntegerLift_projection (W : Submodule ℝ (EuclideanSpace ℝ D))
    (bP : Basis J ℝ Wᗮ) (hP : span ℤ (Set.range bP) = projectedIntegerLattice W) (z : J → ℤ) :
    Wᗮ.orthogonalProjectionOnto (standardLatticeIntegerLift W bP hP z).val =
      bP.equivFun.symm (fun j => (z j : ℝ)) := by
  have h := latticeIntegerLift_projection (standardEuclideanLattice D) W
    (integerBasisOfReal (projectedIntegerLattice W) bP hP) z
  exact h.trans (integerBasisOfReal_synthesis (projectedIntegerLattice W) bP hP z)

noncomputable def standardLatticeCoordinates (W : Submodule ℝ (EuclideanSpace ℝ D))
    (bW : Basis I ℤ (latticeSection (standardEuclideanLattice D) W))
    (bP : Basis J ℝ Wᗮ) (hP : span ℤ (Set.range bP) = projectedIntegerLattice W) :
    (D → ℤ) ≃ₗ[ℤ] (J ⊕ I → ℤ) :=
  (standardEuclideanLinearEquiv D).trans
    ((latticeSignedCoordinates (standardEuclideanLattice D) W bW
      (integerBasisOfReal (projectedIntegerLattice W) bP hP)).trans
      (LinearEquiv.sumArrowLequivProdArrow J I ℤ ℤ).symm)

theorem standardLatticeCoordinates_residue [DecidableEq D]
    (W : Submodule ℝ (EuclideanSpace ℝ D))
    (bW : Basis I ℤ (latticeSection (standardEuclideanLattice D) W))
    (bP : Basis J ℝ Wᗮ) (hP : span ℤ (Set.range bP) = projectedIntegerLattice W)
    (M : ℕ) [NeZero M] :
    ∃ A : Matrix (J ⊕ I) D ℤ,
      (∀ i j, 0 ≤ A i j ∧ A i j < M) ∧
      ∀ β, integerResidueMap (J ⊕ I) M (standardLatticeCoordinates W bW bP hP β) =
        integerResidueMatrix A M *ᵥ integerResidueMap D M β :=
  exists_bounded_integerMap_residue_matrix (standardLatticeCoordinates W bW bP hP).toLinearMap M

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

theorem standardLatticeIntegerLift_sheet {D J : Type*} [Fintype D] [Fintype J]
    (W : Submodule ℝ (EuclideanSpace ℝ D)) (bP : Basis J ℝ Wᗮ)
    (hP : span ℤ (Set.range bP) = projectedIntegerLattice W) (z : J → ℤ) (u : W) :
    latticeSheetQuotient (standardEuclideanLattice D) W
      (latticeBasisEquiv (projectedIntegerLattice W) bP hP z) u =
      QuotientAddGroup.mk (u - W.orthogonalProjectionOnto (standardLatticeIntegerLift W bP hP z).val) := by
  apply latticeSheetQuotient_eq_of_lift
  exact (standardLatticeIntegerLift_projection W bP hP z).trans
    (latticeBasisEquiv_synthesis (projectedIntegerLattice W) bP hP z).symm

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MixedCoefficientSmallSupport
namespace OAI

section

namespace Erdos3

open MeasureTheory Module _root_.Set
open scoped ENNReal

variable {E T I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Countable T] [Fintype I]

noncomputable def translatedQuotientChart (Λ : Submodule ℤ E) (v : T → E)
    (x : E × T) : E ⧸ Λ.toAddSubgroup := QuotientAddGroup.mk (x.1 - v x.2)

theorem translatedQuotientChart_measurable (Λ : Submodule ℤ E) (v : T → E) :
    Measurable (translatedQuotientChart Λ v) := by
  have hq : Measurable (QuotientAddGroup.mk : E → E ⧸ Λ.toAddSubgroup) := measurable_quotient_mk''
  exact hq.comp (measurable_fst.sub ((measurable_of_countable v).comp measurable_snd))

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Countable T] in
theorem translatedQuotientChart_image (Λ : Submodule ℤ E) (v : T → E) (S : Set (E × T)) :
    translatedQuotientChart Λ v '' S =
      ⋃ t, (fun x => (QuotientAddGroup.mk (x - v t) : E ⧸ Λ.toAddSubgroup)) ''
        ((fun x => (x, t)) ⁻¹' S) := by
  ext q
  constructor
  · rintro ⟨⟨x, t⟩, hx, rfl⟩
    exact mem_iUnion.mpr ⟨t, x, hx, rfl⟩
  · intro h
    obtain ⟨t, x, hx, rfl⟩ := mem_iUnion.mp h
    exact ⟨(x,t), hx, rfl⟩

omit [MeasurableSingletonClass T] in
theorem translatedQuotientChart_measurable_image (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    (v : T → E) {S : Set (E × T)} (hS : MeasurableSet S)
    (hinj : InjOn (translatedQuotientChart Λ v) S) :
    MeasurableSet (translatedQuotientChart Λ v '' S) := by
  let : IsClosed (Λ.toAddSubgroup : Set E) := AddSubgroup.isClosed_of_discrete
  rw [translatedQuotientChart_image]
  apply MeasurableSet.iUnion
  intro t
  have hq : Continuous (fun x : E => (QuotientAddGroup.mk (x - v t) : E ⧸ Λ.toAddSubgroup)) :=
    continuous_quotient_mk'.comp (continuous_id.sub continuous_const)
  apply (hS.preimage (measurable_id.prodMk measurable_const)).image_of_continuousOn_injOn
    hq.continuousOn
  intro x hx y hy he
  exact congrArg Prod.fst (hinj hx hy he)

theorem translatedQuotientChart_haar_image (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (b : Basis I ℤ Λ)
    (μ : Measure (E ⧸ Λ.toAddSubgroup)) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    (v : T → E) {S : Set (E × T)} (hS : MeasurableSet S)
    (hinj : InjOn (translatedQuotientChart Λ v) S) :
    μ (translatedQuotientChart Λ v '' S) =
      (volume.prod (Measure.count : Measure T)) S / ENNReal.ofReal (ZLattice.covolume Λ) := by
  rw [translatedQuotientChart_image, Measure.prod_apply_symm hS, lintegral_count]
  apply lattice_quotient_haar_countable_sheets Λ b μ v
  · intro t
    exact hS.preimage (measurable_id.prodMk measurable_const)
  · intro t x hx y hy he
    exact congrArg Prod.fst (hinj hx hy he)
  · intro s t hst
    apply Set.disjoint_left.mpr
    rintro q ⟨x, hx, rfl⟩ ⟨y, hy, he⟩
    exact hst (congrArg Prod.snd (hinj hx hy he.symm))

theorem translatedQuotientChart_map_restrict (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (b : Basis I ℤ Λ)
    (μ : Measure (E ⧸ Λ.toAddSubgroup)) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    (v : T → E) {S : Set (E × T)} (hS : MeasurableSet S)
    (hinj : InjOn (translatedQuotientChart Λ v) S) :
    Measure.map (translatedQuotientChart Λ v) ((volume.prod (Measure.count : Measure T)).restrict S) =
      ENNReal.ofReal (ZLattice.covolume Λ) • μ.restrict (translatedQuotientChart Λ v '' S) := by
  have hq := translatedQuotientChart_measurable Λ v
  ext B hB
  rw [Measure.map_apply hq hB, Measure.restrict_apply (hB.preimage hq),
    Measure.smul_apply, Measure.restrict_apply hB, smul_eq_mul]
  have hm := (hB.preimage hq).inter hS
  have hi := hinj.mono (inter_subset_right : (translatedQuotientChart Λ v ⁻¹' B ∩ S) ⊆ S)
  have he := translatedQuotientChart_haar_image Λ b μ v hm hi
  have hs : translatedQuotientChart Λ v '' (translatedQuotientChart Λ v ⁻¹' B ∩ S) =
      B ∩ translatedQuotientChart Λ v '' S := by
    ext q
    constructor
    · rintro ⟨x, ⟨hx, hxs⟩, rfl⟩
      exact ⟨hx, x, hxs, rfl⟩
    · rintro ⟨hqB, x, hxS, rfl⟩
      exact ⟨x, ⟨hqB, hxS⟩, rfl⟩
  have hc : ENNReal.ofReal (ZLattice.covolume Λ) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (ZLattice.covolume_pos Λ volume)).ne'
  have hx := (ENNReal.eq_div_iff hc ENNReal.ofReal_ne_top).mp he
  rw [hs] at hx
  exact hx.symm

theorem translatedQuotientChart_embedding (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    (v : T → E) {S : Set (E × T)} (hS : MeasurableSet S)
    (hinj : InjOn (translatedQuotientChart Λ v) S) :
    MeasurableEmbedding (fun x : S => translatedQuotientChart Λ v x.val) := by
  refine ⟨fun x y he => Subtype.ext (hinj x.property y.property he),
    (translatedQuotientChart_measurable Λ v).comp measurable_subtype_coe, ?_⟩
  intro A hA
  have hm := (MeasurableEmbedding.subtype_coe hS).measurableSet_image' hA
  have hi := hinj.mono (show ((↑) : S → E × T) '' A ⊆ S by rintro x ⟨y, hy, rfl⟩; exact y.property)
  have he := translatedQuotientChart_measurable_image Λ v hm hi
  simpa only [image_image] using he

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module Submodule _root_.Set

variable {D : Type*} [Fintype D] {n : ℕ}

noncomputable def normalizedLatticePoint (W : Submodule ℝ (EuclideanSpace ℝ D))
    (b : Basis (Fin n) ℝ Wᗮ) (x : W × (Fin n → ℤ)) : EuclideanSpace ℝ D :=
  (normalizedOrthogonalChart W b).symm (x.1, fun i => (x.2 i : ℝ) / (basisAxisScale b i : ℝ))

noncomputable def normalizedLatticeQuotient (W : Submodule ℝ (EuclideanSpace ℝ D))
    (b : Basis (Fin n) ℝ Wᗮ) (hb : span ℤ (Set.range b) = projectedIntegerLattice W) :
    W × (Fin n → ℤ) → W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup :=
  translatedQuotientChart (latticeSection (standardEuclideanLattice D) W)
    (fun z => projectedLatticeShift (standardEuclideanLattice D) W
      (latticeBasisEquiv (projectedIntegerLattice W) b hb z))

theorem normalizedLatticeQuotient_measurable (W : Submodule ℝ (EuclideanSpace ℝ D))
    (b : Basis (Fin n) ℝ Wᗮ) (hb : span ℤ (Set.range b) = projectedIntegerLattice W) :
    Measurable (normalizedLatticeQuotient W b hb) := translatedQuotientChart_measurable _ _

theorem normalizedLatticePoint_eq_sheet (W : Submodule ℝ (EuclideanSpace ℝ D))
    (b : Basis (Fin n) ℝ Wᗮ) (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
    (x : W × (Fin n → ℤ)) : normalizedLatticePoint W b x =
      latticeSheetPoint W (latticeBasisEquiv (projectedIntegerLattice W) b hb x.2).val x.1 :=
  (normalizedLatticeSheet_point W (projectedIntegerLattice W) b hb x.2 x.1).symm

theorem normalizedLatticeQuotient_injOn (W : Submodule ℝ (EuclideanSpace ℝ D))
    (b : Basis (Fin n) ℝ Wᗮ) (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
    {Ω : Set (EuclideanSpace ℝ D)} (hΩ : Ω ⊆ standardLatticeSmallBox D) :
    Set.InjOn (normalizedLatticeQuotient W b hb) (normalizedLatticePoint W b ⁻¹' Ω) := by
  intro x hx y hy he
  have hx' : latticeSheetPoint W (latticeBasisEquiv (projectedIntegerLattice W) b hb x.2).val x.1 ∈ Ω := by
    rw [← normalizedLatticePoint_eq_sheet W b hb]
    exact hx
  have hy' : latticeSheetPoint W (latticeBasisEquiv (projectedIntegerLattice W) b hb y.2).val y.1 ∈ Ω := by
    rw [← normalizedLatticePoint_eq_sheet W b hb]
    exact hy
  have h := latticeSheetQuotient_injective_on_region (standardEuclideanLattice D) W
    (fun a ha c hc hac => standardLatticeSmallBox_separates D (hΩ ha) (hΩ hc) hac) hx' hy' he
  exact Prod.ext h.2 ((latticeBasisEquiv (projectedIntegerLattice W) b hb).injective h.1)

end Erdos3

end

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

open MeasureTheory Module Submodule

variable {D : Type*} [Fintype D] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)

noncomputable def normalizedChartReference (Ω : Set (EuclideanSpace ℝ D)) :
    Measure (W × (Fin n → ℤ)) :=
  (ENNReal.ofReal (ZLattice.covolume (latticeSection (standardEuclideanLattice D) W)))⁻¹ •
    (volume.prod (Measure.count : Measure (Fin n → ℤ))).restrict
      (normalizedLatticePoint W b ⁻¹' Ω)

def normalizedChartRegion (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
    (Ω : Set (EuclideanSpace ℝ D)) :
    Set (W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup) :=
  normalizedLatticeQuotient W b hb '' (normalizedLatticePoint W b ⁻¹' Ω)

variable [IsZLattice ℝ (latticeSection (standardEuclideanLattice D) W)]
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
variable (μ : Measure (W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup))
variable [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]

end Erdos3

end

section

namespace Erdos3

open Module Submodule
open scoped BigOperators

variable {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)

theorem normalizedLatticeQuotient_linear_lift (x : W × (Fin n → ℤ)) :
    normalizedLatticeQuotient W b hb x =
      QuotientAddGroup.mk (x.1 - W.orthogonalProjectionOnto
        (standardLatticeIntegerLift W b hb x.2).val) :=
  standardLatticeIntegerLift_sheet W b hb x.2 x.1

noncomputable def normalizedLatticePointHom :
    W × (Fin n → ℤ) →+ EuclideanSpace ℝ D where
  toFun := normalizedLatticePoint W b
  map_zero' := by
    simp [normalizedLatticePoint]
    rfl
  map_add' x y := by
    unfold normalizedLatticePoint
    rw [← map_add]
    congr 1
    ext i
    · rfl
    · simp [add_div]

noncomputable def orthonormalMixedChartHom (o : OrthonormalBasis I ℝ W) :
    ((I → ℝ) × (Fin n → ℤ)) →+ (W × (Fin n → ℤ)) where
  toFun := orthonormalMixedChart o
  map_zero' := by
    change (orthonormalChart o 0, (0 : Fin n → ℤ)) = 0
    simp
  map_add' x y := by
    change (orthonormalChart o (x.1 + y.1), x.2 + y.2) =
      (orthonormalChart o x.1, x.2) + (orthonormalChart o y.1, y.2)
    simp only [map_add, Prod.mk_add_mk]

end Erdos3

end

section

namespace Erdos3

open Module Submodule
open scoped BigOperators

theorem affineProbabilityProfile_abs_le (c : ℝ) {w x : ℝ} (hw : 0 < w)
    (hx : affineProbabilityProfile c w x ≠ 0) : |x| ≤ |c| + w := by
  have hb := affineProbabilityProfile_support c hw hx
  have ht := abs_add_le (x - c) c
  rw [sub_add_cancel] at ht
  linarith

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

theorem mixedCoefficient_small_support {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}
    (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ) (o : OrthonormalBasis I ℝ W)
    {C R : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hchart : ∀ p, ‖(normalizedOrthogonalChart W b).symm p‖ ≤ C * ‖p‖)
    (hsmall : C * ((Fintype.card I : ℝ) + 1) * R ≤ 1 / 4)
    (c w : I → ℝ) (hw : ∀ i, 0 < w i) (hcw : ∀ i, |c i| + w i ≤ R) (p : Fin n → PMF ℤ)
    (hp : ∀ i k, k ∈ (p i).support → |(k : ℝ) / basisAxisScale b i| ≤ R)
    (x : (I → ℝ) × (Fin n → ℤ)) (hx : mixedCoefficientDensity c w p x ≠ 0) :
    normalizedLatticePoint W b (orthonormalMixedChart o x) ∈ standardLatticeSmallBox D := by
  have hs := (mixedCoefficientDensity_support c w p x).mp hx
  exact normalizedMixedPoint_small W b o hC hR hchart hsmall x
    (fun i => (affineProbabilityProfile_abs_le _ (hw i) (hs.1 i)).trans (hcw i))
    (fun i => hp i _ (hs.2 i))

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedRealPoint
namespace OAI

section

namespace Erdos3

open Module Submodule

variable {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (o : OrthonormalBasis I ℝ W)

noncomputable def mixedRealPoint : ((I → ℝ) × (Fin n → ℝ)) →ₗ[ℝ] EuclideanSpace ℝ D :=
  (normalizedOrthogonalChart W b).symm.toLinearMap.comp
    ((orthonormalChart o).toLinearMap.prodMap (LinearMap.id))

theorem mixedRealPoint_integer (u : I → ℝ) (z : Fin n → ℤ) :
    mixedRealPoint W b o (u, fun i => (z i : ℝ) / basisAxisScale b i) =
      normalizedLatticePoint W b (orthonormalMixedChart o (u, z)) := rfl

theorem mixedRealPoint_norm_le {C R : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hchart : ∀ v, ‖(normalizedOrthogonalChart W b).symm v‖ ≤ C * ‖v‖)
    (u : I → ℝ) (z : Fin n → ℝ) (hu : ∀ i, |u i| ≤ R) (hz : ∀ i, |z i| ≤ R) :
    ‖mixedRealPoint W b o (u, z)‖ ≤ C * (((Fintype.card I : ℝ) + 1) * R) := by
  have hu' : ‖u‖ ≤ R := (pi_norm_le_iff_of_nonneg hR).mpr (by simpa only [Real.norm_eq_abs] using hu)
  have hz' : ‖z‖ ≤ R := (pi_norm_le_iff_of_nonneg hR).mpr (by simpa only [Real.norm_eq_abs] using hz)
  have ho := (orthonormalChart_norm_le o u).trans (mul_le_mul_of_nonneg_left hu' (Nat.cast_nonneg _))
  have hp : ‖(orthonormalChart o u, z)‖ ≤ ((Fintype.card I : ℝ) + 1) * R := by
    rw [Prod.norm_def]
    apply max_le <;> nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card I)]
  exact (hchart _).trans (mul_le_mul_of_nonneg_left hp hC)

theorem mixedRealPoint_scaled_coordinate_bound {C R S : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R) (hS : 0 < S)
    (hchart : ∀ v, ‖(normalizedOrthogonalChart W b).symm v‖ ≤ C * ‖v‖)
    (u : I → ℝ) (z : Fin n → ℝ) (hu : ∀ i, |u i| * S ≤ R) (hz : ∀ i, |z i| * S ≤ R) (d : D) :
    |mixedRealPoint W b o (u, z) d| ≤ C * (((Fintype.card I : ℝ) + 1) * R) / S := by
  apply (le_div_iff₀ hS).mpr
  have hscale := mixedRealPoint_norm_le W b o hC hR hchart (S • u) (S • z)
    (fun i => by simpa only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hS, mul_comm] using hu i)
    (fun i => by simpa only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hS, mul_comm] using hz i)
  have he : mixedRealPoint W b o (S • u, S • z) = S • mixedRealPoint W b o (u, z) :=
    (mixedRealPoint W b o).map_smul S (u, z)
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos hS] at hscale
  have hd : |mixedRealPoint W b o (u, z) d| ≤ ‖mixedRealPoint W b o (u, z)‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (mixedRealPoint W b o (u, z)) d
  exact (mul_le_mul_of_nonneg_right hd hS.le).trans (by simpa only [mul_comm] using hscale)

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

noncomputable def mixedRealCoordinates :
    EuclideanSpace ℝ D →ₗ[ℝ] ((I → ℝ) × (Fin n → ℝ)) :=
  ((orthonormalChart o).symm.toLinearMap.prodMap LinearMap.id).comp
    (normalizedOrthogonalChart W b).toLinearMap

theorem mixedRealCoordinates_point (x : (I → ℝ) × (Fin n → ℝ)) :
    mixedRealCoordinates W b o (mixedRealPoint W b o x) = x := by
  change ((orthonormalChart o).symm
      ((normalizedOrthogonalChart W b) ((normalizedOrthogonalChart W b).symm
        ((orthonormalChart o) x.1, x.2))).1,
    ((normalizedOrthogonalChart W b) ((normalizedOrthogonalChart W b).symm
        ((orthonormalChart o) x.1, x.2))).2) = x
  simp only [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.symm_apply_apply]

theorem mixedRealCoordinates_integer (u : I → ℝ) (z : Fin n → ℤ) :
    mixedRealCoordinates W b o (normalizedLatticePoint W b (orthonormalMixedChart o (u, z))) =
      (u, fun i => (z i : ℝ) / basisAxisScale b i) := by
  rw [← mixedRealPoint_integer W b o]
  exact mixedRealCoordinates_point W b o _

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ProjectedAxisBudgets
namespace OAI

section

namespace Erdos3

open Module Submodule MeasureTheory BohrLattice.MinkowskiSecondBox
open scoped BigOperators

noncomputable def projectedAxisNormBudget (n : ℕ) : ℝ :=
  ((n : ℝ) + 1) * n.factorial * minkowskiSecondConstant n

noncomputable def projectedAxisDefectBudget (n : ℕ) : ℝ :=
  ((n : ℝ) + 1) ^ n * minkowskiSecondConstant n

theorem projectedAxisNormBudget_pos (n : ℕ) : 0 < projectedAxisNormBudget n := by
  unfold projectedAxisNormBudget minkowskiSecondConstant
  positivity

theorem projectedAxisDefectBudget_pos (n : ℕ) : 0 < projectedAxisDefectBudget n := by
  unfold projectedAxisDefectBudget minkowskiSecondConstant
  positivity

theorem exists_projected_basis_with_axis_budgets {J : Type*} [Fintype J]
    (W : Submodule ℝ (EuclideanSpace ℝ J))
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice J) W)] :
    let n := finrank ℝ Wᗮ
    ∃ b : Basis (Fin n) ℝ Wᗮ,
      span ℤ (Set.range b) = projectedIntegerLattice W ∧
      (∏ i, ‖b i‖) ≤ projectedAxisDefectBudget n * ZLattice.covolume (projectedIntegerLattice W) ∧
      ∀ i, ‖b i‖ ≤ projectedAxisNormBudget n := by
  let n := finrank ℝ Wᗮ
  obtain ⟨b, hb, hprod, hnorm⟩ := exists_short_projected_integer_basis W
  have hpow : (n : ℝ) ^ n ≤ ((n : ℝ) + 1) ^ n :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (le_add_of_nonneg_right zero_le_one) n
  have hC := minkowskiSecondConstant_nonneg n
  refine ⟨b, hb, ?_, ?_⟩
  · exact hprod.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hpow hC)
      (ZLattice.covolume_pos (projectedIntegerLattice W) volume).le)
  · intro i
    exact (hnorm i).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (Nat.cast_nonneg _)) hC)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.QuantitativeProjectedChart
namespace OAI

section

namespace Erdos3

open Module Submodule MeasureTheory
open scoped BigOperators

theorem exists_normalized_projected_chart {J : Type*} [Fintype J]
    (W : Submodule ℝ (EuclideanSpace ℝ J))
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice J) W)] :
    let n := finrank ℝ Wᗮ
    let B := projectedAxisNormBudget n
    let D := projectedAxisDefectBudget n
    ∃ b : Basis (Fin n) ℝ Wᗮ,
      span ℤ (Set.range b) = projectedIntegerLattice W ∧
      (∀ i, 0 < basisAxisScale b i) ∧
      (∀ i, 1 ≤ ‖normalizedAxisBasis b i‖ ∧ ‖normalizedAxisBasis b i‖ ≤ B + 1) ∧
      (∀ x, ‖normalizedOrthogonalChart W b x‖ ≤
        (1 + (n : ℝ) * n.factorial * (B + 1) ^ (n - 1) * D) * ‖x‖) ∧
      (∀ p, ‖(normalizedOrthogonalChart W b).symm p‖ ≤ (1 + (n : ℝ) * (B + 1)) * ‖p‖) ∧
      1 / ((n.factorial : ℝ) * (B + 1) ^ n) ≤
        ZLattice.covolume (latticeSection (standardEuclideanLattice J) W) /
          (∏ i, (basisAxisScale b i : ℝ)) ∧
      ZLattice.covolume (latticeSection (standardEuclideanLattice J) W) /
          (∏ i, (basisAxisScale b i : ℝ)) ≤ D := by
  let n := finrank ℝ Wᗮ
  let o := stdOrthonormalBasis ℝ Wᗮ
  obtain ⟨b, hspan, hprod, hnorm⟩ := exists_projected_basis_with_axis_budgets W
  have hprod' : (∏ i, ‖b i‖) ≤ projectedAxisDefectBudget n *
      ZLattice.covolume (span ℤ (Set.range b)) := by
    rw [hspan]
    exact hprod
  have hpair : ZLattice.covolume (latticeSection (standardEuclideanLattice J) W) *
      ZLattice.covolume (span ℤ (Set.range b)) = 1 := by
    rw [hspan]
    exact projectedIntegerLattice_covolume W
  refine ⟨b, hspan, basisAxisScale_pos b, normalizedAxisBasis_norm_bounds b hnorm,
    ?_, ?_, ?_⟩
  · exact normalizedOrthogonalChart_norm_le W b o (projectedAxisNormBudget_pos n).le
      (projectedAxisDefectBudget_pos n) hnorm hprod'
  · exact normalizedOrthogonalChart_symm_norm_le W b (projectedAxisNormBudget_pos n).le hnorm
  · exact normalizedAxisBasis_covolume_ratio_bounds o b (projectedAxisDefectBudget_pos n)
      hnorm hprod' hpair

end Erdos3

end

section

namespace Erdos3

theorem projectedAxisNormBudget_le_exp (n : ℕ) :
    projectedAxisNormBudget n ≤ Real.exp (4 * ((n : ℝ) + 1) ^ 2) := by
  have hn := Real.add_one_le_exp (n : ℝ)
  have hf := factorial_le_exp_sq n
  have hm := BohrProgression.minkowskiSecondConstant_le_exp n
  have hm0 := BohrLattice.MinkowskiSecondBox.minkowskiSecondConstant_nonneg n
  unfold projectedAxisNormBudget
  calc
    _ ≤ Real.exp n * Real.exp ((n : ℝ) ^ 2) * Real.exp (2 * (n : ℝ) ^ 2) := by
      gcongr
    _ = Real.exp ((n : ℝ) + (n : ℝ) ^ 2 + 2 * (n : ℝ) ^ 2) := by
      rw [← Real.exp_add, ← Real.exp_add]
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) n])

theorem projectedAxisDefectBudget_le_exp (n : ℕ) :
    projectedAxisDefectBudget n ≤ Real.exp (4 * ((n : ℝ) + 1) ^ 2) := by
  have hn := Real.add_one_le_exp (n : ℝ)
  have hm := BohrProgression.minkowskiSecondConstant_le_exp n
  have hm0 := BohrLattice.MinkowskiSecondBox.minkowskiSecondConstant_nonneg n
  unfold projectedAxisDefectBudget
  calc
    _ ≤ (Real.exp n) ^ n * Real.exp (2 * (n : ℝ) ^ 2) := by gcongr
    _ = Real.exp ((n : ℝ) * n + 2 * (n : ℝ) ^ 2) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) n])

theorem projectedAxisNormBudget_add_one_le_exp (n : ℕ) :
    projectedAxisNormBudget n + 1 ≤ Real.exp (5 * ((n : ℝ) + 1) ^ 2) := by
  have h := one_add_le_exp_succ (by positivity : 0 ≤ 4 * ((n : ℝ) + 1) ^ 2)
    (projectedAxisNormBudget_le_exp n)
  calc
    _ ≤ Real.exp (4 * ((n : ℝ) + 1) ^ 2 + 1) := by simpa only [add_comm] using h
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) n])

theorem projectedChart_forwardBudget_le_exp (n : ℕ) :
    1 + (n : ℝ) * n.factorial * (projectedAxisNormBudget n + 1) ^ (n - 1) *
      projectedAxisDefectBudget n ≤ Real.exp (20 * ((n : ℝ) + 1) ^ 3) := by
  have hn : (n : ℝ) ≤ Real.exp n := by linarith [Real.add_one_le_exp (n : ℝ)]
  have hf := factorial_le_exp_sq n
  have hb := projectedAxisNormBudget_add_one_le_exp n
  have hd := projectedAxisDefectBudget_le_exp n
  have hd0 := (projectedAxisDefectBudget_pos n).le
  have hb0 := (projectedAxisNormBudget_pos n).le
  have hp : (projectedAxisNormBudget n + 1) ^ (n - 1) ≤
      (projectedAxisNormBudget n + 1) ^ n :=
    pow_le_pow_right₀ (by linarith) (Nat.sub_le _ _)
  have hterm : (n : ℝ) * n.factorial * (projectedAxisNormBudget n + 1) ^ (n - 1) *
      projectedAxisDefectBudget n ≤
      Real.exp ((n : ℝ) + (n : ℝ) ^ 2 + n * (5 * ((n : ℝ) + 1) ^ 2) +
        4 * ((n : ℝ) + 1) ^ 2) := by
    calc
      _ ≤ (n : ℝ) * n.factorial * (projectedAxisNormBudget n + 1) ^ n *
          projectedAxisDefectBudget n := by gcongr
      _ ≤ Real.exp n * Real.exp ((n : ℝ) ^ 2) *
          (Real.exp (5 * ((n : ℝ) + 1) ^ 2)) ^ n *
          Real.exp (4 * ((n : ℝ) + 1) ^ 2) := by gcongr
      _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  apply (one_add_le_exp_succ (by positivity) hterm).trans
  apply Real.exp_le_exp.mpr
  have hn0 := Nat.cast_nonneg (α := ℝ) n
  have hn3 : 0 ≤ (n : ℝ) ^ 3 := by positivity
  nlinarith

theorem projectedChart_inverseBudget_le_exp (n : ℕ) :
    1 + (n : ℝ) * (projectedAxisNormBudget n + 1) ≤
      Real.exp (20 * ((n : ℝ) + 1) ^ 3) := by
  have hn : (n : ℝ) ≤ Real.exp n := by linarith [Real.add_one_le_exp (n : ℝ)]
  have hb := projectedAxisNormBudget_add_one_le_exp n
  have hb0 := (projectedAxisNormBudget_pos n).le
  have hterm : (n : ℝ) * (projectedAxisNormBudget n + 1) ≤
      Real.exp ((n : ℝ) + 5 * ((n : ℝ) + 1) ^ 2) := by
    calc
      _ ≤ Real.exp n * Real.exp (5 * ((n : ℝ) + 1) ^ 2) := by gcongr
      _ = _ := (Real.exp_add _ _).symm
  apply (one_add_le_exp_succ (by positivity) hterm).trans
  apply Real.exp_le_exp.mpr
  have hn0 := Nat.cast_nonneg (α := ℝ) n
  have hn3 : 0 ≤ (n : ℝ) ^ 3 := by positivity
  nlinarith

theorem projectedChart_volumeBudget_le_exp (n : ℕ) :
    (n.factorial : ℝ) * (projectedAxisNormBudget n + 1) ^ n ≤
      Real.exp (20 * ((n : ℝ) + 1) ^ 3) := by
  have hf := factorial_le_exp_sq n
  have hb := projectedAxisNormBudget_add_one_le_exp n
  have hb0 := (projectedAxisNormBudget_pos n).le
  calc
    _ ≤ Real.exp ((n : ℝ) ^ 2) * (Real.exp (5 * ((n : ℝ) + 1) ^ 2)) ^ n := by gcongr
    _ = Real.exp ((n : ℝ) ^ 2 + n * (5 * ((n : ℝ) + 1) ^ 2)) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hn0 := Nat.cast_nonneg (α := ℝ) n
      have hn3 : 0 ≤ (n : ℝ) ^ 3 := by positivity
      nlinarith

theorem projectedChart_defectBudget_le_exp (n : ℕ) :
    projectedAxisDefectBudget n ≤ Real.exp (20 * ((n : ℝ) + 1) ^ 3) := by
  apply (projectedAxisDefectBudget_le_exp n).trans
  apply Real.exp_le_exp.mpr
  have hn0 := Nat.cast_nonneg (α := ℝ) n
  have hn3 : 0 ≤ (n : ℝ) ^ 3 := by positivity
  nlinarith

end Erdos3

end

section

namespace Erdos3

open Module Submodule MeasureTheory
open scoped BigOperators

theorem exists_quantitative_projected_chart {J : Type*} [Fintype J]
    (W : Submodule ℝ (EuclideanSpace ℝ J))
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice J) W)] :
    let n := finrank ℝ Wᗮ
    let C : ℝ := 20 * ((n : ℝ) + 1) ^ 3
    ∃ b : Basis (Fin n) ℝ Wᗮ,
      span ℤ (Set.range b) = projectedIntegerLattice W ∧
      (∀ i, 0 < basisAxisScale b i) ∧
      (∀ x, ‖normalizedOrthogonalChart W b x‖ ≤ Real.exp C * ‖x‖) ∧
      (∀ p, ‖(normalizedOrthogonalChart W b).symm p‖ ≤ Real.exp C * ‖p‖) ∧
      Real.exp (-C) ≤
        ZLattice.covolume (latticeSection (standardEuclideanLattice J) W) /
          (∏ i, (basisAxisScale b i : ℝ)) ∧
      ZLattice.covolume (latticeSection (standardEuclideanLattice J) W) /
          (∏ i, (basisAxisScale b i : ℝ)) ≤ Real.exp C := by
  let n := finrank ℝ Wᗮ
  obtain ⟨b, hspan, hK, _, hf, hi, hvlo, hvhi⟩ := exists_normalized_projected_chart W
  refine ⟨b, hspan, hK, ?_, ?_, ?_, ?_⟩
  · intro x
    exact (hf x).trans (mul_le_mul_of_nonneg_right (projectedChart_forwardBudget_le_exp n)
      (norm_nonneg x))
  · intro p
    exact (hi p).trans (mul_le_mul_of_nonneg_right (projectedChart_inverseBudget_le_exp n)
      (norm_nonneg p))
  · apply le_trans _ hvlo
    rw [Real.exp_neg, one_div]
    apply (inv_le_inv₀ (Real.exp_pos _) _).2
    · exact projectedChart_volumeBudget_le_exp n
    · have hB := projectedAxisNormBudget_pos n
      positivity
  · exact hvhi.trans (projectedChart_defectBudget_le_exp n)

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

noncomputable def normalizedQuotientDensity (W : Submodule ℝ (EuclideanSpace ℝ D))
    (b : Basis (Fin n) ℝ Wᗮ) (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
    (Ω : Set (EuclideanSpace ℝ D)) (f : W × (Fin n → ℤ) → ℝ) :
    (W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup) → ℝ :=
  restrictedChartDensity (normalizedLatticeQuotient W b hb) (normalizedLatticePoint W b ⁻¹' Ω)
    (ZLattice.covolume (latticeSection (standardEuclideanLattice D) W)) f

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

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module Submodule _root_.Set

variable {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W) (o : OrthonormalBasis I ℝ W)

noncomputable def canonicalMixedDensity (c w : I → ℝ) (p : Fin n → PMF ℤ) :
    (W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup) → ℝ :=
  normalizedQuotientDensity W b hb (standardLatticeSmallBox D) (orthonormalMixedDensity o c w p)

theorem canonicalMixedDensity_apply (c w : I → ℝ) (p : Fin n → PMF ℤ)
    {x : (I → ℝ) × (Fin n → ℤ)}
    (hx : normalizedLatticePoint W b (orthonormalMixedChart o x) ∈ standardLatticeSmallBox D) :
    canonicalMixedDensity W b hb o c w p (normalizedLatticeQuotient W b hb (orthonormalMixedChart o x)) =
      ZLattice.covolume (latticeSection (standardEuclideanLattice D) W) * mixedCoefficientDensity c w p x := by
  exact (normalizedQuotientDensity_apply W b hb (Subset.rfl) (orthonormalMixedDensity o c w p) hx).trans
    (by simp only [orthonormalMixedDensity, MeasurableEquiv.symm_apply_apply])

theorem canonicalMixedDensity_recover (c w : I → ℝ) (p : Fin n → PMF ℤ)
    {y : W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup}
    (hy : canonicalMixedDensity W b hb o c w p y ≠ 0) :
    ∃ x : (I → ℝ) × (Fin n → ℤ),
      normalizedLatticePoint W b (orthonormalMixedChart o x) ∈ standardLatticeSmallBox D ∧
      normalizedLatticeQuotient W b hb (orthonormalMixedChart o x) = y ∧
      mixedCoefficientDensity c w p x ≠ 0 := by
  obtain ⟨x, hx, hq, hf⟩ := normalizedQuotientDensity_recover W b hb (Subset.rfl)
    (orthonormalMixedDensity o c w p) hy
  refine ⟨(orthonormalMixedChart o).symm x, ?_, ?_, hf⟩
  · simpa only [MeasurableEquiv.apply_symm_apply] using hx
  · simpa only [MeasurableEquiv.apply_symm_apply] using hq

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module Submodule _root_.Set
open scoped BigOperators

variable {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module Submodule _root_.Set
open scoped BigOperators

variable {D I J : Type*} [Fintype D] [Fintype I] [Fintype J] {n : ℕ}

noncomputable def mixedArrayQuotient (W : Submodule ℝ (EuclideanSpace ℝ D))
    (b : Basis (Fin n) ℝ Wᗮ) (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
    (o : OrthonormalBasis I ℝ W) (x : (I → J → ℝ) × (Fin n → J → ℤ)) :
    J → W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup :=
  fun j => normalizedLatticeQuotient W b hb (orthonormalMixedChart o (mixedArrayRegroup I (Fin n) J x j))

omit [Fintype J] in
theorem mixedArrayQuotient_measurable (W : Submodule ℝ (EuclideanSpace ℝ D))
    (b : Basis (Fin n) ℝ Wᗮ) (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
    (o : OrthonormalBasis I ℝ W) : Measurable (mixedArrayQuotient (J := J) W b hb o) := by
  apply measurable_pi_iff.mpr
  intro j
  exact (normalizedLatticeQuotient_measurable W b hb).comp
    ((orthonormalMixedChart o).measurable.comp
      ((measurable_pi_apply j).comp (mixedArrayRegroup I (Fin n) J).measurable))

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module Submodule _root_.Set
open scoped BigOperators

end Erdos3

end

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

variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (o : OrthonormalBasis I ℝ W)

noncomputable def mixedDensityCovolumeRatio : ℝ :=
  ZLattice.covolume (latticeSection (standardEuclideanLattice D) W) /
    ∏ i, (basisAxisScale b i : ℝ)

theorem mixedDensityCovolumeRatio_pos
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice D) W)] :
    0 < mixedDensityCovolumeRatio W b :=
  div_pos (ZLattice.covolume_pos _ volume)
    (Finset.prod_pos (fun i _ => Nat.cast_pos.mpr (basisAxisScale_pos b i)))

noncomputable def mixedAmbientInterpolation (c w : I → ℝ) (f : Fin n → ℝ → ℝ)
    (v : D → ℝ) : ℝ :=
  mixedDensityCovolumeRatio W b * mixedDensityInterpolation c w f
    (mixedRealCoordinates W b o ((EuclideanSpace.equiv D ℝ).symm v))

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

section

namespace Erdos3

open Module Submodule
open scoped BigOperators

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

noncomputable def earlyConstantDensityCap (a n : ℕ) (R V : ℝ) : ℝ :=
  V * (R / 4)⁻¹ ^ a * (8 * (probabilityProfileLipschitz : ℝ) / (R / 4)) ^ n

theorem earlyConstantDensityCap_nonneg (a n : ℕ) {R V : ℝ} (hR : 0 < R) (hV : 0 ≤ V) :
    0 ≤ earlyConstantDensityCap a n R V := by
  unfold earlyConstantDensityCap
  positivity

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

def earlyFiberCapLog (P : ℝ) : ℝ := 3 * P ^ 3 + 17 * P ^ 2

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

theorem earlyFiberCap_exp_bound {m : ℕ} (a n : Fin m → ℕ) (R V : Fin m → ℝ) {P : ℝ}
    (hP : 0 ≤ P) (hm : (m : ℝ) ≤ P) (hR : ∀ j, 0 < R j) (hV : ∀ j, 0 ≤ V j)
    (ha : ∀ j, (a j : ℝ) ≤ P) (hn : ∀ j, (n j : ℝ) ≤ P)
    (hA : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hVP : ∀ j, V j ≤ Real.exp P) :
    (∏ j, earlyConstantDensityCap (a j) (n j) (R j) (V j)) ≤ Real.exp (earlyFiberCapLog P) := by
  calc
    _ ≤ ∏ _j : Fin m, Real.exp (3*P^2+17*P) :=
      Finset.prod_le_prod (fun j _ => earlyConstantDensityCap_nonneg _ _ (hR j) (hV j))
        (fun j _ => earlyConstantDensityCap_exp_bound _ _ hP (hR j)
          (ha j) (hn j) hA (hRP j) (hVP j))
    _ = (Real.exp (3*P^2+17*P))^m := by simp
    _ ≤ Real.exp (P*(3*P^2+17*P)) :=
      pow_le_exp_mul_of_le_exp (Real.exp_nonneg _) le_rfl (by positivity) m hm
    _ = _ := by congr 1; unfold earlyFiberCapLog; ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MixedArraySourceSupport
namespace OAI

section

namespace Erdos3

open Module Submodule _root_.Set
open scoped BigOperators

def mixedArraySupported {I Z J : Type*} [Fintype I] [Fintype Z]
    (c w : I → J → ℝ) (p : Z → J → PMF ℤ) (x : (I → J → ℝ) × (Z → J → ℤ)) : Prop :=
  ∀ j, mixedCoefficientDensity (fun i => c i j) (fun i => w i j) (fun z => p z j)
    (mixedArrayRegroup I Z J x j) ≠ 0

theorem mixedArraySupported_iff_rows {I Z J : Type*} [Fintype I] [Fintype Z] [Fintype J]
    (c w : I → J → ℝ) (p : Z → J → PMF ℤ) (x : (I → J → ℝ) × (Z → J → ℤ)) :
    mixedArraySupported c w p x ↔
      (∀ i, affineProductProfile (c i) (w i) (x.1 i) ≠ 0) ∧
      (∀ z j, x.2 z j ∈ (p z j).support) := by
  classical
  constructor
  · intro hx
    have hs (j) := (mixedCoefficientDensity_support (fun i => c i j) (fun i => w i j)
      (fun z => p z j) (mixedArrayRegroup I Z J x j)).mp (hx j)
    refine ⟨?_, fun z j => (hs j).2 z⟩
    intro i
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    exact (hs j).1 i
  · rintro ⟨hc, hp⟩ j
    apply (mixedCoefficientDensity_support _ _ _ _).mpr
    refine ⟨?_, fun z => hp z j⟩
    intro i
    exact (Finset.prod_ne_zero_iff.mp (hc i)) j (Finset.mem_univ j)

def mixedArrayInChart {D I J : Type*} [Fintype D] [Fintype I] {n : ℕ}
    (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
    (o : OrthonormalBasis I ℝ W) (x : (I → J → ℝ) × (Fin n → J → ℤ)) : Prop :=
  ∀ j, normalizedLatticePoint W b (orthonormalMixedChart o (mixedArrayRegroup I (Fin n) J x j)) ∈
    standardLatticeSmallBox D

theorem mixedArrayQuotient_injOn_chart {D I J : Type*} [Fintype D] [Fintype I] {n : ℕ}
    (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
    (hb : span ℤ (Set.range b) = projectedIntegerLattice W) (o : OrthonormalBasis I ℝ W) :
    Set.InjOn (mixedArrayQuotient (J := J) W b hb o) {x | mixedArrayInChart W b o x} := by
  intro x hx y hy he
  apply (mixedArrayRegroup I (Fin n) J).injective
  funext j
  apply (orthonormalMixedChart o).injective
  exact normalizedLatticeQuotient_injOn W b hb (Subset.rfl) (hx j) (hy j) (congrFun he j)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.EmptyCoefficientDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory Module Submodule _root_.Set
open scoped BigOperators

variable {D I J : Type*} [Fintype D] [Fintype I] [Fintype J] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W) (o : OrthonormalBasis I ℝ W)

noncomputable def canonicalArrayDensity (c w : I → J → ℝ) (p : Fin n → J → PMF ℤ)
    (y : J → W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup) : ℝ :=
  ∏ j, canonicalMixedDensity W b hb o (fun i => c i j) (fun i => w i j) (fun i => p i j) (y j)

theorem canonicalArrayDensity_recover (c w : I → J → ℝ) (p : Fin n → J → PMF ℤ)
    {y : J → W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup}
    (hy : canonicalArrayDensity W b hb o c w p y ≠ 0) :
    ∃ x : (I → J → ℝ) × (Fin n → J → ℤ),
      mixedArrayQuotient W b hb o x = y ∧ mixedArrayInChart W b o x ∧ mixedArraySupported c w p x := by
  classical
  have hs (j : J) := canonicalMixedDensity_recover W b hb o (fun i => c i j)
    (fun i => w i j) (fun i => p i j) ((Finset.prod_ne_zero_iff.mp hy) j (Finset.mem_univ j))
  choose a hac haq has using hs
  let x := (mixedArrayRegroup I (Fin n) J).symm a
  have hx : mixedArrayRegroup I (Fin n) J x = a := (mixedArrayRegroup I (Fin n) J).apply_symm_apply a
  refine ⟨x, ?_, ?_, ?_⟩
  · funext j
    change normalizedLatticeQuotient W b hb (orthonormalMixedChart o (mixedArrayRegroup I (Fin n) J x j)) = y j
    rw [hx]
    exact haq j
  · intro j
    change normalizedLatticePoint W b (orthonormalMixedChart o (mixedArrayRegroup I (Fin n) J x j)) ∈ _
    rw [hx]
    exact hac j
  · intro j
    rw [hx]
    exact has j

theorem canonicalArrayDensity_recover_unique (c w : I → J → ℝ) (p : Fin n → J → PMF ℤ)
    {y : J → W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup}
    (hy : canonicalArrayDensity W b hb o c w p y ≠ 0) :
    ∃! x : (I → J → ℝ) × (Fin n → J → ℤ),
      mixedArrayQuotient W b hb o x = y ∧ mixedArrayInChart W b o x ∧ mixedArraySupported c w p x := by
  obtain ⟨x, hx⟩ := canonicalArrayDensity_recover W b hb o c w p hy
  refine ⟨x, hx, ?_⟩
  intro z hz
  exact mixedArrayQuotient_injOn_chart W b hb o hz.2.1 hx.2.1 (hz.1.trans hx.1.symm)

end Erdos3

end

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

abbrev CoefficientSamplerArrays (I : Fin m → Type*) (n : Fin m → ℕ) :=
  ∀ j : Fin m,
    (I j → BoundedCoefficientExponent K (j.val + 1) → ℝ) ×
      (Fin (n j) → BoundedCoefficientExponent K (j.val + 1) → ℤ)

noncomputable def canonicalCoefficientSample (a : CoefficientSamplerArrays (K := K) I n) :
    CoefficientTorus (K := K) U :=
  (euclideanCoefficientEquiv U).symm
    (fun j => mixedArrayQuotient (euclideanSubspace (U j)) (b j) (hb j) (o j) (a j))

variable (c w : ∀ j : Fin m, I j → BoundedCoefficientExponent K (j.val + 1) → ℝ)
variable (p : ∀ j : Fin m, Fin (n j) → BoundedCoefficientExponent K (j.val + 1) → PMF ℤ)

noncomputable def canonicalCoefficientDensity (y : CoefficientTorus (K := K) U) : ℝ :=
  ∏ j, canonicalArrayDensity (euclideanSubspace (U j)) (b j) (hb j) (o j) (c j) (w j) (p j)
    (euclideanCoefficientEquiv U y j)

theorem canonicalCoefficientDensity_recover_unique
    {y : CoefficientTorus (K := K) U} (hy : canonicalCoefficientDensity U b hb o c w p y ≠ 0) :
    ∃! a : CoefficientSamplerArrays (K := K) I n,
      canonicalCoefficientSample U b hb o a = y ∧
        ∀ j, mixedArrayInChart (euclideanSubspace (U j)) (b j) (o j) (a j) ∧
          mixedArraySupported (c j) (w j) (p j) (a j) := by
  classical
  have hs (j : Fin m) := canonicalArrayDensity_recover_unique
    (euclideanSubspace (U j)) (b j) (hb j) (o j) (c j) (w j) (p j)
    ((Finset.prod_ne_zero_iff.mp hy) j (Finset.mem_univ j))
  choose a ha hu using hs
  refine ⟨a, ⟨?_, fun j => (ha j).2⟩, ?_⟩
  · apply (euclideanCoefficientEquiv U).injective
    rw [canonicalCoefficientSample, AddEquiv.apply_symm_apply]
    exact funext (fun j => (ha j).1)
  · intro z hz
    have hq := congrArg (euclideanCoefficientEquiv U) hz.1
    rw [canonicalCoefficientSample, AddEquiv.apply_symm_apply] at hq
    exact funext (fun j => hu j (z j) ⟨congrFun hq j, hz.2 j⟩)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

variable [CompactSpace (CoefficientTorus (K := K) U)]
variable [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
variable (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable (hw : ∀ j i d, 0 < w j i d)
variable (hs : ∀ j d x, mixedCoefficientDensity (fun i => c j i d) (fun i => w j i d)
  (fun i => p j i d) x ≠ 0 → normalizedLatticePoint (euclideanSubspace (U j)) (b j)
    (orthonormalMixedChart (o j) x) ∈ standardLatticeSmallBox (J j))

include ν hw hs

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open MeasureTheory Module Submodule
open scoped BigOperators

namespace VectorPolynomial

end VectorPolynomial
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedCoefficientRemainder
namespace OAI

section

namespace Erdos3

open Module Submodule

theorem normalizedLatticePoint_sub_mem_of_mk_eq {D : Type*} [Fintype D] {n : ℕ}
    (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
    (hb : span ℤ (Set.range b) = projectedIntegerLattice W) (u : W) (x : W × (Fin n → ℤ))
    (hx : QuotientAddGroup.mk' (latticeSection (standardEuclideanLattice D) W).toAddSubgroup u =
      normalizedLatticeQuotient W b hb x) :
    u.val - normalizedLatticePoint W b x ∈ standardEuclideanLattice D := by
  let z := latticeBasisEquiv (projectedIntegerLattice W) b hb x.2
  have hm : (u - (x.1 - projectedLatticeShift (standardEuclideanLattice D) W z)).val ∈
      standardEuclideanLattice D := QuotientAddGroup.eq_iff_sub_mem.mp hx
  rw [normalizedLatticePoint_eq_sheet W b hb]
  change u.val - latticeSheetPoint W z.val x.1 ∈ standardEuclideanLattice D
  rw [latticeSheetPoint_reconstruction (standardEuclideanLattice D) W z x.1]
  convert (standardEuclideanLattice D).sub_mem hm
    (projectedLatticeLift (standardEuclideanLattice D) W z).property using 1
  simp only [Submodule.coe_sub]
  abel

namespace VectorPolynomial

theorem euclideanCoefficientEquiv_mk {K : Type*} {m : ℕ} {J : Fin m → Type*}
    [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (c : CoefficientArray (K := K) U) (j : Fin m) (d : BoundedCoefficientExponent K (j.val + 1)) :
    euclideanCoefficientEquiv U (QuotientAddGroup.mk' (coefficientIntegerLattice U) c) j d =
      QuotientAddGroup.mk' _ ((euclideanSubspaceArrayEquiv (U j)).symm (fun _ => c ⟨j, d⟩)) := by
  apply (euclideanSubspaceTorusEquiv (U j)).injective
  rw [euclideanCoefficientEquiv_apply, AddEquiv.apply_symm_apply,
    euclideanSubspaceTorusEquiv_mk, ContinuousLinearEquiv.apply_symm_apply]
  rfl

theorem canonicalCoefficientSample_integer_remainder {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (a : CoefficientSamplerArrays (K := K) I n) (c : CoefficientArray (K := K) U)
    (hc : canonicalCoefficientSample U b hb o a = QuotientAddGroup.mk' (coefficientIntegerLattice U) c)
    (j : Fin m) (d : BoundedCoefficientExponent K (j.val + 1)) (i : J j) :
    ∃ z : ℤ, (c ⟨j, d⟩).val i - normalizedLatticePoint (euclideanSubspace (U j)) (b j)
      (orthonormalMixedChart (o j) (mixedArrayRegroup (I j) (Fin (n j)) _ (a j) d)) i = z := by
  have he := congrArg (fun y => euclideanCoefficientEquiv U y j d) hc
  simp only [canonicalCoefficientSample, AddEquiv.apply_symm_apply, euclideanCoefficientEquiv_mk] at he
  have hm := normalizedLatticePoint_sub_mem_of_mk_eq (euclideanSubspace (U j)) (b j) (hb j)
    ((euclideanSubspaceArrayEquiv (U j)).symm (fun _ => c ⟨j, d⟩)) _ he.symm
  obtain ⟨z, hz⟩ := (mem_standardEuclideanLattice (J j) _).mp hm i
  exact ⟨z, hz.symm⟩

end VectorPolynomial
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CoefficientPolynomialLift
namespace OAI

section

namespace Erdos3

open Module Submodule
open scoped BigOperators

variable {D I J V : Type*} [Fintype D] [Fintype I] [Fintype J] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (o : OrthonormalBasis I ℝ W)

noncomputable def mixedLiftCoefficient (a : (I → J → ℝ) × (Fin n → J → ℤ)) (j : J) :
    EuclideanSpace ℝ D :=
  mixedRealPoint W b o (fun i => a.1 i j, fun i => (a.2 i j : ℝ) / basisAxisScale b i)

omit [Fintype J] in
theorem mixedLiftCoefficient_eq (a : (I → J → ℝ) × (Fin n → J → ℤ)) (j : J) :
    mixedLiftCoefficient W b o a j = normalizedLatticePoint W b
      (orthonormalMixedChart o (mixedArrayRegroup I (Fin n) J a j)) := rfl

theorem mixedPolynomialPoint_sum (e : J → V →₀ ℕ)
    (a : (I → J → ℝ) × (Fin n → J → ℤ)) (x : V → ℝ) :
    mixedPolynomialPoint W b o e a.1 a.2 x =
      ∑ j, monomialScale x (e j) • mixedLiftCoefficient W b o a j := by
  change mixedRealPoint W b o
    (fun i => MvPolynomial.eval x (monomialArrayPolynomial e (a.1 i)),
      fun i => MvPolynomial.eval x (monomialArrayPolynomial e (fun j => (a.2 i j : ℝ) / basisAxisScale b i))) = _
  simp only [mixedLiftCoefficient, ← map_smul, ← map_sum]
  congr 1
  ext i <;> simp [monomialArrayPolynomial_eval, monomialScale, Finsupp.prod,
    Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, mul_comm]

noncomputable def mixedLiftPolynomial (e : J → V →₀ ℕ)
    (a : (I → J → ℝ) × (Fin n → J → ℤ)) (d : D) : MvPolynomial V ℝ :=
  monomialArrayPolynomial e (fun j => mixedLiftCoefficient W b o a j d)

theorem mixedLiftPolynomial_eval (e : J → V →₀ ℕ)
    (a : (I → J → ℝ) × (Fin n → J → ℤ)) (x : V → ℝ) (d : D) :
    MvPolynomial.eval x (mixedLiftPolynomial W b o e a d) = mixedPolynomialPoint W b o e a.1 a.2 x d := by
  change _ = (PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : D => ℝ) d) (mixedPolynomialPoint W b o e a.1 a.2 x)
  rw [mixedPolynomialPoint_sum, map_sum]
  simp [mixedLiftPolynomial, monomialArrayPolynomial_eval, monomialScale, Finsupp.prod, mul_comm]

theorem mixedLiftPolynomial_degree (e : J → V →₀ ℕ)
    (a : (I → J → ℝ) × (Fin n → J → ℤ)) {h : ℕ}
    (he : ∀ j, (e j).sum (fun _ k => k) ≤ h) (d : D) :
    (mixedLiftPolynomial W b o e a d).totalDegree ≤ h := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro j _
  exact (MvPolynomial.totalDegree_monomial_le _ _).trans (he j)

theorem mixedLiftPolynomial_coeff (e : J → V →₀ ℕ) (he : Function.Injective e)
    (a : (I → J → ℝ) × (Fin n → J → ℤ)) (d : D) (j : J) :
    (mixedLiftPolynomial W b o e a d).coeff (e j) = mixedLiftCoefficient W b o a j d :=
  monomialArrayPolynomial_coeff e he _ j

theorem mixedLiftPolynomial_coefficient_bound (e : J → V →₀ ℕ) (he : Function.Injective e)
    (a : (I → J → ℝ) × (Fin n → J → ℤ)) (T : V → ℝ) (hT : ∀ v, 0 < T v)
    {M : ℝ} (hM : 0 ≤ M)
    (hbnd : ∀ j d, |mixedLiftCoefficient W b o a j d| ≤ M / monomialScale T (e j))
    (α : V →₀ ℕ) (d : D) :
    |(mixedLiftPolynomial W b o e a d).coeff α| ≤ M / monomialScale T α := by
  classical
  by_cases hα : ∃ j, e j = α
  · obtain ⟨j, rfl⟩ := hα
    rw [mixedLiftPolynomial_coeff W b o e he]
    exact hbnd j d
  · rw [mixedLiftPolynomial, monomialArrayPolynomial_coeff_zero_of_not_mem e _ α
      (fun j hj => hα ⟨j, hj⟩), abs_zero]
    exact div_nonneg hM (monomialScale_pos T hT α).le

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule

variable {K : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

noncomputable def coefficientRowPolynomial (c : CoefficientArray (K := K) U) (j : Fin m) (i : J j) :
    MvPolynomial K ℝ :=
  monomialArrayPolynomial Subtype.val (fun d : BoundedCoefficientExponent K (j.val + 1) => (c ⟨j, d⟩).val i)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientRowEvaluation
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem boundedSiteMatrix_natAbs_le {K S : Type*} (h : ℕ) (site : S → K → ℤ)
    {L : ℕ} (hL : 1 ≤ L) (hsite : ∀ s k, (site s k).natAbs ≤ L)
    (s : S) (d : BoundedCoefficientExponent K h) :
    (boundedSiteMatrix h site s d).natAbs ≤ L ^ h := by
  classical
  change (∏ k ∈ d.val.support, site s k ^ d.val k).natAbs ≤ L ^ h
  rw [show (∏ k ∈ d.val.support, site s k ^ d.val k).natAbs =
      ∏ k ∈ d.val.support, (site s k ^ d.val k).natAbs from
    map_prod Int.natAbsHom _ _]
  simp only [Int.natAbs_pow]
  calc
    _ ≤ ∏ k ∈ d.val.support, L ^ d.val k :=
      Finset.prod_le_prod' (fun k _ => Nat.pow_le_pow_left (hsite s k) _)
    _ = L ^ d.val.degree := by rw [Finset.prod_pow_eq_pow_sum]; rfl
    _ ≤ L ^ h := Nat.pow_le_pow_right hL d.property

theorem boundedSiteMatrix_height {K S : Type*} (h : ℕ) (site : S → K → ℤ)
    {L : ℕ} (hL : 1 ≤ L) (hsite : ∀ s k, (site s k).natAbs ≤ L)
    (s : S) (d : BoundedCoefficientExponent K h) :
    RationalHeightLE (boundedSiteMatrix h site s d : ℚ) (L ^ h) := by
  constructor
  · simpa using boundedSiteMatrix_natAbs_le h site hL hsite s d
  · simpa using Nat.one_le_pow h L hL

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped Classical

theorem emptyCoefficientExponent_eq (h : ℕ) (d : BoundedCoefficientExponent Empty h) :
    d = zeroCoefficientExponent Empty h := by
  apply Subtype.ext
  ext i
  exact isEmptyElim i

noncomputable def constantCoefficientArray {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) : CoefficientArray (K := Empty) U →ₗ[ℝ] CoefficientArray (K := K) U where
  toFun x s := if s.2.val = 0 then x ⟨s.1, zeroCoefficientExponent Empty (s.1.val + 1)⟩ else 0
  map_add' x y := by
    funext s
    by_cases hs : s.2.val = 0 <;> simp [hs]
  map_smul' c x := by
    funext s
    by_cases hs : s.2.val = 0 <;> simp [hs]

theorem constantCoefficientArray_preserves_lattice {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (x : CoefficientArray (K := Empty) U)
    (hx : x ∈ coefficientIntegerLattice U) :
    constantCoefficientArray (K := K) U x ∈ coefficientIntegerLattice U := by
  intro s a
  by_cases hs : s.2.val = 0
  · simpa only [constantCoefficientArray, LinearMap.coe_mk, AddHom.coe_mk, if_pos hs] using
      hx ⟨s.1, zeroCoefficientExponent Empty (s.1.val + 1)⟩ a
  · exact ⟨0, by simp [constantCoefficientArray, hs]⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

noncomputable def coefficientEvaluationArray {K : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ) :
    CoefficientArray (K := K) U →ₗ[ℝ] CoefficientArray (K := Empty) U where
  toFun x s := ∑ d : BoundedCoefficientExponent K (s.1.val + 1),
    (boundedSiteMatrix (s.1.val + 1) (fun _ : Unit => t) () d : ℝ) • x ⟨s.1, d⟩
  map_add' x y := by
    funext s
    simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    funext s
    simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum, smul_smul]
    apply Finset.sum_congr rfl
    intro d _
    rw [mul_comm]

theorem coefficientEvaluationArray_preserves_lattice {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ)
    (x : CoefficientArray (K := K) U) (hx : x ∈ coefficientIntegerLattice U) :
    coefficientEvaluationArray U t x ∈ coefficientIntegerLattice U := by
  choose z hz using hx
  intro s a
  refine ⟨∑ d : BoundedCoefficientExponent K (s.1.val + 1),
    boundedSiteMatrix (s.1.val + 1) (fun _ : Unit => t) () d * z ⟨s.1, d⟩ a, ?_⟩
  change ((∑ d : BoundedCoefficientExponent K (s.1.val + 1),
    (boundedSiteMatrix (s.1.val + 1) (fun _ : Unit => t) () d : ℝ) •
      (x ⟨s.1, d⟩ : U s.1)) : U s.1).val a = _
  simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply,
    smul_eq_mul, hz, Int.cast_sum, Int.cast_mul]

theorem coefficientEvaluationArray_constant {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ)
    (x : CoefficientArray (K := Empty) U) :
    coefficientEvaluationArray U t (constantCoefficientArray U x) = x := by
  funext s
  rcases s with ⟨j, d⟩
  have hd := emptyCoefficientExponent_eq (j.val + 1) d
  subst d
  change (∑ d : BoundedCoefficientExponent K (j.val + 1),
    (boundedSiteMatrix (j.val + 1) (fun _ : Unit => t) () d : ℝ) •
      (if d.val = 0 then x ⟨j, zeroCoefficientExponent Empty (j.val + 1)⟩ else 0)) =
    x ⟨j, zeroCoefficientExponent Empty (j.val + 1)⟩
  rw [Finset.sum_eq_single (zeroCoefficientExponent K (j.val + 1))]
  · simp only [zeroCoefficientExponent, boundedSiteMatrix, Finsupp.prod_zero_index,
      Int.cast_one, ite_true, one_smul]
  · intro d _ hd
    have hd0 : d.val ≠ 0 := fun he => hd (Subtype.ext he)
    simp [hd0]
  · simp

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

noncomputable def coefficientLayerInsertion {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (j : Fin m) :
    (BoundedCoefficientExponent K (j.val + 1) → U j) →ₗ[ℝ] CoefficientArray (K := K) U where
  toFun v s := (LinearMap.single ℝ (fun k : Fin m => BoundedCoefficientExponent K (k.val + 1) → U k) j v) s.1 s.2
  map_add' v w := by
    funext s
    simp only [map_add, Pi.add_apply]
  map_smul' c v := by
    funext s
    simp only [map_smul, RingHom.id_apply, Pi.smul_apply]

theorem coefficientLayerInsertion_same {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (j : Fin m)
    (v : BoundedCoefficientExponent K (j.val + 1) → U j)
    (d : BoundedCoefficientExponent K (j.val + 1)) :
    coefficientLayerInsertion U j v ⟨j, d⟩ = v d := by
  simp [coefficientLayerInsertion]

theorem coefficientLayerInsertion_ne {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (j k : Fin m) (h : k ≠ j)
    (v : BoundedCoefficientExponent K (j.val + 1) → U j)
    (d : BoundedCoefficientExponent K (k.val + 1)) :
    coefficientLayerInsertion U j v ⟨k, d⟩ = 0 := by
  simp [coefficientLayerInsertion, h]

theorem coefficientArrayFunctional_layerInsertion {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ) (j : Fin m)
    (v : BoundedCoefficientExponent K (j.val + 1) → U j) :
    coefficientArrayFunctional U frequency (coefficientLayerInsertion U j v) =
      subspaceArrayFunctional (U j) (fun d a => (frequency j d.val a : ℝ)) v := by
  change (∑ s : CoefficientSlot K m, ∑ a, (frequency s.1 s.2.val a : ℝ) *
    (coefficientLayerInsertion U j v s).val a) = _
  rw [Fintype.sum_sigma, Finset.sum_eq_single j]
  · simp only [coefficientLayerInsertion_same]
    rfl
  · intro k _ hkj
    simp only [coefficientLayerInsertion_ne U j k hkj, ZeroMemClass.coe_zero,
      Pi.zero_apply, mul_zero, Finset.sum_const_zero]
  · simp

theorem coefficientEvaluationArray_layerInsertion {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ) (j : Fin m)
    (v : BoundedCoefficientExponent K (j.val + 1) → U j) :
    coefficientEvaluationArray U t (coefficientLayerInsertion U j v) =
      coefficientLayerInsertion (K := Empty) U j
        (fun _ => ∑ d, (boundedSiteMatrix (j.val + 1) (fun _ : Unit => t) () d : ℝ) • v d) := by
  funext s
  rcases s with ⟨k, d⟩
  by_cases hk : k = j
  · subst k
    simp only [coefficientEvaluationArray, LinearMap.coe_mk, AddHom.coe_mk,
      coefficientLayerInsertion_same]
  · simp only [coefficientEvaluationArray, LinearMap.coe_mk, AddHom.coe_mk,
      coefficientLayerInsertion_ne U j k hk, smul_zero, Finset.sum_const_zero]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {K : Type*} {m : ℕ} {J : Fin m → Type*}
  (U : ∀ j, Submodule ℝ (J j → ℝ))

noncomputable def coefficientLayerEndomorphism
    (R : ∀ j, (BoundedCoefficientExponent K (j.val + 1) → U j) →ₗ[ℝ]
      (BoundedCoefficientExponent K (j.val + 1) → U j)) :
    CoefficientArray (K := K) U →ₗ[ℝ] CoefficientArray (K := K) U :=
  LinearMap.pi (fun s => (LinearMap.proj s.2).comp ((R s.1).comp (coefficientLayerArray U s.1)))

theorem coefficientLayerEndomorphism_insertion
    (R : ∀ j, (BoundedCoefficientExponent K (j.val + 1) → U j) →ₗ[ℝ]
      (BoundedCoefficientExponent K (j.val + 1) → U j)) (j : Fin m)
    (v : BoundedCoefficientExponent K (j.val + 1) → U j) :
    coefficientLayerEndomorphism U R (coefficientLayerInsertion U j v) =
      coefficientLayerInsertion U j (R j v) := by
  funext s
  rcases s with ⟨k, d⟩
  by_cases hk : k = j
  · subst k
    change R j (fun e => coefficientLayerInsertion U j v ⟨j, e⟩) d = _
    simp only [coefficientLayerInsertion_same]
  · change R k (fun e => coefficientLayerInsertion U j v ⟨k, e⟩) d = _
    simp only [coefficientLayerInsertion_ne U j k hk]
    change R k 0 d = 0
    rw [map_zero, Pi.zero_apply]

theorem coefficientLayerEndomorphism_preserves_lattice
    (R : ∀ j, (BoundedCoefficientExponent K (j.val + 1) → U j) →ₗ[ℝ]
      (BoundedCoefficientExponent K (j.val + 1) → U j))
    (hR : ∀ j x, x ∈ subspaceArrayIntegerLattice _ (U j) →
      R j x ∈ subspaceArrayIntegerLattice _ (U j))
    (x : CoefficientArray (K := K) U) (hx : x ∈ coefficientIntegerLattice U) :
    coefficientLayerEndomorphism U R x ∈ coefficientIntegerLattice U := by
  intro s a
  exact hR s.1 (coefficientLayerArray U s.1 x)
    (coefficientLayerArray_preserves_lattice U s.1 x hx) s.2 a

theorem coefficientArrayFunctional_endomorphism_zero_iff [Fintype K] [∀ j, Fintype (J j)]
    (R : ∀ j, (BoundedCoefficientExponent K (j.val + 1) → U j) →ₗ[ℝ]
      (BoundedCoefficientExponent K (j.val + 1) → U j))
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ) :
    (coefficientArrayFunctional U frequency).comp (coefficientLayerEndomorphism U R) = 0 ↔
      ∀ j, (subspaceArrayFunctional (U j) (fun d => fun a => (frequency j d.val a : ℝ))).comp
        (R j) = 0 := by
  constructor
  · intro h j
    apply LinearMap.ext
    intro v
    have hv := DFunLike.congr_fun h (coefficientLayerInsertion U j v)
    simpa only [LinearMap.comp_apply, coefficientLayerEndomorphism_insertion,
      coefficientArrayFunctional_layerInsertion, LinearMap.zero_apply] using hv
  · intro h
    apply LinearMap.ext
    intro x
    change (∑ s : CoefficientSlot K m, ∑ a,
      (frequency s.1 s.2.val a : ℝ) * ((coefficientLayerEndomorphism U R x) s).val a) = 0
    rw [Fintype.sum_sigma]
    apply Finset.sum_eq_zero
    intro j _
    exact DFunLike.congr_fun (h j) (coefficientLayerArray U j x)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {K S : Type*} [Fintype K] [Fintype S] {m : ℕ}
  {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))

noncomputable def coefficientSiteResidual (site : S → K → ℤ) (q : Fin m → ℕ)
    (T : ∀ j : Fin m, Matrix (BoundedCoefficientExponent K (j.val + 1)) S ℤ) :
    CoefficientArray (K := K) U →ₗ[ℝ] CoefficientArray (K := K) U :=
  coefficientLayerEndomorphism U (fun j =>
    scaledLinearResidual (matrixModuleAction (fun s d => (boundedSiteMatrix (j.val + 1) site s d : ℝ)))
      (matrixModuleAction (fun d s => (T j d s : ℝ))) (q j : ℝ))

theorem coefficientSiteResidual_preserves_lattice (site : S → K → ℤ) (q : Fin m → ℕ)
    (T : ∀ j : Fin m, Matrix (BoundedCoefficientExponent K (j.val + 1)) S ℤ)
    (x : CoefficientArray (K := K) U) (hx : x ∈ coefficientIntegerLattice U) :
    coefficientSiteResidual U site q T x ∈ coefficientIntegerLattice U :=
  coefficientLayerEndomorphism_preserves_lattice U _
    (fun j x hx => scaledSiteResidual_preserves_lattice (U j) _ (T j) (q j) x hx) x hx

theorem coefficientSiteResidual_zero_iff [∀ j, Fintype (J j)]
    (site : S → K → ℤ) (q : Fin m → ℕ)
    (T : ∀ j : Fin m, Matrix (BoundedCoefficientExponent K (j.val + 1)) S ℤ)
    (hq : ∀ j, 0 < q j)
    (hT : ∀ j (x : BoundedCoefficientExponent K (j.val + 1) → U j),
      matrixModuleAction (fun s d => (boundedSiteMatrix (j.val + 1) site s d : ℝ))
        (matrixModuleAction (fun d s => (T j d s : ℝ))
          (matrixModuleAction (fun s d => (boundedSiteMatrix (j.val + 1) site s d : ℝ)) x)) =
        (q j : ℝ) • matrixModuleAction (fun s d => (boundedSiteMatrix (j.val + 1) site s d : ℝ)) x)
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ) :
    (coefficientArrayFunctional U frequency).comp (coefficientSiteResidual U site q T) = 0 ↔
      ∀ j, ∃ M : (S → U j) →ₗ[ℝ] ℝ,
        ∀ p : VectorPolynomial K ℝ (U j), DegreeLE (1 : K → ℕ) (j.val + 1) p →
          coefficientFunctional (fun d a => (frequency j d a : ℝ)) (map (U j).subtype p) =
            M (siteEvaluation (fun s k => (site s k : ℝ)) p) := by
  rw [coefficientSiteResidual, coefficientArrayFunctional_endomorphism_zero_iff]
  constructor
  · intro h j
    obtain ⟨M, hM⟩ := (scaledLinearResidual_factor_iff _ _
      (show (q j : ℝ) ≠ 0 by exact_mod_cast (hq j).ne') (hT j) _).mp (h j)
    refine ⟨M, ?_⟩
    intro p hp
    have he := DFunLike.congr_fun hM (fun d => coefficients p d.val)
    have hr := boundedArrayPolynomial_reconstruct p hp
    rw [← hr, coefficientFunctional_boundedArrayPolynomial, siteEvaluation_boundedArrayPolynomial]
    exact he
  · intro h j
    obtain ⟨M, hM⟩ := h j
    apply (scaledLinearResidual_factor_iff _ _
      (show (q j : ℝ) ≠ 0 by exact_mod_cast (hq j).ne') (hT j) _).mpr
    refine ⟨M, ?_⟩
    apply LinearMap.ext
    intro x
    exact bounded_site_factorization_to_array (U j) (j.val + 1) site _ M hM x

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {K S : Type*} [Fintype K] [Fintype S] {m : ℕ} {J : Fin m → Type*}
  (U : ∀ j, Submodule ℝ (J j → ℝ)) (site : S → K → ℤ) (q : ℕ)
  (T : ∀ j : Fin m, Matrix (BoundedCoefficientExponent K (j.val + 1)) S ℤ)

theorem coefficientSiteResidual_cover_on_kernel (x : CoefficientTorus (K := K) U)
    (hx : coefficientSiteTorusMap U site x = 0) :
    linearQuotientEndomorphism (coefficientIntegerLattice U)
      (coefficientSiteResidual U site (fun _ => q) T)
      (coefficientSiteResidual_preserves_lattice U site (fun _ => q) T) x =
        quotientIntegerCover (coefficientIntegerLattice U) q x := by
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk'_surjective (coefficientIntegerLattice U) x
  rw [quotientIntegerCover_mk]
  change QuotientAddGroup.mk' (coefficientIntegerLattice U)
    (coefficientSiteResidual U site (fun _ => q) T v) =
      QuotientAddGroup.mk' (coefficientIntegerLattice U) ((q : ℝ) • v)
  apply QuotientAddGroup.eq.mpr
  intro s a
  have hsite := congrFun hx s.1
  change QuotientAddGroup.mk' (subspaceArrayIntegerLattice S (U s.1))
    (matrixModuleAction (fun t d => (boundedSiteMatrix (s.1.val + 1) site t d : ℝ))
      (coefficientLayerArray U s.1 v)) = 0 at hsite
  have hi := (QuotientAddGroup.eq_zero_iff _).mp hsite
  have ht := integerMatrix_preserves_array_lattice (U s.1) (T s.1) _ hi
  obtain ⟨z, hz⟩ := ht s.2 a
  refine ⟨z, ?_⟩
  change (-((q : ℝ) * (v s).val a -
      (matrixModuleAction (fun d t => (T s.1 d t : ℝ))
        (matrixModuleAction (fun t d => (boundedSiteMatrix (s.1.val + 1) site t d : ℝ))
          (coefficientLayerArray U s.1 v)) s.2).val a) + (q : ℝ) * (v s).val a) = z
  linarith

theorem coefficientSiteResidual_site_zero
    (hT : ∀ j (x : BoundedCoefficientExponent K (j.val + 1) → U j),
      matrixModuleAction (fun s d => (boundedSiteMatrix (j.val + 1) site s d : ℝ))
        (matrixModuleAction (fun d s => (T j d s : ℝ))
          (matrixModuleAction (fun s d => (boundedSiteMatrix (j.val + 1) site s d : ℝ)) x)) =
        (q : ℝ) • matrixModuleAction (fun s d => (boundedSiteMatrix (j.val + 1) site s d : ℝ)) x)
    (x : CoefficientTorus (K := K) U) :
    coefficientSiteTorusMap U site
      (linearQuotientEndomorphism (coefficientIntegerLattice U)
        (coefficientSiteResidual U site (fun _ => q) T)
        (coefficientSiteResidual_preserves_lattice U site (fun _ => q) T) x) = 0 := by
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk'_surjective (coefficientIntegerLattice U) x
  funext j
  change QuotientAddGroup.mk' (subspaceArrayIntegerLattice S (U j))
    (matrixModuleAction (fun s d => (boundedSiteMatrix (j.val + 1) site s d : ℝ))
      (scaledLinearResidual (matrixModuleAction (fun s d => (boundedSiteMatrix (j.val + 1) site s d : ℝ)))
        (matrixModuleAction (fun d s => (T j d s : ℝ))) (q : ℝ)
        (coefficientLayerArray U j v))) = 0
  rw [scaledLinearResidual_evaluation _ _ _ (hT j), map_zero]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {K : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

theorem coefficientRowPolynomial_sub (c d : CoefficientArray (K := K) U) (j : Fin m) (i : J j) :
    coefficientRowPolynomial U (c - d) j i =
      coefficientRowPolynomial U c j i - coefficientRowPolynomial U d j i := by
  simp only [coefficientRowPolynomial, monomialArrayPolynomial, Pi.sub_apply,
    Submodule.coe_sub, map_sub, Finset.sum_sub_distrib]

theorem coefficientRowPolynomial_constant (z : ∀ j, U j) (j : Fin m) (i : J j) :
    coefficientRowPolynomial U (constantCoefficientArray (K := K) U (fun s => z s.1)) j i =
      MvPolynomial.C ((z j).val i) := by
  classical
  unfold coefficientRowPolynomial monomialArrayPolynomial
  rw [Finset.sum_eq_single (zeroCoefficientExponent K (j.val + 1))]
  · simp [constantCoefficientArray, zeroCoefficientExponent]
  · intro d _ hd
    have hzero : d.val ≠ 0 := fun h => hd (Subtype.ext h)
    simp [constantCoefficientArray, hzero]
  · simp

theorem coefficientRowPolynomial_eval (c : CoefficientArray (K := K) U)
    (j : Fin m) (i : J j) (x : K → ℝ) :
    MvPolynomial.eval x (coefficientRowPolynomial U c j i) =
      eval x (boundedArrayPolynomial (W := J j → ℝ) (j.val + 1) (fun d => (c ⟨j, d⟩).val)) i := by
  simp [coefficientRowPolynomial, monomialArrayPolynomial, boundedArrayPolynomial,
    eval_monomial, MvPolynomial.eval_monomial, Finset.sum_apply, mul_comm]

theorem coefficientRowPolynomial_affine_eval {V : Type*}
    (p : ∀ j, VectorPolynomial V ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : V → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (frame : Option K → V → ℝ) (j : Fin m) (i : J j) (x : K → ℝ) :
    MvPolynomial.eval x (coefficientRowPolynomial U (affineSampleCoefficientArray U p hm frame) j i) =
      eval (fun v => frame none v + ∑ k, frame (some k) v * x k) (p j) i := by
  rw [coefficientRowPolynomial_eval]
  simp_rw [affineSampleCoefficientArray_val]
  rw [boundedArrayPolynomial_reconstruct _
    (degreeLE_substitute_affine _ (affineParameterSubstitution_degree frame) (p j) (hp j)),
    eval_substitute]
  simp only [affineParameterSubstitution_eval]

end Erdos3.VectorPolynomial

end

end OAI

end


