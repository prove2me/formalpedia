-- Prove2me | Definitions.Def_OAIQ246W003
-- name    : OAIQ246W003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T07:17:01.093187+00:00
-- url     : https://prove2.me/theorems/a96cb54e-dc85-4889-8d7e-c9acff937401
-- title:
--   Definitions bundle OAIQ246W003 of the split of OpenAI, Weak pure infiniteness and O-infinity absorption (result family 303)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.WeakPureInfiniteness.exact_weaklyPurelyInfinite_individuallyProperlyInfinite_any` and `OAI.WeakPureInfiniteness.exact_weaklyPurelyInfinite_stronglyPurelyInfinite`, carved from OpenAI's openai/math development (OpenAI, *Weak pure infiniteness and O-infinity absorption (result family 303)*, OpenAI Math Release, September 25, 2026, result family 303, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 114 declarations of OpenAI's Lean: 49 definitions, 1 inductive type or structure, 5 instances and 59 theorems. The definitions and types are `OAI.WeakPureInfiniteness.ExactModelDataAny`, `OAI.WeakPureInfiniteness.FiniteContractionModelsAny`, `OAI.WeakPureInfiniteness.NonzeroOnNormSlice`, `OAI.WeakPureInfiniteness.QuantitativeSeparatingPositives`, `OAI.WeakPureInfiniteness.ReducedFreeLarge`, `OAI.WeakPureInfiniteness.ReducedGroupAlgebra`, `OAI.WeakPureInfiniteness.UniformPerturbationOne_any`, `OAI.WeakPureInfiniteness.amplifiedPolynomial`, `OAI.WeakPureInfiniteness.basisTensorEquiv`, `OAI.WeakPureInfiniteness.contractionAmbientRepresentation`, `OAI.WeakPureInfiniteness.crossTensorSecond`, `OAI.WeakPureInfiniteness.cutVanishingSpace`, `OAI.WeakPureInfiniteness.cutVanishingSpaceNonunital`, `OAI.WeakPureInfiniteness.finiteGroupRepresentation`, `OAI.WeakPureInfiniteness.finiteGroupSpatialRepresentation`, `OAI.WeakPureInfiniteness.freeDiagonalFunctional`, `OAI.WeakPureInfiniteness.freeDiagonalWitness`, `OAI.WeakPureInfiniteness.fullGroupAmbientInclusion`, `OAI.WeakPureInfiniteness.fullGroupPolynomial`, `OAI.WeakPureInfiniteness.fullGroupUnitary`, `OAI.WeakPureInfiniteness.fullToReduced`, `OAI.WeakPureInfiniteness.fullToReducedLarge`, `OAI.WeakPureInfiniteness.fullToUniversal`, `OAI.WeakPureInfiniteness.groupSpan`, `OAI.WeakPureInfiniteness.groupTensorPolynomial`, `OAI.WeakPureInfiniteness.leftRegularRepresentation`, `OAI.WeakPureInfiniteness.matrixOperatorHom`, `OAI.WeakPureInfiniteness.minimalAmbientInclusion`, `OAI.WeakPureInfiniteness.minimalElementaryLeftContinuous`, `OAI.WeakPureInfiniteness.minimalElementaryLeftLinear`, `OAI.WeakPureInfiniteness.minimalElementaryRightLinear`, `OAI.WeakPureInfiniteness.minimalMapAny`, `OAI.WeakPureInfiniteness.minimalMapLeftAny`, `OAI.WeakPureInfiniteness.pairAmbientMap`, `OAI.WeakPureInfiniteness.pairRepresentation`, `OAI.WeakPureInfiniteness.polynomialOperator`, `OAI.WeakPureInfiniteness.realStateComplexification`, `OAI.WeakPureInfiniteness.reducedGroupSubalgebra`, `OAI.WeakPureInfiniteness.reducedLargeToOperators`, `OAI.WeakPureInfiniteness.regularBase` and 10 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `WeakInfiniteness_AlgebraicTensorSpan`, `WeakInfiniteness_CStarClosedRange`, `WeakInfiniteness_CompatibleSeparation`, `WeakInfiniteness_CrossUniverseLeftMap`, `WeakInfiniteness_CrossUniverseTensorBound`, `WeakInfiniteness_CrossUniverseTensorMap`, `WeakInfiniteness_CrossUniverseUniformGap`, `WeakInfiniteness_CrossUniverseUniformModels`, `WeakInfiniteness_DiagonalRegular`, `WeakInfiniteness_FaithfulContractions`, `WeakInfiniteness_FaithfulTensorNorm`, `WeakInfiniteness_FiniteGroupTensor`, `WeakInfiniteness_FullGroupAlgebra`, `WeakInfiniteness_FullGroupDensity`, `WeakInfiniteness_GroupPolynomials`, `WeakInfiniteness_MatrixRepresentation`, `WeakInfiniteness_NonUnitalClosedRange`, `WeakInfiniteness_NonunitalHeredity`, `WeakInfiniteness_PolynomialCompression`, `WeakInfiniteness_PolynomialSpan`, `WeakInfiniteness_PureStates`, `WeakInfiniteness_QuantitativeAssembly`, `WeakInfiniteness_ReducedGroupAlgebra`, `WeakInfiniteness_ReducedOperators`, `WeakInfiniteness_ScalarDiagonal`, `WeakInfiniteness_SquareZero`, `WeakInfiniteness_TensorCompression`, `WeakInfiniteness_TensorCut`, `WeakInfiniteness_TensorDensity`, `WeakInfiniteness_TensorFoundations`, `WeakInfiniteness_TensorIdealCut`, `WeakInfiniteness_TensorMatrixNorm`, `WeakInfiniteness_TensorMultiplier`, `WeakInfiniteness_UniformModels`, `WeakInfiniteness_UniversalGroupMap`, `WeakInfiniteness_UniversalMapping`, `WeakInfiniteness_WordCompression`, `WeakInfiniteness_WordTensorDensity`.
--
--   **Imports.** It imports the published bundle `Def_ExactInfiniteness`; the bundles `OAIQ246W000` and `OAIQ246W001` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ246W005`; the statements `OAI.WeakPureInfiniteness.contractive_spi_of_quantitative_separation`, `OAI.WeakPureInfiniteness.exists_finite_coupling_of_gap_any`, `OAI.WeakPureInfiniteness.exists_separated_supported_model_any`, `OAI.WeakPureInfiniteness.exists_square_zero_on_norm_slice_of_gap_any`, `OAI.WeakPureInfiniteness.exists_uniform_gap_any`, `OAI.WeakPureInfiniteness.freeDiagonalFunctional_bound_of_kernel`, `OAI.WeakPureInfiniteness.quantitative_separatingPositives_any` and `OAI.WeakPureInfiniteness.universal_fixed_kernel_impossible`; the proofs of `OAI.WeakPureInfiniteness.contractive_spi_of_quantitative_separation`, `OAI.WeakPureInfiniteness.exact_weaklyPurelyInfinite_individuallyProperlyInfinite_any`, `OAI.WeakPureInfiniteness.exact_weaklyPurelyInfinite_stronglyPurelyInfinite`, `OAI.WeakPureInfiniteness.exists_binary_splitting_over_norm_slice_any`, `OAI.WeakPureInfiniteness.exists_finite_coupling_of_gap_any`, `OAI.WeakPureInfiniteness.exists_square_zero_on_norm_slice_of_gap_any`, `OAI.WeakPureInfiniteness.freeDiagonalFunctional_bound_of_kernel`, `OAI.WeakPureInfiniteness.quantitative_separatingPositives_any` and `OAI.WeakPureInfiniteness.separation_core_comparisons`.
-- source:
--   OpenAI, Weak pure infiniteness and O-infinity absorption (result family 303), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 303; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Weak-pure-infiniteness-and-O-infinity-absorption-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_ExactInfiniteness
import Definitions.Def_OAIQ246W000
import Definitions.Def_OAIQ246W001

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_TensorFoundations
attribute [-instance] _root_.OAI.WeakPureInfiniteness.groupHilbertNontrivial _root_.OAI.WeakPureInfiniteness.instCoeFunContractionAmbientForallContinuousLinearMapComplexIdCarrierHilbert _root_.OAI.WeakPureInfiniteness.instCoeFunFullGroupAmbientForallContinuousLinearMapComplexIdCarrierHilbert _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace

namespace WeakPureInfiniteness

attribute [instance] ComplexHilbert.normedAddCommGroup
  ComplexHilbert.innerProductSpace ComplexHilbert.completeSpace

instance instCStarAlgebraSubtypePreLpCuntzRepresentationContinuousLinearMapComplexIdCarrierHilbertMemAddSubgroupCuntzAmbientStarSubalgebraOInfinity : CStarAlgebra OInfinity := by
  letI : IsClosed (oInfinitySubalgebra : Set CuntzAmbient) :=
    isClosed_closure
  exact inferInstance

open scoped InnerProductSpace

instance fockSpace_nontrivial : Nontrivial FockSpace := by
  refine ⟨⟨lp.single 2 [] 1, 0, ?_⟩⟩
  intro h
  have h' := congrArg (fun x : FockSpace => x []) h
  simp at h'

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_AlgebraicTensorSpan
attribute [-instance] _root_.OAI.WeakPureInfiniteness.crossTensorGraphCStar _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate

namespace WeakPureInfiniteness

universe u v

section TensorSpan

variable {A : Type u} {B C : Type v} [NonUnitalCStarAlgebra A]
  [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]

lemma minimalTensor_eq_closure_span :
    (minimalTensorSubalgebra A B : Set (SpatialAmbient A B)) =
      closure (Submodule.span ℂ (Set.range fun p : A × B => spatialElementary p.1 p.2) : Set (SpatialAmbient A B)) := by
  apply closure_adjoin_eq_closure_span
  · rintro _ ⟨⟨a,b⟩,rfl⟩ _ ⟨⟨c,d⟩,rfl⟩
    exact ⟨(a*c,b*d), spatialElementary_mul a c b d⟩
  · rintro _ ⟨⟨a,b⟩,rfl⟩
    exact ⟨(star a, star b), spatialElementary_star a b⟩

end TensorSpan

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_CStarClosedRange
attribute [-instance] _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal

namespace WeakPureInfiniteness

lemma continuous_clipScale {M : ℝ} (hM : 0 < M) : Continuous (clipScale M) := by
  exact continuous_const.div
    (Real.continuous_sqrt.comp (continuous_const.max continuous_id))
    (fun t => (clipScale_den_pos hM t).ne')

lemma clipScale_eq_one {M t : ℝ} (hM : 0 < M) (ht : t ≤ M ^ 2) :
    clipScale M t = 1 := by
  simp [clipScale, max_eq_left ht, Real.sqrt_sq hM.le, hM.ne']

lemma clipScale_bound {M t : ℝ} (hM : 0 < M) (ht : 0 ≤ t) :
    |clipScale M t * t * clipScale M t| ≤ M ^ 2 := by
  have hd := clipScale_den_pos hM t
  have hs : (Real.sqrt (max (M ^ 2) t)) ^ 2 = max (M ^ 2) t :=
    Real.sq_sqrt ((sq_nonneg M).trans (le_max_left _ _))
  have hf : 0 ≤ clipScale M t := div_nonneg hM.le hd.le
  rw [abs_of_nonneg (mul_nonneg (mul_nonneg hf ht) hf)]
  unfold clipScale
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hd)).mp
  field_simp
  nlinarith [le_max_right (M ^ 2) t]

section Unital

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B] [Nontrivial B]

theorem starHom_exists_lift_norm_le (φ : A →⋆ₐ[ℂ] B) (x : A)
    {M : ℝ} (hM : 0 < M) (hx : ‖φ x‖ ≤ M) :
    ∃ y : A, φ y = φ x ∧ ‖y‖ ≤ M := by
  let a := star x * x
  let f := clipScale M
  have ha : IsSelfAdjoint a := .star_mul_self x
  have hf : Continuous f := continuous_clipScale hM
  let y := x * cfc f a
  have hprod : star y * y = cfc (fun t => f t * t * f t) a := by
    dsimp only [y]
    rw [star_mul, (IsSelfAdjoint.cfc (f := f) (a := a)).star_eq]
    rw [cfc_mul (fun t => f t * t) f a (hf.mul continuous_id).continuousOn hf.continuousOn,
      cfc_mul f (fun t : ℝ => t) a hf.continuousOn continuous_id.continuousOn, cfc_id' ℝ a ha]
    dsimp only [a]
    noncomm_ring
  have hyn : ‖y‖ ≤ M := by
    have hn : ‖star y * y‖ ≤ M ^ 2 := by
      rw [hprod]
      apply norm_cfc_le (sq_nonneg M)
      intro t ht
      exact clipScale_bound hM (spectrum_star_mul_self_nonneg t ht)
    rw [CStarRing.norm_star_mul_self] at hn
    nlinarith [norm_nonneg y]
  have hφa : φ a = star (φ x) * φ x := by
    dsimp only [a]
    rw [map_mul, map_star]
  have he : cfc f (φ a) = 1 := by
    have heq : cfc f (φ a) = cfc (fun _ : ℝ => (1 : ℝ)) (φ a) := by
      apply cfc_congr
      intro t ht
      apply clipScale_eq_one hM
      have ht' := spectrum.norm_le_norm_of_mem ht
      rw [hφa, CStarRing.norm_star_mul_self] at ht'
      have ht0 : 0 ≤ t := spectrum_star_mul_self_nonneg t (hφa ▸ ht)
      rw [Real.norm_eq_abs, abs_of_nonneg ht0] at ht'
      nlinarith [norm_nonneg (φ x)]
    rw [heq, cfc_const 1 (φ a) (ha.map φ), map_one]
  refine ⟨y, ?_, hyn⟩
  dsimp only [y]
  rw [map_mul, φ.map_cfc f a hf.continuousOn (ha := ha) (hφa := ha.map φ), he, mul_one]

theorem starHom_isClosed_range (φ : A →⋆ₐ[ℂ] B) : IsClosed (Set.range φ) := by
  let f : A →L[ℂ] B := φ.toAlgHom.toLinearMap.mkContinuous 1 (by
    intro x
    change ‖φ x‖ ≤ 1 * ‖x‖
    rw [one_mul]
    exact NonUnitalStarAlgHom.norm_apply_le φ x)
  let K := f.ker
  let F : A ⧸ K →L[ℂ] B := K.liftQL f le_rfl
  have hbound : ∀ z : A ⧸ K, ‖z‖ ≤ (1 : ℝ≥0) * ‖F z‖ := by
    intro z
    induction z using Submodule.Quotient.induction_on K with
    | H x =>
      change ‖(Submodule.Quotient.mk x : A ⧸ K)‖ ≤ (1 : ℝ) * ‖φ x‖
      rw [one_mul]
      by_cases hx : φ x = 0
      · have hk : x ∈ K := hx
        rw [(Submodule.Quotient.mk_eq_zero K).mpr hk, norm_zero, hx, norm_zero]
      · obtain ⟨y, hy, hyn⟩ := starHom_exists_lift_norm_le φ x (norm_pos_iff.mpr hx) le_rfl
        have hq : (Submodule.Quotient.mk x : A ⧸ K) = Submodule.Quotient.mk y := by
          apply (Submodule.Quotient.eq K).mpr
          change φ (x - y) = 0
          rw [map_sub, hy, sub_self]
        rw [hq]
        exact (Submodule.Quotient.norm_mk_le K y).trans hyn
  have hclosed := (F.antilipschitz_of_bound hbound).isClosed_range F.uniformContinuous
  have hr : Set.range F = Set.range φ := by
    ext b
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective K z
      exact ⟨x, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨Submodule.Quotient.mk x, rfl⟩
  exact hr ▸ hclosed

end Unital

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_NonUnitalClosedRange
attribute [-instance] _root_.OAI.WeakPureInfiniteness.groupHilbertNontrivial _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal

namespace WeakPureInfiniteness

section NonUnital

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

theorem nonUnitalStarHom_exists_lift_norm_le (φ : A →⋆ₙₐ[ℂ] B) (x : A)
    {M : ℝ} (hM : 0 < M) (hx : ‖φ x‖ ≤ M) :
    ∃ y : A, φ y = φ x ∧ ‖y‖ ≤ M := by
  obtain ⟨y, hy, hyn⟩ := starHom_exists_lift_norm_le (Unitization.starMap φ)
    (x : Unitization ℂ A) hM (by simpa only [Unitization.starMap_inr, Unitization.norm_inr] using hx)
  have hfst : y.fst = 0 := by
    simpa [Unitization.algebraMap_eq_inl] using congrArg (fun z : Unitization ℂ B => z.fst) hy
  have he : (y.snd : Unitization ℂ A) = y := by
    apply Unitization.ext
    · simpa using hfst.symm
    · rfl
  refine ⟨y.snd, ?_, ?_⟩
  · simpa [Unitization.algebraMap_eq_inl] using congrArg (fun z : Unitization ℂ B => z.snd) hy
  · rw [← Unitization.norm_inr (𝕜 := ℂ), he]
    exact hyn

theorem nonUnitalStarHom_isClosed_range (φ : A →⋆ₙₐ[ℂ] B) : IsClosed (Set.range φ) := by
  let f : A →L[ℂ] B := (φ : A →ₗ[ℂ] B).mkContinuous 1 (by
    intro x
    change ‖φ x‖ ≤ 1 * ‖x‖
    rw [one_mul]
    exact NonUnitalStarAlgHom.norm_apply_le φ x)
  let K := f.ker
  let F : A ⧸ K →L[ℂ] B := K.liftQL f le_rfl
  have hbound : ∀ z : A ⧸ K, ‖z‖ ≤ (1 : ℝ≥0) * ‖F z‖ := by
    intro z
    induction z using Submodule.Quotient.induction_on K with
    | H x =>
      change ‖(Submodule.Quotient.mk x : A ⧸ K)‖ ≤ (1 : ℝ) * ‖φ x‖
      rw [one_mul]
      by_cases hx : φ x = 0
      · have hk : x ∈ K := hx
        rw [(Submodule.Quotient.mk_eq_zero K).mpr hk, norm_zero, hx, norm_zero]
      · obtain ⟨y, hy, hyn⟩ := nonUnitalStarHom_exists_lift_norm_le φ x
          (norm_pos_iff.mpr hx) le_rfl
        have hq : (Submodule.Quotient.mk x : A ⧸ K) = Submodule.Quotient.mk y := by
          apply (Submodule.Quotient.eq K).mpr
          change φ (x - y) = 0
          rw [map_sub, hy, sub_self]
        rw [hq]
        exact (Submodule.Quotient.norm_mk_le K y).trans hyn
  have hclosed := (F.antilipschitz_of_bound hbound).isClosed_range F.uniformContinuous
  have hr : Set.range F = Set.range φ := by
    ext b
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective K z
      exact ⟨x, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨Submodule.Quotient.mk x, rfl⟩
  exact hr ▸ hclosed

end NonUnital

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_TensorCut
attribute [-instance] _root_.OAI.WeakPureInfiniteness.crossTensorGraphCStar _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace

namespace WeakPureInfiniteness

universe u v

section TensorCut

variable {A : Type u} {C : Type v} [CStarAlgebra A] [NonUnitalCStarAlgebra C]

def tensorCut (c : C) (x : MinimalTensor A C) : MinimalTensor A C :=
  x - x * rightElementaryHom c

end TensorCut

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_TensorIdealCut
attribute [-instance] _root_.OAI.WeakPureInfiniteness.crossTensorGraphCStar _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
attribute [-simp] _root_.OAI.WeakPureInfiniteness.minimalElementaryLeft_apply _root_.OAI.WeakPureInfiniteness.minimalElementaryRight_apply _root_.OAI.WeakPureInfiniteness.minimalMapLeft_elementary _root_.OAI.WeakPureInfiniteness.spatialElementaryLeft_apply _root_.OAI.WeakPureInfiniteness.spatialElementaryRight_apply _root_.OAI.WeakPureInfiniteness.spatialMapLeft_elementary _root_.OAI.WeakPureInfiniteness.spatialVectorFunctional_elementary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology

namespace WeakPureInfiniteness

open Filter Topology

section TensorIdealCut

variable {A : Type u} {C D : Type v} [CStarAlgebra A]
  [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra D]

lemma kernelAlgebra_closed (q : C →⋆ₙₐ[ℂ] D) : IsClosed (kernelAlgebra q : Set C) :=
  isClosed_eq (nonUnitalStarHom_continuous q) continuous_const

instance instNonUnitalCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplexKernelAlgebra (q : C →⋆ₙₐ[ℂ] D) : NonUnitalCStarAlgebra (kernelAlgebra q) := by
  letI := kernelAlgebra_closed q
  infer_instance

def tensorCutLinear (e : C) : MinimalTensor A C →ₗ[ℂ] MinimalTensor A C where
  toFun := tensorCut e
  map_add' x y := by simp [tensorCut,add_mul,add_sub_add_comm]
  map_smul' c x := by simp [tensorCut,smul_mul_assoc,smul_sub]

def cutVanishingSpace {ι : Type*} (l : Filter ι) (e : ι → C) :
    Submodule ℂ (MinimalTensor A C) where
  carrier := {x | Tendsto (fun i => tensorCut (e i) x) l (𝓝 0)}
  zero_mem' := by simpa [tensorCut] using (tendsto_const_nhds : Tendsto (fun _ : ι => (0 : MinimalTensor A C)) l (𝓝 0))
  add_mem' hx hy := by
    change Tendsto _ _ _
    have hadd (i) (x y : MinimalTensor A C) :
        tensorCut (e i) (x+y) = tensorCut (e i) x + tensorCut (e i) y :=
      (tensorCutLinear (e i)).map_add x y
    simp only [hadd]
    simpa only [add_zero] using hx.add hy
  smul_mem' c x hx := by
    change Tendsto _ _ _
    have hsmul (i) (y : MinimalTensor A C) :
        tensorCut (e i) (c • y) = c • tensorCut (e i) y :=
      (tensorCutLinear (e i)).map_smul c y
    simp only [hsmul]
    simpa only [smul_zero] using hx.const_smul c

end TensorIdealCut

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_MatrixRepresentation
attribute [-instance] _root_.OAI.WeakPureInfiniteness.completedTensorCStar _root_.OAI.WeakPureInfiniteness.hilbertOperatorsCStar _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace

namespace WeakPureInfiniteness

section MatrixOperators

variable {n H : Type*} [Fintype n]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
@[simp]

lemma matrixOperator_apply (M : CStarMatrix n n (H →L[ℂ] H))
    (x : PiLp 2 (fun _ : n => H)) (i : n) :
    matrixOperator M x i = ∑ j, M i j (x j) := by
  simp [matrixOperator]

omit [CompleteSpace H] in
lemma matrixOperator_add (M N : CStarMatrix n n (H →L[ℂ] H)) :
    matrixOperator (M + N) = matrixOperator M + matrixOperator N := by
  ext x i
  simp [Finset.sum_add_distrib]

omit [CompleteSpace H] in
lemma matrixOperator_smul (c : ℂ) (M : CStarMatrix n n (H →L[ℂ] H)) :
    matrixOperator (c • M) = c • matrixOperator M := by
  ext x i
  simp [Finset.smul_sum]

omit [CompleteSpace H] in
lemma matrixOperator_zero : matrixOperator (0 : CStarMatrix n n (H →L[ℂ] H)) = 0 := by
  ext x i
  simp

omit [CompleteSpace H] in
lemma matrixOperator_mul (M N : CStarMatrix n n (H →L[ℂ] H)) :
    matrixOperator (M * N) = matrixOperator M * matrixOperator N := by
  ext x i
  simp only [matrixOperator_apply, CStarMatrix.mul_apply, sum_apply,
    mul_apply_eq_comp, map_sum]
  exact Finset.sum_comm

lemma matrixOperator_star (M : CStarMatrix n n (H →L[ℂ] H)) :
    matrixOperator (star M) = star (matrixOperator M) := by
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  simp only [PiLp.inner_apply, matrixOperator_apply, sum_inner, inner_sum,
    CStarMatrix.star_apply, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_left]
  exact Finset.sum_comm

noncomputable def matrixOperatorHom : CStarMatrix n n (H →L[ℂ] H) →⋆ₙₐ[ℂ]
    ((PiLp 2 (fun _ : n => H)) →L[ℂ] (PiLp 2 (fun _ : n => H))) where
  toFun := matrixOperator
  map_zero' := matrixOperator_zero
  map_add' := matrixOperator_add
  map_smul' := matrixOperator_smul
  map_mul' := matrixOperator_mul
  map_star' := matrixOperator_star

omit [CompleteSpace H] in
lemma matrixOperator_single [DecidableEq n] (M : CStarMatrix n n (H →L[ℂ] H)) (i j : n) (x : H) :
    matrixOperator M (PiLp.single 2 j x) i = M i j x := by
  simp [PiLp.single_apply, apply_ite]

omit [CompleteSpace H] in
lemma matrixOperator_injective : Function.Injective (matrixOperator (n := n) (H := H)) := by
  classical
  intro M N h
  ext i j x
  have he := congrArg (fun T => T (PiLp.single 2 j x) i) h
  simpa only [matrixOperator_single] using he

lemma norm_matrixOperator (M : CStarMatrix n n (H →L[ℂ] H)) :
    ‖matrixOperator M‖ = ‖M‖ := by
  exact NonUnitalStarAlgHom.norm_map (matrixOperatorHom (n := n) (H := H)) (by exact matrixOperator_injective (n := n) (H := H)) M

end MatrixOperators

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_TensorMatrixNorm
attribute [-instance] _root_.OAI.WeakPureInfiniteness.completedTensorCStar _root_.OAI.WeakPureInfiniteness.hilbertOperatorsCStar _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace

namespace WeakPureInfiniteness

section BasisTensor

variable {n H K : Type*} [Fintype n]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

lemma basisTensorMap_surjective (b : OrthonormalBasis n ℂ H) :
    Function.Surjective (basisTensorMap (K := K) b) := by
  intro z
  induction z using OAI.tensorInductionOn with
  | tmul h k =>
    refine ⟨WithLp.toLp 2 (fun i => (b.repr h i) • k), ?_⟩
    change ∑ i, b i ⊗ₜ[ℂ] ((b.repr h i) • k) = h ⊗ₜ[ℂ] k
    conv_rhs => rw [← b.sum_repr h]
    rw [TensorProduct.sum_tmul]
    simp only [TensorProduct.smul_tmul, TensorProduct.tmul_smul]
  | add z w hz hw =>
    obtain ⟨x, rfl⟩ := hz
    obtain ⟨y, rfl⟩ := hw
    exact ⟨x + y, map_add _ _ _⟩

def basisTensorEquiv (b : OrthonormalBasis n ℂ H) :
    PiLp 2 (fun _ : n => K) ≃ₗᵢ[ℂ] H ⊗[ℂ] K :=
  LinearIsometryEquiv.ofSurjective (basisTensorIsometry b) (basisTensorMap_surjective b)

@[simp]
lemma basisTensorEquiv_apply (b : OrthonormalBasis n ℂ H)
    (x : PiLp 2 (fun _ : n => K)) :
    basisTensorEquiv b x = ∑ i, b i ⊗ₜ[ℂ] x i := rfl

@[simp]
lemma tensorCoefficientMatrix_apply {B : Type*} [AddCommGroup B] [Module ℂ B]
    (b : OrthonormalBasis n ℂ H) (T : H →L[ℂ] H) (a : B) (i j : n) :
    tensorCoefficientMatrix b T a i j = (b.repr (T (b j)) i) • a := rfl

lemma tensorCoefficientMatrix_intertwining (b : OrthonormalBasis n ℂ H)
    (T : H →L[ℂ] H) (S : K →L[ℂ] K) (x : PiLp 2 (fun _ : n => K)) :
    basisTensorEquiv b (matrixOperator (tensorCoefficientMatrix b T S) x) =
      TensorProduct.mapL T S (basisTensorEquiv b x) := by
  simp only [basisTensorEquiv_apply, matrixOperator_apply, tensorCoefficientMatrix_apply,
    smul_apply, TensorProduct.tmul_sum, TensorProduct.tmul_smul,
    map_sum, TensorProduct.mapL_tmul]
  rw [Finset.sum_comm]
  congr 1
  funext j
  simpa only [TensorProduct.sum_tmul, ← TensorProduct.smul_tmul'] using
    congrArg (fun h : H => h ⊗ₜ[ℂ] S (x j)) (b.sum_repr (T (b j)))

lemma tensorCoefficientSum_intertwining {ι : Type*} (s : Finset ι)
    (b : OrthonormalBasis n ℂ H) (T : ι → H →L[ℂ] H) (S : ι → K →L[ℂ] K)
    (x : PiLp 2 (fun _ : n => K)) :
    basisTensorEquiv b (matrixOperator (∑ i ∈ s, tensorCoefficientMatrix b (T i) (S i)) x) =
      (∑ i ∈ s, TensorProduct.mapL (T i) (S i)) (basisTensorEquiv b x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [matrixOperator_zero]
  | @insert i s hi hs =>
    simp only [Finset.sum_insert hi, matrixOperator_add, add_apply,
      map_add, tensorCoefficientMatrix_intertwining, hs]

lemma norm_tensorCoefficientSum [CompleteSpace K] {ι : Type*} (s : Finset ι)
    (b : OrthonormalBasis n ℂ H) (T : ι → H →L[ℂ] H) (S : ι → K →L[ℂ] K) :
    ‖∑ i ∈ s, TensorProduct.mapL (T i) (S i)‖ =
      ‖∑ i ∈ s, tensorCoefficientMatrix b (T i) (S i)‖ := by
  rw [← norm_matrixOperator]
  exact (norm_eq_of_isometric_intertwining (basisTensorEquiv b) _ _
    (tensorCoefficientSum_intertwining s b T S)).symm

end BasisTensor

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_FaithfulTensorNorm
attribute [-instance] _root_.OAI.WeakPureInfiniteness.completedTensorCStar _root_.OAI.WeakPureInfiniteness.hilbertOperatorsCStar _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace

namespace WeakPureInfiniteness

section TensorRightRepresentation

variable {n H K L B : Type*} [Fintype n]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

omit [PartialOrder B] [StarOrderedRing B] in
lemma map_tensorCoefficientMatrix
    (b : OrthonormalBasis n ℂ H) (T : H →L[ℂ] H) (a : B)
    (φ : B →⋆ₙₐ[ℂ] (K →L[ℂ] K)) :
    CStarMatrix.mapₙₐ φ (tensorCoefficientMatrix b T a) =
      tensorCoefficientMatrix b T (φ a) := by
  apply CStarMatrix.ext
  intro i j
  change φ ((b.repr (T (b j)) i) • a) = (b.repr (T (b j)) i) • φ a
  exact map_smul φ _ _

lemma tensor_norm_le_faithful_finite_left {ι : Type*} (s : Finset ι)
    (b : OrthonormalBasis n ℂ H) (T : ι → H →L[ℂ] H) (a : ι → B)
    (φ : B →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (ψ : B →⋆ₙₐ[ℂ] (L →L[ℂ] L))
    (hφ : Function.Injective φ) :
    ‖∑ i ∈ s, TensorProduct.mapL (T i) (ψ (a i))‖ ≤
      ‖∑ i ∈ s, TensorProduct.mapL (T i) (φ (a i))‖ := by
  rw [norm_tensorCoefficientSum s b, norm_tensorCoefficientSum s b]
  let M : CStarMatrix n n B := ∑ i ∈ s, tensorCoefficientMatrix b (T i) (a i)
  have hm (ρ : B →⋆ₙₐ[ℂ] (K →L[ℂ] K)) :
      CStarMatrix.mapₙₐ ρ M = ∑ i ∈ s, tensorCoefficientMatrix b (T i) (ρ (a i)) := by
    simp only [M, map_sum, map_tensorCoefficientMatrix]
  have hn : CStarMatrix.mapₙₐ ψ M = ∑ i ∈ s, tensorCoefficientMatrix b (T i) (ψ (a i)) := by
    simp only [M, map_sum, map_tensorCoefficientMatrix]
  rw [← hm φ, ← hn]
  have hinj : Function.Injective (CStarMatrix.mapₙₐ φ (n := n)) := by
    intro X Y hXY
    ext i j
    apply hφ
    exact congrArg (fun Z : CStarMatrix n n (K →L[ℂ] K) => Z i j) hXY
  rw [NonUnitalStarAlgHom.norm_map (CStarMatrix.mapₙₐ φ) hinj M]
  exact NonUnitalStarAlgHom.norm_apply_le (CStarMatrix.mapₙₐ ψ) M

end TensorRightRepresentation

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_TensorCompression
attribute [-instance] _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace

namespace WeakPureInfiniteness

section FiniteTensorCompressions

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

lemma norm_compress_le (V : Submodule ℂ H) [V.HasOrthogonalProjection]
    (T : H →L[ℂ] H) : ‖compress V T‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  calc
    ‖compress V T x‖ ≤ ‖T (x : H)‖ := V.norm_orthogonalProjectionOnto_apply_le _
    _ ≤ ‖T‖ * ‖x‖ := T.le_opNorm _

end FiniteTensorCompressions

section TensorNormIndependence

variable {H K L B : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

theorem tensor_norm_le_faithful {ι : Type*} [Finite ι] (s : Finset ι)
    (T : ι → H →L[ℂ] H) (a : ι → B)
    (φ : B →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (ψ : B →⋆ₙₐ[ℂ] (L →L[ℂ] L))
    (hφ : Function.Injective φ) :
    ‖∑ i ∈ s, TensorProduct.mapL (T i) (ψ (a i))‖ ≤
      ‖∑ i ∈ s, TensorProduct.mapL (T i) (φ (a i))‖ := by
  apply norm_tensorSum_le_of_finite_compressions s T (fun i => ψ (a i))
    (ContinuousLinearMap.opNorm_nonneg (∑ i ∈ s, TensorProduct.mapL (T i) (φ (a i))))
  intro V hV
  exact (tensor_norm_le_faithful_finite_left s (stdOrthonormalBasis ℂ V)
    (fun i => compress V (T i)) a φ ψ hφ).trans
      (norm_tensorSum_compress_le s V T (fun i => φ (a i)))

end TensorNormIndependence

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_FullGroupAlgebra
attribute [-instance] _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal

namespace WeakPureInfiniteness

lemma closedStarSpan_le {B : Type*} [CStarAlgebra B] (s : Set B)
    (S : StarSubalgebra ℂ B) (hS : IsClosed (S : Set B)) (hs : s ⊆ S) :
    closedStarSpan s ≤ S :=
  StarSubalgebra.topologicalClosure_minimal
    (StarAlgebra.adjoin_le hs) hS

variable {G : Type u} [Group G]

lemma fullGroupElement_unitary (g : G) : fullGroupElement g ∈ unitary (FullGroupAlgebra G) := by
  constructor
  · rw [← fullGroupElement_inv, ← fullGroupElement_mul, inv_mul_cancel, fullGroupElement_one]
  · rw [← fullGroupElement_inv, ← fullGroupElement_mul, mul_inv_cancel, fullGroupElement_one]

def fullGroupUnitary : G →* unitary (FullGroupAlgebra G) where
  toFun g := ⟨fullGroupElement g, fullGroupElement_unitary g⟩
  map_one' := Subtype.ext fullGroupElement_one
  map_mul' g h := Subtype.ext (fullGroupElement_mul g h)

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_ReducedGroupAlgebra
attribute [-instance] _root_.OAI.WeakPureInfiniteness.instCoeFunContractionAmbientForallContinuousLinearMapComplexIdCarrierHilbert _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
attribute [-simp] _root_.OAI.WeakPureInfiniteness.tensorSequence_apply _root_.OAI.WeakPureInfiniteness.tensorToHilbertSumMap_tmul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace

namespace WeakPureInfiniteness

variable {G : Type u} [Group G]

abbrev leftRegularRepresentation (G : Type u) [Group G] : GroupRepresentation G where
  hilbert := ⟨GroupHilbert G⟩
  group := leftRegular

def reducedGroupSubalgebra (G : Type u) [Group G] :
    StarSubalgebra ℂ (GroupHilbert G →L[ℂ] GroupHilbert G) :=
  (fullGroupEvaluation (leftRegularRepresentation G)).range

abbrev ReducedGroupAlgebra (G : Type u) [Group G] : Type u := reducedGroupSubalgebra G

lemma reducedGroupSubalgebra_closed (G : Type u) [Group G] :
    IsClosed (reducedGroupSubalgebra G : Set (GroupHilbert G →L[ℂ] GroupHilbert G)) :=
  starHom_isClosed_range (fullGroupEvaluation (leftRegularRepresentation G))

instance instCStarAlgebraReducedGroupAlgebra (G : Type u) [Group G] : CStarAlgebra (ReducedGroupAlgebra G) := by
  letI := reducedGroupSubalgebra_closed G
  unfold ReducedGroupAlgebra
  infer_instance

def fullToReduced : FullGroupAlgebra G →⋆ₐ[ℂ] ReducedGroupAlgebra G :=
  (fullGroupEvaluation (leftRegularRepresentation G)).rangeRestrict

@[simp]
lemma fullToReduced_element (g : G) :
    ((fullToReduced (fullGroupElement g) : ReducedGroupAlgebra G) :
      GroupHilbert G →L[ℂ] GroupHilbert G) = leftRegular g := rfl

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_FiniteGroupTensor
attribute [-instance] _root_.OAI.WeakPureInfiniteness.instCStarAlgebraReducedGroupAlgebra _root_.OAI.WeakPureInfiniteness.instCoeFunContractionAmbientForallContinuousLinearMapComplexIdCarrierHilbert _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate

namespace WeakPureInfiniteness

section FiniteGroupSpatial

variable {G F : Type u} [Group G] [Group F] [Fintype F] [DecidableEq F]

abbrev finiteGroupRepresentation (q : G →* F) : GroupRepresentation G where
  hilbert := ⟨EuclideanSpace ℂ F⟩
  group := (finiteLeftRegular F).comp q

abbrev finiteGroupSpatialRepresentation (q : G →* F) :
    SpatialRepresentation (FullGroupAlgebra G) (FullGroupAlgebra G) where
  left := ⟨ULift.{u+1} (EuclideanSpace ℂ F)⟩
  right := ⟨ULift.{u+1} (EuclideanSpace ℂ F)⟩
  leftRep := ((LinearIsometryEquiv.ulift ℂ (EuclideanSpace ℂ F)).symm.conjStarAlgEquiv.toStarAlgHom.comp
    (fullGroupEvaluation (finiteGroupRepresentation q))).toNonUnitalStarAlgHom
  rightRep := ((LinearIsometryEquiv.ulift ℂ (EuclideanSpace ℂ F)).symm.conjStarAlgEquiv.toStarAlgHom.comp
    (fullGroupEvaluation (finiteGroupRepresentation q))).toNonUnitalStarAlgHom

end FiniteGroupSpatial

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_FullGroupDensity
attribute [-instance] _root_.OAI.WeakPureInfiniteness.instCStarAlgebraReducedGroupAlgebra _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal

namespace WeakPureInfiniteness

universe u

section GroupPolynomialDensity

variable {G : Type u} [Group G]

def groupSpan : StarSubalgebra ℂ (FullGroupAmbient G) where
  carrier := Submodule.span ℂ (Set.range (fullGroupOperator (G := G)))
  zero_mem' := Submodule.zero_mem _
  add_mem' := Submodule.add_mem _
  algebraMap_mem' c := by
    rw [Algebra.algebraMap_eq_smul_one, ← fullGroupOperator_one]
    exact Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_range_self 1))
  mul_mem' {a} {b} hx hy := by
    change a * b ∈ Submodule.span ℂ (Set.range (fullGroupOperator (G := G)))
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨h, rfl⟩ := hy
        rw [← fullGroupOperator_mul]
        exact Submodule.subset_span (Set.mem_range_self (g*h))
      | zero => simp
      | add x y hx hy hpx hpy => rw [mul_add]; exact Submodule.add_mem _ hpx hpy
      | smul c x hx hpx => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hpx
    | zero => simp
    | add x y hx hy hpx hpy => rw [add_mul]; exact Submodule.add_mem _ hpx hpy
    | smul c x hx hpx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hpx
  star_mem' {a} hx := by
    change star a ∈ Submodule.span ℂ (Set.range (fullGroupOperator (G := G)))
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g,rfl⟩ := hx
      rw [← fullGroupOperator_inv]
      exact Submodule.subset_span (Set.mem_range_self g⁻¹)
    | zero => simp
    | add x y hx hy hpx hpy => rw [star_add]; exact Submodule.add_mem _ hpx hpy
    | smul c x hx hpx => rw [star_smul]; exact Submodule.smul_mem _ (star c) hpx

end GroupPolynomialDensity

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_GroupPolynomials
attribute [-instance] _root_.OAI.WeakPureInfiniteness.instCStarAlgebraReducedGroupAlgebra _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal

namespace WeakPureInfiniteness

variable {G : Type*} [Group G]

def fullGroupAmbientInclusion : FullGroupAlgebra G →⋆ₐ[ℂ] FullGroupAmbient G where
  toFun x := x.val
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_one' := rfl
  commutes' _ := rfl
  map_star' _ := rfl

def fullGroupPolynomial : (G →₀ ℂ) →ₗ[ℂ] FullGroupAlgebra G :=
  Finsupp.linearCombination ℂ fullGroupElement

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_TensorDensity
attribute [-instance] _root_.OAI.WeakPureInfiniteness.crossTensorGraphCStar _root_.OAI.WeakPureInfiniteness.instCStarAlgebraReducedGroupAlgebra _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate

namespace WeakPureInfiniteness

universe u v

section TensorContinuity

variable {A : Type u} {B : Type v} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

def minimalAmbientInclusion : MinimalTensor A B →⋆ₙₐ[ℂ] SpatialAmbient A B where
  toFun x := x.val
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

end TensorContinuity

section GroupTensorDensity

variable {G : Type u} [Group G]

def groupTensorPolynomial : (G × G →₀ ℂ) →ₗ[ℂ]
    MinimalTensor (FullGroupAlgebra G) (FullGroupAlgebra G) :=
  Finsupp.linearCombination ℂ (fun p => minimalElementary (fullGroupElement p.1) (fullGroupElement p.2))

end GroupTensorDensity

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_ScalarDiagonal
attribute [-instance] _root_.OAI.WeakPureInfiniteness.crossTensorGraphCStar _root_.OAI.WeakPureInfiniteness.instCStarAlgebraReducedGroupAlgebra _root_.OAI.WeakPureInfiniteness.instNonUnitalCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplexKernelAlgebra _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate

namespace WeakPureInfiniteness

universe u

section FreeDiagonal

variable {α : Type u} [Fintype α] [DecidableEq α]

def freeDiagonalFunctional :
    MinimalTensor (FullGroupAlgebra (FreeGroup α)) (FullGroupAlgebra (FreeGroup α)) →L[ℂ] ℂ :=
  diagonalCoefficient.extendOfNorm groupTensorPolynomial

end FreeDiagonal

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_DiagonalRegular
attribute [-instance] _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace

namespace WeakPureInfiniteness

section ContinuousGroupCoefficients

variable {G : Type u} [Group G]

def rightGroupEvaluation : FullGroupAlgebra G →⋆ₐ[ℂ]
    (GroupHilbert G →L[ℂ] GroupHilbert G) :=
  (groupInversion.conjStarAlgEquiv.toStarAlgHom).comp
    (fullGroupEvaluation (leftRegularRepresentation G))

end ContinuousGroupCoefficients

section RegularPairing

variable {G : Type u} [Group G]

abbrev regularBase : GroupHilbert G := by
  classical
  exact lp.single 2 1 1

end RegularPairing

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_ReducedOperators
attribute [-instance] _root_.OAI.WeakPureInfiniteness.crossTensorGraphCStar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace

namespace WeakPureInfiniteness

abbrev ReducedFreeLarge := ULift.{1} (ReducedGroupAlgebra FreeTwo)

def fullToReducedLarge : FullGroupAlgebra (FreeGroup Bool) →⋆ₐ[ℂ] ReducedFreeLarge :=
  uliftStarAlgEquiv.symm.toStarAlgHom.comp fullToReduced

def reducedLargeToOperators : ReducedFreeLarge →⋆ₐ[ℂ]
    (GroupHilbert FreeTwo →L[ℂ] GroupHilbert FreeTwo) where
  toFun x := x.down.val
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_one' := rfl
  commutes' _ := rfl
  map_star' _ := rfl

def freeDiagonalWitness : MinimalTensor (FullGroupAlgebra (FreeGroup Bool)) (FullGroupAlgebra (FreeGroup Bool)) :=
  ∑ s : FreeLetter, minimalElementary (fullGroupElement (freeLetter s)) (fullGroupElement (freeLetter s))

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_UniversalGroupMap
attribute [-instance] _root_.OAI.WeakPureInfiniteness.instCStarAlgebraReducedGroupAlgebra _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
attribute [-simp] _root_.OAI.WeakPureInfiniteness.contractionEvaluation_word _root_.OAI.WeakPureInfiniteness.fullToReduced_element
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint

namespace WeakPureInfiniteness

def pairRepresentation (π : ContractionRepresentation) : GroupRepresentation (FreeGroup Bool) where
  hilbert := π.hilbert
  group := pairGroup π.operator

def pairAmbientMap : FullGroupAmbient (FreeGroup Bool) →⋆ₐ[ℂ] ContractionAmbient where
  toFun x := ⟨fun π => x (pairRepresentation π), memℓp_infty ⟨‖x‖, by
    rintro _ ⟨π,rfl⟩
    exact lp.norm_apply_le_norm ENNReal.top_ne_zero x (pairRepresentation π)⟩⟩
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_one' := rfl
  commutes' _ := rfl
  map_star' _ := rfl

lemma pairAmbientMap_element (g : FreeGroup Bool) :
    pairAmbientMap (fullGroupOperator g) =
      ((pairGroup universalContractionGenerator g : UniversalContraction).val) := by
  apply Subtype.ext
  funext π
  exact (map_pairGroup (contractionEvaluation π) universalContractionGenerator g).symm

lemma pairAmbientMap_mem (x : FullGroupAlgebra (FreeGroup Bool)) :
    pairAmbientMap x.val ∈ universalContractionSubalgebra := by
  have hcont : Continuous pairAmbientMap :=
    (pairAmbientMap.toAlgHom.toLinearMap.mkContinuous 1 (fun x => by
      change ‖pairAmbientMap x‖ ≤ 1 * ‖x‖
      rw [one_mul]
      exact NonUnitalStarAlgHom.norm_apply_le pairAmbientMap x)).continuous
  have hs : fullGroupSubalgebra (FreeGroup Bool) ≤
      universalContractionSubalgebra.comap pairAmbientMap := by
    apply closedStarSpan_le
    · exact (closedStarSpan_closed _).preimage hcont
    · rintro _ ⟨g,rfl⟩
      change pairAmbientMap (fullGroupOperator g) ∈ universalContractionSubalgebra
      rw [pairAmbientMap_element]
      exact (pairGroup universalContractionGenerator g : UniversalContraction).property
  exact hs x.property

def fullToUniversal : FullGroupAlgebra (FreeGroup Bool) →⋆ₐ[ℂ] UniversalContraction :=
  (pairAmbientMap.comp (fullGroupSubalgebra (FreeGroup Bool)).subtype).codRestrict
    universalContractionSubalgebra pairAmbientMap_mem

@[simp] lemma fullToUniversal_element (g : FreeGroup Bool) :
    fullToUniversal (fullGroupElement g) =
      (pairGroup universalContractionGenerator g : UniversalContraction) :=
  Subtype.ext (pairAmbientMap_element g)

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_FaithfulContractions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint

namespace WeakPureInfiniteness

def universalHilbert : ComplexHilbert.{1} where
  Carrier := lp (fun π : ContractionRepresentation => π.hilbert) 2

def contractionAmbientRepresentation :
    ContractionAmbient →⋆ₙₐ[ℂ] (universalHilbert →L[ℂ] universalHilbert) :=
  productRepresentation

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_WordCompression
attribute [-instance] _root_.OAI.WeakPureInfiniteness.freeOrbitSpace_finite _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
attribute [-simp] _root_.OAI.WeakPureInfiniteness.contractionEvaluation_word
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint

namespace WeakPureInfiniteness

section FiniteCompression

variable {ι S H : Type*} [Finite ι] [Finite S]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

omit [Finite ι] [Finite S] in
lemma wordEval_mem_wordSpace (T : ι → H →L[ℂ] H) (ξ : S → H) (w : List ι) (j : S) :
    wordEval T w (ξ j) ∈ wordSpace T ξ w.length := by
  induction w with
  | nil => exact Submodule.subset_span (Set.mem_range_self j)
  | cons i w ih =>
    apply (show (⨆ i, (wordSpace T ξ w.length).map (T i).toLinearMap) ≤
      wordSpace T ξ (i :: w).length from le_sup_right)
    apply (le_iSup (fun i => (wordSpace T ξ w.length).map (T i).toLinearMap) i)
    exact Submodule.mem_map.mpr ⟨_, ih, rfl⟩

omit [Finite ι] [Finite S] in
lemma wordEval_mem_wordSpace_of_length_le (T : ι → H →L[ℂ] H) (ξ : S → H)
    (w : List ι) (j : S) {m : ℕ} (hw : w.length ≤ m) :
    wordEval T w (ξ j) ∈ wordSpace T ξ m :=
  wordSpace_mono T ξ hw (wordEval_mem_wordSpace T ξ w j)

omit [Finite ι] [Finite S] in
lemma testVector_mem_wordSpace (T : ι → H →L[ℂ] H) (ξ : S → H) (m : ℕ) (j : S) :
    ξ j ∈ wordSpace T ξ m :=
  wordEval_mem_wordSpace_of_length_le T ξ [] j (Nat.zero_le m)

omit [Finite ι] [Finite S] in
lemma adjoint_compress [CompleteSpace H] (K : Submodule ℂ H) [CompleteSpace K]
    (T : H →L[ℂ] H) :
    (compress K T).adjoint = compress K T.adjoint := by
  simp only [compress, ContinuousLinearMap.adjoint_comp, Submodule.adjoint_subtypeL,
    Submodule.adjoint_orthogonalProjectionOnto, ContinuousLinearMap.comp_assoc]

omit [Finite ι] [Finite S] in
lemma compressed_wordEval (K : Submodule ℂ H) [K.HasOrthogonalProjection]
    (T : ι → H →L[ℂ] H) (ξ : H) (hξ : ξ ∈ K) (w : List ι)
    (hmem : ∀ u : List ι, u.length ≤ w.length → wordEval T u ξ ∈ K) :
    (wordEval (fun i => compress K (T i)) w ⟨ξ, hξ⟩ : H) = wordEval T w ξ := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change (K.orthogonalProjectionOnto
      (T i (wordEval (fun i => compress K (T i)) w ⟨ξ, hξ⟩ : H)) : H) = _
    rw [ih (fun u hu => hmem u (by simpa using Nat.le_succ_of_le hu))]
    exact Submodule.starProjection_eq_self_iff.mpr (hmem (i :: w) le_rfl)

lemma wordSpace_compression_exact (T : ι → H →L[ℂ] H) (ξ : S → H) (m : ℕ)
    (w : List ι) (hw : w.length ≤ m) (j : S) :
    (wordEval (fun i => compress (wordSpace T ξ m) (T i)) w
      ⟨ξ j, testVector_mem_wordSpace T ξ m j⟩ : H) = wordEval T w (ξ j) := by
  apply compressed_wordEval
  intro u hu
  exact wordEval_mem_wordSpace_of_length_le T ξ u j (hu.trans hw)

end FiniteCompression

section Amplification

open scoped TensorProduct

variable {ι K E F : Type*}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

noncomputable def amplifiedPolynomial (s : Finset (List ι))
    (B : List ι → K →L[ℂ] K) (T : ι → E →L[ℂ] E) :
    (K ⊗[ℂ] E) →L[ℂ] (K ⊗[ℂ] E) :=
  ∑ w ∈ s, TensorProduct.mapL (B w) (wordEval T w)

end Amplification

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_PolynomialCompression
attribute [-instance] _root_.OAI.WeakPureInfiniteness.freeOrbitSpace_finite _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint

namespace WeakPureInfiniteness

noncomputable def polynomialOperator {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (s : Finset (List Bool))
    (a : List Bool → ℂ) (T : H →L[ℂ] H) : H →L[ℂ] H :=
  ∑ w ∈ s, a w • wordEval (operatorLetters T) w

section PolynomialCompression

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma operatorLetters_compress (K : Submodule ℂ H) [CompleteSpace K]
    (T : H →L[ℂ] H) (i : Bool) :
    operatorLetters (compress K T) i = compress K (operatorLetters T i) := by
  cases i
  · exact adjoint_compress K T
  · rfl

lemma polynomialOperator_compression_exact (s : Finset (List Bool)) (a : List Bool → ℂ)
    (T : H →L[ℂ] H) (ξ : H) :
    let m := s.sup List.length
    let K := wordSpace (operatorLetters T) (fun _ : Unit => ξ) m
    let ξ₀ : K := ⟨ξ, testVector_mem_wordSpace _ _ _ ()⟩
    (polynomialOperator s a (compress K T) ξ₀ : H) = polynomialOperator s a T ξ := by
  dsimp only
  let m := s.sup List.length
  let K := wordSpace (operatorLetters T) (fun _ : Unit => ξ) m
  let ξ₀ : K := ⟨ξ, testVector_mem_wordSpace _ _ _ ()⟩
  change K.subtypeL (polynomialOperator s a (compress K T) ξ₀) = _
  simp only [polynomialOperator, sum_apply, FunLike.coe_smul,
    Pi.smul_apply, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro w hw
  congr 1
  have he : operatorLetters (compress K T) = fun i => compress K (operatorLetters T i) := by
    funext i
    exact operatorLetters_compress K T i
  rw [he]
  exact wordSpace_compression_exact (operatorLetters T) (fun _ : Unit => ξ) m w
    (Finset.le_sup hw) ()

end PolynomialCompression

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_UniversalMapping
attribute [-instance] _root_.OAI.WeakPureInfiniteness.freeOrbitSpace_finite _root_.OAI.WeakPureInfiniteness.instCStarAlgebraReducedGroupAlgebra _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

lemma algebraWord_operator {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (T : H →L[ℂ] H) (w : List Bool) :
    algebraWord T w = wordEval (operatorLetters T) w := by
  induction w with
  | nil => rfl
  | cons i w ih => cases i <;> simp [algebraWord, ih, wordEval, operatorLetters,
      ContinuousLinearMap.mul_def]

lemma algebraPolynomial_operator {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (T : H →L[ℂ] H) (c : List Bool →₀ ℂ) :
    algebraPolynomial T c = polynomialOperator c.support c T := by
  simp only [algebraPolynomial, Finsupp.sum, algebraWord_operator, polynomialOperator]

lemma norm_finitePolynomial_le_universal {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (T : H →L[ℂ] H)
    (hT : ‖T‖ ≤ 1) (c : List Bool →₀ ℂ) :
    ‖algebraPolynomial T c‖ ≤ ‖algebraPolynomial universalContractionGenerator c‖ := by
  by_cases hn : Nontrivial H
  · let := hn
    let e := (stdOrthonormalBasis ℂ H).repr
    let : Nontrivial (EuclideanSpace ℂ (Fin (Module.finrank ℂ H))) := e.symm.toEquiv.nontrivial
    let D := e.conjStarAlgEquiv T
    have hD : ‖D‖ ≤ 1 := (NonUnitalStarAlgHom.norm_apply_le e.conjStarAlgEquiv T).trans hT
    let π : ContractionRepresentation :=
      { hilbert := { Carrier := EuclideanSpace ℂ (Fin (Module.finrank ℂ H)) }
        operator := D
        norm_operator_le_one := hD }
    have he := map_algebraPolynomial e.conjStarAlgEquiv.toStarAlgHom T c
    calc
      ‖algebraPolynomial T c‖ = ‖algebraPolynomial D c‖ := by
        change ‖algebraPolynomial T c‖ = ‖algebraPolynomial (e.conjStarAlgEquiv.toStarAlgHom T) c‖
        rw [← he]
        exact (StarAlgEquiv.norm_map e.conjStarAlgEquiv _).symm
      _ = ‖contractionEvaluation π (algebraPolynomial universalContractionGenerator c)‖ := by
        rw [map_algebraPolynomial]; rfl
      _ ≤ _ := NonUnitalStarAlgHom.norm_apply_le (contractionEvaluation π) _
  · let := not_nontrivial_iff_subsingleton.mp hn
    have hz : algebraPolynomial T c = 0 := Subsingleton.elim _ _
    rw [hz, norm_zero]
    exact norm_nonneg _

lemma norm_operatorPolynomial_le_universal {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (T : H →L[ℂ] H)
    (hT : ‖T‖ ≤ 1) (c : List Bool →₀ ℂ) :
    ‖algebraPolynomial T c‖ ≤ ‖algebraPolynomial universalContractionGenerator c‖ := by
  rw [algebraPolynomial_operator]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro ξ
  let K := wordSpace (operatorLetters T) (fun _ : Unit => ξ) (c.support.sup List.length)
  let ξ₀ : K := ⟨ξ, testVector_mem_wordSpace _ _ _ ()⟩
  have he : (polynomialOperator c.support c (compress K T) ξ₀ : H) =
      polynomialOperator c.support c T ξ := polynomialOperator_compression_exact _ _ _ _
  rw [← he]
  have hb := norm_finitePolynomial_le_universal (compress K T) ((norm_compress_le _ _).trans hT) c
  rw [algebraPolynomial_operator] at hb
  exact (ContinuousLinearMap.le_opNorm _ ξ₀).trans
    (mul_le_mul_of_nonneg_right hb (norm_nonneg _))

lemma norm_algebraPolynomial_le_universal [PartialOrder A] [StarOrderedRing A]
    (x : A) (hx : ‖x‖ ≤ 1) (c : List Bool →₀ ℂ) :
    ‖algebraPolynomial x c‖ ≤ ‖algebraPolynomial universalContractionGenerator c‖ := by
  by_cases hn : Nontrivial A
  · let := hn
    obtain ⟨f, _, hf⟩ := exists_norming_gns (algebraPolynomial x c)
    rw [← hf, map_algebraPolynomial]
    exact norm_operatorPolynomial_le_universal _
      ((NonUnitalStarAlgHom.norm_apply_le f.gnsNonUnitalStarAlgHom x).trans hx) c
  · let := not_nontrivial_iff_subsingleton.mp hn
    rw [Subsingleton.elim (algebraPolynomial x c) 0, norm_zero]
    exact norm_nonneg _

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_UniformModels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped TensorProduct

lemma tensor_norm_le_faithful_finset {H K L A ι : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
    [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (s : Finset ι) (T : ι → H →L[ℂ] H) (a : ι → A)
    (φ : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (ψ : A →⋆ₙₐ[ℂ] (L →L[ℂ] L))
    (hφ : Function.Injective φ) :
    ‖∑ i ∈ s, TensorProduct.mapL (T i) (ψ (a i))‖ ≤
      ‖∑ i ∈ s, TensorProduct.mapL (T i) (φ (a i))‖ := by
  classical
  rw [← Finset.sum_coe_sort s (fun i => TensorProduct.mapL (T i) (ψ (a i))),
    ← Finset.sum_coe_sort s (fun i => TensorProduct.mapL (T i) (φ (a i)))]
  exact tensor_norm_le_faithful Finset.univ (fun i : s => T i) (fun i : s => a i) φ ψ hφ

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_CrossUniverseTensorBound
attribute [-instance] _root_.OAI.WeakPureInfiniteness.crossTensorGraphCStar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped TensorProduct ENNReal

open UniformSpace

universe u v w x

section

variable {A : Type u} {C : Type v} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra C]

variable {H : Type w} {K : Type x} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma norm_tensorSum_le_spatial_any {ι : Type*} (s : Finset ι) (a : ι → A) (c : ι → C)
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ρ : C →⋆ₙₐ[ℂ] (K →L[ℂ] K)) :
    ‖∑ i ∈ s, TensorProduct.mapL (π (a i)) (ρ (c i))‖ ≤
      ‖∑ i ∈ s, spatialElementary (a i) (c i)‖ := by
  let := CStarAlgebra.spectralOrder A
  let := CStarAlgebra.spectralOrderedRing A
  let := CStarAlgebra.spectralOrder C
  let := CStarAlgebra.spectralOrderedRing C
  obtain ⟨H₀,π₀,hπ₀⟩ := exists_faithful_representation A
  obtain ⟨K₀,ρ₀,hρ₀⟩ := exists_faithful_representation C
  let H' : ComplexHilbert.{max u v} := ⟨ULift.{v} H₀⟩
  let K' : ComplexHilbert.{max u v} := ⟨ULift.{u} K₀⟩
  let e : H₀ ≃ₗᵢ[ℂ] H' := (LinearIsometryEquiv.ulift ℂ H₀).symm
  let f : K₀ ≃ₗᵢ[ℂ] K' := (LinearIsometryEquiv.ulift ℂ K₀).symm
  let π' := e.conjStarAlgEquiv.toNonUnitalStarAlgHom.comp π₀
  let ρ' := f.conjStarAlgEquiv.toNonUnitalStarAlgHom.comp ρ₀
  have hπ' : Function.Injective π' := e.conjStarAlgEquiv.injective.comp hπ₀
  have hρ' : Function.Injective ρ' := f.conjStarAlgEquiv.injective.comp hρ₀
  let σ : SpatialRepresentation A C := {left := H',right := K',leftRep := π',rightRep := ρ'}
  calc
    _ ≤ ‖∑ i ∈ s,TensorProduct.mapL (π (a i)) (ρ' (c i))‖ :=
      tensor_norm_le_faithful_finset s (fun i => π (a i)) c ρ' ρ hρ'
    _ = ‖∑ i ∈ s,TensorProduct.mapL (ρ' (c i)) (π (a i))‖ := norm_tensorSum_flip s _ _
    _ ≤ ‖∑ i ∈ s,TensorProduct.mapL (ρ' (c i)) (π' (a i))‖ :=
      tensor_norm_le_faithful_finset s (fun i => ρ' (c i)) a π' π hπ'
    _ = ‖∑ i ∈ s,TensorProduct.mapL (π' (a i)) (ρ' (c i))‖ := norm_tensorSum_flip s _ _
    _ = ‖(∑ i ∈ s, spatialElementary (a i) (c i)) σ‖ := by rw [spatialSum_apply,norm_completion]
    _ ≤ _ := lp.norm_apply_le_norm ENNReal.top_ne_zero _ σ

end

lemma norm_spatialSum_map_any {A : Type u} {B : Type v} {C : Type w} {D : Type x}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra D]
    {ι : Type*} (s : Finset ι) (a : ι → A) (c : ι → C)
    (φ : A →⋆ₙₐ[ℂ] B) (ψ : C →⋆ₙₐ[ℂ] D) :
    ‖∑ i ∈ s,spatialElementary (φ (a i)) (ψ (c i))‖ ≤
      ‖∑ i ∈ s,spatialElementary (a i) (c i)‖ := by
  apply lp.norm_le_of_forall_le (norm_nonneg _)
  intro π
  rw [spatialSum_apply,norm_completion]
  exact norm_tensorSum_le_spatial_any s a c (π.leftRep.comp φ) (π.rightRep.comp ψ)

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_CrossUniverseTensorMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped TensorProduct ENNReal

open UniformSpace Topology

universe u v w x

section

variable {A : Type u} {B : Type v} {C : Type w} {D : Type x}
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra D]

variable (φ : A →⋆ₙₐ[ℂ] B) (ψ : C →⋆ₙₐ[ℂ] D)

lemma crossTensorGraph_norm (z : crossTensorGraph φ ψ) : ‖z.val.2‖ ≤ ‖z.val.1‖ := by
  have hz := z.property
  change z.val ∈ closure (NonUnitalStarAlgebra.adjoin ℂ (Set.range (crossTensorPair φ ψ)) : Set _) at hz
  rw [closure_adjoin_eq_closure_span _
    (by rintro _ ⟨p,rfl⟩ _ ⟨q,rfl⟩; exact ⟨p*q,crossTensorPair_mul φ ψ p q⟩)
    (by rintro _ ⟨p,rfl⟩; exact ⟨star p,crossTensorPair_star φ ψ p⟩)] at hz
  apply closure_minimal (t := {z : MinimalTensor A C × MinimalTensor B D | ‖z.2‖ ≤ ‖z.1‖})
    ?_ (isClosed_le (by fun_prop) (by fun_prop)) hz
  intro z hz
  classical
  obtain ⟨d,rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hz
  change ‖(d.sum fun p t => t • crossTensorPair φ ψ p).2‖ ≤
    ‖(d.sum fun p t => t • crossTensorPair φ ψ p).1‖
  simp only [Finsupp.sum,Prod.snd_sum,Prod.fst_sum,crossTensorPair]
  change ‖(minimalTensorSubalgebra B D).subtype (∑ p ∈ d.support,d p • minimalElementary (φ p.1) (ψ p.2))‖ ≤
    ‖(minimalTensorSubalgebra A C).subtype (∑ p ∈ d.support,d p • minimalElementary p.1 p.2)‖
  simp only [map_sum,map_smul]
  change ‖∑ p ∈ d.support,d p • spatialElementary (φ p.1) (ψ p.2)‖ ≤
    ‖∑ p ∈ d.support,d p • spatialElementary p.1 p.2‖
  simpa only [map_smul,spatialElementary_smul_left] using
    norm_spatialSum_map_any d.support (fun p => d p • p.1) Prod.snd φ ψ

def crossTensorSecond : crossTensorGraph φ ψ →⋆ₙₐ[ℂ] MinimalTensor B D where
  toFun z := z.val.2
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

lemma crossTensorFirst_isometry : Isometry (crossTensorFirst φ ψ) := by
  apply AddMonoidHomClass.isometry_of_norm
  intro z
  change ‖z.val.1‖=‖z.val‖
  rw [Prod.norm_def,max_eq_left (crossTensorGraph_norm φ ψ z)]

lemma crossTensorFirst_surjective : Function.Surjective (crossTensorFirst φ ψ) := by
  let F := (NonUnitalStarSubalgebraClass.subtype (minimalTensorSubalgebra A C)).comp (crossTensorFirst φ ψ)
  have hle : minimalTensorSubalgebra A C ≤ NonUnitalStarAlgHom.range F := by
    apply NonUnitalStarSubalgebra.topologicalClosure_minimal _ (NonUnitalStarAlgebra.adjoin_le ?_)
    · exact nonUnitalStarHom_isClosed_range F
    · rintro _ ⟨p,rfl⟩
      refine ⟨⟨crossTensorPair φ ψ p,?_⟩,rfl⟩
      exact NonUnitalStarSubalgebra.le_topologicalClosure _
        (NonUnitalStarAlgebra.subset_adjoin ℂ _ (Set.mem_range_self p))
  intro z
  obtain ⟨y,hy⟩ := hle z.property
  exact ⟨y,Subtype.ext hy⟩

def minimalMapAny : MinimalTensor A C →⋆ₙₐ[ℂ] MinimalTensor B D :=
  (crossTensorSecond φ ψ).comp
    (StarAlgEquiv.ofBijective (crossTensorFirst φ ψ)
      ⟨(crossTensorFirst_isometry φ ψ).injective,crossTensorFirst_surjective φ ψ⟩).symm.toNonUnitalStarAlgHom

@[simp] lemma minimalMapAny_elementary (a : A) (c : C) :
    minimalMapAny φ ψ (minimalElementary a c)=minimalElementary (φ a) (ψ c) := by
  let z : crossTensorGraph φ ψ := ⟨crossTensorPair φ ψ (a,c),
    NonUnitalStarSubalgebra.le_topologicalClosure _
      (NonUnitalStarAlgebra.subset_adjoin ℂ _ (Set.mem_range_self (a,c)))⟩
  let e := StarAlgEquiv.ofBijective (crossTensorFirst φ ψ)
    ⟨(crossTensorFirst_isometry φ ψ).injective,crossTensorFirst_surjective φ ψ⟩
  have he : e z=minimalElementary a c := rfl
  change (e.symm (minimalElementary a c)).val.2=_
  rw [← he,StarAlgEquiv.symm_apply_apply]
  rfl

end

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_PolynomialSpan
attribute [-instance] _root_.OAI.WeakPureInfiniteness.instCStarAlgebraReducedGroupAlgebra _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

variable {A : Type*} [CStarAlgebra A]

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

lemma universal_graph_bound (v : B) (hv : ‖v‖ ≤ 1)
    (z : UniversalContraction × B)
    (hz : z ∈ closedStarSpan {(universalContractionGenerator, v)}) :
    ‖z.2‖ ≤ ‖z.1‖ := by
  change z ∈ {z : UniversalContraction × B | ‖z.2‖ ≤ ‖z.1‖}
  apply closure_minimal (s := (StarAlgebra.adjoin ℂ {(universalContractionGenerator, v)} : Set _)) ?_ ?_ hz
  · intro z hz
    obtain ⟨c, rfl⟩ := exists_polynomial_of_mem_adjoin _ _ hz
    change ‖(StarAlgHom.snd ℂ UniversalContraction B) (algebraPolynomial _ c)‖ ≤
      ‖(StarAlgHom.fst ℂ UniversalContraction B) (algebraPolynomial _ c)‖
    rw [map_algebraPolynomial, map_algebraPolynomial]
    exact norm_algebraPolynomial_le_universal v hv c
  · exact isClosed_le (continuous_norm.comp continuous_snd) (continuous_norm.comp continuous_fst)

def universalGraph (v : B) : StarSubalgebra ℂ (UniversalContraction × B) :=
  closedStarSpan {(universalContractionGenerator, v)}

instance universalGraphCStar (v : B) : CStarAlgebra (universalGraph v) := closedStarSpanCStar _

def universalGraphFirst (v : B) : universalGraph v →⋆ₐ[ℂ] UniversalContraction :=
  (StarAlgHom.fst ℂ UniversalContraction B).comp (universalGraph v).subtype

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_WordTensorDensity
attribute [-instance] _root_.OAI.WeakPureInfiniteness.crossTensorGraphCStar _root_.OAI.WeakPureInfiniteness.instNonUnitalCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplexKernelAlgebra _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

section TensorDensity

variable {A : Type*} {C : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra C]

def minimalElementaryRightLinear (a : A) : C →ₗ[ℂ] MinimalTensor A C where
  toFun := minimalElementary a
  map_add' c d := Subtype.ext (spatialElementary_add_right a c d)
  map_smul' r c := Subtype.ext (spatialElementary_smul_right r a c)

def minimalElementaryLeftLinear (c : C) : A →ₗ[ℂ] MinimalTensor A C where
  toFun a := minimalElementary a c
  map_add' a b := Subtype.ext (spatialElementary_add_left a b c)
  map_smul' r a := Subtype.ext (spatialElementary_smul_left r a c)

def minimalElementaryLeftContinuous (c : C) : A →L[ℂ] MinimalTensor A C :=
  (minimalElementaryLeftLinear c).mkContinuous ‖c‖ (fun a => by
    change ‖spatialElementary a c‖ ≤ ‖c‖ * ‖a‖
    simpa only [mul_comm] using norm_spatialElementary_le a c)

end TensorDensity

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_CrossUniverseLeftMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

universe u v w

variable {A : Type u} {B : Type v} {C : Type w}
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]

def minimalMapLeftAny (φ : A →⋆ₙₐ[ℂ] B) : MinimalTensor A C →⋆ₙₐ[ℂ] MinimalTensor B C :=
  minimalMapAny φ (NonUnitalStarAlgHom.id ℂ C)

@[simp] lemma minimalMapLeftAny_elementary (φ : A →⋆ₙₐ[ℂ] B) (a : A) (c : C) :
    minimalMapLeftAny φ (minimalElementary a c)=minimalElementary (φ a) c :=
  minimalMapAny_elementary _ _ _ _

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_CrossUniverseUniformModels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped TensorProduct

universe u

def FiniteContractionModelsAny (B : Type u) [CStarAlgebra B] (v : B) (θ : ℝ) : Prop :=
  ∀ (H : ComplexHilbert.{1}) [FiniteDimensional ℂ H] (D : H →L[ℂ] H), ‖D‖ ≤ 1 →
    ∃ K : ComplexHilbert.{u}, ∃ π : B →⋆ₐ[ℂ] (K →L[ℂ] K), ∃ J : H →ₗᵢ[ℂ] K,
      ‖(π v).comp J.toContinuousLinearMap - J.toContinuousLinearMap.comp D‖ ≤ θ ∧
      ‖(star (π v)).comp J.toContinuousLinearMap - J.toContinuousLinearMap.comp (star D)‖ ≤ θ

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_TensorMultiplier
attribute [-instance] _root_.OAI.WeakPureInfiniteness.crossTensorGraphCStar _root_.OAI.WeakPureInfiniteness.instCStarAlgebraReducedGroupAlgebra _root_.OAI.WeakPureInfiniteness.instCoeFunContractionAmbientForallContinuousLinearMapComplexIdCarrierHilbert _root_.OAI.WeakPureInfiniteness.instCoeFunFullGroupAmbientForallContinuousLinearMapComplexIdCarrierHilbert _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

universe u v

noncomputable section

open scoped TensorProduct ENNReal ComplexOrder

open UniformSpace Filter Topology

variable {A B : Type u} {C D : Type v}
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra D]

def spatialRightMultiplier (c : C) : SpatialAmbient A C :=
  ⟨fun π => (TensorProduct.mapL (1 : π.left →L[ℂ] π.left) (π.rightRep c)).completion,
    memℓp_infty ⟨‖c‖, by
      rintro _ ⟨π,rfl⟩
      dsimp only
      rw [norm_completion]
      exact (TensorProduct.norm_mapL_le _ _).trans
        ((mul_le_mul ContinuousLinearMap.norm_id_le (NonUnitalStarAlgHom.norm_apply_le π.rightRep c)
          (norm_nonneg _) zero_le_one).trans_eq (one_mul _))⟩⟩

lemma spatialElementary_mul_rightMultiplier (a : A) (c e : C) :
    spatialElementary a c * spatialRightMultiplier e=spatialElementary a (c*e) := by
  apply Subtype.ext; funext π
  change (TensorProduct.mapL (π.leftRep a) (π.rightRep c)).completion *
    (TensorProduct.mapL 1 (π.rightRep e)).completion =
      (TensorProduct.mapL (π.leftRep a) (π.rightRep (c*e))).completion
  rw [map_mul, ← mul_one (π.leftRep a), TensorProduct.mapL_mul]
  exact (completion_comp _ _).symm

lemma spatial_mul_rightMultiplier_mem (e : C) (x : MinimalTensor A C) :
    x.val * spatialRightMultiplier e ∈ minimalTensorSubalgebra A C := by
  have hs : ∀ z ∈ Submodule.span ℂ (Set.range fun p : A × C => spatialElementary p.1 p.2),
      z * spatialRightMultiplier e ∈ minimalTensorSubalgebra A C := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨⟨a,c⟩,rfl⟩ := hz
      rw [spatialElementary_mul_rightMultiplier]
      exact spatialElementary_mem a (c*e)
    | zero => simp only [zero_mul]; exact (minimalTensorSubalgebra A C).zero_mem
    | add z w _ _ hz hw => rw [add_mul]; exact (minimalTensorSubalgebra A C).add_mem hz hw
    | smul c z _ hz => rw [smul_mul_assoc]; exact (minimalTensorSubalgebra A C).smul_mem c hz
  have hc : IsClosed {z : SpatialAmbient A C | z*spatialRightMultiplier e ∈ minimalTensorSubalgebra A C} :=
    isClosed_closure.preimage (continuous_id.mul continuous_const)
  have hx := x.property
  change x.val ∈ (minimalTensorSubalgebra A C : Set (SpatialAmbient A C)) at hx
  rw [minimalTensor_eq_closure_span] at hx
  exact (closure_minimal hs hc) hx

def tensorRightMultiply (e : C) (x : MinimalTensor A C) : MinimalTensor A C :=
  ⟨x.val * spatialRightMultiplier e, spatial_mul_rightMultiplier_mem e x⟩

def tensorCutNonunital (e : C) (x : MinimalTensor A C) : MinimalTensor A C :=
  x-tensorRightMultiply e x

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_NonunitalHeredity
attribute [-instance] _root_.OAI.WeakPureInfiniteness.crossTensorGraphCStar _root_.OAI.WeakPureInfiniteness.instNonUnitalCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplexKernelAlgebra _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
attribute [-simp] _root_.OAI.WeakPureInfiniteness.minimalElementaryLeft_apply _root_.OAI.WeakPureInfiniteness.minimalElementaryRight_apply _root_.OAI.WeakPureInfiniteness.minimalMapAny_elementary _root_.OAI.WeakPureInfiniteness.minimalMapLeftAny_elementary _root_.OAI.WeakPureInfiniteness.rightElementaryHom_apply _root_.OAI.WeakPureInfiniteness.spatialElementaryLeft_apply _root_.OAI.WeakPureInfiniteness.spatialElementaryRight_apply _root_.OAI.WeakPureInfiniteness.spatialVectorFunctional_elementary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

universe u v

noncomputable section

open Filter Topology

variable {A B : Type u} {C D : Type v} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra D]

def tensorCutNonunitalLinear (e : C) : MinimalTensor A C →ₗ[ℂ] MinimalTensor A C where
  toFun := tensorCutNonunital e
  map_add' x y := by apply Subtype.ext; change (x.val+y.val)-(x.val+y.val)*_=(_-_*_)+(_-_*_); rw [add_mul,add_sub_add_comm]
  map_smul' c x := by apply Subtype.ext; change c • x.val-(c • x.val)*_ = c • (x.val-x.val*_); rw [smul_mul_assoc,smul_sub]

def cutVanishingSpaceNonunital {ι : Type*} (l : Filter ι) (e : ι → C) :
    Submodule ℂ (MinimalTensor A C) where
  carrier := {x | Tendsto (fun i => tensorCutNonunital (e i) x) l (𝓝 0)}
  zero_mem' := by
    change Tendsto (fun i => tensorCutNonunital (e i) (0 : MinimalTensor A C)) l (𝓝 0)
    have hz (e : C) : tensorCutNonunital e (0 : MinimalTensor A C)=0 :=
      Subtype.ext (by change 0-0*_=0; simp)
    simp only [hz]
    exact tendsto_const_nhds
  add_mem' hx hy := by
    change Tendsto _ _ _
    have hadd (i) (x y : MinimalTensor A C) :
        tensorCutNonunital (e i) (x+y) = tensorCutNonunital (e i) x + tensorCutNonunital (e i) y :=
      (tensorCutNonunitalLinear (e i)).map_add x y
    simp only [hadd]
    simpa only [add_zero] using hx.add hy
  smul_mem' c x hx := by
    change Tendsto _ _ _
    have hsmul (i) (y : MinimalTensor A C) :
        tensorCutNonunital (e i) (c • y) = c • tensorCutNonunital (e i) y :=
      (tensorCutNonunitalLinear (e i)).map_smul c y
    simp only [hsmul]
    simpa only [smul_zero] using hx.const_smul c

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_CrossUniverseUniformGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open Filter

open scoped Topology

universe u

structure ExactModelDataAny (θ : ℝ) where
  Carrier : Type u
  [cStarAlgebra : CStarAlgebra Carrier]
  v : Carrier
  norm_v : ‖v‖ ≤ 1
  exactAlgebra : Exact Carrier
  models : FiniteContractionModelsAny Carrier v θ

attribute [instance] ExactModelDataAny.cStarAlgebra

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_CompatibleSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

universe u

noncomputable section

open scoped CStarAlgebra

section

variable (A : Type u) [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def UniformPerturbationOne_any (σ : ℝ) : Prop :=
  ∀ p q h k c : A, ‖p‖ ≤ 1 → ‖q‖ ≤ 1 → 0 ≤ h → 0 ≤ k → 0 ≤ c →
    star p*p*h=h → q*star q*k=k →
    CuntzSubequiv (diagonalCopies 1 c) (diagonalCopies 1 h) →
    CuntzSubequiv (diagonalCopies 1 c) (diagonalCopies 1 k) →
    ∀ (T : A) (η α : ℝ), 0 < η → 0 < α →
      ∃ y : A, ‖y‖ ≤ 1 ∧
        ∀ (H : ComplexHilbert.{u}) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)),
          α ≤ ‖π c‖ → σ*η ≤ ‖π (T+(η : ℂ) • (p*y*q))‖

end

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_PureStates
attribute [-instance] _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped Topology ComplexOrder

section States

variable (A : Type*) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {A}

def realStateComplexification (f : WeakDual ℝ (selfAdjoint A))
    (hf : f ∈ realStateSpace A) : A →ₚ[ℂ] ℂ :=
  positiveComplexification (WeakDual.toStrongDual f) hf.1 hf.2

end States

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_SquareZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped CStarAlgebra Topology

universe u v

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def NonzeroOnNormSlice (D : NonUnitalStarSubalgebra ℂ A) (b : A) (α : ℝ) : Prop :=
  ∀ (H : ComplexHilbert.{u}) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)),
    NonUnitalRepresentationIrreducible π → α ≤ ‖π b‖ →
      ∃ h ∈ D,0 ≤ h ∧ π h ≠ 0

end

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_QuantitativeAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped Topology CStarAlgebra

universe u

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def QuantitativeSeparatingPositives (A : Type u) [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] (σ : ℝ) : Prop :=
  ∀ (a b : A) (ha : 0 ≤ a) (hb : 0 ≤ b), ‖a‖ ≤ 1 → ‖b‖ ≤ 1 →
    ∀ r l : ℝ,0 < r → r < 1 → 0 < l → l < 1/10 →
    ∃ Q R : A,0 ≤ Q ∧ 0 ≤ R ∧
      Q ∈ hereditarySubalgebra a ha.isSelfAdjoint ∧
      R ∈ hereditarySubalgebra b hb.isSelfAdjoint ∧
      (∀ (H : ComplexHilbert.{u}) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)),
        NonUnitalRepresentationIrreducible π →
        (r ≤ ‖π a‖ → r*σ^2/1024 ≤ ‖π Q‖) ∧
        (r ≤ ‖π b‖ → r*σ^2/1024 ≤ ‖π R‖)) ∧
      ‖Q*R‖ ≤ 20*Real.sqrt l

end

end WeakPureInfiniteness
end

end OAI
end


