-- Prove2me | Definitions.Def_OAIErdos3B209
-- name    : OAIErdos3B209
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-10T16:54:20.751188+00:00
-- url     : https://prove2.me/theorems/9ea9e104-51c6-4ac2-919c-f20bf6ec9b32
-- title:
--   OpenAI Erdős-3 split, definitions bundle 210 of 211
-- statement:
--   Definitions bundle 210 of 211 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B208`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 210 available.
--
--   Modules: `OAI.Erdos3.MixedHigherCorner`, `OAI.Erdos3.MixedMiddleCorner`, `OAI.Erdos3.MixedWeightBlock`, `OAI.Erdos3.MixedWeightCorner`, `OAI.Erdos3.NativeMixedPairFactorization.recOn`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_mixedCyclicDiagonalCorrection_expansion`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_mixedMiddleTensor_row_expansion`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_mixedOriginalWeightCorrection_expansion`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_mixedRootCyclicCorrection_expansion`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_mixed_middle_factor_row_expansion`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_original_mixed_first_tensor_equivalence`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixedCanonicalTensor_grouped_merge`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixedCanonicalTensor_weight_merge`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixedCyclicDiagonalCorrection`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixedCyclicDiagonalCorrection_mean_error`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixedFirstTensor`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixedFirstTensor_norm`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixedFirstTensor_unit`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixedHigherTensor`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixedHigherTensor_split`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixedMiddleTensor`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixedMiddleTensor_norm`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixedMiddleTensor_unit`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixedOriginalWeightCorrection`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixedOriginalWeightCorrection_mean_error`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixedOriginalWeightCorrection_pointwise_error`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixedRootCyclicCorrection`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixedRootCyclicCorrection_mean_error`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixedWeightTensor`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixedWeightTensor_first`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixedWrappedDiagonalCorrection`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixedWrappedDiagonalCorrection_mean_error`, `OAI.Erdos3.NativeSampleCorrelation.mixedPairFrequency_apply`, `OAI.Erdos3.NativeSampleCorrelation.mixedPairFrequency_real`, `OAI.Erdos3.NativeSampleCorrelation.mixedPairNiltest_symbol`, `OAI.Erdos3.NativeSampleCorrelation.mixedPairPolynomial`, `OAI.Erdos3.NativeSampleCorrelation.mixedPairPolynomial_eq_test`, `OAI.Erdos3.NativeSampleCorrelation.mixedPairProjection`, `OAI.Erdos3.NilpotentLieFiltration.homogeneousProjected_scalar_coordinate`, `OAI.Erdos3.NilpotentLieFiltration.homogeneousProjected_scalar_identity`, `OAI.Erdos3.NilpotentLieFiltration.projected_realSymbolRepresentative_coefficient`, `OAI.Erdos3.NilpotentLieFiltration.realGradedSymbolPolynomial_filteredMap_coefficient`, `OAI.Erdos3.NilpotentLieFiltration.realSymbolRepresentative_coordinate_top`, `OAI.Erdos3.NilpotentLieFiltration.realSymbolRepresentative_eq_homogeneous_map`, `OAI.Erdos3.NilpotentLieFiltration.realSymbolRepresentative_homogeneous_coefficient`, `OAI.Erdos3.OrdinaryPolynomialPhase.constantBasisIndex`, `OAI.Erdos3.OrdinaryPolynomialPhase.constantBasisIndex_grade`, `OAI.Erdos3.OrdinaryPolynomialPhase.constantCoefficient`, `OAI.Erdos3.OrdinaryPolynomialPhase.constantCoefficientLie`, `OAI.Erdos3.OrdinaryPolynomialPhase.constantCoefficientLie_apply`, `OAI.Erdos3.OrdinaryPolynomialPhase.constantCoefficient_apply`, `OAI.Erdos3.OrdinaryPolynomialPhase.constantCoefficient_centralRationalElement`, `OAI.Erdos3.OrdinaryPolynomialPhase.constantCoefficient_coordinate_ofCoordinates`, `OAI.Erdos3.OrdinaryPolynomialPhase.constantCoefficient_eq_basis_repr`, `OAI.Erdos3.OrdinaryPolynomialPhase.constantCoefficient_eq_zero_iff`, `OAI.Erdos3.OrdinaryPolynomialPhase.constantCoefficient_injective`, `OAI.Erdos3.OrdinaryPolynomialPhase.constantCoefficient_lie`, `OAI.Erdos3.OrdinaryPolynomialPhase.controlledFactorization_approximation`, `OAI.Erdos3.OrdinaryPolynomialPhase.controlledFactorization_approximation_of_normalized_frequency`, `OAI.Erdos3.OrdinaryPolynomialPhase.eq_constantCoefficient_smul_central`, `OAI.Erdos3.OrdinaryPolynomialPhase.frequency_eq_constantCoefficient`, `OAI.Erdos3.OrdinaryPolynomialPhase.gradedProjection`, `OAI.Erdos3.OrdinaryPolynomialPhase.gradedProjection_eq_zero`, `OAI.Erdos3.OrdinaryPolynomialPhase.gradedProjection_image_eq_bot`, `OAI.Erdos3.OrdinaryPolynomialPhase.lie_eq_zero`, `OAI.Erdos3.OrdinaryPolynomialPhase.mem_top`, `OAI.Erdos3.OrdinaryPolynomialPhase.pairScalarFunctional`, `OAI.Erdos3.OrdinaryPolynomialPhase.pairScalarFunctional_basis_logHeight`, `OAI.Erdos3.OrdinaryPolynomialPhase.polynomial_eq_constant`, `OAI.Erdos3.OrdinaryPolynomialPhase.projectedScalarFunctional`, `OAI.Erdos3.OrdinaryPolynomialPhase.projectedScalarFunctional_lie`, `OAI.Erdos3.OrdinaryPolynomialPhase.projection_filtered`, `OAI.Erdos3.OrdinaryPolynomialPhase.realify_constantCoefficient_eq_basis_coord`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationBaseFunctional`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationBaseFunctional_basis_apply`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationBaseFunctional_basis_height`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationBaseFunctional_basis_logHeight`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationBaseFunctional_lie`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationBaseFunctional_majorOrbitSymbol`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationBaseFunctional_pairOrbitSymbol`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationBaseFunctional_value_logHeight`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationBaseMap`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationBasePolynomial`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationBasePolynomial_coefficients`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationBasePolynomial_coefficients_apply`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationBasePolynomial_coordinate`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationBasePolynomial_exists_coefficient_grid`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationBasePolynomial_factorization`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationBasePolynomial_fast_coefficients_mem_span`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationBasePolynomial_majorOrbitSymbol`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationBasePolynomial_mul`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationBasePolynomial_slow_coefficients`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationBase_exists_common_coefficient_grid`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationBase_slow_coefficients`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationBase_span_eq_real_image`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationProjectedBaseMatrix`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationProjectedBaseMatrix_logHeight`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationProjectedBaseMatrix_real_image_eq_span`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationProjectedBaseMatrix_span`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationProjectedGenerators`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationProjectedGenerators_coordinate_logHeight`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationProjectedGenerators_polynomial_logHeight`, `OAI.Erdos3.PolynomialTranslationLie.detectedTranslationProjectedGenerators_span`, `OAI.Erdos3.PolynomialTranslationLie.exists_majorTranslation_partner_niltest`, `OAI.Erdos3.PolynomialTranslationLie.majorTranslationPartnerModel`, `OAI.Erdos3.PolynomialTranslationLie.pairResidueTranslationProjection_coordinate_logHeight`, `OAI.Erdos3.PolynomialTranslationLie.realifyTranslationBaseFunctional_eq_coord`, `OAI.Erdos3.PolynomialTranslationLie.residuePairProjectedGenerators_data`, `OAI.Erdos3.exists_mixed_pair_step_drop`, `OAI.Erdos3.mixedCornerWeight_le`, `OAI.Erdos3.mixedCornerWeight_pos`, `OAI.Erdos3.mixedCornerWeight_zero_iff`, `OAI.Erdos3.mixedGroupedWeightMerge`, `OAI.Erdos3.mixedSplitHigherMerge`, `OAI.Erdos3.mixedSplitHigherMerge_castSucc`, `OAI.Erdos3.mixedSplitHigherMerge_last`, `OAI.Erdos3.mixedWeightBlockCorner`, `OAI.Erdos3.mixedWeightBlockCorner_injective`, `OAI.Erdos3.mixedWeightBlockCorner_surjective`, `OAI.Erdos3.mixedWeightBlockEquiv`, `OAI.Erdos3.mixedWeightBlock_canonical`, `OAI.Erdos3.mixedWeightCorner_card`, `OAI.Erdos3.mixedWeightMerge`, `OAI.Erdos3.mixedWeightMerge_block`, `OAI.Erdos3.mixedWeightOneEquiv`, `OAI.Erdos3.mixedWeightSample`, `OAI.Erdos3.mixedWeightSample_first_input`, `OAI.Erdos3.mixedWeightSample_last_input`, `OAI.Erdos3.mixedWeightSupportEquiv`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B066

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ControlledDetectedTranslationBaseBounds
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (hb : BasisHomogeneousBrackets b ω) (w : σ → ℕ)

theorem realSymbolRepresentative_eq_homogeneous_map (x : F.RealPolynomialSymbol w) :
    F.realSymbolRepresentative b ω hF w x =
      VectorPolynomial.map
        ((realificationLieHom (F.homogeneousAssociatedGradedEquiv b ω hF hb).toLieHom).toLinearMap.restrictScalars ℚ)
        (F.realGradedSymbolPolynomial b ω hF w x) :=
  F.realSymbolRepresentative_eq_map b ω hF w x

theorem realSymbolRepresentative_homogeneous_coefficient (x : F.RealPolynomialSymbol w)
    (α : σ →₀ ℕ) :
    coefficients (F.realSymbolRepresentative b ω hF w x) α =
      realificationLieHom (F.homogeneousAssociatedGradedEquiv b ω hF hb).toLieHom
        (coefficients (F.realGradedSymbolPolynomial b ω hF w x) α) :=
  F.realSymbolRepresentative_coefficient_splitting b ω hF w x α

end Erdos3.NilpotentLieFiltration

namespace Erdos3.PolynomialTranslationLie

open Module VectorPolynomial
open scoped TensorProduct

variable {B U : Type*} [Fintype B]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (c : Basis κ ℚ M) (ν : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))
    (hc : BasisHomogeneousBrackets c ν)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (w : σ → ℕ)

 theorem realGradedSymbolPolynomial_filteredMap_coefficient
    (x : F.RealPolynomialSymbol w) (α : σ →₀ ℕ) :
    coefficients (G.realGradedSymbolPolynomial c ν hG w
      (realificationLieHom (F.filteredPolynomialSymbolMap G φ hφ w) x)) α =
      realificationLieHom (F.associatedGradedMap G φ hφ)
        (coefficients (F.realGradedSymbolPolynomial b ω hF w x) α) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [realificationLieHom_tmul, G.realGradedSymbolPolynomial_coefficient_tmul,
      F.realGradedSymbolPolynomial_coefficient_tmul, realificationLieHom_tmul,
      F.gradedSymbolPolynomial_filteredMap_coefficient G b ω hF c ν hG φ hφ w]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

 theorem projected_realSymbolRepresentative_coefficient
    (x : F.RealPolynomialSymbol w) (α : σ →₀ ℕ) :
    coefficients (G.realSymbolRepresentative c ν hG w
      (realificationLieHom (F.filteredPolynomialSymbolMap G φ hφ w) x)) α =
      realificationLieHom (F.homogeneousGradedProjection G c ν hG hc φ hφ)
        (coefficients (F.realGradedSymbolPolynomial b ω hF w x) α) := by
  rw [G.realSymbolRepresentative_homogeneous_coefficient c ν hG hc,
    F.realGradedSymbolPolynomial_filteredMap_coefficient G b ω hF c ν hG φ hφ w]
  change (G.homogeneousAssociatedGradedEquiv c ν hG hc).toLinearEquiv.toLinearMap.baseChange ℝ
      ((F.associatedGradedMap G φ hφ).toLinearMap.baseChange ℝ _) =
    (((G.homogeneousAssociatedGradedEquiv c ν hG hc).toLinearEquiv.toLinearMap.comp
      (F.associatedGradedMap G φ hφ).toLinearMap).baseChange ℝ) _
  rw [LinearMap.baseChange_comp]
  rfl

theorem homogeneousProjected_scalar_coordinate (η : M →ₗ[ℚ] ℚ)
    (x : F.RealPolynomialSymbol w) :
    coordinate (realifyFunctional
      (η.comp (F.homogeneousGradedProjection G c ν hG hc φ hφ).toLinearMap)).toAddMonoidHom
        (F.realGradedSymbolPolynomial b ω hF w x) =
      coordinate (realifyFunctional η).toAddMonoidHom
        (G.realSymbolRepresentative c ν hG w
          (realificationLieHom (F.filteredPolynomialSymbolMap G φ hφ w) x)) := by
  apply MvPolynomial.ext
  intro α
  rw [coeff_coordinate, coeff_coordinate,
    F.projected_realSymbolRepresentative_coefficient G b ω hF c ν hG hc φ hφ w]
  exact realifyFunctional_comp η
    (F.homogeneousGradedProjection G c ν hG hc φ hφ).toLinearMap _

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

theorem homogeneousProjected_scalar_identity
    {σ ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (c : Basis κ ℚ M) (ν : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))
    (hc : BasisHomogeneousBrackets c ν)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (w : σ → ℕ) (η : M →ₗ[ℚ] ℚ)
    (x : F.RealPolynomialSymbol w) (y : G.RealPolynomialSymbol w)
    (P : MvPolynomial σ ℝ)
    (hmap : realificationLieHom (F.filteredPolynomialSymbolMap G φ hφ w) x = y)
    (hread : coordinate (realifyFunctional η).toAddMonoidHom
      (G.realSymbolRepresentative c ν hG w y) = P) :
    coordinate (realifyFunctional
      (η.comp (F.homogeneousGradedProjection G c ν hG hc φ hφ).toLinearMap)).toAddMonoidHom
      (F.realGradedSymbolPolynomial b ω hF w x) = P := by
  rw [F.homogeneousProjected_scalar_coordinate G b ω hF c ν hG hc φ hφ w η x,
    hmap, hread]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.PolynomialTranslationLie
open Module RationalFilteredNilmanifold

variable {B L : Type} [Fintype B] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)

noncomputable def detectedTranslationBaseMap :
    (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.AssociatedGraded →ₗ[ℚ]
      (B → ℚ) :=
  (baseLinear.comp (weightedSubalgebra w d).subtype).comp
    (weightedTranslationGradedProjection
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration
      w d hw hwd (liePiEval (R := ℚ) true)
      (pairFirstProjection_filtered (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).toLinearMap

noncomputable def detectedTranslationBaseFunctional (i : B) :
    (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.AssociatedGraded →ₗ[ℚ] ℚ :=
  (LinearMap.proj i).comp (detectedTranslationBaseMap w d hw hwd M hM D)

 theorem detectedTranslationBaseFunctional_lie (i : B)
    (x y : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.AssociatedGraded) :
    detectedTranslationBaseFunctional w d hw hwd M hM D i ⁅x, y⁆ = 0 := by
  change (weightedTranslationGradedProjection
    (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration
    w d hw hwd (liePiEval (R := ℚ) true)
    (pairFirstProjection_filtered (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)
      ⁅x, y⁆).val.base i = 0
  rw [LieHom.map_lie]
  rfl

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie
open Module RationalFilteredNilmanifold

variable {B L : Type} [Fintype B] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)

 theorem pairResidueTranslationProjection_coordinate_logHeight {p : ℝ}
    (x : PairAlgebra (weightedSubalgebra w d) L)
    (hx : ∀ j, rationalLogHeight
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).basis.repr x j) ≤ p)
    (i : WeightedBasisIndex w d) :
    rationalLogHeight ((weightedBasis w d hw).repr (x true) i) ≤ p := by
  have h := productProjection_coordinate_logHeight
    (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D) x hx true
    (weightedIndexOrder w d i)
  change rationalLogHeight ((weightedOrderedBasis w d hw).repr (x true)
    (weightedIndexOrder w d i)) ≤ p at h
  have he := weightedOrderedBasis_repr w d hw (x true) (weightedIndexOrder w d i)
  have he' : (weightedOrderedBasis w d hw).repr (x true) (weightedIndexOrder w d i) =
      (weightedBasis w d hw).repr (x true) i :=
    he.trans (congrArg ((weightedBasis w d hw).repr (x true)) ((weightedIndexOrder w d).symm_apply_apply i))
  exact he' ▸ h

 theorem detectedTranslationBaseFunctional_basis_apply
    {ι : Type*} (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hF : ∀ j,
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j =
        Submodule.span ℚ (b '' {i | j ≤ ω i})) (i : B) (j : ι) :
    detectedTranslationBaseFunctional w d hw hwd M hM D i
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.associatedGradedBasis b ω hF j) =
      if ω j = w i then (b j true).val.base i else 0 := by
  let F := (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration
  let φ : PairAlgebra (weightedSubalgebra w d) L →ₗ⁅ℚ⁆ weightedSubalgebra w d :=
    liePiEval (R := ℚ) (M := BoolLieFamily (weightedSubalgebra w d) L) true
  exact weightedTranslationGradedProjection_basis_base F w d hw hwd φ
    (pairFirstProjection_filtered (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)
    b ω hF j i

 theorem detectedTranslationBaseFunctional_basis_logHeight
    {ι : Type*} (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hF : ∀ j,
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j =
        Submodule.span ℚ (b '' {i | j ≤ ω i}))
    {p : ℝ} (hp : 0 ≤ p)
    (hb : ∀ i j, rationalLogHeight
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).basis.repr (b i) j) ≤ p)
    (i : B) (j : ι) :
    rationalLogHeight (detectedTranslationBaseFunctional w d hw hwd M hM D i
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.associatedGradedBasis b ω hF j)) ≤ p := by
  rw [detectedTranslationBaseFunctional_basis_apply w d hw hwd M hM D b ω hF i j]
  split_ifs
  · have hh := pairResidueTranslationProjection_coordinate_logHeight w d hw hwd M hM D
      (b j) (hb j) (Sum.inl i)
    exact (weightedBasis_repr_inl w d hw (b j true) i) ▸ hh
  · simpa [rationalLogHeight] using hp

 theorem detectedTranslationBaseFunctional_basis_height
    {ι : Type*} (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hF : ∀ j,
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j =
        Submodule.span ℚ (b '' {i | j ≤ ω i}))
    {p : ℝ} (hp : 0 ≤ p)
    (hb : ∀ i j, rationalLogHeight
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).basis.repr (b i) j) ≤ p)
    (i : B) (j : ι) :
    RationalHeightLE (detectedTranslationBaseFunctional w d hw hwd M hM D i
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.associatedGradedBasis b ω hF j))
      ⌈Real.exp p⌉₊ :=
  rationalHeightLE_ceil_exp
    (detectedTranslationBaseFunctional_basis_logHeight w d hw hwd M hM D b ω hF hp hb i j)

theorem detectedTranslationBaseFunctional_value_logHeight
    {ι : Type*} [Fintype ι]
    (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hF : ∀ j,
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j =
        Submodule.span ℚ (b '' {i | j ≤ ω i}))
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hb : ∀ i j, rationalLogHeight
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).basis.repr (b i) j) ≤ p)
    (x : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.AssociatedGraded)
    (hx : ∀ j, rationalLogHeight
      (((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.associatedGradedBasis b ω hF).repr x j) ≤ p)
    (i : B) :
    rationalLogHeight (detectedTranslationBaseFunctional w d hw hwd M hM D i x) ≤ (p + 2)^4 :=
  rational_functional_value_logHeight _ _ hp hι
    (detectedTranslationBaseFunctional_basis_logHeight w d hw hwd M hM D b ω hF hp hb i) x hx

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial _root_.MvPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (v : σ → ℕ)

theorem realSymbolRepresentative_coordinate_top
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (i : ι) :
    coordinate ((b.baseChange ℝ).coord i).toAddMonoidHom
      (F.realSymbolRepresentative b ω hF v (F.realSymbolOfPolynomial b ω hF v P)) =
      weightedHomogeneousComponent v (ω i)
        (coordinate ((b.baseChange ℝ).coord i).toAddMonoidHom P) := by
  classical
  apply MvPolynomial.ext
  intro α
  rw [coeff_coordinate, coeff_weightedHomogeneousComponent, coeff_coordinate]
  simp only [LinearMap.toAddMonoidHom_coe, Basis.coord_apply]
  by_cases h : Finsupp.weight v α = ω i
  · rw [if_pos h]
    have hh := (F.realSymbolRepresentative_coefficient b ω hF v _ ⟨(α, i), h⟩).trans
      (F.realSymbolOfPolynomial_coordinate b ω hF v P ⟨(α, i), h⟩)
    convert hh using 1
  · rw [if_neg h]
    have hh := F.realSymbolRepresentative_coefficient_of_ne b ω hF v
      (F.realSymbolOfPolynomial b ω hF v P) α i h
    convert hh using 1

end Erdos3.NilpotentLieFiltration

namespace Erdos3.PolynomialTranslationLie
open Module VectorPolynomial _root_.MvPolynomial RationalFilteredNilmanifold
open scoped TensorProduct

variable {U B L ι : Type} [Fintype B] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)

omit [Fintype (WeightedBasisIndex w d)] in
theorem realifyTranslationBaseFunctional_eq_coord (i : B) :
    realifyFunctional ((LinearMap.proj i).comp
      (baseLinear.comp (weightedSubalgebra w d).subtype)) =
      ((weightedBasis w d hw).baseChange ℝ).coord (Sum.inl i) := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [realifyFunctional_tmul]
    change a * (x.val.base i : ℝ) =
      ((weightedBasis w d hw).baseChange ℝ).repr (a ⊗ₜ[ℚ] x) (Sum.inl i)
    rw [Basis.baseChange_repr_tmul, weightedBasis_repr_inl]
    simp only [Rat.smul_def, mul_comm]
  | add x y hx hy => simp only [map_add, hx, hy]

variable (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hLayers : ∀ j,
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j =
        Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem detectedTranslationBaseFunctional_pairOrbitSymbol
    (p : (weightedFiltration w d hwd).realification.PolynomialOrbit (fun _ : U => 1))
    (q : D.filtration.realification.PolynomialOrbit (fun _ : U => 1)) (i : B) :
    (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.scalarSymbolPolynomial
      b ω hLayers (fun _ : U => 1) (detectedTranslationBaseFunctional w d hw hwd M hM D i)
      (pairOrbitSymbol (weightedTranslationResidueNilmanifold w d hw hwd M hM) D
        p q b ω hLayers) =
      weightedHomogeneousComponent (fun _ : U => 1) (w i)
        (coordinate (((weightedBasis w d hw).baseChange ℝ).coord (Sum.inl i)).toAddMonoidHom p.log) := by
  let N := pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)
  let G := weightedFiltration w d hwd
  let η := (LinearMap.proj i).comp (baseLinear.comp (weightedSubalgebra w d).subtype)
  have h := N.filtration.homogeneousProjected_scalar_coordinate G b ω hLayers
    (weightedBasis w d hw) (weightedBasisGrade w d)
    (weightedFiltration_layer_eq_span w d hw hwd)
    (weightedBasis_homogeneous_brackets w d hw)
    (liePiEval (R := ℚ) true)
    (pairFirstProjection_filtered (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)
    (fun _ : U => 1) η
    (pairOrbitSymbol (weightedTranslationResidueNilmanifold w d hw hwd M hM) D
      p q b ω hLayers).coord
  change N.filtration.scalarSymbolPolynomial b ω hLayers (fun _ : U => 1)
      (detectedTranslationBaseFunctional w d hw hwd M hM D i)
      (pairOrbitSymbol (weightedTranslationResidueNilmanifold w d hw hwd M hM) D
        p q b ω hLayers) = _ at h
  have hp := pairOrbitSymbol_first_projection
    (weightedTranslationResidueNilmanifold w d hw hwd M hM) D (fun _ : U => 1)
    b ω hLayers (weightedBasis w d hw) (weightedBasisGrade w d)
    (weightedFiltration_layer_eq_span w d hw hwd) p q
  change realificationLieHom
    (N.filtration.filteredPolynomialSymbolMap G (liePiEval (R := ℚ) true)
      (pairFirstProjection_filtered (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)
      (fun _ : U => 1))
      (pairOrbitSymbol (weightedTranslationResidueNilmanifold w d hw hwd M hM) D
        p q b ω hLayers).coord =
    G.realSymbolOfPolynomial (weightedBasis w d hw) (weightedBasisGrade w d)
      (weightedFiltration_layer_eq_span w d hw hwd) (fun _ : U => 1) p.log at hp
  rw [hp] at h
  dsimp only [η] at h
  rw [realifyTranslationBaseFunctional_eq_coord w d hw] at h
  exact h.trans (G.realSymbolRepresentative_coordinate_top
    (weightedBasis w d hw) (weightedBasisGrade w d)
    (weightedFiltration_layer_eq_span w d hw hwd) (fun _ : U => 1) p.log (Sum.inl i))

theorem detectedTranslationBaseFunctional_majorOrbitSymbol
    (F : MvPolynomial (U ⊕ B) ℝ)
    (hF : F ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
    (q : D.filtration.realification.PolynomialOrbit (fun _ : U => 1)) (i : B) :
    (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.scalarSymbolPolynomial
      b ω hLayers (fun _ : U => 1) (detectedTranslationBaseFunctional w d hw hwd M hM D i)
      (pairOrbitSymbol (weightedTranslationResidueNilmanifold w d hw hwd M hM) D
        (majorTranslationPolynomialOrbit w d hw hwd F hF A hA) q b ω hLayers) =
      weightedHomogeneousComponent (fun _ : U => 1) (w i) (A i) := by
  rw [detectedTranslationBaseFunctional_pairOrbitSymbol w d hw hwd M hM D b ω hLayers,
    majorTranslationPolynomialOrbit_base_coordinate w d hw hwd F hF A hA]

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie
open Module RationalFilteredNilmanifold VectorPolynomial

variable {B L : Type} [Fintype B] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)
    {ι : Type*} [Fintype ι]
    (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hF : ∀ j,
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j =
        Submodule.span ℚ (b '' {i | j ≤ ω i}))

 theorem detectedTranslationBase_slow_coefficients
    {σ : Type*} (u : σ → ℕ) (T : σ → ℝ) (hT : ∀ a, 0 < T a)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hb : ∀ i j, rationalLogHeight
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).basis.repr (b i) j) ≤ p)
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup u)
    (hE : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.SymbolSlowBound
      b ω hF u T (Real.exp p) E) (i : B) (α : σ →₀ ℕ) :
    |((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.scalarSymbolPolynomial
        b ω hF u (detectedTranslationBaseFunctional w d hw hwd M hM D i) E).coeff α| ≤
      Real.exp ((p + 3)^3) / monomialScale T α := by
  have hcoeff := (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.scalarSymbolPolynomial_slow_coefficients_of_height b ω hF u
    (detectedTranslationBaseFunctional w d hw hwd M hM D i) T hT (Real.exp_pos p).le
    (detectedTranslationBaseFunctional_basis_height w d hw hwd M hM D b ω hF hp hb i) E hE α
  exact le_trans hcoeff
    (div_le_div_of_nonneg_right
      (detectedTranslationCoordinate_slow_factor_le_exp (Fintype.card ι) hp hι)
      (monomialScale_pos T hT α).le)

 theorem detectedTranslationBase_exists_common_coefficient_grid
    {σ : Type*} (u : σ → ℕ)
    {p : ℝ} (hp : 0 ≤ p) (hB : (Fintype.card B : ℝ) ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p)
    (hb : ∀ i j, rationalLogHeight
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).basis.repr (b i) j) ≤ p)
    (m : ℕ) (hm : 0 < m) (hmp : (m : ℝ) ≤ Real.exp p)
    (Q : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup u)
    (hQ : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.SymbolRationalGrid
      b ω hF u m Q) :
    ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ Real.exp ((p + 3)^3) ∧
      ∀ i, realPolynomialCoefficientGrid q
        ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.scalarSymbolPolynomial
          b ω hF u (detectedTranslationBaseFunctional w d hw hwd M hM D i) Q) := by
  let F := (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration
  obtain ⟨q, hq, hqbound, hgrid⟩ := F.scalarSymbolPolynomial_family_exists_coefficient_grid
    b ω hF u (detectedTranslationBaseFunctional w d hw hwd M hM D)
    (detectedTranslationBaseFunctional_basis_height w d hw hwd M hM D b ω hF hp hb)
    m hm Q hQ
  exact ⟨q, hq,
    detectedTranslationCoordinate_denominator_le_exp (Fintype.card B) (Fintype.card ι) m q
      hp hB hι hmp hqbound, hgrid⟩

end Erdos3.PolynomialTranslationLie

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.DetectedTranslationBasePolynomialBounds
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie
open Module RationalFilteredNilmanifold VectorPolynomial

variable {B L : Type} {σ ι : Type*} [Fintype B] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)

variable (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hN : ∀ j, (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

noncomputable def detectedTranslationBasePolynomial
    (g : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : σ => 1)) :
    VectorPolynomial σ ℝ (B → ℝ) :=
  ofCoordinates (Pi.basisFun ℝ B) (fun i =>
    (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.scalarSymbolPolynomial b ω hN (fun _ : σ => 1)
      (detectedTranslationBaseFunctional w d hw hwd M hM D i) g)

@[simp] theorem detectedTranslationBasePolynomial_coordinate
    (g : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : σ => 1)) (i : B) :
    coordinate (LinearMap.proj i : (B → ℝ) →ₗ[ℝ] ℝ).toAddMonoidHom
      (detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN g) =
    (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.scalarSymbolPolynomial b ω hN (fun _ : σ => 1)
      (detectedTranslationBaseFunctional w d hw hwd M hM D i) g := by
  exact coordinate_ofCoordinates (Pi.basisFun ℝ B) _ i

@[simp] theorem detectedTranslationBasePolynomial_coefficients_apply
    (g : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : σ => 1)) (α : σ →₀ ℕ) (i : B) :
    coefficients (detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN g) α i =
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.scalarSymbolPolynomial b ω hN (fun _ : σ => 1)
        (detectedTranslationBaseFunctional w d hw hwd M hM D i) g).coeff α := by
  rw [← detectedTranslationBasePolynomial_coordinate w d hw hwd M hM D b ω hN g i,
    coeff_coordinate]
  rfl

 theorem detectedTranslationBasePolynomial_coefficients
    (g : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : σ => 1)) (α : σ →₀ ℕ) :
    coefficients (detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN g) α =
      realifyCoordinateMap (detectedTranslationBaseMap w d hw hwd M hM D)
        (coefficients ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.realGradedSymbolPolynomial b ω hN (fun _ : σ => 1) g.coord) α) := by
  funext i
  rw [detectedTranslationBasePolynomial_coefficients_apply,
    NilpotentLieFiltration.coeff_scalarSymbolPolynomial]
  rfl

 theorem detectedTranslationBasePolynomial_mul (hd : 1 ≤ d)
    (x y : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : σ => 1)) :
    detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN (x * y) =
      detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN x +
      detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN y := by
  apply coefficients.injective
  ext α i
  simp only [map_add, Finsupp.add_apply, Pi.add_apply,
    detectedTranslationBasePolynomial_coefficients_apply]
  rw [(pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.scalarSymbolPolynomial_mul b ω hN (fun _ : σ => 1)
    (detectedTranslationBaseFunctional w d hw hwd M hM D i)
    (detectedTranslationBaseFunctional_lie w d hw hwd M hM D i) hd,
    MvPolynomial.coeff_add]

 theorem detectedTranslationBasePolynomial_factorization (hd : 1 ≤ d)
    (E P Q X : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : σ => 1))
    (hprod : E * P * Q = X) :
    detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN X =
      detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN E +
      detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN P +
      detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN Q := by
  rw [← hprod, detectedTranslationBasePolynomial_mul w d hw hwd M hM D b ω hN hd,
    detectedTranslationBasePolynomial_mul w d hw hwd M hM D b ω hN hd]

 theorem detectedTranslationBasePolynomial_fast_coefficients_mem_span {J : Type*}
    (W : LieSubalgebra ℚ (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.AssociatedGraded) (v : J → (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.AssociatedGraded)
    (hv : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    (P : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : σ => 1))
    (hP : P.coord ∈ realificationLieSubalgebra
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.symbolPointwiseSubalgebra b ω hN (fun _ : σ => 1) W)) (α : σ →₀ ℕ) :
    coefficients (detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN P) α ∈
      Submodule.span ℝ (Set.range (fun j i =>
        (detectedTranslationBaseMap w d hw hwd M hM D (v j) i : ℝ))) := by
  rw [detectedTranslationBasePolynomial_coefficients]
  exact realifyCoordinateMap_mem_span W.toSubmodule v hv _
    (((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.mem_real_symbolPointwiseSubalgebra_iff_coefficients
      b ω hN (fun _ : σ => 1) W P.coord).mp hP α)

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie
open Module RationalFilteredNilmanifold VectorPolynomial

variable {B L : Type} {σ ι : Type*} [Fintype B] [Fintype ι]
    [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)

variable (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hN : ∀ j, (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hb : ∀ i j, rationalLogHeight ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).basis.repr (b i) j) ≤ p)

include hp hι hb

 theorem detectedTranslationBasePolynomial_slow_coefficients
    (T : σ → ℝ) (hT : ∀ a, 0 < T a)
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : σ => 1))
    (hE : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.SymbolSlowBound b ω hN (fun _ => 1) T (Real.exp p) E) :
    ∀ α i, |coefficients (detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN E) α i| ≤
      Real.exp ((p + 3)^3) / monomialScale T α := by
  intro α i
  rw [detectedTranslationBasePolynomial_coefficients_apply]
  exact detectedTranslationBase_slow_coefficients w d hw hwd M hM D b ω hN
    (fun _ => 1) T hT hp hι hb E hE i α

 theorem detectedTranslationBasePolynomial_exists_coefficient_grid
    (hB : (Fintype.card B : ℝ) ≤ p)
    (m : ℕ) (hm : 0 < m) (hmp : (m : ℝ) ≤ Real.exp p)
    (Q : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : σ => 1))
    (hQ : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.SymbolRationalGrid b ω hN (fun _ => 1) m Q) :
    ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ Real.exp ((p + 3)^3) ∧
      ∀ α, coefficients (detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN Q) α ∈
        realDenominatorGrid q := by
  obtain ⟨q, hq, hqb, hgrid⟩ := detectedTranslationBase_exists_common_coefficient_grid
    w d hw hwd M hM D b ω hN (fun _ => 1) hp hB hι hb m hm hmp Q hQ
  refine ⟨q, hq, hqb, ?_⟩
  exact coefficients_ofCoordinates_mem_realDenominatorGrid _ q hgrid

end Erdos3.PolynomialTranslationLie

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DetectedTranslationMajorBase
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open Module _root_.MvPolynomial _root_.OAI.MvPolynomial RationalFilteredNilmanifold
open scoped TensorProduct

section General

variable {B ι J L : Type*} [Fintype B] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
    {s : ℕ} (F : NilpotentLieFiltration L s)
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (φ : L →ₗ⁅ℚ⁆ weightedSubalgebra w d)
    (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ (weightedFiltration w d hwd).layer j)

noncomputable def detectedTranslationProjectedGenerators (v : J → F.AssociatedGraded) :
    J → weightedSubalgebra w d :=
  fun j => weightedTranslationGradedProjection F w d hw hwd φ hφ (v j)

noncomputable def detectedTranslationProjectedBaseMatrix (v : J → F.AssociatedGraded) :
    Matrix B J ℚ :=
  fun i j => (detectedTranslationProjectedGenerators F w d hw hwd φ hφ v j).val.base i

theorem detectedTranslationProjectedGenerators_span
    (W : LieSubalgebra ℚ F.AssociatedGraded) (v : J → F.AssociatedGraded)
    (hv : Submodule.span ℚ (Set.range v) = W.toSubmodule) :
    Submodule.span ℚ (Set.range (detectedTranslationProjectedGenerators F w d hw hwd φ hφ v)) =
      (W.map (weightedTranslationGradedProjection F w d hw hwd φ hφ)).toSubmodule :=
  F.homogeneousGradedProjection_span (weightedFiltration w d hwd)
    (weightedBasis w d hw) (weightedBasisGrade w d) (weightedFiltration_layer_eq_span w d hw hwd)
    (weightedBasis_homogeneous_brackets w d hw) φ hφ W v hv

theorem detectedTranslationProjectedBaseMatrix_span
    (W : LieSubalgebra ℚ F.AssociatedGraded) (v : J → F.AssociatedGraded)
    (hv : Submodule.span ℚ (Set.range v) = W.toSubmodule) :
    Submodule.span ℚ (Set.range (fun j i => detectedTranslationProjectedBaseMatrix F w d hw hwd φ hφ v i j)) =
      (W.map (weightedTranslationGradedProjection F w d hw hwd φ hφ)).toSubmodule.map
        (baseLinear.comp (weightedSubalgebra w d).subtype) :=
  (coordinateImage_eq_span _ _ (detectedTranslationProjectedGenerators_span F w d hw hwd φ hφ W v hv)
    (baseLinear.comp (weightedSubalgebra w d).subtype)).symm

theorem detectedTranslationProjectedBaseMatrix_real_image_eq_span
    (W : LieSubalgebra ℚ F.AssociatedGraded) (v : J → F.AssociatedGraded)
    (hv : Submodule.span ℚ (Set.range v) = W.toSubmodule) :
    ((W.map (weightedTranslationGradedProjection F w d hw hwd φ hφ)).toSubmodule.baseChange ℝ).map
      (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra w d).subtype)) =
      Submodule.span ℝ (Set.range (fun j i =>
        (detectedTranslationProjectedBaseMatrix F w d hw hwd φ hφ v i j : ℝ))) :=
  realifyCoordinateMap_image_eq_span _ _
    (detectedTranslationProjectedGenerators_span F w d hw hwd φ hφ W v hv)
    (baseLinear.comp (weightedSubalgebra w d).subtype)

variable (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hentries : ∀ i j, rationalLogHeight ((weightedBasis w d hw).repr (φ (b i)) j) ≤ p)
    (v : J → F.AssociatedGraded)
    (hcoords : ∀ j i, rationalLogHeight ((F.associatedGradedBasis b ω hF).repr (v j) i) ≤ p)

include b ω hF hp hι hentries hcoords

theorem detectedTranslationProjectedGenerators_coordinate_logHeight (j : J) (i : WeightedBasisIndex w d) :
    rationalLogHeight ((weightedBasis w d hw).repr
      (detectedTranslationProjectedGenerators F w d hw hwd φ hφ v j) i) ≤ (p + 2)^4 :=
  F.homogeneousGradedProjection_coordinate_logHeight (weightedFiltration w d hwd)
    (weightedBasis w d hw) (weightedBasisGrade w d) (weightedFiltration_layer_eq_span w d hw hwd)
    (weightedBasis_homogeneous_brackets w d hw) φ hφ b ω hF hp hι hentries (v j) (hcoords j) i

theorem detectedTranslationProjectedBaseMatrix_logHeight (i : B) (j : J) :
    rationalLogHeight (detectedTranslationProjectedBaseMatrix F w d hw hwd φ hφ v i j) ≤ (p + 2)^4 :=
  detectedTranslationProjectedGenerators_coordinate_logHeight F w d hw hwd φ hφ b ω hF
    hp hι hentries v hcoords j (Sum.inl i)

theorem detectedTranslationProjectedGenerators_polynomial_logHeight (j : J) (a : B →₀ ℕ) :
    rationalLogHeight
      ((detectedTranslationProjectedGenerators F w d hw hwd φ hφ v j).val.polynomial.coeff a) ≤ (p + 2)^4 := by
  by_cases ha : Finsupp.weight w a < d
  · exact detectedTranslationProjectedGenerators_coordinate_logHeight F w d hw hwd φ hφ b ω hF
      hp hι hentries v hcoords j (Sum.inr ⟨a, ha⟩)
  · have hz : (detectedTranslationProjectedGenerators F w d hw hwd φ hφ v j).val.polynomial.coeff a = 0 := by
      by_contra hne
      have hh := (detectedTranslationProjectedGenerators F w d hw hwd φ hφ v j).property.2
        (MvPolynomial.mem_support_iff.mpr hne)
      change Finsupp.weight w a + 1 ≤ d at hh
      omega
    rw [hz]
    simp only [rationalLogHeight, Rat.num_zero, Int.natAbs_zero, Nat.cast_zero,
      Rat.den_zero, Nat.cast_one, max_eq_right (zero_le_one : (0 : ℝ) ≤ 1), Real.log_one]
    positivity

end General

theorem residuePairProjectedGenerators_data
    {B L ι : Type} [Fintype B] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e) :
    let N := pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)
    ∀ (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
      (hN : ∀ j, N.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (W : LieSubalgebra ℚ N.filtration.AssociatedGraded)
      {n : ℕ} (v : Fin n → N.filtration.AssociatedGraded),
      Submodule.span ℚ (Set.range v) = W.toSubmodule →
      ∀ {p : ℝ}, 0 ≤ p → (Fintype.card ι : ℝ) ≤ p →
      (∀ i j, rationalLogHeight (N.basis.repr (b i) j) ≤ p) →
      (∀ j i, rationalLogHeight ((N.filtration.associatedGradedBasis b ω hN).repr (v j) i) ≤ p) →
      let φ : PairAlgebra (weightedSubalgebra w d) L →ₗ⁅ℚ⁆ weightedSubalgebra w d := liePiEval true
      let hφ := pairFirstProjection_filtered (weightedTranslationResidueNilmanifold w d hw hwd M hM) D
      let U := W.map (weightedTranslationGradedProjection N.filtration w d hw hwd φ hφ)
      let g := detectedTranslationProjectedGenerators N.filtration w d hw hwd φ hφ v
      let C := detectedTranslationProjectedBaseMatrix N.filtration w d hw hwd φ hφ v
      Submodule.span ℚ (Set.range g) = U.toSubmodule ∧
      Submodule.span ℚ (Set.range (fun j i => C i j)) =
        U.toSubmodule.map (baseLinear.comp (weightedSubalgebra w d).subtype) ∧
      (∀ j i, rationalLogHeight ((weightedBasis w d hw).repr (g j) i) ≤ (p + 2)^4) ∧
      (∀ i j, rationalLogHeight (C i j) ≤ (p + 2)^4) ∧
      ∀ j a, rationalLogHeight ((g j).val.polynomial.coeff a) ≤ (p + 2)^4 := by
  intro N b ω hN W n v hv p hp hι hb hcoords φ hφ U g C
  have hentries (i : ι) (j : WeightedBasisIndex w d) :
      rationalLogHeight ((weightedBasis w d hw).repr (φ (b i)) j) ≤ p := by
    have h := productProjection_coordinate_logHeight
      (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)
      (b i) (hb i) true (weightedIndexOrder w d j)
    change rationalLogHeight ((weightedOrderedBasis w d hw).repr (φ (b i))
      (weightedIndexOrder w d j)) ≤ p at h
    have he := weightedOrderedBasis_repr w d hw (φ (b i)) (weightedIndexOrder w d j)
    have he' : (weightedOrderedBasis w d hw).repr (φ (b i)) (weightedIndexOrder w d j) =
        (weightedBasis w d hw).repr (φ (b i)) j :=
      he.trans (congrArg ((weightedBasis w d hw).repr (φ (b i)))
        ((weightedIndexOrder w d).symm_apply_apply j))
    exact he' ▸ h
  exact ⟨detectedTranslationProjectedGenerators_span N.filtration w d hw hwd φ hφ W v hv,
    detectedTranslationProjectedBaseMatrix_span N.filtration w d hw hwd φ hφ W v hv,
    detectedTranslationProjectedGenerators_coordinate_logHeight N.filtration w d hw hwd φ hφ
      b ω hN hp hι hentries v hcoords,
    detectedTranslationProjectedBaseMatrix_logHeight N.filtration w d hw hwd φ hφ
      b ω hN hp hι hentries v hcoords,
    detectedTranslationProjectedGenerators_polynomial_logHeight N.filtration w d hw hwd φ hφ
      b ω hN hp hι hentries v hcoords⟩

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie
open Module RationalFilteredNilmanifold VectorPolynomial _root_.MvPolynomial _root_.OAI.MvPolynomial

variable {B L σ ι : Type} [Fintype B] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)
    (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hN : ∀ j,
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j =
        Submodule.span ℚ (b '' {i | j ≤ ω i}))

 theorem detectedTranslationBasePolynomial_majorOrbitSymbol
    (F : MvPolynomial (σ ⊕ B) ℝ)
    (hF : F ∈ weightedSupportLE (Sum.elim (fun _ : σ => 1) w) d)
    (A : B → MvPolynomial σ ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
    (q : D.filtration.realification.PolynomialOrbit (fun _ : σ => 1)) :
    detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN
      (pairOrbitSymbol (weightedTranslationResidueNilmanifold w d hw hwd M hM) D
        (majorTranslationPolynomialOrbit w d hw hwd F hF A hA) q b ω hN) =
      ofCoordinates (R := ℝ) (Pi.basisFun ℝ B)
        (fun i => weightedHomogeneousComponent (fun _ : σ => 1) (w i) (A i)) := by
  apply (coordinatesEquiv (R := ℝ) (Pi.basisFun ℝ B)).injective
  funext i
  change coordinate ((Pi.basisFun ℝ B).coord i).toAddMonoidHom _ =
    coordinate ((Pi.basisFun ℝ B).coord i).toAddMonoidHom
      (ofCoordinates (R := ℝ) (Pi.basisFun ℝ B)
        (fun j => weightedHomogeneousComponent (fun _ : σ => 1) (w j) (A j)))
  rw [coordinate_ofCoordinates]
  exact (detectedTranslationBasePolynomial_coordinate w d hw hwd M hM D b ω hN _ i).trans
    (detectedTranslationBaseFunctional_majorOrbitSymbol w d hw hwd M hM D b ω hN F hF A hA q i)

 theorem detectedTranslationBase_span_eq_real_image {J : Type*}
    (W : LieSubalgebra ℚ
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.AssociatedGraded)
    (v : J → (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.AssociatedGraded)
    (hv : Submodule.span ℚ (Set.range v) = W.toSubmodule) :
    Submodule.span ℝ (Set.range (fun j i =>
      (detectedTranslationBaseMap w d hw hwd M hM D (v j) i : ℝ))) =
      (((W.map (weightedTranslationGradedProjection
        (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration
        w d hw hwd (liePiEval (R := ℚ) true)
        (pairFirstProjection_filtered (weightedTranslationResidueNilmanifold w d hw hwd M hM) D))).toSubmodule).baseChange ℝ).map
          (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra w d).subtype)) := by
  exact (detectedTranslationProjectedBaseMatrix_real_image_eq_span
    (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration
    w d hw hwd (liePiEval (R := ℚ) true)
    (pairFirstProjection_filtered (weightedTranslationResidueNilmanifold w d hw hwd M hM) D) W v hv).symm

end Erdos3.PolynomialTranslationLie

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedFrozenMiddleRows
namespace OAI

section

namespace Erdos3

open scoped BigOperators

abbrev MixedWeightCorner (s k : ℕ) :=
  {v : Fin (s + 3) → Fin 2 // mixedCornerWeight v = k}

def mixedWeightSupportEquiv (s k : ℕ) :
    MixedWeightCorner s k ≃ {S : Finset (Fin (s + 3)) // S.card = k} :=
  (binaryWordSupportEquiv (s + 3)).subtypeEquiv (fun v => by
    change mixedCornerWeight v = k ↔ (binaryWordSupport v).card = k
    rw [binaryWordSupport_card]
    rfl)

theorem mixedWeightCorner_card (s k : ℕ) :
    Fintype.card (MixedWeightCorner s k) = (s + 3).choose k := by
  calc
    _ = Fintype.card {S : Finset (Fin (s + 3)) // S.card = k} :=
      Fintype.card_congr (mixedWeightSupportEquiv s k)
    _ = _ := by simpa only [Fintype.card_fin] using
      Fintype.card_finset_len (α := Fin (s + 3)) k

theorem mixedCornerWeight_zero_iff {s : ℕ} (v : Fin (s + 3) → Fin 2) :
    mixedCornerWeight v = 0 ↔ v = fun _ => 0 := by
  constructor
  · intro h
    have hc : (binaryWordSupport v).card = 0 := by
      simpa only [binaryWordSupport_card, mixedCornerWeight] using h
    apply (binaryWordSupportEquiv (s + 3)).injective
    exact (Finset.card_eq_zero.mp hc).trans (binaryWordSupport_zero (s + 3)).symm
  · rintro rfl
    simp [mixedCornerWeight]

theorem mixedCornerWeight_le {s : ℕ} (v : Fin (s + 3) → Fin 2) :
    mixedCornerWeight v ≤ s + 3 := by
  have h := (binaryWordSupport v).card_le_univ
  simpa only [binaryWordSupport_card, Fintype.card_fin, mixedCornerWeight] using h

theorem mixedCornerWeight_pos {s : ℕ} (v : MixedNonconstantCorner s) :
    0 < mixedCornerWeight v.val := by
  have h : mixedCornerWeight v.val ≠ 0 := fun h => v.property ((mixedCornerWeight_zero_iff _).mp h)
  omega

noncomputable def mixedWeightOneEquiv (s : ℕ) : Fin (s + 3) ≃ MixedWeightCorner s 1 :=
  (Fintype.equivFinOfCardEq (by simp only [mixedWeightCorner_card, Nat.choose_one_right])).symm

def mixedWeightSample (s : ℕ) (k : Fin (s + 3)) : Fin (s + 3) → Fin 2 :=
  fun j => if j.val < k.val + 1 then 0 else 1

end Erdos3

end

section

namespace Erdos3

abbrev MixedWeightBlock (s : ℕ) := (k : Fin (s + 3)) × MixedWeightCorner s (k.val + 1)

def mixedWeightBlockCorner {s : ℕ} (z : MixedWeightBlock s) : MixedNonconstantCorner s :=
  ⟨z.2.val, by
    intro h
    have hz := (mixedCornerWeight_zero_iff z.2.val).mpr h
    rw [z.2.property] at hz
    omega⟩

theorem mixedWeightBlockCorner_injective (s : ℕ) :
    Function.Injective (mixedWeightBlockCorner (s := s)) := by
  rintro ⟨i, v⟩ ⟨j, w⟩ h
  have hvw : v.val = w.val := congrArg Subtype.val h
  have hij : i.val + 1 = j.val + 1 :=
    v.property.symm.trans ((congrArg mixedCornerWeight hvw).trans w.property)
  have hi : i = j := Fin.ext (by omega)
  subst j
  exact Sigma.ext rfl (heq_of_eq (Subtype.ext hvw))

theorem mixedWeightBlockCorner_surjective (s : ℕ) :
    Function.Surjective (mixedWeightBlockCorner (s := s)) := by
  intro v
  have hp := mixedCornerWeight_pos v
  have hl := mixedCornerWeight_le v.val
  let k : Fin (s + 3) := ⟨mixedCornerWeight v.val - 1, by omega⟩
  have hk : mixedCornerWeight v.val = k.val + 1 := by dsimp [k]; omega
  exact ⟨⟨k, ⟨v.val, hk⟩⟩, Subtype.ext rfl⟩

noncomputable def mixedWeightBlockEquiv (s : ℕ) : MixedWeightBlock s ≃ MixedNonconstantCorner s :=
  Equiv.ofBijective mixedWeightBlockCorner
    ⟨mixedWeightBlockCorner_injective s, mixedWeightBlockCorner_surjective s⟩

theorem mixedWeightBlock_canonical {s : ℕ} (z : MixedWeightBlock s) :
    mixedCanonicalSample (mixedWeightBlockEquiv s z).val = mixedWeightSample s z.1 := by
  change (fun j : Fin (s + 3) => if j.val < mixedCornerWeight z.2.val then (0 : Fin 2) else 1) =
    (fun j : Fin (s + 3) => if j.val < z.1.val + 1 then 0 else 1)
  rw [z.2.property]

noncomputable def mixedWeightMerge {s : ℕ} {I : Type*}
    (a : (k : Fin (s + 3)) → MixedWeightCorner s (k.val + 1) → I)
    (v : MixedNonconstantCorner s) : I :=
  a ((mixedWeightBlockEquiv s).symm v).1 ((mixedWeightBlockEquiv s).symm v).2

theorem mixedWeightMerge_block {s : ℕ} {I : Type*}
    (a : (k : Fin (s + 3)) → MixedWeightCorner s (k.val + 1) → I) (z : MixedWeightBlock s) :
    mixedWeightMerge a (mixedWeightBlockEquiv s z) = a z.1 z.2 := by
  unfold mixedWeightMerge
  rw [Equiv.symm_apply_apply]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem mixedWeightSample_first_input (s : ℕ) (x : Fin 2 → ℤ) :
    mixedSampledInput (mixedWeightSample s 0) x =
      fun j : MixedReplicatedIndex (s + 2) => x j.1 := by
  funext j
  rcases mixedReplicated_cases j with rfl | ⟨i, rfl⟩
  · rfl
  · change x (if i.succ.val < (0 : Fin (s + 3)).val + 1 then 0 else 1) = x 1
    rw [if_neg (by simp only [Fin.val_succ, Fin.val_zero]; omega)]

namespace NativeMultidegreeNilcharacter

variable {s : ℕ} {p : ℝ}
  (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

noncomputable def mixedWeightTensor (k : Fin (s + 3))
    (a : MixedWeightCorner s (k.val + 1) → Fin W.outputDim) (x : Fin 2 → ℤ) : ℂ :=
  ∏ v, W.eval (a v) (mixedSampledInput (mixedWeightSample s k) x)

noncomputable def mixedFirstTensor (a : Fin (s + 3) → Fin W.outputDim) (x : Fin 2 → ℤ) : ℂ :=
  tensorVector W.eval (s + 3) a (fun j => x j.1)

theorem mixedFirstTensor_norm (a : Fin (s + 3) → Fin W.outputDim) (x : Fin 2 → ℤ) :
    ‖W.mixedFirstTensor a x‖ ≤ 1 := by
  rw [mixedFirstTensor, tensorVector, norm_prod]
  exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => W.norm_eval _ _)

theorem mixedFirstTensor_unit (x : Fin 2 → ℤ) :
    ∑ a : Fin (s + 3) → Fin W.outputDim, ‖W.mixedFirstTensor a x‖ ^ 2 = 1 :=
  tensorVector_unit W.eval W.unit_eval (s + 3) _

theorem mixedWeightTensor_first (a : Fin (s + 3) → Fin W.outputDim) (x : Fin 2 → ℤ) :
    W.mixedWeightTensor 0 (fun v => a ((mixedWeightOneEquiv s).symm v)) x = W.mixedFirstTensor a x := by
  unfold mixedWeightTensor mixedFirstTensor tensorVector
  rw [mixedWeightSample_first_input]
  exact (mixedWeightOneEquiv s).symm.prod_comp
    (fun d : Fin (s + 3) => W.eval (a d) (fun j => x j.1))

theorem mixedCanonicalTensor_weight_merge
    (a : (k : Fin (s + 3)) → MixedWeightCorner s (k.val + 1) → Fin W.outputDim)
    (x : Fin 2 → ℤ) :
    star (W.mixedCanonicalTensor (mixedWeightMerge a) x) = ∏ k, W.mixedWeightTensor k (a k) x := by
  rw [mixedCanonicalTensor, star_star]
  calc
    _ = ∏ z : MixedWeightBlock s,
        W.eval (mixedWeightMerge a (mixedWeightBlockEquiv s z))
          (mixedSampledInput (mixedCanonicalSample (mixedWeightBlockEquiv s z).val) x) :=
      ((mixedWeightBlockEquiv s).prod_comp _).symm
    _ = ∏ z : MixedWeightBlock s,
        W.eval (a z.1 z.2) (mixedSampledInput (mixedWeightSample s z.1) x) := by
      apply Finset.prod_congr rfl
      intro z _
      rw [mixedWeightMerge_block, mixedWeightBlock_canonical]
    _ = _ := by simp only [Fintype.prod_sigma, mixedWeightTensor]

end NativeMultidegreeNilcharacter
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

abbrev MixedHigherCorner (s : ℕ) := (k : Fin (s + 2)) × MixedWeightCorner s (k.val + 2)

noncomputable def mixedGroupedWeightMerge {s : ℕ} {I : Type*}
    (a : Fin (s + 3) → I) (b : MixedHigherCorner s → I) : MixedNonconstantCorner s → I :=
  mixedWeightMerge (Fin.cases (motive := fun k : Fin (s + 3) => MixedWeightCorner s (k.val + 1) → I)
    (fun v => a ((mixedWeightOneEquiv s).symm v)) (fun k v => b ⟨k, v⟩))

namespace NativeMultidegreeNilcharacter

variable {s : ℕ} {p : ℝ}
  (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

noncomputable def mixedHigherTensor (b : MixedHigherCorner s → Fin W.outputDim)
    (x : Fin 2 → ℤ) : ℂ :=
  ∏ z, W.eval (b z) (mixedSampledInput (mixedWeightSample s z.1.succ) x)

theorem mixedCanonicalTensor_grouped_merge (a : Fin (s + 3) → Fin W.outputDim)
    (b : MixedHigherCorner s → Fin W.outputDim) (x : Fin 2 → ℤ) :
    star (W.mixedCanonicalTensor (mixedGroupedWeightMerge a b) x) =
      W.mixedFirstTensor a x * W.mixedHigherTensor b x := by
  rw [mixedGroupedWeightMerge, W.mixedCanonicalTensor_weight_merge, Fin.prod_univ_succ]
  change W.mixedWeightTensor 0 (fun v => a ((mixedWeightOneEquiv s).symm v)) x *
    (∏ k : Fin (s + 2), W.mixedWeightTensor k.succ (fun v => b ⟨k, v⟩) x) = _
  rw [W.mixedWeightTensor_first]
  congr 1
  exact (Fintype.prod_sigma (fun z : MixedHigherCorner s =>
    W.eval (b z) (mixedSampledInput (mixedWeightSample s z.1.succ) x))).symm

end NativeMultidegreeNilcharacter
end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

theorem exists_original_mixed_first_tensor_equivalence (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (M : NativeMultidegreeNilcharacter (mixedCorrelationDegree (s + 2)) p)
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p),
      NativeIntegerVectorEquivalence (s + 2) p M.eval
        (fun k x => W.eval k (fun j => x j.1)) →
      NativeIntegerVectorEquivalence (s + 2) ((p + C) ^ C) M.eval W.mixedIntegrationRoot.mixedFirstTensor := by
  obtain ⟨C, hC, h⟩ := exists_original_mixed_root_equivalence s
  refine ⟨C, hC, ?_⟩
  intro p M W E
  exact h M W E

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3

open scoped BigOperators

abbrev MixedMiddleCorner (s : ℕ) := (k : Fin (s + 1)) × MixedWeightCorner s (k.val + 2)

def mixedSplitHigherMerge {s : ℕ} {I : Type*} (b : MixedMiddleCorner s → I) (c : I)
    (z : MixedHigherCorner s) : I :=
  if h : z.1.val < s + 1 then b ⟨⟨z.1.val, h⟩, z.2⟩ else c

theorem mixedSplitHigherMerge_castSucc {s : ℕ} {I : Type*} (b : MixedMiddleCorner s → I) (c : I)
    (k : Fin (s + 1)) (v : MixedWeightCorner s (k.val + 2)) :
    mixedSplitHigherMerge b c ⟨k.castSucc, v⟩ = b ⟨k, v⟩ := by
  simp only [mixedSplitHigherMerge, Fin.val_castSucc, dif_pos k.isLt]

theorem mixedSplitHigherMerge_last {s : ℕ} {I : Type*} (b : MixedMiddleCorner s → I) (c : I)
    (v : MixedWeightCorner s (s + 3)) :
    mixedSplitHigherMerge b c ⟨Fin.last (s + 1), v⟩ = c := by
  unfold mixedSplitHigherMerge
  exact dif_neg (Nat.lt_irrefl (s + 1))

theorem mixedWeightSample_last_input (s : ℕ) (x : Fin 2 → ℤ) :
    mixedSampledInput (mixedWeightSample s (Fin.last (s + 1)).succ) x = fun _ => x 0 := by
  have hs : mixedWeightSample s (Fin.last (s + 1)).succ = fun _ => (0 : Fin 2) := by
    funext j
    unfold mixedWeightSample
    apply if_pos
    simpa only [Fin.val_succ, Fin.val_last] using j.isLt
  rw [hs, ← mixedSampledInput_coordinates]

namespace NativeMultidegreeNilcharacter

variable {s : ℕ} {p : ℝ}
  (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

noncomputable def mixedMiddleTensor (b : MixedMiddleCorner s → Fin W.outputDim)
    (x : Fin 2 → ℤ) : ℂ :=
  ∏ z, W.eval (b z) (mixedSampledInput (mixedWeightSample s z.1.castSucc.succ) x)

theorem mixedMiddleTensor_norm (b : MixedMiddleCorner s → Fin W.outputDim) (x : Fin 2 → ℤ) :
    ‖W.mixedMiddleTensor b x‖ ≤ 1 := by
  rw [mixedMiddleTensor, norm_prod]
  exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => W.norm_eval _ _)

theorem mixedMiddleTensor_unit (x : Fin 2 → ℤ) :
    ∑ b : MixedMiddleCorner s → Fin W.outputDim, ‖W.mixedMiddleTensor b x‖ ^ 2 = 1 := by
  simp only [mixedMiddleTensor, norm_prod, ← Finset.prod_pow]
  calc
    _ = ∏ z : MixedMiddleCorner s, ∑ i : Fin W.outputDim,
        ‖W.eval i (mixedSampledInput (mixedWeightSample s z.1.castSucc.succ) x)‖ ^ 2 :=
      (Fintype.prod_sum _).symm
    _ = 1 := by simp only [W.unit_eval, Finset.prod_const_one]

theorem mixedHigherTensor_split (b : MixedMiddleCorner s → Fin W.outputDim)
    (c : Fin W.outputDim) (x : Fin 2 → ℤ) :
    W.mixedHigherTensor (mixedSplitHigherMerge b c) x =
      W.mixedMiddleTensor b x * W.eval c (fun _ => x 0) := by
  unfold mixedHigherTensor
  rw [Fintype.prod_sigma, Fin.prod_univ_castSucc]
  congr 1
  · simp only [mixedSplitHigherMerge_castSucc]
    exact (Fintype.prod_sigma (fun z : MixedMiddleCorner s =>
      W.eval (b z) (mixedSampledInput (mixedWeightSample s z.1.castSucc.succ) x))).symm
  · simp only [Fin.val_last, mixedSplitHigherMerge_last, mixedWeightSample_last_input,
      Finset.prod_const, Finset.card_univ, mixedWeightCorner_card, Nat.choose_self, pow_one]

end NativeMultidegreeNilcharacter
end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

variable {s : ℕ} {p : ℝ}
  (M : NativeMultidegreeNilcharacter (mixedCorrelationDegree (s + 2)) p)
  (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

noncomputable def mixedOriginalWeightCorrection
    (F : (Fin W.mixedIntegrationRoot.outputDim × Fin W.mixedIntegrationRoot.outputDim) →
      (MixedNonconstantCorner s → Fin W.mixedIntegrationRoot.outputDim) → (Fin 2 → ℤ) → ℂ)
    (a : Fin W.mixedIntegrationRoot.outputDim × Fin W.mixedIntegrationRoot.outputDim)
    (i : Fin M.outputDim) (b : MixedHigherCorner s → Fin W.mixedIntegrationRoot.outputDim)
    (x : Fin 2 → ℤ) : ℂ :=
  ∑ d : Fin (s + 3) → Fin W.mixedIntegrationRoot.outputDim,
    (M.eval i x * star (W.mixedIntegrationRoot.mixedFirstTensor d x)) *
      F a (mixedGroupedWeightMerge d b) x

theorem mixedOriginalWeightCorrection_pointwise_error
    (F : (Fin W.mixedIntegrationRoot.outputDim × Fin W.mixedIntegrationRoot.outputDim) →
      (MixedNonconstantCorner s → Fin W.mixedIntegrationRoot.outputDim) → (Fin 2 → ℤ) → ℂ)
    (a : Fin W.mixedIntegrationRoot.outputDim × Fin W.mixedIntegrationRoot.outputDim)
    (i : Fin M.outputDim) (b : MixedHigherCorner s → Fin W.mixedIntegrationRoot.outputDim)
    (x : Fin 2 → ℤ) (D : ℂ) :
    ‖D * (M.eval i x * W.mixedIntegrationRoot.mixedHigherTensor b x) -
      M.mixedOriginalWeightCorrection W F a i b x‖ ≤
      ∑ d : Fin (s + 3) → Fin W.mixedIntegrationRoot.outputDim,
        ‖D * star (W.mixedIntegrationRoot.mixedCanonicalTensor (mixedGroupedWeightMerge d b) x) -
          F a (mixedGroupedWeightMerge d b) x‖ := by
  let R := W.mixedIntegrationRoot
  have hres := complex_unit_vector_resolution (fun d => R.mixedFirstTensor d x)
    (R.mixedFirstTensor_unit x) (M.eval i x)
  have heq : D * (M.eval i x * R.mixedHigherTensor b x) =
      ∑ d : Fin (s + 3) → Fin R.outputDim,
        (M.eval i x * star (R.mixedFirstTensor d x)) *
          (D * star (R.mixedCanonicalTensor (mixedGroupedWeightMerge d b) x)) := by
    calc
      _ = D * ((∑ d, (M.eval i x * star (R.mixedFirstTensor d x)) * R.mixedFirstTensor d x) *
          R.mixedHigherTensor b x) := by rw [← hres]
      _ = _ := by
        rw [Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d _
        rw [R.mixedCanonicalTensor_grouped_merge]
        ring
  rw [heq, mixedOriginalWeightCorrection, ← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro d _
  rw [← mul_sub, norm_mul]
  apply mul_le_of_le_one_left (norm_nonneg _)
  rw [norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) (M.norm_eval i x)).trans
    (R.mixedFirstTensor_norm d x)

theorem mixedOriginalWeightCorrection_mean_error {N : ℕ} [NeZero N] {ε : ℝ}
    (F : (Fin W.mixedIntegrationRoot.outputDim × Fin W.mixedIntegrationRoot.outputDim) →
      (MixedNonconstantCorner s → Fin W.mixedIntegrationRoot.outputDim) → (Fin 2 → ℤ) → ℂ)
    (D : (Fin W.mixedIntegrationRoot.outputDim × Fin W.mixedIntegrationRoot.outputDim) →
      (Fin 2 → ZMod N) → ℂ)
    (herr : ∀ a b, (𝔼 x : Fin 2 → ZMod N,
      ‖D a x * star (W.mixedIntegrationRoot.mixedCanonicalTensor b (fun k => ((x k).val : ℤ))) -
        F a b (fun k => ((x k).val : ℤ))‖) ≤ ε)
    (a : Fin W.mixedIntegrationRoot.outputDim × Fin W.mixedIntegrationRoot.outputDim)
    (i : Fin M.outputDim) (b : MixedHigherCorner s → Fin W.mixedIntegrationRoot.outputDim) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖D a x * (M.eval i (fun k => ((x k).val : ℤ)) *
          W.mixedIntegrationRoot.mixedHigherTensor b (fun k => ((x k).val : ℤ))) -
        M.mixedOriginalWeightCorrection W F a i b (fun k => ((x k).val : ℤ))‖) ≤
      (W.mixedIntegrationRoot.outputDim : ℝ) ^ (s + 3) * ε := by
  have hm := Finset.expect_le_expect (s := Finset.univ)
    (fun (x : Fin 2 → ZMod N) _ => M.mixedOriginalWeightCorrection_pointwise_error W F a i b
      (fun k => ((x k).val : ℤ)) (D a x))
  rw [Finset.expect_sum_comm] at hm
  apply hm.trans
  calc
    _ ≤ ∑ _ : Fin (s + 3) → Fin W.mixedIntegrationRoot.outputDim, ε :=
      Finset.sum_le_sum (fun d _ => herr a (mixedGroupedWeightMerge d b))
    _ = _ := by simp

theorem exists_mixedOriginalWeightCorrection_expansion (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q : ℝ}
      (M : NativeMultidegreeNilcharacter (mixedCorrelationDegree (s + 2)) p)
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p), 0 ≤ q →
      NativeIntegerVectorEquivalence (s + 2) p M.eval
        (fun k x => W.eval k (fun j => x j.1)) →
      ∀ F : (Fin W.mixedIntegrationRoot.outputDim × Fin W.mixedIntegrationRoot.outputDim) →
        (MixedNonconstantCorner s → Fin W.mixedIntegrationRoot.outputDim) → (Fin 2 → ℤ) → ℂ,
      (∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) q (F a b))) →
      ∀ a i b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) ((p + q + C) ^ C)
        (M.mixedOriginalWeightCorrection W F a i b)) := by
  obtain ⟨A, _, hcompare⟩ := exists_original_mixed_first_tensor_equivalence s
  obtain ⟨B, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let n := (s + 3) ^ (s + 2)
  let K := (s + 3) * (n + 1)
  let X : Polynomial ℕ := Polynomial.X
  let T := (X + Polynomial.C A) ^ A + X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((T + Polynomial.C B) ^ B + Polynomial.C K * (X + 1))
  refine ⟨C, hC, ?_⟩
  intro p q M W hq E F hF a i b
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let v := p + q
  let t := (v + A) ^ A + v + 2
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hqt : q ≤ t := by
    have hh : 0 ≤ (v + A) ^ A := by positivity
    dsimp [t, v] at *
    linarith
  have hAt : (p + A) ^ A ≤ t := by
    apply (pow_le_pow_left₀ (by positivity) (show p + A ≤ v + A by dsimp [v]; linarith) A).trans
    dsimp [t]
    linarith
  have hterm (d : Fin (s + 3) → Fin W.mixedIntegrationRoot.outputDim) :
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) ((t + B) ^ B)
        (fun x => (M.eval i x * star (W.mixedIntegrationRoot.mixedFirstTensor d x)) *
          F a (mixedGroupedWeightMerge d b) x)) :=
    hmul ht ((Classical.choice ((hcompare M W E).expansion i d)).mono hAt)
      ((Classical.choice (hF a (mixedGroupedWeightMerge d b))).mono hqt)
  have hcard : (Fintype.card (Fin (s + 3) → Fin W.mixedIntegrationRoot.outputDim) : ℝ) ≤
      Real.exp ((K : ℝ) * (v + 1)) := by
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    calc
      _ ≤ Real.exp (tensorPowerBudget n p) ^ (s + 3) :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) W.mixedIntegrationRoot.output_bound _
      _ = Real.exp (((s + 3 : ℕ) : ℝ) * tensorPowerBudget n p) :=
        (Real.exp_nat_mul (tensorPowerBudget n p) (s + 3)).symm
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have heq : (((s + 3 : ℕ) : ℝ) * tensorPowerBudget n p) = (K : ℝ) * (p + 1) := by
          simp only [K, tensorPowerBudget, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
          ring
        rw [heq]
        exact mul_le_mul_of_nonneg_left (by dsimp [v]; linarith) (Nat.cast_nonneg _)
  have hcoeff : (∑ _ : Fin (s + 3) → Fin W.mixedIntegrationRoot.outputDim, ‖(1 : ℂ)‖) ≤
      Real.exp ((K : ℝ) * (v + 1)) := by simpa using hcard
  have H := NativeIntegerExpansion.weightedSum (fun d => Classical.choice (hterm d))
    (fun _ => (1 : ℂ)) (by positivity : 0 ≤ (K : ℝ) * (v + 1)) hcard hcoeff
  have hcost : (t + B) ^ B + (K : ℝ) * (v + 1) ≤ (p + q + C) ^ C := by
    simpa [X, T, t, v, Polynomial.eval₂_pow] using hbudget v hv
  refine ⟨?_⟩
  change NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) ((p + q + C) ^ C)
    (fun x => ∑ d : Fin (s + 3) → Fin W.mixedIntegrationRoot.outputDim,
      (M.eval i x * star (W.mixedIntegrationRoot.mixedFirstTensor d x)) * F a (mixedGroupedWeightMerge d b) x)
  simpa only [one_mul] using H.mono hcost

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_mixed_middle_factor_row_expansion (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)
      (h : ℤ) (k : Fin (s + 1)) (a : Fin W.outputDim),
      Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) (s + 1) ((p + C) ^ C)
        (fun x => W.eval a (mixedSampledInput (mixedWeightSample s k.castSucc.succ) ![h, x ()]))) := by
  obtain ⟨C, hC, hfreeze⟩ := exists_frozen_affine_expansion (fun _ : MixedReplicatedIndex (s + 2) => 1)
  refine ⟨C, hC, ?_⟩
  intro p W h k a
  classical
  let S : Finset (MixedReplicatedIndex (s + 2)) :=
    Finset.univ.image (fun i : Fin (s + 1) => mixedReplica i.succ)
  let A : MixedReplicatedIndex (s + 2) → ℤ :=
    fun j => if (mixedInputCoordinate (s + 1) j).val < k.val + 2 then 0 else 1
  let b : MixedReplicatedIndex (s + 2) → ℤ :=
    fun j => if (mixedInputCoordinate (s + 1) j).val < k.val + 2 then h else 0
  have hA : ∀ j, j ∉ S → A j = 0 := by
    intro j hj
    rcases mixedReplicated_cases j with rfl | ⟨i, rfl⟩
    · change (if (0 : ℕ) < k.val + 2 then (0 : ℤ) else 1) = 0
      simp
    · revert hj
      refine Fin.cases ?_ (fun i => ?_) i
      · intro _
        change (if (1 : ℕ) < k.val + 2 then (0 : ℤ) else 1) = 0
        split_ifs <;> omega
      · intro hj
        exact False.elim (hj (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))
  have hi : Function.Injective (fun i : Fin (s + 1) => mixedReplica i.succ) := by
    intro i j hij
    exact Fin.succ_injective _ (mixedReplica_injective _ hij)
  have hc : S.card = s + 1 := by
    dsimp [S]
    rw [Finset.card_image_of_injective _ hi]
    simp
  have hdegree : (∑ i ∈ S, (fun _ : MixedReplicatedIndex (s + 2) => 1) i) = s + 1 := by
    simpa using hc
  obtain ⟨E, _⟩ := hfreeze W S A b a hA
  have hin (x : Unit → ℤ) : (fun j => b j + A j * x ()) =
      mixedSampledInput (mixedWeightSample s k.castSucc.succ) ![h, x ()] := by
    rw [← mixedSampledInput_coordinates]
    funext j
    simp only [A, b, mixedWeightSample, Fin.val_succ, Fin.val_castSucc, Nat.add_assoc]
    split_ifs <;> simp
  have heq : (fun x : Unit → ℤ => W.eval a (fun j => b j + A j * x ())) =
      (fun x => W.eval a (mixedSampledInput (mixedWeightSample s k.castSucc.succ) ![h, x ()])) := by
    funext x
    rw [hin]
  rw [hdegree, heq] at E
  exact ⟨E⟩

theorem exists_mixedMiddleTensor_row_expansion (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)
      (h : ℤ) (b : MixedMiddleCorner s → Fin W.outputDim),
      Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) (s + 1) ((p + C) ^ C)
        (fun x => W.mixedMiddleTensor b ![h, x ()])) := by
  obtain ⟨A, _, hfactor⟩ := exists_mixed_middle_factor_row_expansion s
  obtain ⟨B, _, hprod⟩ := NativeIntegerExpansion.exists_fin_prod_budget (Fintype.card (MixedMiddleCorner s))
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (((X + Polynomial.C A) ^ A + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p W h b
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let e := (Fintype.equivFin (MixedMiddleCorner s)).symm
  obtain ⟨F⟩ := hprod
    (fun i (x : Unit → ℤ) => W.eval (b (e i))
      (mixedSampledInput (mixedWeightSample s (e i).1.castSucc.succ) ![h, x ()]))
    (by positivity : 0 ≤ (p + A) ^ A) (fun i => hfactor W h (e i).1 (b (e i)))
  have hcost : ((p + A) ^ A + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have heq : (fun x : Unit → ℤ => ∏ i, W.eval (b (e i))
      (mixedSampledInput (mixedWeightSample s (e i).1.castSucc.succ) ![h, x ()])) =
      (fun x => W.mixedMiddleTensor b ![h, x ()]) := by
    funext x
    exact e.prod_comp (fun z => W.eval (b z)
      (mixedSampledInput (mixedWeightSample s z.1.castSucc.succ) ![h, x ()]))
  exact ⟨heq ▸ F.mono hcost⟩

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedPairStepDrop
namespace OAI

section

namespace Erdos3

open Module RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

structure NativeMixedPairFactorization {n : ℕ} {p q : ℝ} {N : ℕ} [NeZero N]
    {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p}
    {i j : Fin W.outputDim}
    (V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
      Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
      (fun z => W.mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))) (r : ℝ) where
  [topology : TopologicalSpace (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [topologicalAdd : IsTopologicalAddGroup (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [continuousSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [hausdorff : T2Space (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  basis : Basis (Fin (finrank ℚ V.MixedPairAlgebra)) ℚ V.MixedPairAlgebra
  weight : Fin (finrank ℚ V.MixedPairAlgebra) → ℕ
  adapted : ∀ k, (pi V.mixedPairModels).filtration.layer k =
    Submodule.span ℚ (basis '' {l | k ≤ weight l})
  height : ∀ a b, rationalLogHeight ((pi V.mixedPairModels).basis.repr (basis a) b) ≤ r
  factorization : (pi V.mixedPairModels).filtration.ControlledSymbolFactorization
    basis weight adapted (piFrequency V.mixedPairFrequencies) (fun _ : Fin (n + 2) => (N : ℝ))
    (V.mixedPairNiltest.symbol basis weight adapted) r

theorem exists_mixed_pair_step_drop (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q : ℝ}
      {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p}
      {N : ℕ} [NeZero N] {i j : Fin W.outputDim}
      (V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
        Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => W.mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))),
      Real.exp ((p + q + C) ^ C) ≤ (N : ℝ) →
      Nonempty (NativeMixedPairFactorization V ((p + q + C) ^ C)) := by
  obtain ⟨a, _, hstep⟩ := exists_intrinsic_step_drop (∑ _ : MixedReplicatedIndex (n + 1), 1) (by rw [mixedReplicated_totalDegree]; omega)
  let X : Polynomial ℕ := Polynomial.X
  let Q := 4 * (X + 1) + (X + (X + 2) ^ 2 + 3) + 6
  let R := (Q + 2) ^ 2 + Q + (Q + (Q ^ 2 + Q + 3) ^ 2) + Q ^ 2 + 4 + X + Polynomial.C (n + 2)
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (R + 1 + (R + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro p q W N _ i j V hN
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let r := productNiltestBudget (mixedPairBudget p q) + (p + q) + ((n + 2 : ℕ) : ℝ)
  have hprod : 0 ≤ productNiltestBudget (mixedPairBudget p q) := by
    have hbase := V.mixedPairBudget_six_le
    unfold productNiltestBudget productObservableLipBudget
    positivity
  have hdim : (0 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hqr : q ≤ r := by dsimp only [r]; linarith only [hp, hprod, hdim]
  have hdimr : ((n + 2 : ℕ) : ℝ) ≤ r := by dsimp only [r]; linarith only [hp, hq, hprod]
  have hTr : productNiltestBudget (mixedPairBudget p q) ≤ r := by dsimp only [r]; linarith only [hp, hq, hdim]
  have hr : 0 ≤ r := hq.trans hqr
  have hcost : r + 1 + (r + a) ^ a ≤ (p + q + C) ^ C := by
    simpa [X, Q, R, r, mixedPairBudget, raisedNiltestBudget,
      productNiltestBudget, productObservableLipBudget, Polynomial.eval₂_pow]
      using hbudget (p + q) (add_nonneg hp hq)
  have hpow : 0 ≤ (r + a) ^ a := by positivity
  have hheight : r + 1 ≤ (p + q + C) ^ C := by linarith only [hcost, hpow]
  have hfactor : (r + a) ^ a ≤ (p + q + C) ^ C := by linarith only [hcost, hr]
  obtain ⟨τ, htA, htM, htT⟩ := exists_real_module_topology (productFinBasis V.mixedPairModels)
  let : TopologicalSpace (ℝ ⊗[ℚ] V.MixedPairAlgebra) := τ
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] V.MixedPairAlgebra) := htA
  let : ContinuousSMul ℝ (ℝ ⊗[ℚ] V.MixedPairAlgebra) := htM
  let : T2Space (ℝ ⊗[ℚ] V.MixedPairAlgebra) := htT
  let D := pi V.mixedPairModels
  let T := V.mixedPairNiltest
  obtain ⟨e, ω, hF, he, hconstruct⟩ := hstep D hr T (V.mixedPairNiltest_complexity.mono hTr)
  have hbias : Real.exp (-r) ≤ ‖𝔼 x ∈ translatedIntegerBox 0 (fun _ : Fin (n + 2) => N), T.eval x‖ := by
    have hzero : translatedIntegerBox 0 (fun _ : Fin (n + 2) => N) = integerBox (fun _ : Fin (n + 2) => N) := by
      ext x
      simp only [mem_translatedIntegerBox, mem_integerBox, Pi.zero_apply, zero_add]
    rw [hzero]
    exact (Real.exp_le_exp.mpr (neg_le_neg hqr)).trans V.mixedPairNiltest_bias
  have hf := hconstruct (piFrequency V.mixedPairFrequencies) V.mixedPairNiltest_vertical
    0 (fun _ : Fin (n + 2) => N) (fun _ => NeZero.pos N) (by simpa only [Fintype.card_fin] using hdimr)
    (fun _ => (Real.exp_le_exp.mpr hfactor).trans hN) hbias
  exact ⟨{
    topology := τ
    topologicalAdd := htA
    continuousSMul := htM
    hausdorff := htT
    basis := e
    weight := ω
    adapted := hF
    height := fun a b => (he a b).trans hheight
    factorization := NilpotentLieFiltration.ControlledSymbolFactorization.mono
      D.filtration e ω hF hf hfactor (fun _ => by exact_mod_cast NeZero.pos N) }⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedRootCyclicComparison
namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators NNReal

variable {s : ℕ} {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

noncomputable def mixedWrappedDiagonalCorrection (N : ℕ)
    (F : (Fin W.outputDim × Fin W.outputDim) →
      (MixedNonconstantCorner s → Fin W.outputDim) → (Fin 2 → ℤ) → ℂ)
    (a : Fin W.outputDim × Fin W.outputDim)
    (b : MixedNonconstantCorner s → Fin W.outputDim) (x : Fin 2 → ℤ) : ℂ :=
  ∑ k, W.mixedDiagonalWrapCoefficient N a.2 k x * F (a.1, k) b x

noncomputable def mixedCyclicDiagonalCorrection (N : ℕ) (δ : ℝ≥0)
    (F : (Fin W.outputDim × Fin W.outputDim) →
      (MixedNonconstantCorner s → Fin W.outputDim) → (Fin 2 → ℤ) → ℂ)
    (a : Fin W.outputDim × Fin W.outputDim)
    (b : MixedNonconstantCorner s → Fin W.outputDim) (x : Fin 2 → ℤ) : ℂ :=
  (1 - (smoothCyclicCarry N δ x : ℂ)) * F a b x +
    (smoothCyclicCarry N δ x : ℂ) * W.mixedWrappedDiagonalCorrection N F a b x

theorem mixedWrappedDiagonalCorrection_mean_error {N : ℕ} [NeZero N] {ε : ℝ}
    (F : (Fin W.outputDim × Fin W.outputDim) →
      (MixedNonconstantCorner s → Fin W.outputDim) → (Fin 2 → ℤ) → ℂ)
    (herr : ∀ a b, (𝔼 x : Fin 2 → ZMod N,
      ‖W.mixedDiagonalDerivative a (fun z => ((x z).val : ℤ)) *
          star (W.mixedCanonicalTensor b (fun z => ((x z).val : ℤ))) -
        F a b (fun z => ((x z).val : ℤ))‖) ≤ ε)
    (a : Fin W.outputDim × Fin W.outputDim)
    (b : MixedNonconstantCorner s → Fin W.outputDim) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.mixedWrappedDiagonalDerivative N a (fun z => ((x z).val : ℤ)) *
          star (W.mixedCanonicalTensor b (fun z => ((x z).val : ℤ))) -
        W.mixedWrappedDiagonalCorrection N F a b (fun z => ((x z).val : ℤ))‖) ≤ W.outputDim * ε := by
  have hpoint (x : Fin 2 → ℤ) :
      ‖W.mixedWrappedDiagonalDerivative N a x * star (W.mixedCanonicalTensor b x) -
        W.mixedWrappedDiagonalCorrection N F a b x‖ ≤
      ∑ k, ‖W.mixedDiagonalDerivative (a.1, k) x * star (W.mixedCanonicalTensor b x) -
        F (a.1, k) b x‖ := by
    have heq : W.mixedWrappedDiagonalDerivative N a x * star (W.mixedCanonicalTensor b x) -
        W.mixedWrappedDiagonalCorrection N F a b x =
        ∑ k, W.mixedDiagonalWrapCoefficient N a.2 k x *
          (W.mixedDiagonalDerivative (a.1, k) x * star (W.mixedCanonicalTensor b x) -
            F (a.1, k) b x) := by
      rw [W.mixedWrappedDiagonalDerivative_resolution, Finset.sum_mul]
      simp only [mixedWrappedDiagonalCorrection, mul_sub, Finset.sum_sub_distrib, mul_assoc]
    rw [heq]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro k _
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (W.mixedDiagonalWrapCoefficient_norm N a.2 k x)
  calc
    _ ≤ 𝔼 x : Fin 2 → ZMod N,
        ∑ k, ‖W.mixedDiagonalDerivative (a.1, k) (fun z => ((x z).val : ℤ)) *
            star (W.mixedCanonicalTensor b (fun z => ((x z).val : ℤ))) -
          F (a.1, k) b (fun z => ((x z).val : ℤ))‖ :=
      Finset.expect_le_expect (fun x _ => hpoint _)
    _ = ∑ k, 𝔼 x : Fin 2 → ZMod N,
        ‖W.mixedDiagonalDerivative (a.1, k) (fun z => ((x z).val : ℤ)) *
            star (W.mixedCanonicalTensor b (fun z => ((x z).val : ℤ))) -
          F (a.1, k) b (fun z => ((x z).val : ℤ))‖ := Finset.expect_sum_comm _ _ _
    _ ≤ ∑ _k : Fin W.outputDim, ε := Finset.sum_le_sum (fun k _ => herr (a.1, k) b)
    _ = _ := by simp

theorem mixedCyclicDiagonalCorrection_mean_error {N : ℕ} [NeZero N] {ε : ℝ}
    (δ : ℝ≥0) (hδ : 0 < δ)
    (F : (Fin W.outputDim × Fin W.outputDim) →
      (MixedNonconstantCorner s → Fin W.outputDim) → (Fin 2 → ℤ) → ℂ)
    (herr : ∀ a b, (𝔼 x : Fin 2 → ZMod N,
      ‖W.mixedDiagonalDerivative a (fun z => ((x z).val : ℤ)) *
          star (W.mixedCanonicalTensor b (fun z => ((x z).val : ℤ))) -
        F a b (fun z => ((x z).val : ℤ))‖) ≤ ε)
    (a : Fin W.outputDim × Fin W.outputDim)
    (b : MixedNonconstantCorner s → Fin W.outputDim) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.mixedCyclicDiagonalDerivative a x * star (W.mixedCanonicalTensor b (fun z => ((x z).val : ℤ))) -
        W.mixedCyclicDiagonalCorrection N δ F a b (fun z => ((x z).val : ℤ))‖) ≤
      (W.outputDim + 1) * ε + 12 * (δ : ℝ) + 2 / N := by
  have hpoint (x : Fin 2 → ZMod N) := norm_smoothed_branch_error
    (cyclicCarry (x 0) (x 1)) (smoothCyclicCarry N δ (fun z => ((x z).val : ℤ)))
    (circleCarryCutoff_range δ _)
    (W.mixedDiagonalDerivative a (fun z => ((x z).val : ℤ)) *
      star (W.mixedCanonicalTensor b (fun z => ((x z).val : ℤ))))
    (W.mixedWrappedDiagonalDerivative N a (fun z => ((x z).val : ℤ)) *
      star (W.mixedCanonicalTensor b (fun z => ((x z).val : ℤ))))
    (F a b (fun z => ((x z).val : ℤ)))
    (W.mixedWrappedDiagonalCorrection N F a b (fun z => ((x z).val : ℤ)))
    (by
      rw [norm_mul, norm_star]
      exact (mul_le_of_le_one_left (norm_nonneg _)
        (W.mixedDiagonalDerivative_norm a _)).trans (W.mixedCanonicalTensor_norm b _))
    (by
      rw [norm_mul, norm_star]
      exact (mul_le_of_le_one_left (norm_nonneg _)
        (W.mixedWrappedDiagonalDerivative_norm N a _)).trans (W.mixedCanonicalTensor_norm b _))
  have hm := Finset.expect_le_expect (s := Finset.univ) (fun x _ => hpoint x)
  simp only [Complex.ofReal_sub, Complex.ofReal_one, ← mul_assoc, ← add_mul,
    ← W.mixedCyclicDiagonalDerivative_branches] at hm
  simp only [Finset.expect_add_distrib, ← Finset.mul_expect] at hm
  have hi := herr a b
  have hw := W.mixedWrappedDiagonalCorrection_mean_error F herr a b
  have hc := smoothCyclicCarry_mean_error (N := N) δ hδ
  dsimp only [mixedCyclicDiagonalCorrection]
  exact hm.trans ((add_le_add (add_le_add hi hw)
    (mul_le_mul_of_nonneg_left hc (by norm_num : (0 : ℝ) ≤ 2))).trans_eq (by ring))

theorem exists_mixedCyclicDiagonalCorrection_expansion (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q e : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p) (N : ℕ)
      (δ : ℝ≥0), 0 < δ → 0 ≤ q → 0 ≤ e → (δ : ℝ)⁻¹ ≤ Real.exp e →
      ∀ F : (Fin W.outputDim × Fin W.outputDim) →
          (MixedNonconstantCorner s → Fin W.outputDim) → (Fin 2 → ℤ) → ℂ,
        (∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) q (F a b))) →
        ∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2)
          ((p + q + e + C) ^ C) (W.mixedCyclicDiagonalCorrection N δ F a b)) := by
  obtain ⟨A, _, hwrap⟩ := exists_mixedDiagonalWrapCoefficient_expansion s
  obtain ⟨B, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  let R := (X + Polynomial.C A) ^ A + X + (X + 6) ^ 2 + 13
  let T := (R + Polynomial.C B) ^ B + X + R + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C B) ^ B + T + 2)
  refine ⟨C, hC, ?_⟩
  intro p q e W N δ hδ hq he hinv F hF a b
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let v := p + q + e
  let r := (v + A) ^ A + v + (v + 6) ^ 2 + 13
  let t := (r + B) ^ B + v + r + 2
  let d := (t + B) ^ B + t
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have har : (p + A) ^ A ≤ r := by
    calc
      _ ≤ (v + A) ^ A := pow_le_pow_left₀ (by positivity) (by dsimp [v]; linarith) A
      _ ≤ r := by dsimp [r]; nlinarith [sq_nonneg (v + 6)]
  have hqr : q ≤ r := by
    have : 0 ≤ (v + A) ^ A := by positivity
    have hs : 0 ≤ (v + 6) ^ 2 := sq_nonneg _
    dsimp [r, v] at *
    linarith
  have her : raisedNiltestBudget (e + 4) ≤ r := by
    have hpow : (e + 6) ^ 2 ≤ (v + 6) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by dsimp [v]; linarith) 2
    have hA : 0 ≤ (v + A) ^ A := by positivity
    have hev : e ≤ v := by dsimp [v]; linarith
    dsimp [raisedNiltestBudget, r]
    nlinarith
  have hrt : r ≤ t := by
    have : 0 ≤ (r + B) ^ B := by positivity
    dsimp [t]
    linarith
  have hwt : (r + B) ^ B + p ≤ t := by dsimp [t, v]; linarith
  have htd : t ≤ d := le_add_of_nonneg_left (by positivity)
  have hpd : (t + B) ^ B ≤ d := le_add_of_nonneg_right ht
  have hcost : d + 2 ≤ (p + q + e + C) ^ C := by
    simpa [X, R, T, r, t, d, v, Polynomial.eval₂_pow] using hbudget v hv
  have hdim : (Fintype.card (Fin W.outputDim) : ℝ) ≤ Real.exp p := by
    simpa only [Fintype.card_fin] using W.output_bound
  have hcoeff : (∑ _k : Fin W.outputDim, ‖(1 : ℂ)‖) ≤ Real.exp p := by simpa using hdim
  have hterms (k : Fin W.outputDim) := hmul hr
    ((Classical.choice (hwrap W N a.2 k)).mono har) ((Classical.choice (hF (a.1, k) b)).mono hqr)
  have EW : NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) t
      (W.mixedWrappedDiagonalCorrection N F a b) := by
    have E := (NativeIntegerExpansion.weightedSum (fun k => Classical.choice (hterms k))
      (fun _ => (1 : ℂ)) hp hdim hcoeff).mono hwt
    change NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) t
      (fun x => ∑ k, W.mixedDiagonalWrapCoefficient N a.2 k x * F (a.1, k) b x)
    simpa only [one_mul] using E
  let w := fun x => (smoothCyclicCarry N δ x : ℂ)
  have EC := ((Classical.choice (exists_smoothCyclicCarry_expansion N δ hδ he hinv)).raiseStep
    (by omega : 1 ≤ s + 2) (by positivity : 0 ≤ e + 4)).mono (her.trans hrt)
  have E₀ := (Classical.choice (hF a b)).mono (hqr.trans (hrt.trans htd))
  have E₁ := (Classical.choice (hmul ht EC EW)).mono hpd
  have E₂ := (Classical.choice (hmul ht EC ((Classical.choice (hF a b)).mono (hqr.trans hrt)))).mono hpd
  let fs : Fin 3 → (Fin 2 → ℤ) → ℂ := ![F a b,
    (fun x => w x * W.mixedWrappedDiagonalCorrection N F a b x), (fun x => w x * F a b x)]
  have Efs (j : Fin 3) : Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) d (fs j)) := by
    fin_cases j
    · exact ⟨E₀⟩
    · exact ⟨E₁⟩
    · exact ⟨E₂⟩
  let cs : Fin 3 → ℂ := ![1, 1, -1]
  have hthree : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have E := (NativeIntegerExpansion.weightedSum (fun j => Classical.choice (Efs j)) cs
    (by norm_num : (0 : ℝ) ≤ 2) (by simpa using hthree)
    (by convert hthree using 1; norm_num [cs, Fin.sum_univ_succ])).mono hcost
  have heq : (fun x => ∑ j, cs j * fs j x) = W.mixedCyclicDiagonalCorrection N δ F a b := by
    funext x
    simp [cs, fs, Fin.sum_univ_succ, w, mixedCyclicDiagonalCorrection]
    ring
  exact ⟨heq ▸ E⟩

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators NNReal

variable {s : ℕ} {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

noncomputable def mixedRootCyclicCorrection (N : ℕ) (δ : ℝ≥0)
    (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ) :=
  W.mixedIntegrationRoot.mixedCyclicDiagonalCorrection N δ (W.mixedRootCornerCorrection G)

theorem mixedRootCyclicCorrection_mean_error {N : ℕ} [NeZero N] (δ : ℝ≥0) (hδ : 0 < δ)
    (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ) {ε : ℝ}
    (hε : 0 ≤ ε)
    (hG : ∀ π i j (x : Fin 2 → ZMod N), ‖G π i j (fun k => ((x k).val : ℤ))‖ ≤ 1)
    (herr : ∀ π i j, (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval i (mixedSampledInput π (fun k => ((x k).val : ℤ))) *
          star (W.eval j (mixedSampledInput (mixedSwapSample π) (fun k => ((x k).val : ℤ)))) -
        G π i j (fun k => ((x k).val : ℤ))‖) ≤ ε)
    (a : Fin W.mixedIntegrationRoot.outputDim × Fin W.mixedIntegrationRoot.outputDim)
    (b : MixedNonconstantCorner s → Fin W.mixedIntegrationRoot.outputDim) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.mixedIntegrationRoot.mixedCyclicDiagonalDerivative a x *
          star (W.mixedIntegrationRoot.mixedCanonicalTensor b (fun k => ((x k).val : ℤ))) -
        W.mixedRootCyclicCorrection N δ G a b (fun k => ((x k).val : ℤ))‖) ≤
      (W.mixedIntegrationRoot.outputDim + 1) *
        ((mixedRootCornerCoefficient s : ℝ) * (W.outputDim : ℝ) ^ mixedRootCornerExponent s * ε) +
          12 * (δ : ℝ) + 2 / N :=
  W.mixedIntegrationRoot.mixedCyclicDiagonalCorrection_mean_error δ hδ (W.mixedRootCornerCorrection G)
    (W.mixedRootCornerCorrection_mean_error_power G hε hG herr) a b

theorem exists_mixedRootCyclicCorrection_expansion (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q e : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p) (N : ℕ) (δ : ℝ≥0),
      0 < δ → 0 ≤ q → 0 ≤ e → (δ : ℝ)⁻¹ ≤ Real.exp e →
      (∀ (a : ReplicatedPermutation (mixedCorrelationDegree (s + 2))) k x,
        W.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree (s + 2)) a).symm j)) = W.eval k x) →
      ∀ G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ,
      (∀ π a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) q (G π a b))) →
      ∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) ((p + q + e + C) ^ C)
        (W.mixedRootCyclicCorrection N δ G a b)) := by
  obtain ⟨A, _, hroot⟩ := exists_mixedRootCornerCorrection_expansion s
  obtain ⟨B, _, hcyclic⟩ := exists_mixedCyclicDiagonalCorrection_expansion s
  let n := mixedRootTensorExponent s
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((Polynomial.C (n + 1) * (X + 1) + (X + Polynomial.C A) ^ A + X + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p q e W N δ hδ hq he hinv hsymm G hG a b
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let v := p + q + e
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hA : (p + q + A) ^ A ≤ (v + A) ^ A :=
    pow_le_pow_left₀ (by positivity) (by dsimp [v]; linarith) A
  have hbound : (tensorPowerBudget n p + (p + q + A) ^ A + e + B) ^ B ≤
      (p + q + e + C) ^ C := by
    have hh : ((n + 1 : ℝ) * (v + 1) + (v + A) ^ A + v + B) ^ B ≤ (v + C) ^ C := by
      simpa [X, Polynomial.eval₂_pow] using hbudget v hv
    apply le_trans _ hh
    apply pow_le_pow_left₀ (by unfold tensorPowerBudget; positivity)
    have hb : tensorPowerBudget n p ≤ (n + 1 : ℝ) * (v + 1) := by
      unfold tensorPowerBudget
      exact mul_le_mul_of_nonneg_left (by dsimp [v]; linarith) (by positivity)
    dsimp only [v] at *
    linarith
  obtain ⟨E⟩ := hcyclic W.mixedIntegrationRoot N δ hδ (by positivity : 0 ≤ (p + q + A) ^ A) he hinv
    (W.mixedRootCornerCorrection G) (hroot W hq hsymm G hG) a b
  exact ⟨E.mono hbound⟩

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.MajorTranslationPartnerNiltest
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial Module RationalFilteredNilmanifold
open scoped NNReal TensorProduct

noncomputable abbrev majorTranslationPartnerModel {L : Type}
    [LieRing L] [LieAlgebra ℚ L] {m t e : ℕ}
    (w : Fin m → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)]
    (D : RationalFilteredNilmanifold L t e) (htd : t ≤ d) :=
  pi (pairModels (weightedTranslationNilmanifold w d hw hwd) (D.raiseStep htd))

theorem exists_majorTranslation_partner_niltest (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {U L : Type} [Fintype U] [LieRing L] [LieAlgebra ℚ L]
      {m t e : ℕ} (w : Fin m → ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
      [Fintype (WeightedBasisIndex w d)]
      [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L t e) (htd : t ≤ d)
      (R : D.Niltest (fun _ : U => 1)) (_hd : 0 < d)
      (Ψ : PatchKernel m) (F : MvPolynomial (U ⊕ Fin m) ℝ)
      (_hF : F ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
      (A : Fin m → MvPolynomial U ℝ) (_hA : ∀ i, (A i).totalDegree ≤ w i)
      (p : ℝ), 0 ≤ p → (Fintype.card U + m : ℕ) ≤ p →
      (Ψ.lip : ℝ) ≤ Real.exp p → R.ComplexityLE p → (R.normBound : ℝ) ≤ 1 →
      let N := majorTranslationPartnerModel w d hw hwd D htd
      letI : FiniteDimensional ℚ (PairAlgebra (weightedSubalgebra w d) L) :=
        N.basis.finiteDimensional_of_finite
      letI := moduleTopology ℝ (ℝ ⊗[ℚ] PairAlgebra (weightedSubalgebra w d) L)
      letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] PairAlgebra (weightedSubalgebra w d) L) :=
        IsModuleTopology.topologicalAddGroup ℝ _
      letI : T2Space (ℝ ⊗[ℚ] PairAlgebra (weightedSubalgebra w d) L) :=
        realification_moduleTopology_t2 N.basis
      ∃ S : N.Niltest (fun _ : U => 1), S.normBound = 1 ∧ S.ComplexityLE ((p + C) ^ C) ∧
        ∀ u : U → ℤ, ∀ β : Fin m → ℤ,
          (∀ i, |eval (fun j => (u j : ℝ)) (A i) - (β i : ℝ)| ≤ 1 / 2) →
          S.eval u =
            ((Ψ.value (fun i => eval (fun j => (u j : ℝ)) (A i) - (β i : ℝ)) : ℂ) *
              (Real.fourierChar (eval (fun j => ((Sum.elim u β j : ℤ) : ℝ)) F) : ℂ)) *
                R.eval u := by
  obtain ⟨a, ha, hmajor⟩ := exists_majorTranslation_degree_reduced_niltest d
  obtain ⟨C, hC, hbudget⟩ := exists_majorTranslationPartnerBudget_bound a
  refine ⟨C, hC, ?_⟩
  intro U L _ _ _ m t e w hw hwd _ _ _ _ _ _ _ _ _ D htd R hd Ψ F hF A hA p
    hp hdim hΨ hR hcap
  let N := majorTranslationPartnerModel w d hw hwd D htd
  let : FiniteDimensional ℚ (PairAlgebra (weightedSubalgebra w d) L) :=
    N.basis.finiteDimensional_of_finite
  let := moduleTopology ℝ (ℝ ⊗[ℚ] PairAlgebra (weightedSubalgebra w d) L)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] PairAlgebra (weightedSubalgebra w d) L) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] PairAlgebra (weightedSubalgebra w d) L) :=
    realification_moduleTopology_t2 N.basis
  obtain ⟨V, hVnorm, hV, _, hVeval⟩ := hmajor w hw hwd hd Ψ F hF A hA hp hdim hΨ
  let q : ℝ := (p + a) ^ a + raisedNiltestBudget p + 2
  have hraise : 0 ≤ raisedNiltestBudget p := hp.trans (le_raisedNiltestBudget p)
  have hpow : 0 ≤ (p + a) ^ a := by positivity
  have hq : 2 ≤ q := by dsimp [q]; linarith
  have hVq : V.ComplexityLE q := hV.mono (by dsimp [q]; linarith)
  have hRq : (R.raiseStep htd).ComplexityLE q :=
    (R.raiseStep_complexity htd hp hR).mono (by dsimp [q]; linarith)
  let models := pairModels (weightedTranslationNilmanifold w d hw hwd) (D.raiseStep htd)
  let tests := pairTests (weightedTranslationNilmanifold w d hw hwd) (D.raiseStep htd)
    V (R.raiseStep htd)
  have htests : ∀ i, (tests i).ComplexityLE q :=
    pairTests_complexity _ _ V (R.raiseStep htd) hVq hRq
  have hcaps : ∀ i, (tests i).normBound ≤ 1 := by
    intro i
    cases i
    · change R.normBound ≤ 1
      exact_mod_cast hcap
    · change V.normBound ≤ 1
      exact hVnorm.le
  have hcard : (Fintype.card Bool : ℝ) ≤ q := by simpa using hq
  let S := unitBoundedPiNiltest models tests (by linarith : 0 ≤ q) hcard htests hcaps
  refine ⟨S, rfl, ?_, ?_⟩
  · exact (unitBoundedPiNiltest_complexity models tests (by linarith : 0 ≤ q)
      hcard htests hcaps).mono (hbudget p hp)
  · intro u β hβ
    change (unitBoundedPiNiltest models tests _ _ _ _).eval u = _
    rw [unitBoundedPiNiltest_eval, Fintype.prod_bool]
    change V.eval u * (R.raiseStep htd).eval u = _
    rw [hVeval u β hβ, R.raiseStep_eval]

end Erdos3.PolynomialTranslationLie

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MixedPairPolynomial
namespace OAI

section

namespace Erdos3.NativeSampleCorrelation

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

variable {n : ℕ} {p q : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p}
  {i j : Fin W.outputDim}
  (V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
    Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.mixedAntisymmetric i j (fun k => ((z k).val : ℤ))))

noncomputable def mixedPairPolynomial :
    ((pi V.mixedPairModels).filtration.realification.adaptedPolynomialFiltration
      (fun _ : Fin (n + 2) => 1)).Group :=
  let o := NilpotentLieFiltration.piRealOrbit (fun k => (V.mixedPairModels k).filtration)
    (fun k => (V.mixedPairTests k).orbit)
  ⟨⟨o.log, o.property⟩⟩

def mixedPairProjection (k : Fin 2) : V.MixedPairAlgebra →ₗ⁅ℚ⁆ W.L := liePiEval (some k)

theorem mixedPairFrequency_apply (x : V.MixedPairAlgebra) :
    piFrequency V.mixedPairFrequencies x =
      W.vertical.frequency (V.mixedPairProjection 0 x) -
        W.vertical.frequency (V.mixedPairProjection 1 x) := by
  have h (x₀ x₁ : W.L) :
      0 + (W.vertical.frequency x₀ + (-W.vertical.frequency) x₁) =
        W.vertical.frequency x₀ - W.vertical.frequency x₁ := by
    simp only [LinearMap.neg_apply]
    ring
  rw [piFrequency_apply, Fintype.sum_option, Fin.sum_univ_two]
  exact h (x (some 0)) (x (some 1))

theorem mixedPairFrequency_real (x : ℝ ⊗[ℚ] V.MixedPairAlgebra) :
    realifyFunctional (piFrequency V.mixedPairFrequencies) x =
      realifyFunctional W.vertical.frequency (realificationLieHom (V.mixedPairProjection 0) x) -
        realifyFunctional W.vertical.frequency (realificationLieHom (V.mixedPairProjection 1) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    simp only [realifyFunctional_tmul, V.mixedPairFrequency_apply,
      realificationLieHom_tmul, Rat.cast_sub, mul_sub]
  | add x y hx hy => simp only [map_add, hx, hy]; ring

variable
  [TopologicalSpace (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.MixedPairAlgebra)]

theorem mixedPairPolynomial_eq_test : V.mixedPairPolynomial =
    ⟨⟨V.mixedPairNiltest.orbit.log, V.mixedPairNiltest.orbit.property⟩⟩ := rfl

theorem mixedPairNiltest_symbol {ι : Type*}
    (b : Module.Basis ι ℚ V.MixedPairAlgebra) (w : ι → ℕ)
    (hF : ∀ k, (pi V.mixedPairModels).filtration.layer k =
      Submodule.span ℚ (b '' {a | k ≤ w a})) :
    V.mixedPairNiltest.symbol b w hF =
      (pi V.mixedPairModels).filtration.realPolynomialSymbolHom b w hF
        (fun _ : Fin (n + 2) => 1) V.mixedPairPolynomial := rfl

end Erdos3.NativeSampleCorrelation

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.OrdinaryPhasePairFunctionalBounds
namespace OAI

section

namespace Erdos3.OrdinaryPolynomialPhase

open Module _root_.MvPolynomial PolynomialTranslationLie

theorem polynomial_eq_constant (P : MvPolynomial (Fin 0) ℚ) :
    P = C (P.coeff 0) := by
  ext α
  have hα : α = 0 := Subsingleton.elim _ _
  subst α
  simp

noncomputable def constantCoefficient (s : ℕ) : weightedSubalgebra weight s →ₗ[ℚ] ℚ where
  toFun x := x.val.polynomial.coeff 0
  map_add' x y := by change (x.val.polynomial + y.val.polynomial).coeff 0 = _; simp
  map_smul' r x := by change (r • x.val.polynomial).coeff 0 = _; simp

@[simp] theorem constantCoefficient_apply (s : ℕ) (x : weightedSubalgebra weight s) :
    constantCoefficient s x = x.val.polynomial.coeff 0 := rfl

theorem constantCoefficient_injective (s : ℕ) : Function.Injective (constantCoefficient s) := by
  intro x y hxy
  apply Subtype.ext
  apply PolynomialTranslationLie.ext
  · exact Subsingleton.elim _ _
  · rw [polynomial_eq_constant x.val.polynomial, polynomial_eq_constant y.val.polynomial]
    exact congrArg C hxy

theorem constantCoefficient_eq_zero_iff (s : ℕ) (x : weightedSubalgebra weight s) :
    constantCoefficient s x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    exact constantCoefficient_injective s (hx.trans (map_zero (constantCoefficient s)).symm)
  · rintro rfl
    exact map_zero _

theorem lie_eq_zero (s : ℕ) (x y : weightedSubalgebra weight s) : ⁅x, y⁆ = 0 := by
  apply Subtype.ext
  apply PolynomialTranslationLie.ext
  · rfl
  · change scalarDirectionalDerivative x.val.base y.val.polynomial -
      scalarDirectionalDerivative y.val.base x.val.polynomial = 0
    simp [scalarDirectionalDerivative_apply]

theorem constantCoefficient_lie (s : ℕ) (x y : weightedSubalgebra weight s) :
    constantCoefficient s ⁅x, y⁆ = 0 := by
  rw [lie_eq_zero, map_zero]

section ScalarLieHom

attribute [local instance 100] LieRing.ofAssociativeRing

noncomputable def constantCoefficientLie (s : ℕ) : weightedSubalgebra weight s →ₗ⁅ℚ⁆ ℚ where
  toLinearMap := constantCoefficient s
  map_lie' {x y} := by
    change constantCoefficient s ⁅x, y⁆ = ⁅constantCoefficient s x, constantCoefficient s y⁆
    rw [constantCoefficient_lie]
    simp only [LieRing.of_associative_ring_bracket, mul_comm, sub_self]

@[simp] theorem constantCoefficientLie_apply (s : ℕ) (x : weightedSubalgebra weight s) :
    constantCoefficientLie s x = constantCoefficient s x := rfl

end ScalarLieHom

theorem mem_top (s : ℕ) (x : weightedSubalgebra weight s) :
    x ∈ (weightedFiltration weight s (weight_le s)).layer s := by
  change (∀ i, weight i < s → x.val.base i = 0) ∧
    x.val.polynomial ∈ weightedSupportDrop weight s s
  refine ⟨fun i => Fin.elim0 i, ?_⟩
  intro α _
  have hα : α = 0 := Subsingleton.elim _ _
  change Finsupp.weight weight α + s ≤ s
  simp only [hα, map_zero, zero_add, le_refl]

@[simp] theorem constantCoefficient_centralRationalElement (s : ℕ) (hs : 0 < s) (q : ℚ) :
    constantCoefficient s (centralRationalElement weight s hs q) = q := by
  change (C q : MvPolynomial (Fin 0) ℚ).coeff 0 = q
  simp

theorem eq_constantCoefficient_smul_central (s : ℕ) (hs : 0 < s)
    (x : weightedSubalgebra weight s) :
    x = constantCoefficient s x • centralRationalElement weight s hs 1 := by
  apply constantCoefficient_injective s
  rw [map_smul, constantCoefficient_centralRationalElement, smul_eq_mul, mul_one]

theorem frequency_eq_constantCoefficient (s : ℕ) (hs : 0 < s)
    (η : weightedSubalgebra weight s →ₗ[ℚ] ℚ)
    (hη : η (centralRationalElement weight s hs 1) = 1) :
    η = constantCoefficient s := by
  ext x
  conv_lhs => rw [eq_constantCoefficient_smul_central s hs x]
  rw [map_smul, hη, smul_eq_mul, mul_one]

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

theorem projection_filtered (F : NilpotentLieFiltration L s)
    (φ : L →ₗ⁅ℚ⁆ weightedSubalgebra weight s) :
    ∀ j, ∀ x ∈ F.layer j, φ x ∈ (weightedFiltration weight s (weight_le s)).layer j := by
  intro j x hx
  by_cases hj : j ≤ s
  · exact (weightedFiltration weight s (weight_le s)).antitone hj (mem_top s (φ x))
  · have hz : x ∈ F.layer (s + 1) := F.antitone (by omega) hx
    rw [F.terminal] at hz
    have hx0 : x = 0 := hz
    rw [hx0, map_zero]
    exact Submodule.zero_mem _

noncomputable def gradedProjection (F : NilpotentLieFiltration L s)
    (φ : L →ₗ⁅ℚ⁆ weightedSubalgebra weight s) :
    F.AssociatedGraded →ₗ⁅ℚ⁆ weightedSubalgebra weight s :=
  F.homogeneousGradedProjection (weightedFiltration weight s (weight_le s))
    (weightedBasis weight s weight_pos) (weightedBasisGrade weight s)
    (weightedFiltration_layer_eq_span weight s weight_pos (weight_le s))
    (weightedBasis_homogeneous_brackets weight s weight_pos) φ (projection_filtered F φ)

theorem gradedProjection_image_eq_bot
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (φ : L →ₗ⁅ℚ⁆ weightedSubalgebra weight s)
    (W : LieSubalgebra ℚ F.AssociatedGraded)
    (hW : BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω W.toSubmodule)
    (hη : ∀ x ∈ W, basisGradeProjection (F.associatedGradedBasis b ω hF) ω s x = x →
      F.gradedFrequency b ω hF ((constantCoefficient s).comp φ.toLinearMap) x = 0) :
    W.map (gradedProjection F φ) = ⊥ := by
  apply bot_unique
  intro y hy
  change y = 0
  apply (constantCoefficient_eq_zero_iff s y).mp
  exact F.homogeneousGradedProjection_top_frequency_zero
    (weightedFiltration weight s (weight_le s))
    (weightedBasis weight s weight_pos) (weightedBasisGrade weight s)
    (weightedFiltration_layer_eq_span weight s weight_pos (weight_le s))
    (weightedBasis_homogeneous_brackets weight s weight_pos) φ (projection_filtered F φ)
    b ω hF W hW (constantCoefficient s) hη hy (mem_top s y)

theorem gradedProjection_eq_zero
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (φ : L →ₗ⁅ℚ⁆ weightedSubalgebra weight s)
    (W : LieSubalgebra ℚ F.AssociatedGraded)
    (hW : BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω W.toSubmodule)
    (hη : ∀ x ∈ W, basisGradeProjection (F.associatedGradedBasis b ω hF) ω s x = x →
      F.gradedFrequency b ω hF ((constantCoefficient s).comp φ.toLinearMap) x = 0)
    (x : F.AssociatedGraded) (hx : x ∈ W) : gradedProjection F φ x = 0 := by
  have hm : gradedProjection F φ x ∈ W.map (gradedProjection F φ) := ⟨x, hx, rfl⟩
  rw [gradedProjection_image_eq_bot F b ω hF φ W hW hη] at hm
  exact (LieSubalgebra.mem_bot _).mp hm

end Erdos3.OrdinaryPolynomialPhase

end

section

namespace Erdos3.OrdinaryPolynomialPhase

open Module PolynomialTranslationLie

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s)

noncomputable def projectedScalarFunctional
    (φ : L →ₗ⁅ℚ⁆ weightedSubalgebra weight s) : F.AssociatedGraded →ₗ[ℚ] ℚ :=
  (constantCoefficient s).comp (gradedProjection F φ).toLinearMap

theorem projectedScalarFunctional_lie
    (φ : L →ₗ⁅ℚ⁆ weightedSubalgebra weight s) (x y : F.AssociatedGraded) :
    projectedScalarFunctional F φ ⁅x, y⁆ = 0 := by
  change constantCoefficient s (gradedProjection F φ ⁅x, y⁆) = 0
  rw [(gradedProjection F φ).map_lie, constantCoefficient_lie]

theorem controlledFactorization_approximation [Fintype ι]
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (φ : L →ₗ⁅ℚ⁆ weightedSubalgebra weight s) (hs : 0 < s)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (X : F.RealPolynomialSymbolGroup (fun _ : σ => 1)) (p : ℝ)
    (hp : 0 ≤ p) (hdim : (Fintype.card ι : ℝ) ≤ p)
    (hθ : ∀ i, rationalLogHeight
      (projectedScalarFunctional F φ (F.associatedGradedBasis b ω hF i)) ≤ p)
    (hfactor : F.ControlledSymbolFactorization b ω hF
      ((constantCoefficient s).comp φ.toLinearMap) T X p) :
    PolynomialRationalApproximation T (Real.exp ((p + 3) ^ 3))
      (F.scalarSymbolPolynomial b ω hF (fun _ : σ => 1) (projectedScalarFunctional F φ) X) := by
  obtain ⟨m, E, P, Q, W, v, hm, hmp, hprod, hE, hQ, _, hW, _, hη, hP⟩ := hfactor
  let H := ⌈Real.exp p⌉₊
  have hH : (H : ℝ) ≤ Real.exp (p + 1) := ceil_exp_le_exp_add_one hp
  have hθH : ∀ i, RationalHeightLE
      (projectedScalarFunctional F φ (F.associatedGradedBasis b ω hF i)) H :=
    fun i => rationalHeightLE_ceil_exp (hθ i)
  have hc : (Fintype.card ι : ℝ) ≤ Real.exp p :=
    hdim.trans (by linarith [Real.add_one_le_exp p])
  have hcube : 0 ≤ p ^ 3 := by positivity
  have hden : ((H ^ Fintype.card ι * m : ℕ) : ℝ) ≤ Real.exp ((p + 3) ^ 3) := by
    calc
      _ ≤ (Real.exp (p + 1)) ^ Fintype.card ι * Real.exp p := by
        push_cast
        gcongr
      _ = Real.exp ((Fintype.card ι : ℝ) * (p + 1) + p) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have hn := mul_le_mul_of_nonneg_right hdim (show 0 ≤ p + 1 by linarith)
        nlinarith [sq_nonneg p]
  have hslow : (Fintype.card ι : ℝ) * H * Real.exp p ≤ Real.exp ((p + 3) ^ 3) := by
    calc
      _ ≤ Real.exp p * Real.exp (p + 1) * Real.exp p := by gcongr
      _ = Real.exp (3 * p + 1) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [sq_nonneg p])
  apply F.scalarSymbolPolynomial_approximation_of_factorization b ω hF (fun _ : σ => 1)
    (projectedScalarFunctional F φ) (projectedScalarFunctional_lie F φ) hs T hT
    (Real.exp ((p + 3) ^ 3)) (Real.exp p) (Real.exp_nonneg p) hm hθH hden hslow
    E P Q X hprod hE hQ W _ hP
  intro x hx
  change constantCoefficient s (gradedProjection F φ x) = 0
  rw [gradedProjection_eq_zero F b ω hF φ W hW hη x hx, map_zero]

theorem controlledFactorization_approximation_of_normalized_frequency [Fintype ι]
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (φ : L →ₗ⁅ℚ⁆ weightedSubalgebra weight s) (hs : 0 < s)
    (η : weightedSubalgebra weight s →ₗ[ℚ] ℚ)
    (hη : η (centralRationalElement weight s hs 1) = 1)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (X : F.RealPolynomialSymbolGroup (fun _ : σ => 1)) (p : ℝ)
    (hp : 0 ≤ p) (hdim : (Fintype.card ι : ℝ) ≤ p)
    (hθ : ∀ i, rationalLogHeight
      (projectedScalarFunctional F φ (F.associatedGradedBasis b ω hF i)) ≤ p)
    (hfactor : F.ControlledSymbolFactorization b ω hF (η.comp φ.toLinearMap) T X p) :
    PolynomialRationalApproximation T (Real.exp ((p + 3) ^ 3))
      (F.scalarSymbolPolynomial b ω hF (fun _ : σ => 1) (projectedScalarFunctional F φ) X) := by
  rw [frequency_eq_constantCoefficient s hs η hη] at hfactor
  exact controlledFactorization_approximation F b ω hF φ hs T hT X p hp hdim hθ hfactor

end Erdos3.OrdinaryPolynomialPhase

end

section

namespace Erdos3.OrdinaryPolynomialPhase

open Module _root_.MvPolynomial PolynomialTranslationLie VectorPolynomial
open scoped TensorProduct

def constantBasisIndex (s : ℕ) (hs : 0 < s) : WeightedBasisIndex weight s :=
  Sum.inr ⟨0, by change Finsupp.weight weight 0 < s; simpa only [map_zero] using hs⟩

@[simp] theorem constantBasisIndex_grade (s : ℕ) (hs : 0 < s) :
    weightedBasisGrade weight s (constantBasisIndex s hs) = s := by
  simp only [constantBasisIndex, weightedBasisGrade_inr, map_zero, Nat.sub_zero]

theorem constantCoefficient_eq_basis_repr (s : ℕ) (hs : 0 < s)
    (x : weightedSubalgebra weight s) :
    constantCoefficient s x =
      (weightedBasis weight s weight_pos).repr x (constantBasisIndex s hs) := rfl

theorem realify_constantCoefficient_eq_basis_coord (s : ℕ) (hs : 0 < s) :
    realifyFunctional (constantCoefficient s) =
      ((weightedBasis weight s weight_pos).baseChange ℝ).coord (constantBasisIndex s hs) := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    simp only [realifyFunctional_tmul, Basis.coord_apply, Basis.baseChange_repr_tmul]
    rw [constantCoefficient_eq_basis_repr s hs]
    simp [Rat.smul_def, mul_comm]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem constantCoefficient_coordinate_ofCoordinates {U : Type*}
    (s : ℕ) (hs : 0 < s) [Fintype (WeightedBasisIndex weight s)]
    (P : WeightedBasisIndex weight s → MvPolynomial U ℝ) :
    coordinate (realifyFunctional (constantCoefficient s)).toAddMonoidHom
        (ofCoordinates (R := ℚ) ((weightedBasis weight s weight_pos).baseChange ℝ) P) =
      P (constantBasisIndex s hs) := by
  rw [realify_constantCoefficient_eq_basis_coord s hs, coordinate_ofCoordinates]

end Erdos3.OrdinaryPolynomialPhase

end

section

namespace Erdos3.OrdinaryPolynomialPhase

open Module PolynomialTranslationLie RationalFilteredNilmanifold

variable {L : Type} [LieRing L] [LieAlgebra ℚ L] {e : ℕ}

noncomputable def pairScalarFunctional (s : ℕ)
    (D : RationalFilteredNilmanifold L s e) :
    (pi (pairModels (nilmanifold s) D)).filtration.AssociatedGraded →ₗ[ℚ] ℚ :=
  (constantCoefficient s).comp
    (gradedProjection (pi (pairModels (nilmanifold s) D)).filtration
      (liePiEval (R := ℚ) (M := BoolLieFamily (weightedSubalgebra weight s) L) true)).toLinearMap

theorem pairScalarFunctional_basis_logHeight
    (s : ℕ) (hs : 0 < s) (D : RationalFilteredNilmanifold L s e)
    {ι : Type*} (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra weight s) L))
    (ω : ι → ℕ)
    (hF : ∀ j, (pi (pairModels (nilmanifold s) D)).filtration.layer j =
      Submodule.span ℚ (b '' {i | j ≤ ω i}))
    {p : ℝ} (hp : 0 ≤ p)
    (hb : ∀ i j, rationalLogHeight
      ((pi (pairModels (nilmanifold s) D)).basis.repr (b i) j) ≤ p) (i : ι) :
    rationalLogHeight (pairScalarFunctional s D
      ((pi (pairModels (nilmanifold s) D)).filtration.associatedGradedBasis b ω hF i)) ≤ p := by
  let := weightedBasisIndex_finite weight s weight_pos
  let : Fintype (WeightedBasisIndex weight s) := Fintype.ofFinite _
  let a : {a : Fin 0 →₀ ℕ | Finsupp.weight weight a < s} :=
    ⟨0, by change Finsupp.weight weight 0 < s; simpa only [map_zero] using hs⟩
  let N := (pi (pairModels (nilmanifold s) D)).filtration
  let φ : PairAlgebra (weightedSubalgebra weight s) L →ₗ⁅ℚ⁆ weightedSubalgebra weight s :=
    liePiEval (R := ℚ) (M := BoolLieFamily (weightedSubalgebra weight s) L) true
  change rationalLogHeight ((weightedBasis weight s weight_pos).repr
    (N.homogeneousGradedProjection (weightedFiltration weight s (weight_le s))
      (weightedBasis weight s weight_pos) (weightedBasisGrade weight s)
      (weightedFiltration_layer_eq_span weight s weight_pos (weight_le s))
      (weightedBasis_homogeneous_brackets weight s weight_pos) φ
      (projection_filtered N φ) (N.associatedGradedBasis b ω hF i)) (Sum.inr a)) ≤ p
  rw [N.homogeneousGradedProjection_basis_repr (weightedFiltration weight s (weight_le s))
    (weightedBasis weight s weight_pos) (weightedBasisGrade weight s)
    (weightedFiltration_layer_eq_span weight s weight_pos (weight_le s))
    (weightedBasis_homogeneous_brackets weight s weight_pos) φ (projection_filtered N φ)
    b ω hF i (Sum.inr a)]
  split_ifs
  · exact pairTranslationProjection_coordinate_logHeight weight s weight_pos
      (weight_le s) D (b i) (hb i) (Sum.inr a)
  · simpa [rationalLogHeight] using hp

end Erdos3.OrdinaryPolynomialPhase

end

end OAI

end


