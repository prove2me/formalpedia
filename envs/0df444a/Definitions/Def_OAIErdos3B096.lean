-- Prove2me | Definitions.Def_OAIErdos3B096
-- name    : OAIErdos3B096
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-08T14:51:58.79062+00:00
-- url     : https://prove2.me/theorems/b9cabb66-0d89-46db-9f13-44d34f29fbd3
-- title:
--   OpenAI Erdős-3 split, definitions bundle 97 of 97
-- statement:
--   Definitions bundle 97 of 97 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B095`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 97 available.
--
--   Modules: `OAI.Erdos3.CellRefinement.independentReturnScale`, `OAI.Erdos3.CellRefinement.outerMatchingScale`, `OAI.Erdos3.CellRefinement.outerMatchingScaleLoss`, `OAI.Erdos3.LocalConvolution.controlledLocalMomentScale`, `OAI.Erdos3.LocalConvolution.localMomentErrorBudget`, `OAI.Erdos3.NilpotentLieFiltration.AdaptedBinomial`, `OAI.Erdos3.NilpotentLieFiltration.AdaptedBinomial.coe_logarithm`, `OAI.Erdos3.NilpotentLieFiltration.AdaptedBinomial.logarithm`, `OAI.Erdos3.NilpotentLieFiltration.AdaptedBinomial.orbit`, `OAI.Erdos3.NilpotentLieFiltration.AdaptedBinomial.orbit_log`, `OAI.Erdos3.NilpotentLieFiltration.AdaptedBinomial.scale`, `OAI.Erdos3.NilpotentLieFiltration.AdaptedMonomial.casesOn`, `OAI.Erdos3.NilpotentLieFiltration.AdaptedMonomial.coe_logarithm`, `OAI.Erdos3.NilpotentLieFiltration.AdaptedMonomial.logarithm`, `OAI.Erdos3.NilpotentLieFiltration.AdaptedMonomial.orbit`, `OAI.Erdos3.NilpotentLieFiltration.AdaptedMonomial.orbit_log`, `OAI.Erdos3.NilpotentLieFiltration.adaptedBCHToOrbit`, `OAI.Erdos3.NilpotentLieFiltration.polynomialOrbitRealEval`, `OAI.Erdos3.NilpotentLieFiltration.polynomialOrbitRealEval_coord`, `OAI.Erdos3.NilpotentLieFiltration.polynomialOrbitRealEval_integer`, `OAI.Erdos3.NilpotentLieFiltration.realPolynomialOrbitChangeFiltration`, `OAI.Erdos3.NilpotentLieFiltration.realPolynomialOrbitChangeFiltration_eval`, `OAI.Erdos3.NilpotentLieFiltration.realPolynomialOrbitChangeFiltration_log`, `OAI.Erdos3.NilpotentLieFiltration.tensor_adapted_of_supportBox`, `OAI.Erdos3.PolynomialTranslationLie`, `OAI.Erdos3.PolynomialTranslationLie.WeightedBasisIndex`, `OAI.Erdos3.PolynomialTranslationLie.base_add`, `OAI.Erdos3.PolynomialTranslationLie.base_lie`, `OAI.Erdos3.PolynomialTranslationLie.base_smul`, `OAI.Erdos3.PolynomialTranslationLie.base_zero`, `OAI.Erdos3.PolynomialTranslationLie.constantDirection`, `OAI.Erdos3.PolynomialTranslationLie.instAddCommGroup`, `OAI.Erdos3.PolynomialTranslationLie.instBracket`, `OAI.Erdos3.PolynomialTranslationLie.instLieAlgebraRat`, `OAI.Erdos3.PolynomialTranslationLie.instLieRing`, `OAI.Erdos3.PolynomialTranslationLie.instModuleRat`, `OAI.Erdos3.PolynomialTranslationLie.mem_potentialRelationOfTopFrequency`, `OAI.Erdos3.PolynomialTranslationLie.mem_relationSpace`, `OAI.Erdos3.PolynomialTranslationLie.mem_weightedSubalgebra`, `OAI.Erdos3.PolynomialTranslationLie.polynomial_add`, `OAI.Erdos3.PolynomialTranslationLie.polynomial_lie`, `OAI.Erdos3.PolynomialTranslationLie.polynomial_smul`, `OAI.Erdos3.PolynomialTranslationLie.polynomial_zero`, `OAI.Erdos3.PolynomialTranslationLie.potentialRelationOfTopFrequency`, `OAI.Erdos3.PolynomialTranslationLie.pure_constant_zero_of_top_frequency`, `OAI.Erdos3.PolynomialTranslationLie.raw_lie_mem`, `OAI.Erdos3.PolynomialTranslationLie.realShearEmbedding`, `OAI.Erdos3.PolynomialTranslationLie.realShearEmbedding_shape`, `OAI.Erdos3.PolynomialTranslationLie.realShearEmbedding_tmul`, `OAI.Erdos3.PolynomialTranslationLie.relationSpace`, `OAI.Erdos3.PolynomialTranslationLie.shearDerivation`, `OAI.Erdos3.PolynomialTranslationLie.shearDerivationHom`, `OAI.Erdos3.PolynomialTranslationLie.shearDerivationHom_injective`, `OAI.Erdos3.PolynomialTranslationLie.shearDerivation_X_inl`, `OAI.Erdos3.PolynomialTranslationLie.shearDerivation_X_inr`, `OAI.Erdos3.PolynomialTranslationLie.shearDerivation_mem_drop`, `OAI.Erdos3.PolynomialTranslationLie.shearDerivation_pow_X_inl`, `OAI.Erdos3.PolynomialTranslationLie.shearDerivation_pow_X_inr`, `OAI.Erdos3.PolynomialTranslationLie.shearDerivation_rename`, `OAI.Erdos3.PolynomialTranslationLie.shearWeight`, `OAI.Erdos3.PolynomialTranslationLie.shearWeight_le`, `OAI.Erdos3.PolynomialTranslationLie.toProd`, `OAI.Erdos3.PolynomialTranslationLie.toProdl`, `OAI.Erdos3.PolynomialTranslationLie.topProjection`, `OAI.Erdos3.PolynomialTranslationLie.topProjection_base`, `OAI.Erdos3.PolynomialTranslationLie.topProjection_mem_of_basisGraded`, `OAI.Erdos3.PolynomialTranslationLie.topProjection_mem_top`, `OAI.Erdos3.PolynomialTranslationLie.topProjection_polynomial`, `OAI.Erdos3.PolynomialTranslationLie.topProjection_pure`, `OAI.Erdos3.PolynomialTranslationLie.weightedBasis`, `OAI.Erdos3.PolynomialTranslationLie.weightedBasisGrade`, `OAI.Erdos3.PolynomialTranslationLie.weightedBasisGrade_inl`, `OAI.Erdos3.PolynomialTranslationLie.weightedBasisGrade_inr`, `OAI.Erdos3.PolynomialTranslationLie.weightedBasisIndex_finite`, `OAI.Erdos3.PolynomialTranslationLie.weightedBasis_base_height`, `OAI.Erdos3.PolynomialTranslationLie.weightedBasis_projection_base`, `OAI.Erdos3.PolynomialTranslationLie.weightedBasis_projection_coeff`, `OAI.Erdos3.PolynomialTranslationLie.weightedBasis_projection_isWeightedHomogeneous`, `OAI.Erdos3.PolynomialTranslationLie.weightedBasis_repr_inl`, `OAI.Erdos3.PolynomialTranslationLie.weightedBasis_repr_inr`, `OAI.Erdos3.PolynomialTranslationLie.weightedBasis_top_projection_eq`, `OAI.Erdos3.PolynomialTranslationLie.weightedBasis_top_projection_polynomial`, `OAI.Erdos3.PolynomialTranslationLie.weightedBasis_top_projection_val`, `OAI.Erdos3.PolynomialTranslationLie.weightedCoordinates`, `OAI.Erdos3.PolynomialTranslationLie.weightedCoordinatesEquiv`, `OAI.Erdos3.PolynomialTranslationLie.weightedCoordinates_injective`, `OAI.Erdos3.PolynomialTranslationLie.weightedFiltration`, `OAI.Erdos3.PolynomialTranslationLie.weightedFiltration_layer_eq_span`, `OAI.Erdos3.PolynomialTranslationLie.weightedLayer`, `OAI.Erdos3.PolynomialTranslationLie.weightedLayer_antitone`, `OAI.Erdos3.PolynomialTranslationLie.weightedLayer_lie_mem`, `OAI.Erdos3.PolynomialTranslationLie.weightedLayer_terminal`, `OAI.Erdos3.PolynomialTranslationLie.weightedShearEmbedding`, `OAI.Erdos3.PolynomialTranslationLie.weightedShearEmbedding_injective`, `OAI.Erdos3.PolynomialTranslationLie.weightedShearExp_X_inl`, `OAI.Erdos3.PolynomialTranslationLie.weightedShearExp_X_inr`, `OAI.Erdos3.PolynomialTranslationLie.weightedShearGroupHom`, `OAI.Erdos3.PolynomialTranslationLie.weightedShearGroupHom_apply`, `OAI.Erdos3.PolynomialTranslationLie.weightedShearRealEmbedding_injective`, `OAI.Erdos3.PolynomialTranslationLie.weightedShearRealGroupHom`, `OAI.Erdos3.PolynomialTranslationLie.weightedShearRealGroupHom_apply`, `OAI.Erdos3.PolynomialTranslationLie.weightedShearRealGroupHom_injective`, `OAI.Erdos3.PolynomialTranslationLie.weightedShearRealGroupHom_rational`, `OAI.Erdos3.PolynomialTranslationLie.weightedSubalgebra`, `OAI.Erdos3.PolynomialTranslationLie.weightedSubalgebra_finrank_le`, `OAI.Erdos3.VectorPolynomial.exists_jointRationalSpace_generators`, `OAI.Erdos3.binomialVariable`, `OAI.Erdos3.binomialVariable_mem_supportBox`, `OAI.Erdos3.binomialVariable_zero`, `OAI.Erdos3.exists_real_kernel_generators`, `OAI.Erdos3.finsupp_weight_mono`, `OAI.Erdos3.jointSpaceGeneratorHeight`, `OAI.Erdos3.jointSpaceGeneratorHeight_le_exp`, `OAI.Erdos3.monomial_mem_polynomialSupportBox`, `OAI.Erdos3.mul_mem_polynomialSupportBox`, `OAI.Erdos3.multivariateBinomial`, `OAI.Erdos3.multivariateBinomial_mem_supportBox`, `OAI.Erdos3.multivariateBinomial_single`, `OAI.Erdos3.multivariateBinomial_zero`, `OAI.Erdos3.polynomialShearAssociativeActionOver`, `OAI.Erdos3.polynomialShearAssociativeActionOver_positive`, `OAI.Erdos3.polynomialShearAssociativeRatAction`, `OAI.Erdos3.polynomialShearBCHEquivOver`, `OAI.Erdos3.polynomialShearExpAut_lieBCH_over`, `OAI.Erdos3.polynomialShearExpOn_lieBCH_over`, `OAI.Erdos3.polynomialShearExp_map`, `OAI.Erdos3.polynomialShearMap`, `OAI.Erdos3.polynomialShearMap_X`, `OAI.Erdos3.polynomialShearMap_add`, `OAI.Erdos3.polynomialShearMap_apply_map`, `OAI.Erdos3.polynomialShearMap_basis`, `OAI.Erdos3.polynomialShearMap_comp`, `OAI.Erdos3.polynomialShearMap_lie`, `OAI.Erdos3.polynomialShearMap_monomial`, `OAI.Erdos3.polynomialShearMap_pow_apply`, `OAI.Erdos3.polynomialShearMap_smul`, `OAI.Erdos3.polynomialShearMap_sum`, `OAI.Erdos3.polynomialShearMap_zero`, `OAI.Erdos3.polynomialShearRatFiltration`, `OAI.Erdos3.polynomialShearRatLieAlgebra`, `OAI.Erdos3.polynomialShearRationalRealMap`, `OAI.Erdos3.polynomialShearRealAutEquiv`, `OAI.Erdos3.polynomialShearRealAutEquiv_apply`, `OAI.Erdos3.polynomialShearRealAutEquiv_rational`, `OAI.Erdos3.polynomialShearRealGroupEquiv`, `OAI.Erdos3.polynomialShearRealificationEquiv`, `OAI.Erdos3.polynomialShearRealificationEquiv_tmul`, `OAI.Erdos3.polynomialShearRealificationHom`, `OAI.Erdos3.polynomialShearRealificationHom_basis`, `OAI.Erdos3.polynomialShearRealificationLinearEquiv`, `OAI.Erdos3.polynomialShearRealificationMap`, `OAI.Erdos3.polynomialShearRealificationMap_eq`, `OAI.Erdos3.polynomialShearRealificationMap_tmul`, `OAI.Erdos3.polynomialShearRealificationRatHom`, `OAI.Erdos3.polynomialSupportBox`, `OAI.Erdos3.polynomial_aeval_X_mem_supportBox`, `OAI.Erdos3.prod_mem_polynomialSupportBox`, `OAI.Erdos3.scalarDirectionalDerivative_commute`, `OAI.Erdos3.scalarDirectionalDerivative_direction_add`, `OAI.Erdos3.scalarDirectionalDerivative_direction_smul`, `OAI.Erdos3.scalarDirectionalDerivative_direction_zero`, `OAI.Erdos3.scalarDirectionalDerivative_weight_drop`, `OAI.Erdos3.schmidtRadiusFactor`, `OAI.Erdos3.weightedPolynomialEndRatFiltration`, `OAI.Erdos3.weightedPolynomialEndRatLayer`, `OAI.Erdos3.weightedSupportDrop_map`, `OAI.Erdos3.weightedSupportLE_map`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B019
import Definitions.Def_OAIErdos3B020

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialShearRationalFiltration
namespace OAI

section

namespace Erdos3

variable {σ R : Type*} [CommRing R] [Algebra ℚ R] (w : σ → ℕ)

noncomputable instance (priority := 100) polynomialShearRatLieAlgebra :
    LieAlgebra ℚ (PolynomialShearLieAlgebra w R) where
  lie_smul c D E := by
    rw [← IsScalarTower.algebraMap_smul R c E, lie_smul, IsScalarTower.algebraMap_smul]

noncomputable def polynomialShearRatFiltration (s : ℕ) (hw : ∀ i, w i ≤ s) :
    NilpotentLieFiltration (PolynomialShearLieAlgebra w R) s where
  layer i := (polynomialShearLayer (R := R) w i).restrictScalars ℚ
  antitone := polynomialShearLayer_antitone w
  one_eq_top := by rw [polynomialShearLayer_one]; rfl
  lie_mem := polynomialShearLayer_bracket w _ _
  terminal := by rw [polynomialShearLayer_terminal w s hw]; rfl

noncomputable def weightedPolynomialEndRatLayer (s k : ℕ) :
    Submodule ℚ (weightedPolynomialEndAlgebra (R := R) w s) :=
  ((weightedPolynomialEndDrop w s k).comap
    (weightedPolynomialEndAlgebra (R := R) w s).val.toLinearMap).restrictScalars ℚ

noncomputable def weightedPolynomialEndRatFiltration (s : ℕ) :
    NilpotentAlgebraFiltration (weightedPolynomialEndAlgebra (R := R) w s) s where
  layer := weightedPolynomialEndRatLayer w s
  antitone := by
    intro a b hab F hF
    exact weightedPolynomialEndDrop_antitone w s hab hF
  zero_eq_top := by
    apply top_unique
    intro F hF
    exact F.property
  mul_mem := by
    intro a b F G hF hG
    exact weightedPolynomialEndDrop_mul w s a b hF hG
  terminal := by
    apply bot_unique
    intro F hF
    change F = 0
    exact Subtype.ext (weightedPolynomialEndDrop_terminal w s hF)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.PolynomialShearBCHOver
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
attribute [local instance 100] LieRing.ofAssociativeRing

variable {σ R : Type*} [CommRing R] [Algebra ℚ R]

noncomputable def polynomialShearAssociativeActionOver (w : σ → ℕ) (s : ℕ) :
    PolynomialShearLieAlgebra w R →ₗ⁅R⁆ weightedPolynomialEndAlgebra (R := R) w s where
  toLinearMap :=
    { toFun := fun D => ⟨polynomialShearEnd D s,
        weightedPolynomialEndDrop_antitone w s (Nat.zero_le 1)
          (polynomialShearEnd_mem_drop w s 1 D.property)⟩
      map_add' := by
        intro D E
        apply Subtype.ext
        exact (polynomialShearAction w s).map_add D E
      map_smul' := by
        intro c D
        apply Subtype.ext
        exact (polynomialShearAction w s).map_smul c D }
  map_lie' := by
    intro D E
    apply Subtype.ext
    exact (polynomialShearAction w s).map_lie D E

noncomputable def polynomialShearAssociativeRatAction (w : σ → ℕ) (s : ℕ) :
    PolynomialShearLieAlgebra w R →ₗ⁅ℚ⁆ weightedPolynomialEndAlgebra (R := R) w s where
  toLinearMap := (polynomialShearAssociativeActionOver (R := R) w s).toLinearMap.restrictScalars ℚ
  map_lie' := by
    intro D E
    exact (polynomialShearAssociativeActionOver (R := R) w s).map_lie D E

theorem polynomialShearAssociativeActionOver_positive (w : σ → ℕ) (s : ℕ)
    (D : PolynomialShearLieAlgebra w R) :
    polynomialShearAssociativeRatAction (R := R) w s D ∈ (weightedPolynomialEndRatFiltration (R := R) w s).layer 1 :=
  polynomialShearEnd_mem_drop w s 1 D.property

theorem polynomialShearExpOn_lieBCH_over (w : σ → ℕ) (s : ℕ)
    (D E : PolynomialShearLieAlgebra w R) :
    polynomialShearExpOn (lieBCH s D E) s = polynomialShearExpOn D s * polynomialShearExpOn E s := by
  let F := weightedPolynomialEndRatFiltration (R := R) w s
  let φ := polynomialShearAssociativeRatAction (R := R) w s
  have hp (A : PolynomialShearLieAlgebra w R) : φ A ∈ F.layer 1 :=
    polynomialShearAssociativeActionOver_positive w s A
  have hnil (A : PolynomialShearLieAlgebra w R) : IsNilpotent (φ A) :=
    F.isNilpotent_of_mem le_rfl (hp A)
  have he : IsNilpotent.exp (φ (lieBCH s D E)) = IsNilpotent.exp (φ D) * IsNilpotent.exp (φ E) := by
    rw [map_lieBCH, F.lieBCH_eq (hp D) (hp E)]
    exact exp_nilpotentBCH (F.layerAlgebra 1) F.positive_nilpotent (hp D) (hp E)
  have hv := congrArg (weightedPolynomialEndAlgebra (R := R) w s).val he
  rw [map_mul, IsNilpotent.map_exp (hnil (lieBCH s D E)),
    IsNilpotent.map_exp (hnil D), IsNilpotent.map_exp (hnil E)] at hv
  exact hv

theorem polynomialShearExpAut_lieBCH_over (w : σ → ℕ) (s : ℕ) (hw : ∀ i, w i ≤ s)
    (D E : PolynomialShearLieAlgebra w R) :
    polynomialShearExpAut (lieBCH s D E) = polynomialShearExpAut D * polynomialShearExpAut E := by
  apply WeightedLoweringAut.degreeActionHom_injective s hw
  apply LinearEquiv.toLinearMap_injective
  change ((polynomialShearExpAut (lieBCH s D E)).degreeAction s).toLinearMap =
    ((polynomialShearExpAut D).degreeAction s).toLinearMap *
      ((polynomialShearExpAut E).degreeAction s).toLinearMap
  rw [polynomialShearExp_degreeAction, polynomialShearExp_degreeAction,
    polynomialShearExp_degreeAction]
  exact polynomialShearExpOn_lieBCH_over w s D E

noncomputable def polynomialShearBCHEquivOver (w : σ → ℕ) (s : ℕ) (hw : ∀ i, w i ≤ s) :
    (polynomialShearRatFiltration (R := R) w s hw).Group ≃* WeightedLoweringAut w R where
  toFun A := polynomialShearExpAut A.coord
  invFun e := ⟨polynomialShearLog e⟩
  left_inv A := NilpotentLieBCHGroup.ext (polynomialShearLog_exp A.coord)
  right_inv := polynomialShearExp_log
  map_mul' A B := polynomialShearExpAut_lieBCH_over w s hw A.coord B.coord

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialShearRealGroup
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ R S : Type*} [CommRing R] [CommRing S] {w : σ → ℕ}

theorem weightedSupportDrop_map (f : R →+* S) {P : MvPolynomial σ R} {n r : ℕ}
    (hP : P ∈ weightedSupportDrop w n r) : map f P ∈ weightedSupportDrop w n r := by
  intro a ha
  exact hP (MvPolynomial.support_map_subset f P ha)

noncomputable def polynomialShearMap (f : R →+* S) (D : PolynomialShearLieAlgebra w R) :
    PolynomialShearLieAlgebra w S :=
  ⟨MvPolynomial.mkDerivation S (fun i => map f (D.val (X i))), fun i => by
    rw [MvPolynomial.mkDerivation_X]
    exact weightedSupportDrop_map f (D.property i)⟩

theorem polynomialShearMap_X (f : R →+* S) (D : PolynomialShearLieAlgebra w R) (i : σ) :
    (polynomialShearMap f D).val (X i) = map f (D.val (X i)) :=
  MvPolynomial.mkDerivation_X _ _ _

theorem polynomialShearMap_apply_map (f : R →+* S) (D : PolynomialShearLieAlgebra w R)
    (P : MvPolynomial σ R) :
    (polynomialShearMap f D).val (map f P) = map f (D.val P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp only [map_C, MvPolynomial.derivation_C, map_zero]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
    simp only [map_mul, map_X, Derivation.leibniz, smul_eq_mul, map_add,
      polynomialShearMap_X, hP]

theorem polynomialShearMap_add (f : R →+* S) (D E : PolynomialShearLieAlgebra w R) :
    polynomialShearMap f (D + E) = polynomialShearMap f D + polynomialShearMap f E := by
  apply Subtype.ext
  apply MvPolynomial.derivation_ext
  intro i
  rw [polynomialShearMap_X]
  change map f (D.val (X i) + E.val (X i)) =
    (polynomialShearMap f D).val (X i) + (polynomialShearMap f E).val (X i)
  rw [map_add, polynomialShearMap_X, polynomialShearMap_X]

theorem polynomialShearMap_smul (f : R →+* S) (c : R) (D : PolynomialShearLieAlgebra w R) :
    polynomialShearMap f (c • D) = f c • polynomialShearMap f D := by
  apply Subtype.ext
  apply MvPolynomial.derivation_ext
  intro i
  rw [polynomialShearMap_X]
  change map f (c • D.val (X i)) = f c • (polynomialShearMap f D).val (X i)
  rw [polynomialShearMap_X, ← MvPolynomial.C_mul', ← MvPolynomial.C_mul', map_mul, map_C]

theorem polynomialShearMap_lie (f : R →+* S) (D E : PolynomialShearLieAlgebra w R) :
    polynomialShearMap f ⁅D, E⁆ = ⁅polynomialShearMap f D, polynomialShearMap f E⁆ := by
  apply Subtype.ext
  apply MvPolynomial.derivation_ext
  intro i
  rw [polynomialShearMap_X]
  change map f (D.val (E.val (X i)) - E.val (D.val (X i))) =
    (polynomialShearMap f D).val ((polynomialShearMap f E).val (X i)) -
      (polynomialShearMap f E).val ((polynomialShearMap f D).val (X i))
  rw [map_sub, polynomialShearMap_X, polynomialShearMap_X,
    polynomialShearMap_apply_map, polynomialShearMap_apply_map]

theorem polynomialShearMap_monomial (f : R →+* S) (a : PolynomialShearIndex w) :
    polynomialShearMap f (polynomialShearMonomial w a) = polynomialShearMonomial w a := by
  classical
  apply Subtype.ext
  apply MvPolynomial.derivation_ext
  intro i
  rw [polynomialShearMap_X, polynomialShearMonomial_X, polynomialShearMonomial_X]
  split_ifs <;> simp

theorem polynomialShearMap_basis [Fintype σ] (f : R →+* S) (a : PolynomialShearIndex w) :
    polynomialShearMap f (polynomialShearBasis (R := R) w a) =
      polynomialShearBasis (R := S) w a := by
  rw [polynomialShearBasis_eq_monomial, polynomialShearBasis_eq_monomial,
    polynomialShearMap_monomial]

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {R S T I : Type*} [CommRing R] [CommRing S] [CommRing T] {w : I → ℕ}

theorem polynomialShearMap_zero (f : R →+* S) :
    polynomialShearMap (w := w) f 0 = 0 := by
  apply Subtype.ext
  apply MvPolynomial.derivation_ext
  intro i
  simp only [polynomialShearMap_X]
  exact map_zero _

theorem polynomialShearMap_sum {κ : Type*} (f : R →+* S)
    (t : Finset κ) (D : κ → PolynomialShearLieAlgebra w R) :
    polynomialShearMap f (∑ k ∈ t, D k) = ∑ k ∈ t, polynomialShearMap f (D k) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, polynomialShearMap_zero]
  | @insert k t hk ih =>
    simp only [Finset.sum_insert hk, polynomialShearMap_add, ih]

theorem polynomialShearMap_comp (f : R →+* S) (g : S →+* T)
    (D : PolynomialShearLieAlgebra w R) :
    polynomialShearMap g (polynomialShearMap f D) = polynomialShearMap (g.comp f) D := by
  apply Subtype.ext
  apply MvPolynomial.derivation_ext
  intro i
  simp only [polynomialShearMap_X, MvPolynomial.map_map]

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {σ : Type*} (w : σ → ℕ)

noncomputable def polynomialShearRationalRealMap :
    PolynomialShearLieAlgebra w ℚ →ₗ[ℚ] PolynomialShearLieAlgebra w ℝ where
  toFun := polynomialShearMap (algebraMap ℚ ℝ)
  map_add' := polynomialShearMap_add _
  map_smul' c D := by
    rw [polynomialShearMap_smul]
    exact IsScalarTower.algebraMap_smul ℝ c _

noncomputable def polynomialShearRealificationMap :
    (ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ) →ₗ[ℝ] PolynomialShearLieAlgebra w ℝ :=
  TensorProduct.AlgebraTensorModule.lift
    (LinearMap.toSpanSingleton ℝ _ (polynomialShearRationalRealMap w))

theorem polynomialShearRealificationMap_tmul (r : ℝ) (D : PolynomialShearLieAlgebra w ℚ) :
    polynomialShearRealificationMap w (r ⊗ₜ[ℚ] D) =
      r • polynomialShearMap (algebraMap ℚ ℝ) D := rfl

noncomputable def polynomialShearRealificationHom :
    (ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ) →ₗ⁅ℝ⁆ PolynomialShearLieAlgebra w ℝ where
  toLinearMap := polynomialShearRealificationMap w
  map_lie' := by
    intro x y
    change polynomialShearRealificationMap w ⁅x, y⁆ =
      ⁅polynomialShearRealificationMap w x, polynomialShearRealificationMap w y⁆
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r D =>
      induction y using TensorProduct.induction_on with
      | zero =>
        refine (congrArg _ (lie_zero (L := ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ)
          (M := ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ) _)).trans ?_
        first | (simp; done) | (rw [map_zero]; exact (lie_zero (L := PolynomialShearLieAlgebra w ℝ)
          (M := PolynomialShearLieAlgebra w ℝ) _).symm)
      | tmul t E =>
        simp only [LieAlgebra.ExtendScalars.bracket_tmul, polynomialShearRealificationMap_tmul,
          polynomialShearMap_lie, smul_lie, lie_smul, smul_smul, mul_comm]
      | add y z hy hz => simp only [LieRing.lie_add, map_add, hy, hz]
    | add x z hx hz => simp only [LieRing.add_lie, map_add, hx, hz]

variable [Fintype σ]

theorem polynomialShearRealificationHom_basis (a : PolynomialShearIndex w) :
    polynomialShearRealificationHom w ((polynomialShearBasis (R := ℚ) w).baseChange ℝ a) =
      polynomialShearBasis (R := ℝ) w a := by
  change polynomialShearRealificationMap w ((polynomialShearBasis (R := ℚ) w).baseChange ℝ a) = _
  rw [Basis.baseChange_apply, polynomialShearRealificationMap_tmul, polynomialShearMap_basis, one_smul]

noncomputable def polynomialShearRealificationLinearEquiv :
    (ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ) ≃ₗ[ℝ] PolynomialShearLieAlgebra w ℝ :=
  ((polynomialShearBasis (R := ℚ) w).baseChange ℝ).repr.trans
    (polynomialShearBasis (R := ℝ) w).repr.symm

theorem polynomialShearRealificationMap_eq :
    (polynomialShearRealificationHom w).toLinearMap =
      (polynomialShearRealificationLinearEquiv w).toLinearMap := by
  apply ((polynomialShearBasis (R := ℚ) w).baseChange ℝ).ext
  intro a
  change polynomialShearRealificationHom w ((polynomialShearBasis (R := ℚ) w).baseChange ℝ a) = _
  rw [polynomialShearRealificationHom_basis]
  change polynomialShearBasis (R := ℝ) w a =
    (polynomialShearBasis (R := ℝ) w).repr.symm
      (((polynomialShearBasis (R := ℚ) w).baseChange ℝ).repr
        (((polynomialShearBasis (R := ℚ) w).baseChange ℝ) a))
  apply (polynomialShearBasis (R := ℝ) w).repr.injective
  rw [LinearEquiv.apply_symm_apply, Basis.repr_self, Basis.repr_self]

noncomputable def polynomialShearRealificationEquiv :
    (ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ) ≃ₗ⁅ℝ⁆ PolynomialShearLieAlgebra w ℝ :=
  LieEquiv.ofBijective (polynomialShearRealificationHom w) (by
    change Function.Bijective (polynomialShearRealificationHom w).toLinearMap
    rw [polynomialShearRealificationMap_eq]
    exact (polynomialShearRealificationLinearEquiv w).bijective)

theorem polynomialShearRealificationEquiv_tmul (r : ℝ) (D : PolynomialShearLieAlgebra w ℚ) :
    polynomialShearRealificationEquiv w (r ⊗ₜ[ℚ] D) =
      r • polynomialShearMap (algebraMap ℚ ℝ) D := rfl

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ R S : Type*} [CommRing R] [CommRing S] {w : σ → ℕ}

theorem weightedSupportLE_map (f : R →+* S) {P : MvPolynomial σ R} {n : ℕ}
    (hP : P ∈ weightedSupportLE w n) : map f P ∈ weightedSupportLE w n := by
  intro a ha
  exact hP (MvPolynomial.support_map_subset f P ha)

theorem polynomialShearMap_pow_apply (f : R →+* S) (D : PolynomialShearLieAlgebra w R)
    (k : ℕ) (P : MvPolynomial σ R) :
    ((polynomialShearMap f D).val.toLinearMap ^ k) (map f P) =
      map f ((D.val.toLinearMap ^ k) P) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih, pow_succ', Module.End.mul_apply]
    exact polynomialShearMap_apply_map f D _

variable [Algebra ℚ R] [Algebra ℚ S]

theorem polynomialShearExp_map (f : R →+* S) (D : PolynomialShearLieAlgebra w R)
    (P : MvPolynomial σ R) :
    map f (polynomialShearExp D P) = polynomialShearExp (polynomialShearMap f D) (map f P) := by
  have hp : P ∈ weightedSupportLE w (P.weightedTotalDegree w) :=
    (mem_weightedSupportLE_iff w _ P).mpr le_rfl
  rw [polynomialShearExp_eq_sum D hp,
    polynomialShearExp_eq_sum (polynomialShearMap f D) (weightedSupportLE_map f hp), map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [map_rat_smul, polynomialShearMap_pow_apply]

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped TensorProduct

variable {σ : Type*} [Fintype σ] (w : σ → ℕ)

noncomputable def polynomialShearRealificationRatHom :
    (ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ) →ₗ⁅ℚ⁆ PolynomialShearLieAlgebra w ℝ where
  toLinearMap := (polynomialShearRealificationEquiv w).toLinearEquiv.toLinearMap.restrictScalars ℚ
  map_lie' := by
    intro D E
    exact (polynomialShearRealificationEquiv w).map_lie D E

noncomputable def polynomialShearRealGroupEquiv (s : ℕ) (hw : ∀ i, w i ≤ s) :
    (polynomialShearFiltration w s hw).realification.Group ≃*
      (polynomialShearRatFiltration (R := ℝ) w s hw).Group where
  toFun g := ⟨polynomialShearRealificationEquiv w g.coord⟩
  invFun g := ⟨(polynomialShearRealificationEquiv w).symm g.coord⟩
  left_inv g := NilpotentLieBCHGroup.ext ((polynomialShearRealificationEquiv w).symm_apply_apply g.coord)
  right_inv g := NilpotentLieBCHGroup.ext ((polynomialShearRealificationEquiv w).apply_symm_apply g.coord)
  map_mul' g h :=
    NilpotentLieBCHGroup.ext (map_lieBCH (polynomialShearRealificationRatHom w) s g.coord h.coord)

noncomputable def polynomialShearRealAutEquiv (s : ℕ) (hw : ∀ i, w i ≤ s) :
    (polynomialShearFiltration w s hw).realification.Group ≃* WeightedLoweringAut w ℝ :=
  (polynomialShearRealGroupEquiv w s hw).trans (polynomialShearBCHEquivOver w s hw)

theorem polynomialShearRealAutEquiv_apply (s : ℕ) (hw : ∀ i, w i ≤ s)
    (g : (polynomialShearFiltration w s hw).realification.Group) :
    polynomialShearRealAutEquiv w s hw g =
      polynomialShearExpAut (polynomialShearRealificationEquiv w g.coord) := rfl

theorem polynomialShearRealAutEquiv_rational (s : ℕ) (hw : ∀ i, w i ≤ s)
    (g : (polynomialShearFiltration w s hw).Group) (P : MvPolynomial σ ℚ) :
    (polynomialShearRealAutEquiv w s hw (NilpotentLieBCHGroup.realificationHom g)).val
        (MvPolynomial.map (algebraMap ℚ ℝ) P) =
      MvPolynomial.map (algebraMap ℚ ℝ) ((polynomialShearBCHEquiv w s hw g).val P) := by
  change polynomialShearExp (polynomialShearRealificationEquiv w ((1 : ℝ) ⊗ₜ[ℚ] g.coord))
      (MvPolynomial.map (algebraMap ℚ ℝ) P) =
    MvPolynomial.map (algebraMap ℚ ℝ) (polynomialShearExp g.coord P)
  rw [polynomialShearRealificationEquiv_tmul, one_smul]
  exact (polynomialShearExp_map (algebraMap ℚ ℝ) g.coord P).symm

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedTranslationShearExponential
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {σ : Type*} [Fintype σ]

theorem scalarDirectionalDerivative_direction_add (x z : σ → ℚ) (P : MvPolynomial σ ℚ) :
    scalarDirectionalDerivative (x + z) P =
      scalarDirectionalDerivative x P + scalarDirectionalDerivative z P := by
  simp only [scalarDirectionalDerivative_apply, Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem scalarDirectionalDerivative_direction_smul (r : ℚ) (x : σ → ℚ)
    (P : MvPolynomial σ ℚ) :
    scalarDirectionalDerivative (r • x) P = r • scalarDirectionalDerivative x P := by
  simp only [scalarDirectionalDerivative_apply, Pi.smul_apply, smul_eq_mul, smul_smul, Finset.smul_sum]

theorem scalarDirectionalDerivative_direction_zero (P : MvPolynomial σ ℚ) :
    scalarDirectionalDerivative (0 : σ → ℚ) P = 0 := by
  simp [scalarDirectionalDerivative_apply]

theorem scalarDirectionalDerivative_commute (x z : σ → ℚ) (P : MvPolynomial σ ℚ) :
    scalarDirectionalDerivative x (scalarDirectionalDerivative z P) =
      scalarDirectionalDerivative z (scalarDirectionalDerivative x P) := by
  have h : ⁅scalarDirectionalDerivative x, scalarDirectionalDerivative z⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro i
    simp only [Derivation.commutator_apply, scalarDirectionalDerivative_X,
      scalarDirectionalDerivative_C, sub_self, Derivation.zero_apply]
  have hh := congrArg (fun D : Derivation ℚ (MvPolynomial σ ℚ) (MvPolynomial σ ℚ) => D P) h
  exact sub_eq_zero.mp hh

@[ext] structure PolynomialTranslationLie (σ : Type*) where
  base : σ → ℚ
  polynomial : MvPolynomial σ ℚ

namespace PolynomialTranslationLie

noncomputable def toProd : PolynomialTranslationLie σ ≃ (σ → ℚ) × MvPolynomial σ ℚ where
  toFun x := (x.base, x.polynomial)
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance : AddCommGroup (PolynomialTranslationLie σ) := toProd.addCommGroup
noncomputable instance : Module ℚ (PolynomialTranslationLie σ) :=
  { toProd with map_add' _ _ := rfl : PolynomialTranslationLie σ ≃+ (σ → ℚ) × MvPolynomial σ ℚ }.module ℚ

noncomputable def toProdl : PolynomialTranslationLie σ ≃ₗ[ℚ] (σ → ℚ) × MvPolynomial σ ℚ :=
  { toProd with map_add' _ _ := rfl, map_smul' _ _ := rfl }

omit [Fintype σ] in
@[simp] theorem base_zero : (0 : PolynomialTranslationLie σ).base = 0 := rfl
omit [Fintype σ] in
@[simp] theorem polynomial_zero : (0 : PolynomialTranslationLie σ).polynomial = 0 := rfl
omit [Fintype σ] in
@[simp] theorem base_add (x y : PolynomialTranslationLie σ) : (x+y).base = x.base+y.base := rfl
omit [Fintype σ] in
@[simp] theorem polynomial_add (x y : PolynomialTranslationLie σ) : (x+y).polynomial = x.polynomial+y.polynomial := rfl
omit [Fintype σ] in
@[simp] theorem base_smul (r : ℚ) (x : PolynomialTranslationLie σ) : (r • x).base = r • x.base := rfl
omit [Fintype σ] in
@[simp] theorem polynomial_smul (r : ℚ) (x : PolynomialTranslationLie σ) : (r • x).polynomial = r • x.polynomial := rfl

noncomputable instance : Bracket (PolynomialTranslationLie σ) (PolynomialTranslationLie σ) where
  bracket x y := ⟨0, scalarDirectionalDerivative x.base y.polynomial -
    scalarDirectionalDerivative y.base x.polynomial⟩

@[simp] theorem base_lie (x y : PolynomialTranslationLie σ) : ⁅x,y⁆.base = 0 := rfl
@[simp] theorem polynomial_lie (x y : PolynomialTranslationLie σ) : ⁅x,y⁆.polynomial =
    scalarDirectionalDerivative x.base y.polynomial - scalarDirectionalDerivative y.base x.polynomial := rfl

noncomputable instance : LieRing (PolynomialTranslationLie σ) where
  add_lie x y z := by
    ext <;> simp [scalarDirectionalDerivative_direction_add]; abel
  lie_add x y z := by
    ext <;> simp [scalarDirectionalDerivative_direction_add]; abel
  lie_self x := by ext <;> simp
  leibniz_lie x y z := by
    ext
    · simp
    · simp only [polynomial_lie, base_lie, polynomial_add, map_sub,
        scalarDirectionalDerivative_direction_zero, sub_zero, zero_sub]
      rw [scalarDirectionalDerivative_commute x.base y.base,
        scalarDirectionalDerivative_commute x.base z.base,
        scalarDirectionalDerivative_commute y.base z.base]
      abel_nf

noncomputable instance : LieAlgebra ℚ (PolynomialTranslationLie σ) where
  lie_smul r x y := by
    ext <;> simp [scalarDirectionalDerivative_direction_smul, smul_sub]

end PolynomialTranslationLie
end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ : Type*} [Fintype σ]

theorem scalarDirectionalDerivative_weight_drop (w : σ → ℕ) (x : σ → ℚ) (k : ℕ)
    (hx : ∀ i, w i < k → x i = 0) {n r : ℕ} {P : MvPolynomial σ ℚ}
    (hP : P ∈ weightedSupportDrop w n r) :
    scalarDirectionalDerivative x P ∈ weightedSupportDrop w n (r + k) := by
  apply weightedDerivation_apply w (scalarDirectionalDerivative x) k _ hP
  intro i
  rw [scalarDirectionalDerivative_X]
  by_cases hi : k ≤ w i
  · exact (monomial_mem_restrictSupport ℚ).mpr (Or.inl (by simpa using hi))
  · rw [hx i (by omega), map_zero]
    exact Submodule.zero_mem _

namespace PolynomialTranslationLie

noncomputable def weightedLayer (w : σ → ℕ) (d k : ℕ) : Submodule ℚ (PolynomialTranslationLie σ) where
  carrier := {x | (∀ i, w i < k → x.base i = 0) ∧
    x.polynomial ∈ weightedSupportDrop w d k}
  zero_mem' := ⟨by simp, Submodule.zero_mem _⟩
  add_mem' := by
    intro x y hx hy
    exact ⟨fun i hi => by simp [hx.1 i hi, hy.1 i hi],
      Submodule.add_mem _ hx.2 hy.2⟩
  smul_mem' := by
    intro r x hx
    exact ⟨fun i hi => by simp [hx.1 i hi], Submodule.smul_mem _ r hx.2⟩

omit [Fintype σ] in
theorem weightedLayer_antitone (w : σ → ℕ) (d : ℕ) : Antitone (weightedLayer w d) := by
  intro i j hij x hx
  exact ⟨fun a ha => hx.1 a (ha.trans_le hij), weightedSupportDrop_antitone hij hx.2⟩

theorem weightedLayer_lie_mem (w : σ → ℕ) (d : ℕ) {i j : ℕ}
    {x y : PolynomialTranslationLie σ} (hx : x ∈ weightedLayer w d i)
    (hy : y ∈ weightedLayer w d j) : ⁅x,y⁆ ∈ weightedLayer w d (i+j) := by
  refine ⟨by simp, ?_⟩
  change scalarDirectionalDerivative x.base y.polynomial -
    scalarDirectionalDerivative y.base x.polynomial ∈ _
  apply Submodule.sub_mem
  · simpa only [Nat.add_comm j i] using scalarDirectionalDerivative_weight_drop w x.base i hx.1 hy.2
  · exact scalarDirectionalDerivative_weight_drop w y.base j hy.1 hx.2

omit [Fintype σ] in
theorem weightedLayer_terminal (w : σ → ℕ) (d : ℕ) (hw : ∀ i, w i ≤ d) :
    weightedLayer w d (d+1) = ⊥ := by
  apply bot_unique
  intro x hx
  change x = 0
  apply PolynomialTranslationLie.ext
  · funext i
    exact hx.1 i (Nat.lt_succ_of_le (hw i))
  · exact weightedSupportDrop_eq_zero (Nat.lt_succ_self d) hx.2

noncomputable def weightedSubalgebra (w : σ → ℕ) (d : ℕ) : LieSubalgebra ℚ (PolynomialTranslationLie σ) :=
  { weightedLayer w d 1 with
    lie_mem' := fun hx hy => weightedLayer_antitone w d (by omega : 1 ≤ 1+1)
      (weightedLayer_lie_mem w d hx hy) }

@[simp] theorem mem_weightedSubalgebra (w : σ → ℕ) (d : ℕ) (x : PolynomialTranslationLie σ) :
    x ∈ weightedSubalgebra w d ↔ x ∈ weightedLayer w d 1 := Iff.rfl

noncomputable def weightedFiltration (w : σ → ℕ) (d : ℕ) (hw : ∀ i, w i ≤ d) :
    NilpotentLieFiltration (weightedSubalgebra w d) d where
  layer k := (weightedLayer w d k).comap (weightedSubalgebra w d).subtype
  antitone := fun i j hij x hx => weightedLayer_antitone w d hij hx
  one_eq_top := by
    apply top_unique
    intro x _
    exact x.property
  lie_mem := fun hx hy => weightedLayer_lie_mem w d hx hy
  terminal := by
    rw [weightedLayer_terminal w d hw]
    exact LinearMap.ker_eq_bot.mpr (weightedSubalgebra w d).subtype_injective

noncomputable def weightedCoordinates (w : σ → ℕ) (d : ℕ) :
    weightedSubalgebra w d →ₗ[ℚ] (σ → ℚ) × weightedSupportLE (R := ℚ) w d where
  toFun x := (x.val.base, ⟨x.val.polynomial, weightedSupportDrop_le x.property.2⟩)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem weightedCoordinates_injective (w : σ → ℕ) (d : ℕ) :
    Function.Injective (weightedCoordinates w d) := by
  intro x y h
  apply Subtype.ext
  apply PolynomialTranslationLie.ext
  · exact congrArg Prod.fst h
  · exact congrArg (fun z => (z.2 : MvPolynomial σ ℚ)) h

theorem weightedSubalgebra_finrank_le (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) :
    Module.finrank ℚ (weightedSubalgebra w d) ≤
      Fintype.card σ + (Fintype.card σ + 1)^d := by
  let := weightedSupportLE_moduleFinite (R := ℚ) w hw d
  have h := LinearMap.finrank_le_finrank_of_injective (weightedCoordinates_injective w d)
  calc
    Module.finrank ℚ (weightedSubalgebra w d) ≤
      Module.finrank ℚ ((σ → ℚ) × weightedSupportLE (R := ℚ) w d) := h
    _ = Fintype.card σ + Module.finrank ℚ (weightedSupportLE (R := ℚ) w d) := by
      rw [Module.finrank_prod, Module.finrank_pi_fintype]
      simp
    _ ≤ _ := Nat.add_le_add_left (weightedSupportLE_finrank_le w hw d) _

end PolynomialTranslationLie
end Erdos3

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial

variable {σ : Type*} [Fintype σ]

def shearWeight (w : σ → ℕ) (d : ℕ) : σ ⊕ Unit → ℕ := Sum.elim w (fun _ => d)

noncomputable def shearDerivation (x : PolynomialTranslationLie σ) :
    Derivation ℚ (MvPolynomial (σ ⊕ Unit) ℚ) (MvPolynomial (σ ⊕ Unit) ℚ) :=
  mkDerivation ℚ (Sum.elim (fun i => C (x.base i)) (fun _ => rename Sum.inl x.polynomial))

omit [Fintype σ] in
@[simp] theorem shearDerivation_X_inl (x : PolynomialTranslationLie σ) (i : σ) :
    shearDerivation x (X (Sum.inl i)) = C (x.base i) := mkDerivation_X _ _ _

omit [Fintype σ] in
@[simp] theorem shearDerivation_X_inr (x : PolynomialTranslationLie σ) (u : Unit) :
    shearDerivation x (X (Sum.inr u)) = rename Sum.inl x.polynomial := mkDerivation_X _ _ _

theorem shearDerivation_rename (x : PolynomialTranslationLie σ) (P : MvPolynomial σ ℚ) :
    shearDerivation x (rename Sum.inl P) =
      rename Sum.inl (scalarDirectionalDerivative x.base P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [MvPolynomial.derivation_C]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
      simp only [map_mul, rename_X, Derivation.leibniz, smul_eq_mul,
        shearDerivation_X_inl, scalarDirectionalDerivative_X, map_add, rename_C, hP]

noncomputable def shearDerivationHom : PolynomialTranslationLie σ →ₗ⁅ℚ⁆
    Derivation ℚ (MvPolynomial (σ ⊕ Unit) ℚ) (MvPolynomial (σ ⊕ Unit) ℚ) where
  toFun := shearDerivation
  map_add' x y := by
    apply MvPolynomial.derivation_ext
    intro i
    cases i <;> simp [Pi.add_apply]
  map_smul' r x := by
    apply MvPolynomial.derivation_ext
    intro i
    cases i <;> simp [Derivation.smul_apply, Pi.smul_apply, Algebra.smul_def]
  map_lie' := by
    intro x y
    apply MvPolynomial.derivation_ext
    intro i
    cases i <;> simp [Derivation.commutator_apply, MvPolynomial.derivation_C,
      shearDerivation_rename]

theorem shearDerivationHom_injective : Function.Injective (shearDerivationHom (σ := σ)) := by
  intro x y h
  apply PolynomialTranslationLie.ext
  · funext i
    have hh := congrArg (fun D : Derivation ℚ (MvPolynomial (σ ⊕ Unit) ℚ)
      (MvPolynomial (σ ⊕ Unit) ℚ) => D (X (Sum.inl i))) h
    simpa [shearDerivationHom] using hh
  · apply MvPolynomial.rename_injective Sum.inl Sum.inl_injective
    have hh := congrArg (fun D : Derivation ℚ (MvPolynomial (σ ⊕ Unit) ℚ)
      (MvPolynomial (σ ⊕ Unit) ℚ) => D (X (Sum.inr ()))) h
    simpa [shearDerivationHom] using hh

omit [Fintype σ] in

theorem shearDerivation_mem_drop (w : σ → ℕ) (d k : ℕ)
    {x : PolynomialTranslationLie σ} (hx : x ∈ weightedLayer w d k) :
    shearDerivation x ∈ polynomialDerivationDrop (shearWeight w d) k := by
  intro i
  cases i with
  | inl i =>
      rw [shearDerivation_X_inl]
      by_cases hi : k ≤ w i
      · exact (monomial_mem_restrictSupport ℚ).mpr (Or.inl (by simpa [shearWeight] using hi))
      · rw [hx.1 i (by omega), map_zero]
        exact Submodule.zero_mem _
  | inr u =>
      rw [shearDerivation_X_inr]
      exact weightedSupportDrop_rename Sum.inl (fun _ => rfl) hx.2

noncomputable def weightedShearEmbedding (w : σ → ℕ) (d : ℕ) :
    weightedSubalgebra w d →ₗ⁅ℚ⁆ PolynomialShearLieAlgebra (shearWeight w d) ℚ where
  toFun x := ⟨shearDerivationHom x.val, shearDerivation_mem_drop w d 1 x.property⟩
  map_add' x y := Subtype.ext (shearDerivationHom.map_add x.val y.val)
  map_smul' r x := Subtype.ext (shearDerivationHom.map_smul r x.val)
  map_lie' := by
    intro x y
    exact Subtype.ext (shearDerivationHom.map_lie x.val y.val)

theorem weightedShearEmbedding_injective (w : σ → ℕ) (d : ℕ) :
    Function.Injective (weightedShearEmbedding w d) := by
  intro x y h
  apply Subtype.ext
  exact shearDerivationHom_injective (congrArg Subtype.val h)

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial
open scoped TensorProduct

variable {σ : Type*} [Fintype σ]

omit [Fintype σ] in
theorem shearWeight_le (w : σ → ℕ) (d : ℕ) (hw : ∀ i, w i ≤ d) :
    ∀ i, shearWeight w d i ≤ d := by
  intro i
  cases i with
  | inl i => exact hw i
  | inr _ => exact le_rfl

noncomputable def weightedShearGroupHom (w : σ → ℕ) (d : ℕ) (hw : ∀ i, w i ≤ d) :
    (weightedFiltration w d hw).Group →* WeightedLoweringAut (shearWeight w d) ℚ :=
  (polynomialShearBCHEquiv _ d (shearWeight_le w d hw)).toMonoidHom.comp
    (NilpotentLieBCHGroup.map (weightedShearEmbedding w d))

@[simp] theorem weightedShearGroupHom_apply (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, w i ≤ d) (g : (weightedFiltration w d hw).Group) :
    weightedShearGroupHom w d hw g = polynomialShearExpAut (weightedShearEmbedding w d g.coord) := rfl

noncomputable def weightedShearRealGroupHom (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, w i ≤ d) :
    (weightedFiltration w d hw).realification.Group →*
      WeightedLoweringAut (shearWeight w d) ℝ :=
  (polynomialShearRealAutEquiv _ d (shearWeight_le w d hw)).toMonoidHom.comp
    (NilpotentLieBCHGroup.mapReal (realificationLieHom (weightedShearEmbedding w d)))

@[simp] theorem weightedShearRealGroupHom_apply (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, w i ≤ d) (g : (weightedFiltration w d hw).realification.Group) :
    weightedShearRealGroupHom w d hw g = polynomialShearExpAut
      (polynomialShearRealificationEquiv (shearWeight w d)
        (realificationLieHom (weightedShearEmbedding w d) g.coord)) := rfl

theorem weightedShearRealEmbedding_injective (w : σ → ℕ) (d : ℕ) :
    Function.Injective (realificationLieHom (weightedShearEmbedding w d)) := by
  let : Module.Free ℚ ℝ := Module.Free.of_divisionRing ℚ ℝ
  exact Module.Flat.lTensor_preserves_injective_linearMap (M := ℝ)
    (weightedShearEmbedding w d).toLinearMap (weightedShearEmbedding_injective w d)

theorem weightedShearRealGroupHom_injective (w : σ → ℕ) (d : ℕ) (hw : ∀ i, w i ≤ d) :
    Function.Injective (weightedShearRealGroupHom w d hw) := by
  intro g h heq
  apply NilpotentLieBCHGroup.ext
  apply weightedShearRealEmbedding_injective w d
  have hh := (polynomialShearRealAutEquiv _ d (shearWeight_le w d hw)).injective heq
  exact congrArg NilpotentLieBCHGroup.coord hh

theorem weightedShearRealGroupHom_rational (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, w i ≤ d) (g : (weightedFiltration w d hw).Group)
    (P : MvPolynomial (σ ⊕ Unit) ℚ) :
    (weightedShearRealGroupHom w d hw (NilpotentLieBCHGroup.realificationHom g)).val
      (MvPolynomial.map (algebraMap ℚ ℝ) P) =
    MvPolynomial.map (algebraMap ℚ ℝ) ((weightedShearGroupHom w d hw g).val P) := by
  exact polynomialShearRealAutEquiv_rational (shearWeight w d) d
    (shearWeight_le w d hw) (NilpotentLieBCHGroup.map (weightedShearEmbedding w d) g) P

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial
open scoped TensorProduct

variable {σ : Type*} [Fintype σ]

noncomputable def realShearEmbedding (w : σ → ℕ) (d : ℕ) :
    (ℝ ⊗[ℚ] weightedSubalgebra w d) →ₗ⁅ℝ⁆ PolynomialShearLieAlgebra (shearWeight w d) ℝ :=
  (polynomialShearRealificationEquiv (shearWeight w d)).toLieHom.comp
    (realificationLieHom (weightedShearEmbedding w d))

@[simp] theorem realShearEmbedding_tmul (w : σ → ℕ) (d : ℕ)
    (r : ℝ) (x : weightedSubalgebra w d) :
    realShearEmbedding w d (r ⊗ₜ[ℚ] x) =
      r • polynomialShearMap (algebraMap ℚ ℝ) (weightedShearEmbedding w d x) := rfl

theorem realShearEmbedding_shape (w : σ → ℕ) (d : ℕ)
    (x : ℝ ⊗[ℚ] weightedSubalgebra w d) :
    ∃ b : σ → ℝ, ∃ P : MvPolynomial σ ℝ,
      (∀ i, (realShearEmbedding w d x).val (X (Sum.inl i)) = C (b i)) ∧
      (realShearEmbedding w d x).val (X (Sum.inr ())) = rename Sum.inl P := by
  induction x using TensorProduct.induction_on with
  | zero =>
    simp only [map_zero, ZeroMemClass.coe_zero]
    first
      | exact ⟨fun _ => 0, 0, fun _ => by simp, by simp⟩
      | (simp; exact ⟨⟨0, fun _ => by simp⟩, 0, by simp⟩)
  | tmul r x =>
      refine ⟨fun i => r * (x.val.base i : ℝ),
        r • MvPolynomial.map (algebraMap ℚ ℝ) x.val.polynomial, ?_, ?_⟩
      · intro i
        rw [realShearEmbedding_tmul]
        change r • (polynomialShearMap (algebraMap ℚ ℝ)
          (weightedShearEmbedding w d x)).val (X (Sum.inl i)) = _
        rw [polynomialShearMap_X]
        change r • MvPolynomial.map (algebraMap ℚ ℝ)
          (x.val.shearDerivation (X (Sum.inl i))) = _
        rw [shearDerivation_X_inl, map_C]
        simp [Algebra.smul_def]
      · rw [realShearEmbedding_tmul]
        change r • (polynomialShearMap (algebraMap ℚ ℝ)
          (weightedShearEmbedding w d x)).val (X (Sum.inr ())) = _
        rw [polynomialShearMap_X]
        change r • MvPolynomial.map (algebraMap ℚ ℝ)
          (x.val.shearDerivation (X (Sum.inr ()))) = _
        rw [shearDerivation_X_inr]
        simp [MvPolynomial.map_rename]
  | add x y hx hy =>
      obtain ⟨bx, Px, hbx, hPx⟩ := hx
      obtain ⟨by', Py, hby, hPy⟩ := hy
      refine ⟨bx + by', Px + Py, ?_, ?_⟩
      · intro i
        rw [map_add]
        change (realShearEmbedding w d x).val (X (Sum.inl i)) +
          (realShearEmbedding w d y).val (X (Sum.inl i)) = _
        rw [hbx, hby]
        simp
      · rw [map_add]
        change (realShearEmbedding w d x).val (X (Sum.inr ())) +
          (realShearEmbedding w d y).val (X (Sum.inr ())) = _
        rw [hPx, hPy, map_add]

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial
open scoped BigOperators

variable {σ : Type*} [Fintype σ]

theorem shearDerivation_pow_X_inr (x : PolynomialTranslationLie σ) (n : ℕ) :
    (x.shearDerivation.toLinearMap ^ (n+1)) (X (Sum.inr ())) =
      rename Sum.inl ((scalarDirectionalDerivative x.base).toLinearMap ^ n $ x.polynomial) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, ih]
      change shearDerivation x (rename Sum.inl _) = _
      rw [shearDerivation_rename, pow_succ', Module.End.mul_apply]
      rfl

omit [Fintype σ] in
theorem shearDerivation_pow_X_inl (x : PolynomialTranslationLie σ) (n : ℕ) (i : σ) :
    (x.shearDerivation.toLinearMap ^ (n+2)) (X (Sum.inl i)) = 0 := by
  induction n with
  | zero =>
      rw [show 0+2=1+1 by omega, pow_succ', Module.End.mul_apply]
      simp [MvPolynomial.derivation_C]
  | succ n ih =>
      rw [show n+1+2=(n+2)+1 by omega, pow_succ', Module.End.mul_apply, ih, map_zero]

theorem weightedShearExp_X_inr (w : σ → ℕ) (d : ℕ)
    (x : weightedSubalgebra w d) (N : ℕ) (hN : d ≤ N) :
    (polynomialShearExpAut (weightedShearEmbedding w d x)).val (X (Sum.inr ())) =
      X (Sum.inr ()) + rename Sum.inl
        (∑ k ∈ Finset.range N, ((k+1).factorial : ℚ)⁻¹ •
          ((scalarDirectionalDerivative x.val.base).toLinearMap ^ k) x.val.polynomial) := by
  rw [polynomialShearExpAut_apply,
    polynomialShearExp_eq_sum _ (weightedSupportLE_mono hN
      (weightedSupportLE_X (shearWeight w d) (Sum.inr ()))), Finset.sum_range_succ']
  simp only [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero,
    Module.End.one_apply, one_smul, map_sum, map_smul]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  exact shearDerivation_pow_X_inr x.val k

theorem weightedShearExp_X_inl (w : σ → ℕ) (d : ℕ)
    (x : weightedSubalgebra w d) (i : σ) :
    (polynomialShearExpAut (weightedShearEmbedding w d x)).val (X (Sum.inl i)) =
      X (Sum.inl i) + C (x.val.base i) := by
  rw [polynomialShearExpAut_apply,
    polynomialShearExp_eq_sum _ (weightedSupportLE_mono (Nat.le_add_right (w i) 2)
      (weightedSupportLE_X (shearWeight w d) (Sum.inl i))),
    Finset.sum_range_succ', Finset.sum_range_succ']
  have hz : ∑ k ∈ Finset.range (w i + 1),
      ((k+1+1).factorial : ℚ)⁻¹ •
      ((weightedShearEmbedding w d x).val.toLinearMap ^ (k+1+1)) (X (Sum.inl i)) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    change ((k+1+1).factorial : ℚ)⁻¹ •
      (x.val.shearDerivation.toLinearMap ^ (k+2)) (X (Sum.inl i)) = 0
    rw [shearDerivation_pow_X_inl, smul_zero]
  rw [hz]
  simp only [Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, inv_one, pow_zero,
    pow_one, Module.End.one_apply, one_smul, zero_add]
  change x.val.shearDerivation (X (Sum.inl i)) + X (Sum.inl i) = _
  rw [shearDerivation_X_inl, add_comm]

end Erdos3.PolynomialTranslationLie

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.WeightedTranslationBasisHeight
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial
variable {σ : Type*} [Fintype σ]

noncomputable def constantDirection : PolynomialTranslationLie σ := ⟨0, 1⟩

noncomputable def topProjection (w : σ → ℕ) (d : ℕ) :
    PolynomialTranslationLie σ →ₗ[ℚ] PolynomialTranslationLie σ where
  toFun x := ⟨fun i => if w i = d then x.base i else 0, C (x.polynomial.coeff 0)⟩
  map_add' x y := by
    ext i
    · by_cases hi : w i = d <;> simp [hi]
    · simp
  map_smul' r x := by
    ext i
    · by_cases hi : w i = d <;> simp [hi]
    · simp

omit [Fintype σ] in
@[simp] theorem topProjection_base (w : σ → ℕ) (d : ℕ)
    (x : PolynomialTranslationLie σ) (i : σ) :
    (topProjection w d x).base i = if w i = d then x.base i else 0 := rfl

omit [Fintype σ] in
@[simp] theorem topProjection_polynomial (w : σ → ℕ) (d : ℕ)
    (x : PolynomialTranslationLie σ) :
    (topProjection w d x).polynomial = C (x.polynomial.coeff 0) := rfl

omit [Fintype σ] in
theorem topProjection_mem_top (w : σ → ℕ) (d : ℕ) (x : PolynomialTranslationLie σ) :
    topProjection w d x ∈ weightedLayer w d d := by
  refine ⟨fun i hi => ?_, ?_⟩
  · simp [Nat.ne_of_lt hi]
  · exact (monomial_mem_restrictSupport ℚ).mpr (Or.inl (by simp))

omit [Fintype σ] in
theorem topProjection_pure (w : σ → ℕ) (d : ℕ) (P : MvPolynomial σ ℚ) :
    topProjection w d ⟨0, P⟩ = P.coeff 0 • (constantDirection : PolynomialTranslationLie σ) := by
  apply PolynomialTranslationLie.ext
  · funext i
    simp [constantDirection]
  · simp [constantDirection, MvPolynomial.C_eq_smul_one]

theorem pure_constant_zero_of_top_frequency (w : σ → ℕ) (d : ℕ)
    (U : LieSubalgebra ℚ (PolynomialTranslationLie σ))
    (hgraded : ∀ x ∈ U, topProjection w d x ∈ U)
    (frequency : PolynomialTranslationLie σ →ₗ[ℚ] ℚ)
    (hfrequency : frequency constantDirection ≠ 0)
    (hkill : ∀ x ∈ U, x ∈ weightedLayer w d d → frequency x = 0)
    (P : MvPolynomial σ ℚ) (hP : (⟨0, P⟩ : PolynomialTranslationLie σ) ∈ U) :
    P.coeff 0 = 0 := by
  have h := hkill _ (hgraded _ hP) (topProjection_mem_top w d ⟨0, P⟩)
  rw [topProjection_pure, map_smul, smul_eq_mul] at h
  exact (mul_eq_zero.mp h).resolve_right hfrequency

theorem raw_lie_mem (U : LieSubalgebra ℚ (PolynomialTranslationLie σ))
    (x z : σ → ℚ) (P Q : MvPolynomial σ ℚ)
    (hx : (⟨x,P⟩ : PolynomialTranslationLie σ) ∈ U)
    (hz : (⟨z,Q⟩ : PolynomialTranslationLie σ) ∈ U) :
    (⟨0, scalarDirectionalDerivative x Q - scalarDirectionalDerivative z P⟩ :
      PolynomialTranslationLie σ) ∈ U :=
  U.lie_mem (x := ⟨x,P⟩) (y := ⟨z,Q⟩) hx hz

noncomputable def relationSpace (U : LieSubalgebra ℚ (PolynomialTranslationLie σ)) :
    Submodule ℚ ((σ → ℚ) × MvPolynomial σ ℚ) :=
  U.toSubmodule.comap toProdl.symm.toLinearMap

theorem mem_relationSpace (U : LieSubalgebra ℚ (PolynomialTranslationLie σ))
    (x : σ → ℚ) (P : MvPolynomial σ ℚ) :
    (x,P) ∈ relationSpace U ↔ (⟨x,P⟩ : PolynomialTranslationLie σ) ∈ U := Iff.rfl

noncomputable def potentialRelationOfTopFrequency (w : σ → ℕ) (d : ℕ)
    (U : LieSubalgebra ℚ (PolynomialTranslationLie σ))
    (hgraded : ∀ x ∈ U, topProjection w d x ∈ U)
    (frequency : PolynomialTranslationLie σ →ₗ[ℚ] ℚ)
    (hfrequency : frequency constantDirection ≠ 0)
    (hkill : ∀ x ∈ U, x ∈ weightedLayer w d d → frequency x = 0) :
    Erdos3.PolynomialPotentialRelation σ where
  space := relationSpace U
  bracket_mem := by
    intro x P z Q hx hz
    exact (mem_relationSpace U _ _).mpr (raw_lie_mem U x z P Q
      ((mem_relationSpace U _ _).mp hx) ((mem_relationSpace U _ _).mp hz))
  pure_constant_zero := fun P hP => pure_constant_zero_of_top_frequency w d U hgraded
    frequency hfrequency hkill P ((mem_relationSpace U _ _).mp hP)

@[simp] theorem mem_potentialRelationOfTopFrequency (w : σ → ℕ) (d : ℕ)
    (U : LieSubalgebra ℚ (PolynomialTranslationLie σ))
    (hgraded : ∀ x ∈ U, topProjection w d x ∈ U)
    (frequency : PolynomialTranslationLie σ →ₗ[ℚ] ℚ)
    (hfrequency : frequency constantDirection ≠ 0)
    (hkill : ∀ x ∈ U, x ∈ weightedLayer w d d → frequency x = 0)
    (x : σ → ℚ) (P : MvPolynomial σ ℚ) :
    (x,P) ∈ (potentialRelationOfTopFrequency w d U hgraded frequency hfrequency hkill).space ↔
      (⟨x,P⟩ : PolynomialTranslationLie σ) ∈ U := Iff.rfl

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial Module

variable {σ : Type*} [Fintype σ]

noncomputable def weightedCoordinatesEquiv (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) :
    weightedSubalgebra w d ≃ₗ[ℚ] (σ → ℚ) × weightedSupportLT (R := ℚ) w d where
  toFun x := (x.val.base, ⟨x.val.polynomial,
    by simpa only [← weightedSupportDrop_one] using x.property.2⟩)
  invFun x := ⟨⟨x.1, x.2.val⟩, ⟨fun i hi => by have := hw i; omega,
    by simpa only [weightedSupportDrop_one] using x.2.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

abbrev WeightedBasisIndex (w : σ → ℕ) (d : ℕ) :=
  σ ⊕ {a : σ →₀ ℕ | Finsupp.weight w a < d}

noncomputable def weightedBasis (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) :
    Basis (WeightedBasisIndex w d) ℚ (weightedSubalgebra w d) :=
  ((Pi.basisFun ℚ σ).prod
    (MvPolynomial.basisRestrictSupport ℚ {a : σ →₀ ℕ | Finsupp.weight w a < d})).map
    (weightedCoordinatesEquiv w d hw).symm

noncomputable def weightedBasisGrade (w : σ → ℕ) (d : ℕ) : WeightedBasisIndex w d → ℕ :=
  Sum.elim w (fun a => d - Finsupp.weight w a.val)

@[simp] theorem weightedBasis_repr_inl (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (x : weightedSubalgebra w d) (i : σ) :
    (weightedBasis w d hw).repr x (Sum.inl i) = x.val.base i := by
  change (Pi.basisFun ℚ σ).repr x.val.base i = _
  simp only [Pi.basisFun_repr]

@[simp] theorem weightedBasis_repr_inr (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (x : weightedSubalgebra w d) (a : {a : σ →₀ ℕ | Finsupp.weight w a < d}) :
    (weightedBasis w d hw).repr x (Sum.inr a) = x.val.polynomial.coeff a.val := by
  rfl

omit [Fintype σ] in
@[simp] theorem weightedBasisGrade_inl (w : σ → ℕ) (d : ℕ) (i : σ) :
    weightedBasisGrade w d (Sum.inl i) = w i := rfl

omit [Fintype σ] in
@[simp] theorem weightedBasisGrade_inr (w : σ → ℕ) (d : ℕ)
    (a : {a : σ →₀ ℕ | Finsupp.weight w a < d}) :
    weightedBasisGrade w d (Sum.inr a) = d - Finsupp.weight w a.val := rfl

@[simp] theorem weightedBasis_projection_base (w : σ → ℕ) (d j : ℕ)
    (hw : ∀ i, 0 < w i) (x : weightedSubalgebra w d) (i : σ) :
    (basisGradeProjection (weightedBasis w d hw) (weightedBasisGrade w d) j x).val.base i =
      if w i = j then x.val.base i else 0 := by
  simpa only [weightedBasis_repr_inl, weightedBasisGrade_inl] using
    basisGradeProjection_repr (weightedBasis w d hw) (weightedBasisGrade w d) j x (Sum.inl i)

@[simp] theorem weightedBasis_projection_coeff (w : σ → ℕ) (d j : ℕ)
    (hw : ∀ i, 0 < w i) (x : weightedSubalgebra w d)
    (a : {a : σ →₀ ℕ | Finsupp.weight w a < d}) :
    (basisGradeProjection (weightedBasis w d hw) (weightedBasisGrade w d) j x).val.polynomial.coeff a.val =
      if d - Finsupp.weight w a.val = j then x.val.polynomial.coeff a.val else 0 := by
  simpa only [weightedBasis_repr_inr, weightedBasisGrade_inr] using
    basisGradeProjection_repr (weightedBasis w d hw) (weightedBasisGrade w d) j x (Sum.inr a)

theorem weightedBasis_top_projection_polynomial (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (hd : 0 < d) (x : weightedSubalgebra w d) :
    (basisGradeProjection (weightedBasis w d hw) (weightedBasisGrade w d) d x).val.polynomial =
      C (x.val.polynomial.coeff 0) := by
  classical
  let : Finsupp.NonTorsionWeight ℕ w := Finsupp.nonTorsionWeight_of ℕ w (fun i => (hw i).ne')
  apply MvPolynomial.ext
  intro a
  by_cases ha : Finsupp.weight w a < d
  · rw [weightedBasis_projection_coeff w d d hw x ⟨a, ha⟩]
    have he : d - Finsupp.weight w a = d ↔ a = 0 := by
      rw [← Finsupp.weight_eq_zero_iff_eq_zero w]
      omega
    simp only [he]
    by_cases ha0 : a = 0
    · subst a
      simp
    · simp [ha0, Ne.symm ha0]
  · have ha0 : a ≠ 0 := by
      intro h
      subst a
      simp only [map_zero] at ha
      omega
    rw [coeff_C, if_neg (Ne.symm ha0)]
    by_contra hne
    have hh := (basisGradeProjection (weightedBasis w d hw) (weightedBasisGrade w d) d x).property.2
      (MvPolynomial.mem_support_iff.mpr hne)
    change Finsupp.weight w a + 1 ≤ d at hh
    omega

theorem weightedBasis_top_projection_val (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (hd : 0 < d) (x : weightedSubalgebra w d) :
    (basisGradeProjection (weightedBasis w d hw) (weightedBasisGrade w d) d x).val =
      ⟨fun i => if w i = d then x.val.base i else 0, C (x.val.polynomial.coeff 0)⟩ := by
  apply PolynomialTranslationLie.ext
  · funext i
    exact weightedBasis_projection_base w d d hw x i
  · exact weightedBasis_top_projection_polynomial w d hw hd x

theorem weightedFiltration_layer_eq_span (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d) (j : ℕ) :
    (weightedFiltration w d hwd).layer j =
      Submodule.span ℚ (weightedBasis w d hw '' {i | j ≤ weightedBasisGrade w d i}) := by
  ext x
  rw [basis_mem_span_image_iff]
  constructor
  · intro hx a ha
    change (∀ i, w i < j → x.val.base i = 0) ∧
      x.val.polynomial ∈ weightedSupportDrop w d j at hx
    cases a with
    | inl i =>
        rw [weightedBasis_repr_inl]
        exact hx.1 i (by change ¬ j ≤ w i at ha; omega)
    | inr a =>
        rw [weightedBasis_repr_inr]
        by_contra hne
        have hh := hx.2 (MvPolynomial.mem_support_iff.mpr hne)
        change Finsupp.weight w a.val + j ≤ d at hh
        change ¬ j ≤ d - Finsupp.weight w a.val at ha
        omega
  · intro hx
    change (∀ i, w i < j → x.val.base i = 0) ∧
      x.val.polynomial ∈ weightedSupportDrop w d j
    constructor
    · intro i hi
      exact (weightedBasis_repr_inl w d hw x i) ▸ hx (Sum.inl i) (by
        change ¬ j ≤ w i
        omega)
    · intro a ha
      have hb := x.property.2 ha
      change Finsupp.weight w a + 1 ≤ d at hb
      change Finsupp.weight w a + j ≤ d
      by_contra hnot
      have haLT : Finsupp.weight w a < d := by omega
      have hh := hx (Sum.inr ⟨a, haLT⟩) (by
        change ¬ j ≤ d - Finsupp.weight w a
        omega)
      rw [weightedBasis_repr_inr] at hh
      exact (MvPolynomial.mem_support_iff.mp ha) hh

theorem weightedBasis_top_projection_eq (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (hd : 0 < d) (x : weightedSubalgebra w d) :
    (basisGradeProjection (weightedBasis w d hw) (weightedBasisGrade w d) d x).val =
      topProjection w d x.val :=
  weightedBasis_top_projection_val w d hw hd x

theorem topProjection_mem_of_basisGraded (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (hd : 0 < d)
    (U : Submodule ℚ (PolynomialTranslationLie σ))
    (hU : U ≤ (weightedSubalgebra w d).toSubmodule)
    (hgraded : BasisGradedSubmodule (weightedBasis w d hw) (weightedBasisGrade w d)
      (U.comap (weightedSubalgebra w d).subtype))
    {x : PolynomialTranslationLie σ} (hx : x ∈ U) : topProjection w d x ∈ U := by
  let y : weightedSubalgebra w d := ⟨x, hU hx⟩
  have hy := hgraded d y hx
  change (basisGradeProjection (weightedBasis w d hw) (weightedBasisGrade w d) d y).val ∈ U at hy
  rw [weightedBasis_top_projection_eq w d hw hd] at hy
  exact hy

theorem weightedBasis_projection_isWeightedHomogeneous (w : σ → ℕ) (d j : ℕ)
    (hw : ∀ i, 0 < w i) (x : weightedSubalgebra w d) :
    (basisGradeProjection (weightedBasis w d hw) (weightedBasisGrade w d) j x).val.polynomial.IsWeightedHomogeneous w (d - j) := by
  classical
  intro a ha
  have hbound := (basisGradeProjection (weightedBasis w d hw) (weightedBasisGrade w d) j x).property.2
    (MvPolynomial.mem_support_iff.mpr ha)
  change Finsupp.weight w a + 1 ≤ d at hbound
  have haLT : Finsupp.weight w a < d := by omega
  rw [weightedBasis_projection_coeff w d j hw x ⟨a, haLT⟩] at ha
  have hgrade : d - Finsupp.weight w a = j := by
    by_contra hne
    simp only [hne, ↓reduceIte, ne_self_iff_false] at ha
  omega

theorem weightedBasisIndex_finite (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) :
    Finite (WeightedBasisIndex w d) := by
  let : Finite {a : σ →₀ ℕ | Finsupp.weight w a < d} :=
    (Finsupp.finite_of_nat_weight_lt w (fun i => (hw i).ne') d).to_subtype
  infer_instance

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial

variable {σ : Type*} [Fintype σ]
    (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (x : weightedSubalgebra w d) {H : ℕ}

theorem weightedBasis_base_height
    (hall : ∀ i : WeightedBasisIndex w d,
      RationalHeightLE ((weightedBasis w d hw).repr x i) H) :
    ∀ i, RationalHeightLE (x.val.base i) H := by
  intro i
  simpa only [weightedBasis_repr_inl] using hall (Sum.inl i)

end Erdos3.PolynomialTranslationLie

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.AdaptedBinomialFactorization
namespace OAI

section

namespace Erdos3

open scoped Pointwise

variable {σ R : Type*} [CommRing R]

noncomputable def polynomialSupportBox (α : σ →₀ ℕ) : Submodule R (MvPolynomial σ R) where
  carrier := {p | ∀ β ∈ p.support, β ≤ α}
  zero_mem' := by simp
  add_mem' hp hq := by
    classical
    intro β hβ
    rcases Finset.mem_union.mp (MvPolynomial.support_add hβ) with h | h
    · exact hp β h
    · exact hq β h
  smul_mem' c p hp := by
    intro β hβ
    exact hp β (MvPolynomial.support_smul hβ)

theorem monomial_mem_polynomialSupportBox {α β : σ →₀ ℕ} (hβα : β ≤ α) (c : R) :
    MvPolynomial.monomial β c ∈ polynomialSupportBox α := by
  classical
  intro γ hγ
  have h : γ = β := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hγ)
  simpa only [h] using hβα

theorem mul_mem_polynomialSupportBox {α β : σ →₀ ℕ} {p q : MvPolynomial σ R}
    (hp : p ∈ polynomialSupportBox α) (hq : q ∈ polynomialSupportBox β) :
    p * q ∈ polynomialSupportBox (α + β) := by
  classical
  intro γ hγ
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul p q hγ)
  exact add_le_add (hp a ha) (hq b hb)

theorem prod_mem_polynomialSupportBox {κ : Type*} (u : Finset κ)
    (α : κ → σ →₀ ℕ) (p : κ → MvPolynomial σ R)
    (hp : ∀ i ∈ u, p i ∈ polynomialSupportBox (α i)) :
    (∏ i ∈ u, p i) ∈ polynomialSupportBox (∑ i ∈ u, α i) := by
  classical
  induction u using Finset.induction_on with
  | empty =>
    change MvPolynomial.monomial 0 (1 : R) ∈ polynomialSupportBox 0
    exact monomial_mem_polynomialSupportBox le_rfl 1
  | @insert i u hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact mul_mem_polynomialSupportBox (hp i (Finset.mem_insert_self ..))
      (ih (fun j hj => hp j (Finset.mem_insert_of_mem hj)))

theorem finsupp_weight_mono (w : σ → ℕ) {α β : σ →₀ ℕ} (h : α ≤ β) :
    Finsupp.weight w α ≤ Finsupp.weight w β := by
  obtain ⟨γ, rfl⟩ := exists_add_of_le h
  rw [map_add]
  exact Nat.le_add_right _ _

theorem polynomial_aeval_X_mem_supportBox (i : σ) (p : Polynomial R) {n : ℕ}
    (hp : p.natDegree ≤ n) :
    Polynomial.aeval (MvPolynomial.X i : MvPolynomial σ R) p ∈
      polynomialSupportBox (Finsupp.single i n) := by
  classical
  rw [Polynomial.aeval_eq_sum_range]
  apply Submodule.sum_mem
  intro k hk
  apply Submodule.smul_mem
  rw [MvPolynomial.X_pow_eq_monomial]
  apply monomial_mem_polynomialSupportBox
  have hkn : k ≤ n := (Nat.le_of_lt_succ (Finset.mem_range.mp hk)).trans hp
  intro j
  by_cases h : i = j
  · subst j
    simpa using hkn
  · simp [h]

end Erdos3

end

section

namespace Erdos3

variable {σ : Type*}

noncomputable def binomialVariable (i : σ) (n : ℕ) : MvPolynomial σ ℚ :=
  Polynomial.aeval (MvPolynomial.X i) (binomialPolynomial n)

@[simp] theorem binomialVariable_zero (i : σ) : binomialVariable i 0 = 1 := by
  simp [binomialVariable]

noncomputable def multivariateBinomial (α : σ →₀ ℕ) : MvPolynomial σ ℚ :=
  α.prod binomialVariable

@[simp] theorem multivariateBinomial_zero : multivariateBinomial (0 : σ →₀ ℕ) = 1 := by
  simp [multivariateBinomial]

@[simp] theorem multivariateBinomial_single (i : σ) (n : ℕ) :
    multivariateBinomial (Finsupp.single i n) = binomialVariable i n := by
  classical
  simp [multivariateBinomial]

theorem binomialVariable_mem_supportBox (i : σ) (n : ℕ) :
    binomialVariable i n ∈ polynomialSupportBox (Finsupp.single i n) :=
  polynomial_aeval_X_mem_supportBox i _ (le_of_eq (binomialPolynomial_natDegree n))

theorem multivariateBinomial_mem_supportBox (α : σ →₀ ℕ) :
    multivariateBinomial α ∈ polynomialSupportBox α := by
  have h := prod_mem_polynomialSupportBox α.support (fun i => Finsupp.single i (α i))
    (fun i => binomialVariable i (α i)) (fun i _ => binomialVariable_mem_supportBox i (α i))
  have heq : (∑ i ∈ α.support, Finsupp.single i (α i)) = α := Finsupp.sum_single α
  simpa only [heq, multivariateBinomial, Finsupp.prod] using h

end Erdos3

end

section

namespace Erdos3

open Polynomial

end Erdos3

end

section

namespace Erdos3

open scoped Pointwise

variable {σ : Type*}

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial Module
open scoped Manifold ContDiff TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] {s : ℕ} (F : NilpotentLieFiltration L s)

noncomputable def polynomialOrbitRealEval (w : σ → ℕ) (x : σ → ℝ) :
    F.PolynomialOrbit w →* F.Group :=
  (NilpotentLieBCHGroup.map (eval₂Lie (R := ℚ) (L := L) x)).comp
    (F.polynomialSubgroup w).subtype

@[simp] theorem polynomialOrbitRealEval_coord (w : σ → ℕ)
    (p : F.PolynomialOrbit w) (x : σ → ℝ) :
    (F.polynomialOrbitRealEval w x p).coord = eval₂ x p.log := rfl

theorem polynomialOrbitRealEval_integer (w : σ → ℕ) (p : F.PolynomialOrbit w)
    (x : σ → ℤ) :
    F.polynomialOrbitRealEval w (fun i => (x i : ℝ)) p = F.polynomialOrbitEval w x p := by
  apply NilpotentLieBCHGroup.ext
  simpa only [polynomialOrbitRealEval_coord, polynomialOrbitEval_coord,
    map_intCast] using
    eval₂_algebraMap (S := ℝ) (fun i => (x i : ℚ)) p.log

section Smooth

variable [Fintype ι] [Fintype σ] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]

end Smooth
end Erdos3.NilpotentLieFiltration

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial Module
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

structure AdaptedMonomial (w : σ → ℕ) where
  exponent : σ →₀ ℕ
  coefficient : L
  coefficient_mem : coefficient ∈ F.layer (Finsupp.weight w exponent)

namespace AdaptedMonomial

variable {F} {w : σ → ℕ}

noncomputable def logarithm (u : F.AdaptedMonomial w) : F.adaptedLieSubalgebra w :=
  ⟨monomial u.exponent u.coefficient,
    F.monomial_mem_adaptedSubmodule w u.exponent u.coefficient_mem⟩

@[simp] theorem coe_logarithm (u : F.AdaptedMonomial w) :
    (u.logarithm : VectorPolynomial σ ℚ L) = monomial u.exponent u.coefficient := rfl

end AdaptedMonomial

noncomputable def adaptedBCHToOrbit (w : σ → ℕ) :
    (F.adaptedPolynomialFiltration w).Group →* F.PolynomialOrbit w :=
  (NilpotentLieBCHGroup.map (hnil := (F.adaptedPolynomialFiltration w).lowerCentralSeries_eq_bot)
    (hM := VectorPolynomial.lowerCentralSeries_eq_bot F.lowerCentralSeries_eq_bot)
    (F.adaptedLieSubalgebra w).incl).codRestrict _ (fun g => g.coord.property)

namespace AdaptedMonomial

variable {F} {w : σ → ℕ}

noncomputable def orbit (u : F.AdaptedMonomial w) : F.PolynomialOrbit w :=
  F.adaptedBCHToOrbit w ⟨u.logarithm⟩

@[simp] theorem orbit_log (u : F.AdaptedMonomial w) :
    u.orbit.log = monomial u.exponent u.coefficient := rfl

end AdaptedMonomial

section Real

variable [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]

end Real

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F G : NilpotentLieFiltration L s) (hGF : G = F) (w : σ → ℕ)

noncomputable def realPolynomialOrbitChangeFiltration
    (orbit : F.realification.PolynomialOrbit w) : G.realification.PolynomialOrbit w :=
  polynomialOrbitOfLog orbit.log (by rw [hGF]; exact orbit.adapted)

@[simp] theorem realPolynomialOrbitChangeFiltration_log
    (orbit : F.realification.PolynomialOrbit w) :
    (F.realPolynomialOrbitChangeFiltration G hGF w orbit).log = orbit.log := rfl

theorem realPolynomialOrbitChangeFiltration_eval
    (orbit : F.realification.PolynomialOrbit w) (t : σ → ℤ) :
    G.realification.polynomialOrbitEval w t
      (F.realPolynomialOrbitChangeFiltration G hGF w orbit) =
        F.realification.polynomialOrbitEval w t orbit := by
  apply NilpotentLieBCHGroup.ext
  rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem tensor_adapted_of_supportBox (w : σ → ℕ) {α : σ →₀ ℕ}
    {q : MvPolynomial σ ℚ} (hq : q ∈ polynomialSupportBox α) {a : L}
    (ha : a ∈ F.layer (Finsupp.weight w α)) : F.Adapted w (q ⊗ₜ[ℚ] a) := by
  apply (F.adapted_iff_coefficients w _).mpr
  intro β
  rw [coefficients_tmul]
  by_cases hc : q.coeff β = 0
  · simp [hc]
  · apply Submodule.smul_mem
    exact F.antitone (finsupp_weight_mono w (hq β (MvPolynomial.mem_support_iff.mpr hc))) ha

structure AdaptedBinomial (w : σ → ℕ) where
  exponent : σ →₀ ℕ
  coefficient : L
  coefficient_mem : coefficient ∈ F.layer (Finsupp.weight w exponent)

namespace AdaptedBinomial

variable {F} {w : σ → ℕ}

noncomputable def logarithm (u : F.AdaptedBinomial w) : F.adaptedLieSubalgebra w :=
  ⟨multivariateBinomial u.exponent ⊗ₜ[ℚ] u.coefficient,
    (F.mem_adaptedSubmodule w _).mpr
      (F.tensor_adapted_of_supportBox w (multivariateBinomial_mem_supportBox u.exponent)
        u.coefficient_mem)⟩

@[simp] theorem coe_logarithm (u : F.AdaptedBinomial w) :
    (u.logarithm : VectorPolynomial σ ℚ L) =
      multivariateBinomial u.exponent ⊗ₜ[ℚ] u.coefficient := rfl

def scale (c : ℚ) (u : F.AdaptedBinomial w) : F.AdaptedBinomial w where
  exponent := u.exponent
  coefficient := c • u.coefficient
  coefficient_mem := (F.layer _).smul_mem c u.coefficient_mem

noncomputable def orbit (u : F.AdaptedBinomial w) : F.PolynomialOrbit w :=
  F.adaptedBCHToOrbit w ⟨u.logarithm⟩

@[simp] theorem orbit_log (u : F.AdaptedBinomial w) :
    u.orbit.log = multivariateBinomial u.exponent ⊗ₜ[ℚ] u.coefficient := rfl

end AdaptedBinomial
end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

section Real

variable [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]

end Real
end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.GaussianTailRadius
namespace OAI

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

end Erdos3

end

section

namespace Erdos3

noncomputable def schmidtRadiusFactor (d : ℕ) (A : ℝ) : ℝ :=
  4 * ((d : ℝ) + Real.log A + 1)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.IndependentReturnScale
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3.CellRefinement

open scoped NNReal

noncomputable def outerMatchingScale (rank : ℕ) (W epsilon : ℝ) (scale : ℝ≥0) : ℝ≥0 :=
  min scale (localizedAverageScale rank W (epsilon / 4))

noncomputable def outerMatchingScaleLoss (rank : ℕ) (A E T : ℝ) : ℝ :=
  T + rank + A + E + 1602

end Erdos3.CellRefinement

end

section

namespace Erdos3.LocalConvolution

open scoped NNReal

noncomputable def controlledLocalMomentScale (rank : ℕ) (M delta : ℝ) : ℝ≥0 :=
  localizedAverageScale rank M (min (delta / 2) (localMomentGain delta) / 3) / 2

noncomputable def localMomentErrorBudget (delta : ℝ) : ℝ :=
  -Real.log (2 * min (delta / 2) (localMomentGain delta) / 3)

end Erdos3.LocalConvolution

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

end Erdos3.LocalConvolution

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators NNReal

noncomputable def independentReturnScale (rank : ℕ) (M epsilon : ℝ) : ℝ≥0 :=
  localizedAverageScale rank M (epsilon / 2) / 2

variable {N : ℕ} [NeZero N]

end Erdos3.CellRefinement

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.JointRationalSpaceGenerators
namespace OAI

section

namespace Erdos3

open scoped Matrix

theorem exists_real_kernel_generators {J V : Type*} [Fintype J] [Fintype V]
    (A : Matrix V J ℚ) {H : ℕ} (hH : 1 ≤ H) (hA : ∀ v j, RationalHeightLE (A v j) H) :
    ∃ P : Matrix J J ℚ,
      (∀ i j, RationalHeightLE (P i j) (imageDefiningHeight (Fintype.card V) (Fintype.card V) H)) ∧
      LinearMap.range (Matrix.of (fun i j => (P i j : ℝ))).mulVecLin =
        LinearMap.ker (Matrix.of (fun v j => (A v j : ℝ))).mulVecLin := by
  classical
  obtain ⟨S, hS, hSH⟩ := exists_bounded_rational_image_section A hH hA
  let P : Matrix J J ℚ := 1 - S * A
  have hSr := real_matrix_image_section A S hS
  have hPr : Matrix.of (fun i j => (P i j : ℝ)) =
      1 - Matrix.of (fun i v => (S i v : ℝ)) * Matrix.of (fun v j => (A v j : ℝ)) := by
    ext i j
    by_cases hij : i = j <;> simp [P, Matrix.sub_apply, Matrix.mul_apply, Matrix.one_apply, hij]
  refine ⟨P, ?_, ?_⟩
  · intro i j
    have hI : RationalHeightLE ((1 : Matrix J J ℚ) i j) 1 := by
      by_cases hij : i = j
      · simpa [Matrix.one_apply, hij] using rationalHeightLE_one (by decide : 1 ≤ 1)
      · simpa [Matrix.one_apply, hij] using rationalHeightLE_zero (by decide : 1 ≤ 1)
    have hprod := rationalHeightLE_matrix_mul S A hSH hA i j
    simpa only [P, Matrix.sub_apply, imageDefiningHeight, mul_one, one_mul, mul_comm] using hI.sub hprod
  · ext x
    change (∃ y, Matrix.of (fun i j => (P i j : ℝ)) *ᵥ y = x) ↔
      Matrix.of (fun v j => (A v j : ℝ)) *ᵥ x = 0
    rw [hPr]
    constructor
    · rintro ⟨y, rfl⟩
      rw [Matrix.mulVec_mulVec, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hSr,
        sub_self, Matrix.zero_mulVec]
    · intro hx
      refine ⟨x, ?_⟩
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero, sub_zero]

def jointSpaceGeneratorHeight (ambient columns rows H R : ℕ) : ℕ :=
  imageDefiningHeight (ambient + rows) (ambient + rows)
    (max (imageDefiningHeight columns ambient H) R)

namespace VectorPolynomial

theorem exists_jointRationalSpace_generators {J C V : Type*}
    [Fintype J] [Fintype C] [Fintype V]
    (B : Matrix J C ℚ) (A : Matrix V J ℚ) {H R : ℕ}
    (hH : 1 ≤ H) (hR : 1 ≤ R)
    (hB : ∀ i j, RationalHeightLE (B i j) H) (hA : ∀ v j, RationalHeightLE (A v j) R) :
    ∃ P : Matrix J J ℚ,
      (∀ i j, RationalHeightLE (P i j)
        (jointSpaceGeneratorHeight (Fintype.card J) (Fintype.card C) (Fintype.card V) H R)) ∧
      LinearMap.range (Matrix.of (fun i j => (P i j : ℝ))).mulVecLin = jointRationalSpace B A := by
  obtain ⟨Q, hQ, hQker⟩ := exists_real_span_defining_matrix B hH hB
  let A' : Matrix (J ⊕ V) J ℚ := Matrix.of (fun v j => Sum.elim (fun i => Q i j) (fun v => A v j) v)
  have hA' : ∀ v j, RationalHeightLE (A' v j) (max (imageDefiningHeight (Fintype.card C) (Fintype.card J) H) R) := by
    intro v j
    cases v with
    | inl i => exact (hQ i j).mono (le_max_left _ _)
    | inr v => exact (hA v j).mono (le_max_right _ _)
  obtain ⟨P, hP, hPker⟩ := exists_real_kernel_generators A' (hR.trans (le_max_right _ _)) hA'
  refine ⟨P, ?_, hPker.trans ?_⟩
  · simpa only [Fintype.card_sum, jointSpaceGeneratorHeight] using hP
  · ext x
    change LinearMap.ker (Matrix.of (fun i j => (Q i j : ℝ))).mulVecLin =
      LinearMap.range (Matrix.of (fun i j => (B i j : ℝ))).mulVecLin at hQker
    change (Matrix.of (fun v j => (A' v j : ℝ)) *ᵥ x = 0) ↔
      x ∈ LinearMap.range (Matrix.of (fun i j => (B i j : ℝ))).mulVecLin ∧
      Matrix.of (fun v j => (A v j : ℝ)) *ᵥ x = 0
    rw [← hQker]
    change (Matrix.of (fun v j => (A' v j : ℝ)) *ᵥ x = 0) ↔
      (Matrix.of (fun i j => (Q i j : ℝ)) *ᵥ x = 0) ∧
      Matrix.of (fun v j => (A v j : ℝ)) *ᵥ x = 0
    constructor
    · intro hx
      exact ⟨funext (fun i => congrFun hx (.inl i)), funext (fun v => congrFun hx (.inr v))⟩
    · rintro ⟨hQx, hAx⟩
      ext v
      cases v with
      | inl i => exact congrFun hQx i
      | inr v => exact congrFun hAx v

end VectorPolynomial

theorem jointSpaceGeneratorHeight_le_exp (ambient columns rows H R : ℕ) {p : ℝ}
    (hp : 0 ≤ p) (ha : (ambient : ℝ) ≤ p) (hc : (columns : ℝ) ≤ p) (hr : (rows : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) (hR : (R : ℝ) ≤ Real.exp p) :
    (jointSpaceGeneratorHeight ambient columns rows H R : ℝ) ≤ Real.exp ((p + 2) ^ 120) := by
  have hfirst := imageDefiningHeight_le_exp columns ambient H hp hc ha hH
  have hpp := le_power_budget hp (by decide : 1 ≤ 10)
  have hmax : ((max (imageDefiningHeight columns ambient H) R : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 10) := by
    rw [Nat.cast_max]
    exact max_le hfirst (hR.trans (Real.exp_le_exp.mpr hpp))
  have hsum : ((ambient + rows : ℕ) : ℝ) ≤ (p + 2) ^ 10 := by
    have hpow : (p + 2) ^ 2 ≤ (p + 2) ^ 10 := pow_le_pow_right₀ (by linarith) (by decide)
    push_cast
    nlinarith
  have hsecond := imageDefiningHeight_le_exp (ambient + rows) (ambient + rows)
    (max (imageDefiningHeight columns ambient H) R) (by positivity) hsum hsum hmax
  exact hsecond.trans (Real.exp_le_exp.mpr (shifted_power_budget_le hp 10 10))

end Erdos3

end

end OAI

end


