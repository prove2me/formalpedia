-- Prove2me | Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_IntrinsicNorm
-- name    : QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_IntrinsicNorm
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T16:19:30.821405+00:00
-- url     : https://prove2.me/theorems/c34bfb87-a671-472f-bf38-86c3ceb908f9
-- title:
--   Intrinsic Norm
-- statement:
--   Definitions and structural lemmas for Intrinsic Norm, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Norm/IntrinsicNorm.lean

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_GlobalNormOneBridge
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_SplittingFieldDescent
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Algebra_MatrixAlgebraNorm
import Mathlib.Algebra.Polynomial.Roots
import Theorems.Thm_Matrix_affineLineDet_conj
import Theorems.Thm_Matrix_map_affineLineDet
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CongruenceLifting_residueTransvectionSpecial_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_arithmeticRingToFunctionField_arithmeticOnePlusY
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_arithmeticRingToFunctionField_arithmeticOnePlusYInv
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingCompactCyclicSemidirectHom_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingGeneratorNeighborAtEquiv_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingIntegralUnitPGLHom_monomial
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingLatticeVertexMap_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingLocalCyclicBasis_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerGeneratorCyclicElement_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerGeneratorCyclicUnit_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerGeneratorCyclicUnit_to_buildingGL
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerGeneratorCyclicUnit_to_buildingPGL
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerNormUnit_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrixHom_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrix_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraSplitNormOneGeneratorRatio_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraToBuilding_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraToBuilding_cartwrightStegerBCyclicElement
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraToBuilding_cartwrightStegerGeneratorCyclicElement
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraToBuilding_constantCyclicElement
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraToBuilding_cyclicGeneratorCyclicElement
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraToBuilding_cyclicGeneratorInverseCyclicElement
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraToBuilding_cyclicMonomial
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_frobeniusPowerEquiv_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_functionFieldCyclicBasis_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_globalIntegralUnitGLHom_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_globalIntegralUnitPGLHom_monomial
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexConstantGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexCyclicGeneratorGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_infinityConjugationCorrectionSum_bound_zero
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_infinityCyclicCoefficient_rank
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_infinityCyclicCoefficient_zero
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_integralArithmeticToBuildingIntegerRing_algebraMap
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_integralArithmeticToBuildingIntegerRing_y
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_integralArithmeticToFunctionField_y
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_integralArithmeticToGlobalSkewScalarRange_algebraMap
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_mem_skewLaurentIntSupport
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_orderUnitToBuildingPGL_generator
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_orderUnitToGlobalGL_generator
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueBGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueConstantGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueXAdjoinRootEquiv_root
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueYAdjoinRootEquiv_root
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewExponentResidue_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewLaurentCyclicLaurentCoordinate_add
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewLaurentCyclicLaurentCoordinate_zero
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewLaurentMonomialUnit_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewLaurentToBuildingMatrix_single
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewLaurentToCyclicAlgebra_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewLaurentToGlobalMatrix_single
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankFour_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankFour_three
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankFour_two
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankThree_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankThree_two
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coe_uniformizerUnit
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_diagonalGeneralLinear_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFourFundamentalHeckeAlgEquiv_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFourSecondCompoundGeneralLinear_inv_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankThreeFundamentalHeckeAlgEquiv_apply
import Theorems.Thm_RatFunc_coefficientRingEquiv_C
import Theorems.Thm_RatFunc_coefficientRingEquiv_X
import Theorems.Thm_RatFunc_coefficientRingEquiv_apply_div
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.CongruenceLifting.residueTransvectionSpecial_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticRingToFunctionField_arithmeticOnePlusY
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticRingToFunctionField_arithmeticOnePlusYInv
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingCompactCyclicSemidirectHom_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingGeneratorNeighborAtEquiv_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingIntegralUnitPGLHom_monomial
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingLatticeVertexMap_one
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingLocalCyclicBasis_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerGeneratorCyclicElement_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerGeneratorCyclicUnit_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerGeneratorCyclicUnit_to_buildingGL
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerGeneratorCyclicUnit_to_buildingPGL
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerNormUnit_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantUnitMatrixHom_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantUnitMatrix_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraSplitNormOneGeneratorRatio_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraToBuilding_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraToBuilding_cartwrightStegerBCyclicElement
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraToBuilding_cartwrightStegerGeneratorCyclicElement
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraToBuilding_constantCyclicElement
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraToBuilding_cyclicGeneratorCyclicElement
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraToBuilding_cyclicGeneratorInverseCyclicElement
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraToBuilding_cyclicMonomial
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.frobeniusPowerEquiv_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.functionFieldCyclicBasis_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.globalIntegralUnitGLHom_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.globalIntegralUnitPGLHom_monomial
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexConstantGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexCyclicGeneratorGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.infinityConjugationCorrectionSum_bound_zero
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.infinityCyclicCoefficient_rank
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.infinityCyclicCoefficient_zero
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.integralArithmeticToBuildingIntegerRing_algebraMap
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.integralArithmeticToBuildingIntegerRing_y
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.integralArithmeticToFunctionField_y
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.integralArithmeticToGlobalSkewScalarRange_algebraMap
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.mem_skewLaurentIntSupport
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.orderUnitToBuildingPGL_generator
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.orderUnitToGlobalGL_generator
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueBGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueConstantGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueXAdjoinRootEquiv_root
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueYAdjoinRootEquiv_root
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewExponentResidue_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurentCyclicLaurentCoordinate_add
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurentCyclicLaurentCoordinate_zero
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurentMonomialUnit_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurentToBuildingMatrix_single
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurentToCyclicAlgebra_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurentToGlobalMatrix_single
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankFour_one
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankFour_three
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankFour_two
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankThree_one
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankThree_two
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.coe_uniformizerUnit
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.diagonalGeneralLinear_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.rankFourFundamentalHeckeAlgEquiv_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.rankFourSecondCompoundGeneralLinear_inv_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.rankThreeFundamentalHeckeAlgEquiv_apply
attribute [local simp] RatFunc.coefficientRingEquiv_C
attribute [local simp] RatFunc.coefficientRingEquiv_X
attribute [local simp] RatFunc.coefficientRingEquiv_apply_div


set_option autoImplicit false
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped Polynomial
noncomputable def cyclicAlgebraRegularNorm
    (P : BasePrime) (r : Rank) :
    CyclicAlgebra P r →* FunctionField P :=
  Algebra.norm (FunctionField P)
abbrev SplittingCyclicScalarExtension (P : BasePrime) (r : Rank) :=
  TensorProduct (FunctionField P) (SplittingFunctionField P r)
    (CyclicAlgebra P r)
noncomputable def splittingCyclicScalarExtensionMap
    (P : BasePrime) (r : Rank) :
    SplittingCyclicScalarExtension P r →ₐ[SplittingFunctionField P r]
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r) :=
  Algebra.TensorProduct.lift
    (Algebra.ofId (SplittingFunctionField P r) <|
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r))
    (CyclicAlgebra P r).val
    (fun a M => by
      change Commute
        (algebraMap (SplittingFunctionField P r)
          (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (SplittingFunctionField P r)) a)
        ((M : CyclicAlgebra P r) :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (SplittingFunctionField P r))
      exact Algebra.commutes a _)
noncomputable def splittingCyclicScalarExtensionBasis
    (P : BasePrime) (r : Rank) :
    Module.Basis (Fin r.matrixRank × Fin r.matrixRank)
      (SplittingFunctionField P r) (SplittingCyclicScalarExtension P r) :=
  Algebra.TensorProduct.basis (SplittingFunctionField P r)
    (functionFieldCyclicBasis P r)
@[simp] theorem splittingCyclicScalarExtensionMap_basis
    (P : BasePrime) (r : Rank)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    splittingCyclicScalarExtensionMap P r
        (splittingCyclicScalarExtensionBasis P r p) =
      splittingCyclicBasis P r p := by
  rw [splittingCyclicScalarExtensionBasis,
    Algebra.TensorProduct.basis_apply,
    splittingCyclicScalarExtensionMap,
    Algebra.TensorProduct.lift_tmul]
  simp only [functionFieldCyclicBasis_apply, splittingCyclicBasis_apply]
  simp
theorem splittingCyclicScalarExtensionMap_bijective
    (P : BasePrime) (r : Rank) :
    Function.Bijective (splittingCyclicScalarExtensionMap P r) := by
  let e := (splittingCyclicScalarExtensionBasis P r).equiv
    (splittingCyclicBasis P r) (Equiv.refl _)
  have heq : (splittingCyclicScalarExtensionMap P r).toLinearMap =
      e.toLinearMap := by
    apply (splittingCyclicScalarExtensionBasis P r).ext
    intro p
    change splittingCyclicScalarExtensionMap P r
        (splittingCyclicScalarExtensionBasis P r p) =
      e (splittingCyclicScalarExtensionBasis P r p)
    rw [splittingCyclicScalarExtensionMap_basis]
    exact (Module.Basis.equiv_apply
      (splittingCyclicScalarExtensionBasis P r) p
      (splittingCyclicBasis P r) (Equiv.refl _)).symm
  rw [show (splittingCyclicScalarExtensionMap P r : _ → _) = e by
    funext x
    exact DFunLike.congr_fun heq x]
  exact e.bijective
noncomputable def splittingCyclicScalarExtensionEquivMatrix
    (P : BasePrime) (r : Rank) :
    SplittingCyclicScalarExtension P r ≃ₐ[SplittingFunctionField P r]
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r) :=
  AlgEquiv.ofBijective (splittingCyclicScalarExtensionMap P r)
    (splittingCyclicScalarExtensionMap_bijective P r)
@[simp] theorem splittingCyclicScalarExtensionMap_includeRight
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r) :
    splittingCyclicScalarExtensionMap P r
        (Algebra.TensorProduct.includeRight x) =
      (x : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r)) := by
  rw [Algebra.TensorProduct.includeRight_apply,
    splittingCyclicScalarExtensionMap,
    Algebra.TensorProduct.lift_tmul]
  simp
theorem splittingFunctionFieldFrobenius_affineLineDet
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r) :
    Polynomial.map (splittingFunctionFieldFrobenius P r).toRingHom
        (Matrix.affineLineDet
          (x : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (SplittingFunctionField P r))) =
      Matrix.affineLineDet
        (x : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (SplittingFunctionField P r)) := by
  rw [Matrix.map_affineLineDet]
  change Matrix.affineLineDet
      ((splittingFunctionFieldFrobenius P r).toRingHom.mapMatrix
        (x : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (SplittingFunctionField P r))) = _
  rw [splittingFunctionFieldFrobenius_mapMatrix_eq_cyclicGenerator_conj]
  exact Matrix.affineLineDet_conj _ _ _ (cyclicGenerator_mul_inverse P r)
theorem exists_eq_polynomial_map_functionFieldEmbedding_of_frobenius_eq
    (P : BasePrime) (r : Rank)
    (p : (SplittingFunctionField P r)[X])
    (hp : Polynomial.map (splittingFunctionFieldFrobenius P r).toRingHom p = p) :
    ∃ q : (FunctionField P)[X],
      Polynomial.map (functionFieldEmbedding P r) q = p := by
  have hcoeff (i : ℕ) : splittingFunctionFieldFrobenius P r (p.coeff i) =
      p.coeff i := by
    have h := congrArg
      (fun q : (SplittingFunctionField P r)[X] => q.coeff i) hp
    simpa using h
  have hlifts : p ∈ Polynomial.lifts (functionFieldEmbedding P r) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    exact exists_eq_functionFieldEmbedding_of_frobenius_eq P r
      (p.coeff i) (hcoeff i)
  obtain ⟨q, hq, -⟩ := Polynomial.exists_support_eq_of_mem_lifts hlifts
  exact ⟨q, hq⟩
noncomputable def cyclicAlgebraReducedNormPolynomial
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r) :
    (FunctionField P)[X] :=
  Classical.choose
    (exists_eq_polynomial_map_functionFieldEmbedding_of_frobenius_eq P r
      (Matrix.affineLineDet
        (x : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (SplittingFunctionField P r)))
      (splittingFunctionFieldFrobenius_affineLineDet P r x))
end QEC.Coding.HighDimensionalExpander.CartwrightSteger


