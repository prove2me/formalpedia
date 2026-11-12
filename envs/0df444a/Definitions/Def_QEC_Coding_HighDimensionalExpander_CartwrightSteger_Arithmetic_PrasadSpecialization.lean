-- Prove2me | Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadSpecialization
-- name    : QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadSpecialization
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T17:31:56.119796+00:00
-- url     : https://prove2.me/theorems/f952c7e5-e71c-42cd-a4f9-115bbe471ac3
-- title:
--   Prasad Specialization
-- statement:
--   Definitions and structural lemmas for Prasad Specialization, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadSpecialization.lean

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_IntrinsicStrongApproximation
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Algebra.IsOpenUnits
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CongruenceLifting_residueTransvectionSpecial_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_arithmeticRingToFunctionField_arithmeticOnePlusY
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_arithmeticRingToFunctionField_arithmeticOnePlusYInv
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_baseNormOneOrderUnitsReduction_factor_completed
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_baseNormOneOrderUnitsReduction_surjective_iff_PSL_le_image
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
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerOrderToCyclicAlgebra_injective
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerOrderToCyclic_mem_arithmeticCyclicSpan
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantArithmeticToSplittingFunctionField_arithmeticBaseChange
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrixHom_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrix_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraBuildingNormOne_eq_normOne
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
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexCompletedNormOneReduction_global_compatibility
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexConstantGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexCyclicGeneratorGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexPlacePolynomial_irreducible
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_infinityConjugationCorrectionSum_bound_zero
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_infinityCyclicCoefficient_rank
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_infinityCyclicCoefficient_zero
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_integralArithmeticToBuildingIntegerRing_algebraMap
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_integralArithmeticToBuildingIntegerRing_y
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_integralArithmeticToFunctionField_y
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_integralArithmeticToGlobalSkewScalarRange_algebraMap
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_mem_IndexCartwrightStegerColorZero_iff_mem_PSL
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_mem_skewLaurentIntSupport
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_one_mem_arithmeticCyclicSpan
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_orderNormOneInnerFormToOrderUnits_injective
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
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_specialLinearToPSL_surjective
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankFour_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankFour_three
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankFour_two
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankThree_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankThree_two
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_MatrixOrderLowerBound_add
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
open scoped TensorProduct
open scoped commutatorElement
open Topology
noncomputable instance polynomialArithmeticFunctionFieldTower
    (P : BasePrime) :
    IsScalarTower (PolynomialRing P) (ArithmeticRing P)
      (FunctionField P) :=
  IsScalarTower.of_algebraMap_eq fun f =>
    (arithmeticRingToFunctionField_algebraMap P f).symm
theorem arithmeticLocalizationElement_ne_zero
    (P : BasePrime) :
    (Polynomial.X * (1 + Polynomial.X) : PolynomialRing P) ≠ 0 := by
  apply mul_ne_zero Polynomial.X_ne_zero
  intro h
  have := congrArg (Polynomial.eval (0 : BaseField P)) h
  simp at this
noncomputable instance arithmeticRingIsDomain
    (P : BasePrime) : IsDomain (ArithmeticRing P) :=
  IsLocalization.isDomain_of_le_nonZeroDivisors (ArithmeticRing P)
    (powers_le_nonZeroDivisors_of_noZeroDivisors
      (arithmeticLocalizationElement_ne_zero P))
noncomputable instance arithmeticRingFunctionFieldIsFractionRing
    (P : BasePrime) :
    IsFractionRing (ArithmeticRing P) (FunctionField P) :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (Submonoid.powers
      (Polynomial.X * (1 + Polynomial.X) : PolynomialRing P))
    (ArithmeticRing P) (FunctionField P)
noncomputable instance arithmeticRingIsDedekindDomain
    (P : BasePrime) : IsDedekindDomain (ArithmeticRing P) := by
  exact IsLocalization.isDedekindDomain (PolynomialRing P)
    (powers_le_nonZeroDivisors_of_noZeroDivisors
      (arithmeticLocalizationElement_ne_zero P))
    (ArithmeticRing P)
noncomputable abbrev ArithmeticFiniteAdeleRing (P : BasePrime) :=
  IsDedekindDomain.FiniteAdeleRing (ArithmeticRing P) (FunctionField P)
noncomputable def functionFieldToArithmeticFiniteAdeles
    (P : BasePrime) :
    FunctionField P →+* ArithmeticFiniteAdeleRing P :=
  IsDedekindDomain.FiniteAdeleRing.algebraMap
    (ArithmeticRing P) (FunctionField P)
noncomputable def ArithmeticIntegralFiniteAdeles
    (P : BasePrime) : Subring (ArithmeticFiniteAdeleRing P) where
  carrier a := ∀ v, a v ∈ v.adicCompletionIntegers (FunctionField P)
  zero_mem' v := (v.adicCompletionIntegers (FunctionField P)).zero_mem
  one_mem' v := (v.adicCompletionIntegers (FunctionField P)).one_mem
  add_mem' {a b} ha hb v := by
    exact
      (v.adicCompletionIntegers (FunctionField P)).add_mem
        (a v) (b v) (ha v) (hb v)
  mul_mem' {a b} ha hb v := by
    exact
      (v.adicCompletionIntegers (FunctionField P)).mul_mem
        (a v) (b v) (ha v) (hb v)
  neg_mem' {a} ha v := by
    exact
      (v.adicCompletionIntegers (FunctionField P)).neg_mem (a v) (ha v)
theorem functionFieldToArithmeticFiniteAdeles_algebraMap_mem_integral
    (P : BasePrime) (a : ArithmeticRing P) :
    functionFieldToArithmeticFiniteAdeles P
        (algebraMap (ArithmeticRing P) (FunctionField P) a) ∈
      ArithmeticIntegralFiniteAdeles P := by
  show ∀ v, _
  intro v
  exact IsDedekindDomain.HeightOneSpectrum.coe_algebraMap_mem
    (ArithmeticRing P) (FunctionField P) v a
theorem functionFieldToArithmeticFiniteAdeles_mem_integral_iff
    (P : BasePrime) (x : FunctionField P) :
    functionFieldToArithmeticFiniteAdeles P x ∈
        ArithmeticIntegralFiniteAdeles P ↔
      x ∈ (algebraMap (ArithmeticRing P) (FunctionField P)).range := by
  constructor
  · intro hx
    apply IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one
    intro v
    have hv := hx v
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] at hv
    change Valued.v
        (x : v.adicCompletion (FunctionField P)) ≤ 1 at hv
    rw [IsDedekindDomain.HeightOneSpectrum.adicCompletion.valued_coe] at hv
    exact hv
  · rintro ⟨a, rfl⟩
    exact functionFieldToArithmeticFiniteAdeles_algebraMap_mem_integral P a
noncomputable abbrev ArithmeticFiniteAdeleCyclicAlgebra
    (P : BasePrime) (r : Rank) :=
  TensorProduct (FunctionField P) (ArithmeticFiniteAdeleRing P)
    (CyclicAlgebra P r)
noncomputable def cyclicAlgebraToArithmeticFiniteAdeles
    (P : BasePrime) (r : Rank) :
    CyclicAlgebra P r →ₐ[FunctionField P]
      ArithmeticFiniteAdeleCyclicAlgebra P r :=
  Algebra.TensorProduct.includeRight
@[simp] theorem cyclicAlgebraToArithmeticFiniteAdeles_apply
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r) :
    cyclicAlgebraToArithmeticFiniteAdeles P r x =
      TensorProduct.tmul (FunctionField P) 1 x :=
  rfl
noncomputable def arithmeticFiniteAdeleCyclicBasis
    (P : BasePrime) (r : Rank) :
    Module.Basis (Fin r.matrixRank × Fin r.matrixRank)
      (ArithmeticFiniteAdeleRing P)
      (ArithmeticFiniteAdeleCyclicAlgebra P r) :=
  (functionFieldCyclicBasis P r).baseChange
    (ArithmeticFiniteAdeleRing P)
noncomputable instance arithmeticFiniteAdeleCyclicAlgebraTopologicalSpace
    (P : BasePrime) (r : Rank) :
    TopologicalSpace (ArithmeticFiniteAdeleCyclicAlgebra P r) :=
  TopologicalSpace.induced
    (arithmeticFiniteAdeleCyclicBasis P r).equivFun inferInstance
noncomputable def ArithmeticFiniteAdeleCyclicIntegralLattice
    (P : BasePrime) (r : Rank) :
    Set (ArithmeticFiniteAdeleCyclicAlgebra P r) :=
  {x | ∀ p, (arithmeticFiniteAdeleCyclicBasis P r).equivFun x p ∈
    ArithmeticIntegralFiniteAdeles P}
noncomputable def arithmeticFiniteAdeleCyclicNonintegralPlaces
    (P : BasePrime) (r : Rank)
    (x : ArithmeticFiniteAdeleCyclicAlgebra P r) :
    Set (IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P)) :=
  {v | ∃ p,
    (arithmeticFiniteAdeleCyclicBasis P r).equivFun x p v ∉
      v.adicCompletionIntegers (FunctionField P)}
noncomputable def arithmeticFiniteAdeleCyclicUnitDenominatorPlaces
    (P : BasePrime) (r : Rank)
    (u : (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ) :
    Set (IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P)) :=
  arithmeticFiniteAdeleCyclicNonintegralPlaces P r u ∪
    arithmeticFiniteAdeleCyclicNonintegralPlaces P r (↑u⁻¹)
noncomputable abbrev ArithmeticFiniteAdeleCyclicIntegralElement
    (P : BasePrime) (r : Rank) :=
  ↥(ArithmeticFiniteAdeleCyclicIntegralLattice P r)
theorem arithmeticFiniteAdeleCyclicBasis_equivFun_diagonal
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    (arithmeticFiniteAdeleCyclicBasis P r).equivFun
        (cyclicAlgebraToArithmeticFiniteAdeles P r x) p =
      functionFieldToArithmeticFiniteAdeles P
        ((functionFieldCyclicBasis P r).equivFun x p) := by
  rw [Module.Basis.equivFun_apply, Module.Basis.equivFun_apply,
    cyclicAlgebraToArithmeticFiniteAdeles_apply,
    arithmeticFiniteAdeleCyclicBasis,
    Module.Basis.baseChange_repr_tmul]
  rw [Algebra.smul_def, mul_one]
  rfl
theorem exists_arithmetic_coordinate_of_mem_arithmeticCyclicSpan
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r)
    (hx : x ∈ arithmeticCyclicSpan P r)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    ∃ a : ArithmeticRing P,
      arithmeticRingToFunctionField P a =
        (functionFieldCyclicBasis P r).equivFun x p := by
  obtain ⟨c, hc⟩ :=
    (Submodule.mem_span_range_iff_exists_fun (ArithmeticRing P)).mp hx
  have hc' : (∑ q, arithmeticRingToFunctionField P (c q) •
      functionFieldCyclicBasis P r q) = x := by
    simp only [functionFieldCyclicBasis_apply, Algebra.smul_def] at hc ⊢
    exact hc
  refine ⟨c p, ?_⟩
  have hp := congrArg ((functionFieldCyclicBasis P r).coord p) hc'
  have hrepr (q : Fin r.matrixRank × Fin r.matrixRank) :
      (functionFieldCyclicBasis P r).coord p
          (functionFieldCyclicBasis P r q) =
        if q = p then 1 else 0 := by
    have hq := congrArg
      (fun f : (Fin r.matrixRank × Fin r.matrixRank) →₀ FunctionField P =>
        f p)
      ((functionFieldCyclicBasis P r).repr_self q)
    simp only [Finsupp.single_apply, eq_comm] at hq ⊢
    exact hq
  simp only [map_sum, map_smul, smul_eq_mul] at hp
  simp_rw [hrepr] at hp
  simpa [Module.Basis.equivFun_apply] using hp
noncomputable def arithmeticCyclicCoordinate
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r)
    (hx : x ∈ arithmeticCyclicSpan P r)
    (p : Fin r.matrixRank × Fin r.matrixRank) : ArithmeticRing P :=
  Classical.choose
    (exists_arithmetic_coordinate_of_mem_arithmeticCyclicSpan P r x hx p)
@[simp] theorem arithmeticRingToFunctionField_arithmeticCyclicCoordinate
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r)
    (hx : x ∈ arithmeticCyclicSpan P r)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    arithmeticRingToFunctionField P
        (arithmeticCyclicCoordinate P r x hx p) =
      (functionFieldCyclicBasis P r).equivFun x p :=
  Classical.choose_spec
    (exists_arithmetic_coordinate_of_mem_arithmeticCyclicSpan P r x hx p)
theorem sum_arithmeticCyclicCoordinate_smul_basis
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r)
    (hx : x ∈ arithmeticCyclicSpan P r) :
    (∑ p, arithmeticRingToFunctionField P
        (arithmeticCyclicCoordinate P r x hx p) •
          functionFieldCyclicBasis P r p) = x := by
  simp_rw [arithmeticRingToFunctionField_arithmeticCyclicCoordinate]
  exact (functionFieldCyclicBasis P r).sum_equivFun x
noncomputable def arithmeticCyclicCoordinateMatrix
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r)
    (hx : x ∈ arithmeticCyclicSpan P r) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (ConstantArithmeticRing P r) :=
  ∑ p, arithmeticToConstantArithmetic P r
      (arithmeticCyclicCoordinate P r x hx p) •
        orderIndexCyclicBasisVector P r p
theorem arithmeticCyclicCoordinateMatrix_to_global
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r)
    (hx : x ∈ arithmeticCyclicSpan P r) :
    (arithmeticCyclicCoordinateMatrix P r x hx).map
        (constantArithmeticToSplittingFunctionField P r) = x.1 := by
  rw [arithmeticCyclicCoordinateMatrix]
  have hmapSum :
      ((∑ p, arithmeticToConstantArithmetic P r
          (arithmeticCyclicCoordinate P r x hx p) •
            orderIndexCyclicBasisVector P r p).map
          (constantArithmeticToSplittingFunctionField P r)) =
        ∑ p, (arithmeticToConstantArithmetic P r
          (arithmeticCyclicCoordinate P r x hx p) •
            orderIndexCyclicBasisVector P r p).map
          (constantArithmeticToSplittingFunctionField P r) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.sum_apply, map_sum]
  rw [hmapSum]
  simp_rw [Matrix.map_smul' _ _ _ (map_mul _),
    constantArithmeticToSplittingFunctionField_arithmeticBaseChange,
    orderIndexCyclicBasisVector_to_global]
  have hsum := congrArg Subtype.val
    (sum_arithmeticCyclicCoordinate_smul_basis P r x hx)
  simp [functionFieldCyclicBasis_apply,
    arithmeticRingToSplittingFunctionField, Algebra.smul_def] at hsum ⊢
  exact hsum
theorem cyclicAlgebraToArithmeticFiniteAdeles_mem_integralLattice
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r)
    (hx : x ∈ arithmeticCyclicSpan P r) :
    cyclicAlgebraToArithmeticFiniteAdeles P r x ∈
      ArithmeticFiniteAdeleCyclicIntegralLattice P r := by
  intro p
  obtain ⟨a, ha⟩ :=
    exists_arithmetic_coordinate_of_mem_arithmeticCyclicSpan P r x hx p
  rw [arithmeticFiniteAdeleCyclicBasis_equivFun_diagonal, ← ha]
  exact functionFieldToArithmeticFiniteAdeles_algebraMap_mem_integral P a
theorem cyclicAlgebraToArithmeticFiniteAdeles_mem_integralLattice_iff
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r) :
    cyclicAlgebraToArithmeticFiniteAdeles P r x ∈
        ArithmeticFiniteAdeleCyclicIntegralLattice P r ↔
      x ∈ arithmeticCyclicSpan P r := by
  constructor
  · intro hx
    have hcoord : ∀ p : Fin r.matrixRank × Fin r.matrixRank,
        ∃ a : ArithmeticRing P,
          arithmeticRingToFunctionField P a =
            (functionFieldCyclicBasis P r).equivFun x p := by
      intro p
      have hp := hx p
      rw [arithmeticFiniteAdeleCyclicBasis_equivFun_diagonal,
        functionFieldToArithmeticFiniteAdeles_mem_integral_iff] at hp
      exact hp
    choose c hc using hcoord
    apply (Submodule.mem_span_range_iff_exists_fun
      (ArithmeticRing P)).mpr
    refine ⟨c, ?_⟩
    have hsum := (functionFieldCyclicBasis P r).sum_equivFun x
    calc
      (∑ p, c p • functionFieldCyclicBasisVector P r p) =
          ∑ p, (functionFieldCyclicBasis P r).equivFun x p •
            functionFieldCyclicBasisVector P r p := by
        apply Finset.sum_congr rfl
        intro p _
        change arithmeticRingToFunctionField P (c p) •
            functionFieldCyclicBasisVector P r p = _
        rw [hc]
      _ = x := by
        simpa [functionFieldCyclicBasis_apply] using hsum
  · exact cyclicAlgebraToArithmeticFiniteAdeles_mem_integralLattice P r x
theorem exists_cartwrightStegerOrder_of_mem_arithmeticCyclicSpan
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r)
    (hx : x ∈ arithmeticCyclicSpan P r) :
    ∃ y : CartwrightStegerOrder P r,
      cartwrightStegerOrderToCyclicAlgebra P r y = x := by
  refine Submodule.span_induction
    (p := fun x _ => ∃ y : CartwrightStegerOrder P r,
      cartwrightStegerOrderToCyclicAlgebra P r y = x)
    ?basis ?zero ?add ?smul hx
  · intro x hxRange
    obtain ⟨p, rfl⟩ := hxRange
    let y : CartwrightStegerOrder P r :=
      ⟨(functionFieldCyclicBasisVector P r p :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (SplittingFunctionField P r)),
        (CartwrightStegerOrder P r).mul_mem
          (constantMatrix_mem_cartwrightStegerOrder P r
            (constantBasis P r p.1))
          ((CartwrightStegerOrder P r).pow_mem
            (cyclicGeneratorMatrix_mem_cartwrightStegerOrder P r)
            (p.2 : Nat))⟩
    exact ⟨y, Subtype.ext rfl⟩
  · exact ⟨0, map_zero (cartwrightStegerOrderToCyclicAlgebra P r)⟩
  · intro x y _ _ hx hy
    obtain ⟨x', rfl⟩ := hx
    obtain ⟨y', rfl⟩ := hy
    exact ⟨x' + y', map_add (cartwrightStegerOrderToCyclicAlgebra P r) x' y'⟩
  · intro a x _ hx
    obtain ⟨x', rfl⟩ := hx
    refine ⟨a • x', ?_⟩
    apply Subtype.ext
    change ((a • x' : CartwrightStegerOrder P r) :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (SplittingFunctionField P r)) =
      ((a • cartwrightStegerOrderToCyclicAlgebra P r x' :
          CyclicAlgebra P r) :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (SplittingFunctionField P r))
    rw [Subalgebra.coe_smul]
    change a • (x'.1 : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r)) =
      (((arithmeticRingToFunctionField P a) •
          cartwrightStegerOrderToCyclicAlgebra P r x' :
        CyclicAlgebra P r) :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (SplittingFunctionField P r))
    rw [Subalgebra.coe_smul]
    change a • (x'.1 : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r)) =
      arithmeticRingToFunctionField P a • x'.1
    simp only [Algebra.smul_def]
    congr 1
noncomputable def cyclicAlgebraUnitToArithmeticFiniteAdeles
    (P : BasePrime) (r : Rank) :
    (CyclicAlgebra P r)ˣ →*
      (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ :=
  Units.map (cyclicAlgebraToArithmeticFiniteAdeles P r).toRingHom
@[simp] theorem cyclicAlgebraUnitToArithmeticFiniteAdeles_coe
    (P : BasePrime) (r : Rank) (u : (CyclicAlgebra P r)ˣ) :
    (cyclicAlgebraUnitToArithmeticFiniteAdeles P r u :
        ArithmeticFiniteAdeleCyclicAlgebra P r) =
      cyclicAlgebraToArithmeticFiniteAdeles P r (u : CyclicAlgebra P r) :=
  rfl
noncomputable abbrev ArithmeticFiniteAdeleSplittingRing
    (P : BasePrime) (r : Rank) :=
  TensorProduct (FunctionField P) (ArithmeticFiniteAdeleRing P)
    (SplittingFunctionField P r)
noncomputable def splittingFunctionFieldToArithmeticFiniteAdeleSplittingRing
    (P : BasePrime) (r : Rank) :
    SplittingFunctionField P r →ₐ[FunctionField P]
      ArithmeticFiniteAdeleSplittingRing P r :=
  Algebra.TensorProduct.includeRight
noncomputable def cyclicAlgebraToArithmeticFiniteAdeleSplittingMatrix
    (P : BasePrime) (r : Rank) :
    CyclicAlgebra P r →ₐ[FunctionField P]
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (ArithmeticFiniteAdeleSplittingRing P r) :=
  (splittingFunctionFieldToArithmeticFiniteAdeleSplittingRing P r).mapMatrix.comp
    (CyclicAlgebra P r).val
noncomputable def arithmeticFiniteAdeleCyclicSplittingMap
    (P : BasePrime) (r : Rank) :
    ArithmeticFiniteAdeleCyclicAlgebra P r →ₐ[ArithmeticFiniteAdeleRing P]
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (ArithmeticFiniteAdeleSplittingRing P r) :=
  Algebra.TensorProduct.lift
    (Algebra.ofId (ArithmeticFiniteAdeleRing P)
      (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (ArithmeticFiniteAdeleSplittingRing P r)))
    (cyclicAlgebraToArithmeticFiniteAdeleSplittingMatrix P r)
    (fun a M => by
      change Commute
        (algebraMap (ArithmeticFiniteAdeleRing P)
          (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (ArithmeticFiniteAdeleSplittingRing P r)) a)
        (cyclicAlgebraToArithmeticFiniteAdeleSplittingMatrix P r M)
      exact Algebra.commutes a _)
noncomputable def arithmeticFiniteAdeleSplittingFrobenius
    (P : BasePrime) (r : Rank) :
    ArithmeticFiniteAdeleSplittingRing P r
      →ₐ[ArithmeticFiniteAdeleRing P]
        ArithmeticFiniteAdeleSplittingRing P r where
  toRingHom := (Algebra.TensorProduct.map
    (AlgHom.id (FunctionField P) (ArithmeticFiniteAdeleRing P))
    (splittingFunctionFieldFrobenius P r).toAlgHom).toRingHom
  commutes' a := by
    change Algebra.TensorProduct.map
      (AlgHom.id (FunctionField P) (ArithmeticFiniteAdeleRing P))
      (splittingFunctionFieldFrobenius P r).toAlgHom
        (TensorProduct.tmul (FunctionField P) a 1) = _
    simp
@[simp] theorem arithmeticFiniteAdeleSplittingFrobenius_tmul
    (P : BasePrime) (r : Rank)
    (a : ArithmeticFiniteAdeleRing P) (x : SplittingFunctionField P r) :
    arithmeticFiniteAdeleSplittingFrobenius P r
        (TensorProduct.tmul (FunctionField P) a x) =
      TensorProduct.tmul (FunctionField P) a
        (splittingFunctionFieldFrobenius P r x) := by
  simp [arithmeticFiniteAdeleSplittingFrobenius]
noncomputable def arithmeticFiniteAdeleCyclicGeneratorMatrix
    (P : BasePrime) (r : Rank) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (ArithmeticFiniteAdeleSplittingRing P r) :=
  (cyclicGeneratorMatrix P r).map
    (splittingFunctionFieldToArithmeticFiniteAdeleSplittingRing P r)
noncomputable def arithmeticFiniteAdeleCyclicGeneratorInverseMatrix
    (P : BasePrime) (r : Rank) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (ArithmeticFiniteAdeleSplittingRing P r) :=
  (cyclicGeneratorInverseMatrix P r).map
    (splittingFunctionFieldToArithmeticFiniteAdeleSplittingRing P r)
theorem arithmeticFiniteAdeleCyclicSplittingMap_frobenius
    (P : BasePrime) (r : Rank)
    (x : ArithmeticFiniteAdeleCyclicAlgebra P r) :
    (arithmeticFiniteAdeleSplittingFrobenius P r).toRingHom.mapMatrix
        (arithmeticFiniteAdeleCyclicSplittingMap P r x) =
      arithmeticFiniteAdeleCyclicGeneratorMatrix P r *
        arithmeticFiniteAdeleCyclicSplittingMap P r x *
          arithmeticFiniteAdeleCyclicGeneratorInverseMatrix P r := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
      rw [map_add, map_add, hx, hy, Matrix.mul_add, Matrix.add_mul]
  | tmul a x =>
      rw [arithmeticFiniteAdeleCyclicSplittingMap,
        Algebra.TensorProduct.lift_tmul]
      have hglobal := congrArg
        (fun M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (SplittingFunctionField P r) =>
          M.map
            (splittingFunctionFieldToArithmeticFiniteAdeleSplittingRing P r))
        (splittingFunctionFieldFrobenius_mapMatrix_eq_cyclicGenerator_conj
          P r x)
      simp only [RingHom.mapMatrix_apply, Matrix.map_mul] at hglobal
      have hscalar :
          (arithmeticFiniteAdeleSplittingFrobenius P r).toRingHom.mapMatrix
            ((Algebra.ofId (ArithmeticFiniteAdeleRing P)
              (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
                (ArithmeticFiniteAdeleSplittingRing P r))) a) =
          (Algebra.ofId (ArithmeticFiniteAdeleRing P)
              (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
                (ArithmeticFiniteAdeleSplittingRing P r))) a := by
        ext i j
        by_cases hij : i = j
        · subst j
          simp [arithmeticFiniteAdeleSplittingFrobenius,
            Matrix.algebraMap_matrix_apply]
        · simp [arithmeticFiniteAdeleSplittingFrobenius,
            Matrix.algebraMap_matrix_apply, hij]
      rw [show
          (arithmeticFiniteAdeleSplittingFrobenius P r).toRingHom.mapMatrix
            ((Algebra.ofId (ArithmeticFiniteAdeleRing P)
              (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
                (ArithmeticFiniteAdeleSplittingRing P r))) a *
              cyclicAlgebraToArithmeticFiniteAdeleSplittingMatrix P r x) =
          (Algebra.ofId (ArithmeticFiniteAdeleRing P)
              (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
                (ArithmeticFiniteAdeleSplittingRing P r))) a *
            (arithmeticFiniteAdeleSplittingFrobenius P r).toRingHom.mapMatrix
              (cyclicAlgebraToArithmeticFiniteAdeleSplittingMatrix P r x) by
          change (((Algebra.ofId (ArithmeticFiniteAdeleRing P)
            (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
              (ArithmeticFiniteAdeleSplittingRing P r))) a *
            cyclicAlgebraToArithmeticFiniteAdeleSplittingMatrix P r x).map
              (arithmeticFiniteAdeleSplittingFrobenius P r).toRingHom) = _
          rw [Matrix.map_mul]
          change
            (arithmeticFiniteAdeleSplittingFrobenius P r).toRingHom.mapMatrix
                ((Algebra.ofId (ArithmeticFiniteAdeleRing P)
                  (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
                    (ArithmeticFiniteAdeleSplittingRing P r))) a) * _ = _
          rw [hscalar]
          rfl]
      rw [show
          (arithmeticFiniteAdeleSplittingFrobenius P r).toRingHom.mapMatrix
              (cyclicAlgebraToArithmeticFiniteAdeleSplittingMatrix P r x) =
            arithmeticFiniteAdeleCyclicGeneratorMatrix P r *
              cyclicAlgebraToArithmeticFiniteAdeleSplittingMatrix P r x *
                arithmeticFiniteAdeleCyclicGeneratorInverseMatrix P r by
          calc
            _ = ((splittingFunctionFieldFrobenius P r).toRingHom.mapMatrix
                (x : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
                  (SplittingFunctionField P r))).map
                (splittingFunctionFieldToArithmeticFiniteAdeleSplittingRing P r) := by
              ext i j
              exact arithmeticFiniteAdeleSplittingFrobenius_tmul P r 1 (x.1 i j)
            _ = _ := hglobal]
      let A := (Algebra.ofId (ArithmeticFiniteAdeleRing P)
        (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (ArithmeticFiniteAdeleSplittingRing P r))) a
      let M := cyclicAlgebraToArithmeticFiniteAdeleSplittingMatrix P r x
      change A * (arithmeticFiniteAdeleCyclicGeneratorMatrix P r * M *
          arithmeticFiniteAdeleCyclicGeneratorInverseMatrix P r) =
        arithmeticFiniteAdeleCyclicGeneratorMatrix P r * (A * M) *
          arithmeticFiniteAdeleCyclicGeneratorInverseMatrix P r
      calc
        A * (arithmeticFiniteAdeleCyclicGeneratorMatrix P r * M *
            arithmeticFiniteAdeleCyclicGeneratorInverseMatrix P r) =
          (A * arithmeticFiniteAdeleCyclicGeneratorMatrix P r) * M *
            arithmeticFiniteAdeleCyclicGeneratorInverseMatrix P r := by
              simp only [mul_assoc]
        _ = (arithmeticFiniteAdeleCyclicGeneratorMatrix P r * A) * M *
            arithmeticFiniteAdeleCyclicGeneratorInverseMatrix P r := by
          rw [show A * arithmeticFiniteAdeleCyclicGeneratorMatrix P r =
              arithmeticFiniteAdeleCyclicGeneratorMatrix P r * A from
            Algebra.commutes a _]
        _ = arithmeticFiniteAdeleCyclicGeneratorMatrix P r * (A * M) *
            arithmeticFiniteAdeleCyclicGeneratorInverseMatrix P r := by
          simp only [mul_assoc]
theorem arithmeticFiniteAdeleCyclicSplitting_det_frobenius
    (P : BasePrime) (r : Rank)
    (x : ArithmeticFiniteAdeleCyclicAlgebra P r) :
    arithmeticFiniteAdeleSplittingFrobenius P r
        (Matrix.det (arithmeticFiniteAdeleCyclicSplittingMap P r x)) =
      Matrix.det (arithmeticFiniteAdeleCyclicSplittingMap P r x) := by
  rw [(arithmeticFiniteAdeleSplittingFrobenius P r).map_det]
  change Matrix.det
      ((arithmeticFiniteAdeleCyclicSplittingMap P r x).map
        (arithmeticFiniteAdeleSplittingFrobenius P r).toRingHom) = _
  rw [show (arithmeticFiniteAdeleCyclicSplittingMap P r x).map
        (arithmeticFiniteAdeleSplittingFrobenius P r).toRingHom =
      arithmeticFiniteAdeleCyclicGeneratorMatrix P r *
        arithmeticFiniteAdeleCyclicSplittingMap P r x *
          arithmeticFiniteAdeleCyclicGeneratorInverseMatrix P r by
      exact arithmeticFiniteAdeleCyclicSplittingMap_frobenius P r x]
  rw [Matrix.det_mul, Matrix.det_mul]
  have hz : arithmeticFiniteAdeleCyclicGeneratorMatrix P r *
        arithmeticFiniteAdeleCyclicGeneratorInverseMatrix P r = 1 := by
    have h := congrArg
      (fun M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (SplittingFunctionField P r) =>
        M.map
          (splittingFunctionFieldToArithmeticFiniteAdeleSplittingRing P r))
      (cyclicGenerator_mul_inverse P r)
    simpa [arithmeticFiniteAdeleCyclicGeneratorMatrix,
      arithmeticFiniteAdeleCyclicGeneratorInverseMatrix,
      Matrix.map_mul] using h
  calc
    Matrix.det (arithmeticFiniteAdeleCyclicGeneratorMatrix P r) *
          Matrix.det (arithmeticFiniteAdeleCyclicSplittingMap P r x) *
        Matrix.det (arithmeticFiniteAdeleCyclicGeneratorInverseMatrix P r) =
      Matrix.det (arithmeticFiniteAdeleCyclicSplittingMap P r x) *
        (Matrix.det (arithmeticFiniteAdeleCyclicGeneratorMatrix P r) *
          Matrix.det
            (arithmeticFiniteAdeleCyclicGeneratorInverseMatrix P r)) := by
      ac_rfl
    _ = _ := by rw [← Matrix.det_mul, hz, Matrix.det_one, mul_one]
noncomputable def SplittingFunctionFieldFrobeniusFixedSubspace
    (P : BasePrime) (r : Rank) :=
  LinearMap.eqLocus (splittingFunctionFieldFrobenius P r).toLinearMap
    (LinearMap.id : SplittingFunctionField P r →ₗ[FunctionField P]
      SplittingFunctionField P r)
noncomputable def functionFieldToSplittingFrobeniusFixed
    (P : BasePrime) (r : Rank) :
    FunctionField P →ₗ[FunctionField P]
      SplittingFunctionFieldFrobeniusFixedSubspace P r where
  toFun a := ⟨functionFieldEmbedding P r a,
    splittingFunctionFieldFrobeniusRingEquiv_functionFieldEmbedding P r a⟩
  map_add' a b := by
    apply Subtype.ext
    simp
  map_smul' a b := by
    apply Subtype.ext
    change functionFieldEmbedding P r (a * b) =
      algebraMap (FunctionField P) (SplittingFunctionField P r) a *
        functionFieldEmbedding P r b
    rw [map_mul]
    rfl
theorem functionFieldToSplittingFrobeniusFixed_bijective
    (P : BasePrime) (r : Rank) :
    Function.Bijective (functionFieldToSplittingFrobeniusFixed P r) := by
  constructor
  · intro a b h
    apply (functionFieldEmbedding P r).injective
    exact congrArg Subtype.val h
  · intro x
    obtain ⟨a, ha⟩ := exists_eq_functionFieldEmbedding_of_frobenius_eq
      P r x x.property
    refine ⟨a, ?_⟩
    apply Subtype.ext
    exact ha
noncomputable def functionFieldEquivSplittingFrobeniusFixed
    (P : BasePrime) (r : Rank) :
    FunctionField P ≃ₗ[FunctionField P]
      SplittingFunctionFieldFrobeniusFixedSubspace P r :=
  LinearEquiv.ofBijective
    (functionFieldToSplittingFrobeniusFixed P r)
    (functionFieldToSplittingFrobeniusFixed_bijective P r)
noncomputable def arithmeticFiniteAdeleSplittingFrobeniusLinear
    (P : BasePrime) (r : Rank) :
    ArithmeticFiniteAdeleSplittingRing P r
      →ₗ[ArithmeticFiniteAdeleRing P]
        ArithmeticFiniteAdeleSplittingRing P r :=
  TensorProduct.AlgebraTensorModule.lTensor (ArithmeticFiniteAdeleRing P)
    (ArithmeticFiniteAdeleRing P)
    (splittingFunctionFieldFrobenius P r).toLinearMap
noncomputable def arithmeticFiniteAdeleSplittingIdentityLinear
    (P : BasePrime) (r : Rank) :
    ArithmeticFiniteAdeleSplittingRing P r
      →ₗ[ArithmeticFiniteAdeleRing P]
        ArithmeticFiniteAdeleSplittingRing P r :=
  TensorProduct.AlgebraTensorModule.lTensor (ArithmeticFiniteAdeleRing P)
    (ArithmeticFiniteAdeleRing P)
    (LinearMap.id : SplittingFunctionField P r →ₗ[FunctionField P]
      SplittingFunctionField P r)
theorem arithmeticFiniteAdeleSplittingFrobeniusLinear_eq
    (P : BasePrime) (r : Rank) :
    arithmeticFiniteAdeleSplittingFrobeniusLinear P r =
      (arithmeticFiniteAdeleSplittingFrobenius P r).toLinearMap := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro a x
  simp [arithmeticFiniteAdeleSplittingFrobeniusLinear,
    arithmeticFiniteAdeleSplittingFrobenius]
theorem arithmeticFiniteAdeleSplittingIdentityLinear_eq
    (P : BasePrime) (r : Rank) :
    arithmeticFiniteAdeleSplittingIdentityLinear P r = LinearMap.id := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro a x
  simp [arithmeticFiniteAdeleSplittingIdentityLinear]
noncomputable def arithmeticFiniteAdeleFixedTensorCollapse
    (P : BasePrime) (r : Rank) :
    (ArithmeticFiniteAdeleRing P ⊗[FunctionField P]
        (SplittingFunctionFieldFrobeniusFixedSubspace P r))
      →ₗ[ArithmeticFiniteAdeleRing P] ArithmeticFiniteAdeleRing P :=
  (TensorProduct.AlgebraTensorModule.rid (FunctionField P)
      (ArithmeticFiniteAdeleRing P) (ArithmeticFiniteAdeleRing P)) ∘ₗ
    (LinearEquiv.baseChange (FunctionField P) (ArithmeticFiniteAdeleRing P)
      (SplittingFunctionFieldFrobeniusFixedSubspace P r) (FunctionField P)
      (functionFieldEquivSplittingFrobeniusFixed P r).symm).toLinearMap
@[simp] theorem arithmeticFiniteAdeleFixedTensorCollapse_tmul
    (P : BasePrime) (r : Rank)
    (a : ArithmeticFiniteAdeleRing P)
    (x : SplittingFunctionFieldFrobeniusFixedSubspace P r) :
    arithmeticFiniteAdeleFixedTensorCollapse P r
        (a ⊗ₜ[FunctionField P] x) =
      (functionFieldEquivSplittingFrobeniusFixed P r).symm x • a := by
  simp [arithmeticFiniteAdeleFixedTensorCollapse]
theorem arithmeticFiniteAdeleTensorFixed_val_eq
    (P : BasePrime) (r : Rank)
    (y : ArithmeticFiniteAdeleRing P ⊗[FunctionField P]
      (SplittingFunctionFieldFrobeniusFixedSubspace P r)) :
    ((LinearMap.tensorEqLocus
        (ArithmeticFiniteAdeleRing P) (ArithmeticFiniteAdeleRing P)
        (splittingFunctionFieldFrobenius P r).toLinearMap
        (LinearMap.id : SplittingFunctionField P r →ₗ[FunctionField P]
          SplittingFunctionField P r) y :
      LinearMap.eqLocus
        (arithmeticFiniteAdeleSplittingFrobeniusLinear P r)
        (arithmeticFiniteAdeleSplittingIdentityLinear P r)) :
        ArithmeticFiniteAdeleSplittingRing P r) =
      algebraMap (ArithmeticFiniteAdeleRing P)
        (ArithmeticFiniteAdeleSplittingRing P r)
          (arithmeticFiniteAdeleFixedTensorCollapse P r y) := by
  let lhs := (LinearMap.eqLocus
    (arithmeticFiniteAdeleSplittingFrobeniusLinear P r)
    (arithmeticFiniteAdeleSplittingIdentityLinear P r)).subtype.comp
      (LinearMap.tensorEqLocus
        (ArithmeticFiniteAdeleRing P) (ArithmeticFiniteAdeleRing P)
        (splittingFunctionFieldFrobenius P r).toLinearMap
        (LinearMap.id : SplittingFunctionField P r →ₗ[FunctionField P]
          SplittingFunctionField P r))
  let rhs := (Algebra.linearMap (ArithmeticFiniteAdeleRing P)
    (ArithmeticFiniteAdeleSplittingRing P r)).comp
      (arithmeticFiniteAdeleFixedTensorCollapse P r)
  have hmaps : lhs = rhs := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro a x
    change TensorProduct.tmul (FunctionField P) a x.1 =
      algebraMap (ArithmeticFiniteAdeleRing P)
        (ArithmeticFiniteAdeleSplittingRing P r)
          ((functionFieldEquivSplittingFrobeniusFixed P r).symm x • a)
    have hxdesc :=
      (functionFieldEquivSplittingFrobeniusFixed P r).apply_symm_apply x
    have hxval := congrArg Subtype.val hxdesc
    change TensorProduct.tmul (FunctionField P) a x.1 =
      TensorProduct.tmul (FunctionField P)
        ((functionFieldEquivSplittingFrobeniusFixed P r).symm x • a) 1
    change functionFieldEmbedding P r
        ((functionFieldEquivSplittingFrobeniusFixed P r).symm x) = x.1
      at hxval
    rw [← hxval]
    rw [show functionFieldEmbedding P r
          ((functionFieldEquivSplittingFrobeniusFixed P r).symm x) =
        (functionFieldEquivSplittingFrobeniusFixed P r).symm x •
          (1 : SplittingFunctionField P r) by
      change functionFieldEmbedding P r
          ((functionFieldEquivSplittingFrobeniusFixed P r).symm x) =
        functionFieldEmbedding P r
          ((functionFieldEquivSplittingFrobeniusFixed P r).symm x) * 1
      rw [mul_one]]
    rw [TensorProduct.tmul_smul]
    rfl
  exact DFunLike.congr_fun hmaps y
theorem exists_eq_arithmeticFiniteAdele_algebraMap_of_frobenius_eq
    (P : BasePrime) (r : Rank)
    (x : ArithmeticFiniteAdeleSplittingRing P r)
    (hx : arithmeticFiniteAdeleSplittingFrobenius P r x = x) :
    ∃ a : ArithmeticFiniteAdeleRing P,
      algebraMap (ArithmeticFiniteAdeleRing P)
        (ArithmeticFiniteAdeleSplittingRing P r) a = x := by
  let xfixed : LinearMap.eqLocus
      (arithmeticFiniteAdeleSplittingFrobeniusLinear P r)
      (arithmeticFiniteAdeleSplittingIdentityLinear P r) := ⟨x, by
    rw [arithmeticFiniteAdeleSplittingFrobeniusLinear_eq,
      arithmeticFiniteAdeleSplittingIdentityLinear_eq]
    exact hx⟩
  let eqv := LinearMap.tensorEqLocusEquiv
    (ArithmeticFiniteAdeleRing P) (ArithmeticFiniteAdeleRing P)
    (splittingFunctionFieldFrobenius P r).toLinearMap
    (LinearMap.id : SplittingFunctionField P r →ₗ[FunctionField P]
      SplittingFunctionField P r)
  let y := eqv.symm xfixed
  refine ⟨arithmeticFiniteAdeleFixedTensorCollapse P r y, ?_⟩
  have hback := congrArg Subtype.val (eqv.apply_symm_apply xfixed)
  calc
    algebraMap (ArithmeticFiniteAdeleRing P)
        (ArithmeticFiniteAdeleSplittingRing P r)
          (arithmeticFiniteAdeleFixedTensorCollapse P r y) =
      ((LinearMap.tensorEqLocus
        (ArithmeticFiniteAdeleRing P) (ArithmeticFiniteAdeleRing P)
        (splittingFunctionFieldFrobenius P r).toLinearMap
        (LinearMap.id : SplittingFunctionField P r →ₗ[FunctionField P]
          SplittingFunctionField P r) y :
        LinearMap.eqLocus
          (arithmeticFiniteAdeleSplittingFrobeniusLinear P r)
          (arithmeticFiniteAdeleSplittingIdentityLinear P r)) :
          ArithmeticFiniteAdeleSplittingRing P r) :=
      (arithmeticFiniteAdeleTensorFixed_val_eq P r y).symm
    _ = x := hback
noncomputable def arithmeticFiniteAdeleCyclicUnitToGL
    (P : BasePrime) (r : Rank) :
    (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ →*
      Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (ArithmeticFiniteAdeleSplittingRing P r) :=
  Units.map (arithmeticFiniteAdeleCyclicSplittingMap P r).toRingHom
noncomputable def arithmeticFiniteAdeleCyclicReducedNorm
    (P : BasePrime) (r : Rank) :
    (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ →*
      (ArithmeticFiniteAdeleSplittingRing P r)ˣ :=
  Matrix.GeneralLinearGroup.det.comp
    (arithmeticFiniteAdeleCyclicUnitToGL P r)
theorem arithmeticFiniteAdeleToSplittingRing_injective
    (P : BasePrime) (r : Rank) :
    Function.Injective
      (algebraMap (ArithmeticFiniteAdeleRing P)
        (ArithmeticFiniteAdeleSplittingRing P r)) :=
  Algebra.TensorProduct.includeLeft_injective
    (R := FunctionField P)
    (S := ArithmeticFiniteAdeleRing P)
    (A := ArithmeticFiniteAdeleRing P)
    (B := SplittingFunctionField P r)
    (algebraMap (FunctionField P) (SplittingFunctionField P r)).injective
noncomputable def arithmeticFiniteAdeleCyclicBaseReducedNormValue
    (P : BasePrime) (r : Rank)
    (x : ArithmeticFiniteAdeleCyclicAlgebra P r) :
    ArithmeticFiniteAdeleRing P :=
  Classical.choose
    (exists_eq_arithmeticFiniteAdele_algebraMap_of_frobenius_eq P r
      (Matrix.det (arithmeticFiniteAdeleCyclicSplittingMap P r x))
      (arithmeticFiniteAdeleCyclicSplitting_det_frobenius P r x))
theorem algebraMap_arithmeticFiniteAdeleCyclicBaseReducedNormValue
    (P : BasePrime) (r : Rank)
    (x : ArithmeticFiniteAdeleCyclicAlgebra P r) :
    algebraMap (ArithmeticFiniteAdeleRing P)
        (ArithmeticFiniteAdeleSplittingRing P r)
        (arithmeticFiniteAdeleCyclicBaseReducedNormValue P r x) =
      Matrix.det (arithmeticFiniteAdeleCyclicSplittingMap P r x) :=
  Classical.choose_spec
    (exists_eq_arithmeticFiniteAdele_algebraMap_of_frobenius_eq P r
      (Matrix.det (arithmeticFiniteAdeleCyclicSplittingMap P r x))
      (arithmeticFiniteAdeleCyclicSplitting_det_frobenius P r x))
@[simp] theorem arithmeticFiniteAdeleCyclicBaseReducedNormValue_one
    (P : BasePrime) (r : Rank) :
    arithmeticFiniteAdeleCyclicBaseReducedNormValue P r 1 = 1 := by
  apply arithmeticFiniteAdeleToSplittingRing_injective P r
  rw [algebraMap_arithmeticFiniteAdeleCyclicBaseReducedNormValue]
  change Matrix.det (arithmeticFiniteAdeleCyclicSplittingMap P r
      (1 : ArithmeticFiniteAdeleCyclicAlgebra P r)) =
    (1 : ArithmeticFiniteAdeleSplittingRing P r)
  rw [map_one, Matrix.det_one]
theorem arithmeticFiniteAdeleCyclicBaseReducedNormValue_mul
    (P : BasePrime) (r : Rank)
    (x y : ArithmeticFiniteAdeleCyclicAlgebra P r) :
    arithmeticFiniteAdeleCyclicBaseReducedNormValue P r (x * y) =
      arithmeticFiniteAdeleCyclicBaseReducedNormValue P r x *
        arithmeticFiniteAdeleCyclicBaseReducedNormValue P r y := by
  apply arithmeticFiniteAdeleToSplittingRing_injective P r
  calc
    algebraMap (ArithmeticFiniteAdeleRing P)
        (ArithmeticFiniteAdeleSplittingRing P r)
        (arithmeticFiniteAdeleCyclicBaseReducedNormValue P r (x * y)) =
      Matrix.det (arithmeticFiniteAdeleCyclicSplittingMap P r (x * y)) :=
        algebraMap_arithmeticFiniteAdeleCyclicBaseReducedNormValue P r (x * y)
    _ = Matrix.det (arithmeticFiniteAdeleCyclicSplittingMap P r x) *
        Matrix.det (arithmeticFiniteAdeleCyclicSplittingMap P r y) := by
      rw [map_mul, Matrix.det_mul]
    _ = algebraMap (ArithmeticFiniteAdeleRing P)
        (ArithmeticFiniteAdeleSplittingRing P r)
          (arithmeticFiniteAdeleCyclicBaseReducedNormValue P r x *
            arithmeticFiniteAdeleCyclicBaseReducedNormValue P r y) := by
      rw [map_mul,
        algebraMap_arithmeticFiniteAdeleCyclicBaseReducedNormValue,
        algebraMap_arithmeticFiniteAdeleCyclicBaseReducedNormValue]
noncomputable def arithmeticFiniteAdeleCyclicBaseReducedNorm
    (P : BasePrime) (r : Rank) :
    (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ →*
      (ArithmeticFiniteAdeleRing P)ˣ where
  toFun u :=
    ⟨arithmeticFiniteAdeleCyclicBaseReducedNormValue P r u,
      arithmeticFiniteAdeleCyclicBaseReducedNormValue P r
        ((u⁻¹ : (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ) :
          ArithmeticFiniteAdeleCyclicAlgebra P r), by
        rw [← arithmeticFiniteAdeleCyclicBaseReducedNormValue_mul]
        have hu : (u : ArithmeticFiniteAdeleCyclicAlgebra P r) *
            ((u⁻¹ : (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ) :
              ArithmeticFiniteAdeleCyclicAlgebra P r) = 1 :=
          congrArg Units.val (mul_inv_cancel u)
        rw [hu, arithmeticFiniteAdeleCyclicBaseReducedNormValue_one], by
        rw [← arithmeticFiniteAdeleCyclicBaseReducedNormValue_mul]
        have hu :
            ((u⁻¹ : (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ) :
              ArithmeticFiniteAdeleCyclicAlgebra P r) *
              (u : ArithmeticFiniteAdeleCyclicAlgebra P r) = 1 :=
          congrArg Units.val (inv_mul_cancel u)
        rw [hu, arithmeticFiniteAdeleCyclicBaseReducedNormValue_one]⟩
  map_one' := by
    apply Units.ext
    exact arithmeticFiniteAdeleCyclicBaseReducedNormValue_one P r
  map_mul' u v := by
    apply Units.ext
    exact arithmeticFiniteAdeleCyclicBaseReducedNormValue_mul P r u v
theorem arithmeticFiniteAdeleCyclicReducedNorm_eq_baseChange
    (P : BasePrime) (r : Rank)
    (u : (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ) :
    arithmeticFiniteAdeleCyclicReducedNorm P r u =
      Units.map
        (algebraMap (ArithmeticFiniteAdeleRing P)
          (ArithmeticFiniteAdeleSplittingRing P r))
        (arithmeticFiniteAdeleCyclicBaseReducedNorm P r u) := by
  apply Units.ext
  exact
    (algebraMap_arithmeticFiniteAdeleCyclicBaseReducedNormValue P r u).symm
theorem arithmeticFiniteAdeleCyclicReducedNorm_eq_one_iff_base
    (P : BasePrime) (r : Rank)
    (u : (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ) :
    arithmeticFiniteAdeleCyclicReducedNorm P r u = 1 ↔
      arithmeticFiniteAdeleCyclicBaseReducedNorm P r u = 1 := by
  rw [arithmeticFiniteAdeleCyclicReducedNorm_eq_baseChange]
  constructor
  · intro h
    apply Units.ext
    apply arithmeticFiniteAdeleToSplittingRing_injective P r
    exact congrArg Units.val h
  · intro h
    rw [h, map_one]
noncomputable def ArithmeticFiniteAdeleCyclicNormOne
    (P : BasePrime) (r : Rank) :
    Subgroup (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ :=
  (arithmeticFiniteAdeleCyclicReducedNorm P r).ker
@[simp] theorem arithmeticFiniteAdeleCyclicSplittingMap_diagonal
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r) :
    arithmeticFiniteAdeleCyclicSplittingMap P r
        (cyclicAlgebraToArithmeticFiniteAdeles P r x) =
      (splittingFunctionFieldToArithmeticFiniteAdeleSplittingRing P r).mapMatrix
        x.1 := by
  rw [cyclicAlgebraToArithmeticFiniteAdeles_apply,
    arithmeticFiniteAdeleCyclicSplittingMap,
    Algebra.TensorProduct.lift_tmul]
  simp [cyclicAlgebraToArithmeticFiniteAdeleSplittingMatrix]
theorem arithmeticFiniteAdeleCyclicReducedNorm_diagonal
    (P : BasePrime) (r : Rank) (u : (CyclicAlgebra P r)ˣ) :
    arithmeticFiniteAdeleCyclicReducedNorm P r
        (cyclicAlgebraUnitToArithmeticFiniteAdeles P r u) =
      Units.map
        (splittingFunctionFieldToArithmeticFiniteAdeleSplittingRing P r).toRingHom.toMonoidHom
        (cyclicAlgebraSplitReducedNorm P r u) := by
  apply Units.ext
  change Matrix.det
      (arithmeticFiniteAdeleCyclicSplittingMap P r
        (cyclicAlgebraToArithmeticFiniteAdeles P r
          (u : CyclicAlgebra P r))) =
    splittingFunctionFieldToArithmeticFiniteAdeleSplittingRing P r
      (Matrix.det (u : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r)))
  rw [arithmeticFiniteAdeleCyclicSplittingMap_diagonal]
  exact
    ((splittingFunctionFieldToArithmeticFiniteAdeleSplittingRing P r).map_det
      (u : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r))).symm
noncomputable def cyclicAlgebraNormOneToArithmeticFiniteAdeleNormOne
    (P : BasePrime) (r : Rank) :
    CyclicAlgebraNormOne P r →* ArithmeticFiniteAdeleCyclicNormOne P r where
  toFun u := ⟨cyclicAlgebraUnitToArithmeticFiniteAdeles P r u, by
    change arithmeticFiniteAdeleCyclicReducedNorm P r
      (cyclicAlgebraUnitToArithmeticFiniteAdeles P r u) = 1
    rw [arithmeticFiniteAdeleCyclicReducedNorm_diagonal]
    change Units.map
      (splittingFunctionFieldToArithmeticFiniteAdeleSplittingRing P r).toRingHom.toMonoidHom
        (cyclicAlgebraSplitReducedNorm P r u) = 1
    have hu : (u : (CyclicAlgebra P r)ˣ) ∈
        CyclicAlgebraSplitNormOne P r := by
      rw [cyclicAlgebraSplitNormOne_eq_normOne]
      exact u.property
    rw [hu, map_one]⟩
  map_one' := Subtype.ext
    (map_one (cyclicAlgebraUnitToArithmeticFiniteAdeles P r))
  map_mul' u v := Subtype.ext
    (map_mul (cyclicAlgebraUnitToArithmeticFiniteAdeles P r)
      (u : (CyclicAlgebra P r)ˣ) (v : (CyclicAlgebra P r)ˣ))
noncomputable def ArithmeticFiniteAdeleCyclicIntegralNormOneSet
    (P : BasePrime) (r : Rank) :
    Set (ArithmeticFiniteAdeleCyclicNormOne P r) :=
  {u |
    ((u : (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ) :
        ArithmeticFiniteAdeleCyclicAlgebra P r) ∈
      ArithmeticFiniteAdeleCyclicIntegralLattice P r ∧
    (((u : (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ)⁻¹ :
        (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ) :
        ArithmeticFiniteAdeleCyclicAlgebra P r) ∈
      ArithmeticFiniteAdeleCyclicIntegralLattice P r}
noncomputable def cyclicAlgebraNormOneDenominatorPlaces
    (P : BasePrime) (r : Rank) (u : CyclicAlgebraNormOne P r) :
    Set (IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P)) :=
  arithmeticFiniteAdeleCyclicUnitDenominatorPlaces P r
    (cyclicAlgebraUnitToArithmeticFiniteAdeles P r u)
noncomputable def cartwrightStegerOrderUnitOfLifts
    (P : BasePrime) (r : Rank) (u : (CyclicAlgebra P r)ˣ)
    (v vInv : CartwrightStegerOrder P r)
    (hv : cartwrightStegerOrderToCyclicAlgebra P r v =
      (u : CyclicAlgebra P r))
    (hvInv : cartwrightStegerOrderToCyclicAlgebra P r vInv =
      (↑(u⁻¹) : CyclicAlgebra P r)) :
    (CartwrightStegerOrder P r)ˣ where
  val := v
  inv := vInv
  val_inv := by
    apply cartwrightStegerOrderToCyclicAlgebra_injective P r
    calc
      cartwrightStegerOrderToCyclicAlgebra P r (v * vInv) =
          cartwrightStegerOrderToCyclicAlgebra P r v *
            cartwrightStegerOrderToCyclicAlgebra P r vInv :=
        map_mul (cartwrightStegerOrderToCyclicAlgebra P r) v vInv
      _ = (u : CyclicAlgebra P r) *
          (↑(u⁻¹) : CyclicAlgebra P r) :=
        congrArg₂ (· * ·) hv hvInv
      _ = 1 := u.val_inv
      _ = cartwrightStegerOrderToCyclicAlgebra P r 1 :=
        (map_one (cartwrightStegerOrderToCyclicAlgebra P r)).symm
  inv_val := by
    apply cartwrightStegerOrderToCyclicAlgebra_injective P r
    calc
      cartwrightStegerOrderToCyclicAlgebra P r (vInv * v) =
          cartwrightStegerOrderToCyclicAlgebra P r vInv *
            cartwrightStegerOrderToCyclicAlgebra P r v :=
        map_mul (cartwrightStegerOrderToCyclicAlgebra P r) vInv v
      _ = (↑(u⁻¹) : CyclicAlgebra P r) *
          (u : CyclicAlgebra P r) :=
        congrArg₂ (· * ·) hvInv hv
      _ = 1 := u.inv_val
      _ = cartwrightStegerOrderToCyclicAlgebra P r 1 :=
        (map_one (cartwrightStegerOrderToCyclicAlgebra P r)).symm
theorem orderUnitToCyclicUnit_orderUnitOfLifts
    (P : BasePrime) (r : Rank) (u : (CyclicAlgebra P r)ˣ)
    (v vInv : CartwrightStegerOrder P r)
    (hv : cartwrightStegerOrderToCyclicAlgebra P r v =
      (u : CyclicAlgebra P r))
    (hvInv : cartwrightStegerOrderToCyclicAlgebra P r vInv =
      (↑(u⁻¹) : CyclicAlgebra P r)) :
    orderUnitToCyclicUnit P r
        (cartwrightStegerOrderUnitOfLifts P r u v vInv hv hvInv) = u := by
  apply Units.ext
  exact hv
theorem exists_cartwrightStegerOrderUnit_of_finiteAdele_integral
    (P : BasePrime) (r : Rank) (u : (CyclicAlgebra P r)ˣ)
    (hu : (cyclicAlgebraUnitToArithmeticFiniteAdeles P r u :
        ArithmeticFiniteAdeleCyclicAlgebra P r) ∈
      ArithmeticFiniteAdeleCyclicIntegralLattice P r)
    (huInv : (cyclicAlgebraUnitToArithmeticFiniteAdeles P r u⁻¹ :
        ArithmeticFiniteAdeleCyclicAlgebra P r) ∈
      ArithmeticFiniteAdeleCyclicIntegralLattice P r) :
    ∃ v : (CartwrightStegerOrder P r)ˣ,
      orderUnitToCyclicUnit P r v = u := by
  have huSpan : (u : CyclicAlgebra P r) ∈ arithmeticCyclicSpan P r :=
    (cyclicAlgebraToArithmeticFiniteAdeles_mem_integralLattice_iff
      P r (u : CyclicAlgebra P r)).mp hu
  have huInvSpan : (↑(u⁻¹) : CyclicAlgebra P r) ∈
      arithmeticCyclicSpan P r :=
    (cyclicAlgebraToArithmeticFiniteAdeles_mem_integralLattice_iff
      P r (↑(u⁻¹) : CyclicAlgebra P r)).mp huInv
  obtain ⟨v, hv⟩ :=
    exists_cartwrightStegerOrder_of_mem_arithmeticCyclicSpan
      P r (u : CyclicAlgebra P r) huSpan
  obtain ⟨vInv, hvInv⟩ :=
    exists_cartwrightStegerOrder_of_mem_arithmeticCyclicSpan
      P r (↑(u⁻¹) : CyclicAlgebra P r) huInvSpan
  exact ⟨cartwrightStegerOrderUnitOfLifts P r u v vInv hv hvInv,
    orderUnitToCyclicUnit_orderUnitOfLifts P r u v vInv hv hvInv⟩
theorem orderUnitToArithmeticFiniteAdeles_mem_integralLattice
    (P : BasePrime) (r : Rank) (u : (CartwrightStegerOrder P r)ˣ) :
    (cyclicAlgebraUnitToArithmeticFiniteAdeles P r
        (orderUnitToCyclicUnit P r u) :
      ArithmeticFiniteAdeleCyclicAlgebra P r) ∈
        ArithmeticFiniteAdeleCyclicIntegralLattice P r := by
  rw [cyclicAlgebraUnitToArithmeticFiniteAdeles_coe]
  apply cyclicAlgebraToArithmeticFiniteAdeles_mem_integralLattice
  exact cartwrightStegerOrderToCyclic_mem_arithmeticCyclicSpan P r u.1
noncomputable def cyclicAlgebraNormOneToArithmeticFiniteAdeles
    (P : BasePrime) (r : Rank) :
    CyclicAlgebraNormOne P r →*
      (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ :=
  (cyclicAlgebraUnitToArithmeticFiniteAdeles P r).comp
    (CyclicAlgebraNormOne P r).subtype
theorem orderNormOneInnerFormToArithmeticFiniteAdeles_mem_integralLattice
    (P : BasePrime) (r : Rank) (s : OrderNormOneInnerForm P r) :
    (cyclicAlgebraNormOneToArithmeticFiniteAdeles P r
        (orderNormOneInnerFormToCyclicAlgebraNormOne P r s) :
      ArithmeticFiniteAdeleCyclicAlgebra P r) ∈
        ArithmeticFiniteAdeleCyclicIntegralLattice P r := by
  change (cyclicAlgebraUnitToArithmeticFiniteAdeles P r
      (orderUnitToCyclicUnit P r
        (orderNormOneInnerFormToOrderUnits P r s)) :
    ArithmeticFiniteAdeleCyclicAlgebra P r) ∈
      ArithmeticFiniteAdeleCyclicIntegralLattice P r
  exact orderUnitToArithmeticFiniteAdeles_mem_integralLattice P r
    (orderNormOneInnerFormToOrderUnits P r s)
theorem exists_orderNormOneInnerForm_of_finiteAdele_integral
    (P : BasePrime) (r : Rank) (u : CyclicAlgebraNormOne P r)
    (hu : (cyclicAlgebraNormOneToArithmeticFiniteAdeles P r u :
        ArithmeticFiniteAdeleCyclicAlgebra P r) ∈
      ArithmeticFiniteAdeleCyclicIntegralLattice P r)
    (huInv : (cyclicAlgebraUnitToArithmeticFiniteAdeles P r
        ((u : (CyclicAlgebra P r)ˣ)⁻¹) :
        ArithmeticFiniteAdeleCyclicAlgebra P r) ∈
      ArithmeticFiniteAdeleCyclicIntegralLattice P r) :
    ∃ s : OrderNormOneInnerForm P r,
      orderNormOneInnerFormToCyclicAlgebraNormOne P r s = u := by
  obtain ⟨v, hv⟩ :=
    exists_cartwrightStegerOrderUnit_of_finiteAdele_integral
      P r (u : (CyclicAlgebra P r)ˣ) hu huInv
  have hvNorm : v ∈ CartwrightStegerBaseNormOneOrderUnits P r := by
    change cyclicAlgebraReducedNorm P r
      (orderUnitToCyclicUnit P r v) = 1
    rw [hv]
    exact u.property
  let vn : CartwrightStegerBaseNormOneOrderUnits P r := ⟨v, hvNorm⟩
  let s : OrderNormOneInnerForm P r :=
    (orderNormOneInnerFormEquivBaseNormOneOrderUnits P r).symm vn
  refine ⟨s, ?_⟩
  have hs : orderNormOneInnerFormToBaseNormOneOrderUnits P r s = vn :=
    (orderNormOneInnerFormEquivBaseNormOneOrderUnits P r).apply_symm_apply vn
  have hsVal : orderNormOneInnerFormToOrderUnits P r s = v :=
    congrArg (fun w : CartwrightStegerBaseNormOneOrderUnits P r =>
      (w : (CartwrightStegerOrder P r)ˣ)) hs
  apply Subtype.ext
  change orderUnitToCyclicUnit P r
      (orderNormOneInnerFormToOrderUnits P r s) =
    (u : (CyclicAlgebra P r)ˣ)
  rw [hsVal, hv]
theorem cyclicAlgebraNormOne_finiteAdele_integral_iff_mem_range
    (P : BasePrime) (r : Rank) (u : CyclicAlgebraNormOne P r) :
    ((cyclicAlgebraNormOneToArithmeticFiniteAdeles P r u :
          ArithmeticFiniteAdeleCyclicAlgebra P r) ∈
        ArithmeticFiniteAdeleCyclicIntegralLattice P r ∧
      (cyclicAlgebraUnitToArithmeticFiniteAdeles P r
          ((u : (CyclicAlgebra P r)ˣ)⁻¹) :
          ArithmeticFiniteAdeleCyclicAlgebra P r) ∈
        ArithmeticFiniteAdeleCyclicIntegralLattice P r) ↔
      u ∈ (orderNormOneInnerFormToCyclicAlgebraNormOne P r).range := by
  constructor
  · rintro ⟨hu, huInv⟩
    exact exists_orderNormOneInnerForm_of_finiteAdele_integral
      P r u hu huInv
  · rintro ⟨s, rfl⟩
    constructor
    · exact
        orderNormOneInnerFormToArithmeticFiniteAdeles_mem_integralLattice
          P r s
    · have hsInv :=
        orderNormOneInnerFormToArithmeticFiniteAdeles_mem_integralLattice
          P r s⁻¹
      simp only [map_inv] at hsInv ⊢
      exact hsInv
theorem cyclicAlgebraNormOne_preimage_integralNormOneSet
    (P : BasePrime) (r : Rank) (u : CyclicAlgebraNormOne P r) :
    cyclicAlgebraNormOneToArithmeticFiniteAdeleNormOne P r u ∈
        ArithmeticFiniteAdeleCyclicIntegralNormOneSet P r ↔
      u ∈ (orderNormOneInnerFormToCyclicAlgebraNormOne P r).range := by
  exact cyclicAlgebraNormOne_finiteAdele_integral_iff_mem_range P r u
noncomputable def orderNormOneInnerFormToArithmeticFiniteAdeleNormOne
    (P : BasePrime) (r : Rank) :
    OrderNormOneInnerForm P r →*
      ArithmeticFiniteAdeleCyclicNormOne P r :=
  (cyclicAlgebraNormOneToArithmeticFiniteAdeleNormOne P r).comp
    (orderNormOneInnerFormToCyclicAlgebraNormOne P r)
theorem orderNormOneInnerFormToCyclicAlgebraNormOne_injective
    (P : BasePrime) (r : Rank) :
    Function.Injective
      (orderNormOneInnerFormToCyclicAlgebraNormOne P r) := by
  intro s t hst
  apply orderNormOneInnerFormToOrderUnits_injective P r
  apply Units.ext
  apply cartwrightStegerOrderToCyclicAlgebra_injective P r
  exact congrArg
    (fun u : CyclicAlgebraNormOne P r =>
      (((u : (CyclicAlgebra P r)ˣ) : CyclicAlgebra P r))) hst
noncomputable def orderNormOneInnerFormEquivGlobalIntegralRange
    (P : BasePrime) (r : Rank) :
    OrderNormOneInnerForm P r ≃*
      (orderNormOneInnerFormToCyclicAlgebraNormOne P r).range :=
  MulEquiv.ofBijective
    (orderNormOneInnerFormToCyclicAlgebraNormOne P r).rangeRestrict
    ⟨fun _ _ h =>
        orderNormOneInnerFormToCyclicAlgebraNormOne_injective P r
          (congrArg Subtype.val h),
      MonoidHom.rangeRestrict_surjective _⟩
noncomputable def orderNormOneInnerFormCyclicAlgebraPoint
    (P : BasePrime) (r : Rank) (s : OrderNormOneInnerForm P r) :
    CyclicAlgebra P r :=
  (((orderNormOneInnerFormToCyclicAlgebraNormOne P r s :
      CyclicAlgebraNormOne P r) : (CyclicAlgebra P r)ˣ) :
    CyclicAlgebra P r)
theorem orderNormOneInnerFormCyclicAlgebraPoint_coe
    (P : BasePrime) (r : Rank) (s : OrderNormOneInnerForm P r) :
    (orderNormOneInnerFormCyclicAlgebraPoint P r s :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r)) =
      ((s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
          (ConstantArithmeticRing P r)) :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (ConstantArithmeticRing P r)).map
        (constantArithmeticToSplittingFunctionField P r) := by
  rfl
theorem orderNormOneInnerFormCyclicAlgebraPoint_mem_arithmeticCyclicSpan
    (P : BasePrime) (r : Rank) (s : OrderNormOneInnerForm P r) :
    orderNormOneInnerFormCyclicAlgebraPoint P r s ∈
      arithmeticCyclicSpan P r := by
  change cartwrightStegerOrderToCyclicAlgebra P r
      (orderNormOneInnerFormToOrderUnits P r s).1 ∈
        arithmeticCyclicSpan P r
  exact cartwrightStegerOrderToCyclic_mem_arithmeticCyclicSpan P r
    (orderNormOneInnerFormToOrderUnits P r s).1
theorem arithmeticCyclicCoordinateMatrix_orderNormOneInnerForm
    (P : BasePrime) (r : Rank) (s : OrderNormOneInnerForm P r) :
    arithmeticCyclicCoordinateMatrix P r
        (orderNormOneInnerFormCyclicAlgebraPoint P r s)
        (orderNormOneInnerFormCyclicAlgebraPoint_mem_arithmeticCyclicSpan
          P r s) =
      ((s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
          (ConstantArithmeticRing P r)) :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (ConstantArithmeticRing P r)) := by
  apply Matrix.map_injective
    (constantArithmeticToSplittingFunctionField_injective P r)
  change (arithmeticCyclicCoordinateMatrix P r
      (orderNormOneInnerFormCyclicAlgebraPoint P r s)
      (orderNormOneInnerFormCyclicAlgebraPoint_mem_arithmeticCyclicSpan
        P r s)).map (constantArithmeticToSplittingFunctionField P r) =
    (((s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
        (ConstantArithmeticRing P r)) :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (ConstantArithmeticRing P r)).map
          (constantArithmeticToSplittingFunctionField P r))
  rw [arithmeticCyclicCoordinateMatrix_to_global]
  exact orderNormOneInnerFormCyclicAlgebraPoint_coe P r s
noncomputable def arithmeticFiniteAdeleAt
    (P : BasePrime)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P)) :
    ArithmeticFiniteAdeleRing P →+*
      v.adicCompletion (FunctionField P) where
  toFun a := a v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
@[simp] theorem arithmeticFiniteAdeleAt_diagonal
    (P : BasePrime)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (x : FunctionField P) :
    arithmeticFiniteAdeleAt P v
        (functionFieldToArithmeticFiniteAdeles P x) =
      algebraMap (FunctionField P)
        (v.adicCompletion (FunctionField P)) x :=
  rfl
noncomputable def arithmeticFiniteAdeleAtAlgHom
    (P : BasePrime)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P)) :
    ArithmeticFiniteAdeleRing P →ₐ[FunctionField P]
      v.adicCompletion (FunctionField P) where
  __ := arithmeticFiniteAdeleAt P v
  commutes' := arithmeticFiniteAdeleAt_diagonal P v
noncomputable abbrev ArithmeticAdicSplittingRing
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P)) :=
  TensorProduct (FunctionField P)
    (v.adicCompletion (FunctionField P)) (SplittingFunctionField P r)
noncomputable def arithmeticFiniteAdeleSplittingRingAt
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P)) :
    ArithmeticFiniteAdeleSplittingRing P r →ₐ[FunctionField P]
      ArithmeticAdicSplittingRing P r v :=
  Algebra.TensorProduct.map (arithmeticFiniteAdeleAtAlgHom P v)
    (AlgHom.id (FunctionField P) (SplittingFunctionField P r))
@[simp] theorem arithmeticFiniteAdeleSplittingRingAt_left
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (a : ArithmeticFiniteAdeleRing P) :
    arithmeticFiniteAdeleSplittingRingAt P r v
        (algebraMap (ArithmeticFiniteAdeleRing P)
          (ArithmeticFiniteAdeleSplittingRing P r) a) =
      algebraMap (v.adicCompletion (FunctionField P))
        (ArithmeticAdicSplittingRing P r v)
          (arithmeticFiniteAdeleAt P v a) := by
  change arithmeticFiniteAdeleSplittingRingAt P r v
      (TensorProduct.tmul (FunctionField P) a 1) = _
  simp [arithmeticFiniteAdeleSplittingRingAt,
    arithmeticFiniteAdeleAtAlgHom]
  rfl
theorem arithmeticFiniteAdeleCyclicBaseReducedNorm_atPlace
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (u : (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ) :
    algebraMap (v.adicCompletion (FunctionField P))
        (ArithmeticAdicSplittingRing P r v)
        (arithmeticFiniteAdeleAt P v
          (arithmeticFiniteAdeleCyclicBaseReducedNorm P r u)) =
      Matrix.det
        ((arithmeticFiniteAdeleCyclicSplittingMap P r
          (u : ArithmeticFiniteAdeleCyclicAlgebra P r)).map
            (arithmeticFiniteAdeleSplittingRingAt P r v)) := by
  calc
    algebraMap (v.adicCompletion (FunctionField P))
        (ArithmeticAdicSplittingRing P r v)
        (arithmeticFiniteAdeleAt P v
          (arithmeticFiniteAdeleCyclicBaseReducedNorm P r u)) =
      arithmeticFiniteAdeleSplittingRingAt P r v
        (algebraMap (ArithmeticFiniteAdeleRing P)
          (ArithmeticFiniteAdeleSplittingRing P r)
          (arithmeticFiniteAdeleCyclicBaseReducedNorm P r u)) := by
        symm
        exact arithmeticFiniteAdeleSplittingRingAt_left P r v _
    _ = arithmeticFiniteAdeleSplittingRingAt P r v
        (Matrix.det (arithmeticFiniteAdeleCyclicSplittingMap P r
          (u : ArithmeticFiniteAdeleCyclicAlgebra P r))) := by
      change arithmeticFiniteAdeleSplittingRingAt P r v
        (algebraMap (ArithmeticFiniteAdeleRing P)
          (ArithmeticFiniteAdeleSplittingRing P r)
            (arithmeticFiniteAdeleCyclicBaseReducedNormValue P r
              (u : ArithmeticFiniteAdeleCyclicAlgebra P r))) = _
      rw [algebraMap_arithmeticFiniteAdeleCyclicBaseReducedNormValue]
    _ = _ :=
      (arithmeticFiniteAdeleSplittingRingAt P r v).map_det
        (arithmeticFiniteAdeleCyclicSplittingMap P r
          (u : ArithmeticFiniteAdeleCyclicAlgebra P r))
noncomputable instance indexCongruenceIdealIsMaximal
    (P : BasePrime) (r : Rank) (level : Nat) :
    (IndexCongruenceIdeal P r level).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective
    (indexArithmeticEval P r level)
    (indexArithmeticEval_surjective P r level)
theorem indexPlacePolynomial_arithmetic_ne_zero
    (P : BasePrime) (r : Rank) (level : Nat) :
    algebraMap (PolynomialRing P) (ArithmeticRing P)
        (indexPlacePolynomial P r level) ≠ 0 := by
  rw [map_ne_zero_iff _ (IsLocalization.injective (ArithmeticRing P)
    (powers_le_nonZeroDivisors_of_noZeroDivisors
      (arithmeticLocalizationElement_ne_zero P)))]
  exact (indexPlacePolynomial_irreducible P r level).ne_zero
theorem indexPlacePolynomial_mem_indexCongruenceIdeal
    (P : BasePrime) (r : Rank) (level : Nat) :
    algebraMap (PolynomialRing P) (ArithmeticRing P)
        (indexPlacePolynomial P r level) ∈
      IndexCongruenceIdeal P r level := by
  change indexArithmeticEval P r level
      (algebraMap (PolynomialRing P) (ArithmeticRing P)
        (indexPlacePolynomial P r level)) = 0
  rw [indexArithmeticEval_algebraMap]
  exact minpoly.aeval (BaseField P) (indexPlaceY P r level)
theorem indexCongruenceIdeal_ne_bot
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexCongruenceIdeal P r level ≠ ⊥ := by
  intro hbot
  have hp := indexPlacePolynomial_mem_indexCongruenceIdeal P r level
  rw [hbot, Ideal.mem_bot] at hp
  exact indexPlacePolynomial_arithmetic_ne_zero P r level hp
noncomputable def indexCongruencePlace
    (P : BasePrime) (r : Rank) (level : Nat) :
    IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P) where
  asIdeal := IndexCongruenceIdeal P r level
  isPrime := RingHom.ker_isPrime (indexArithmeticEval P r level)
  ne_bot := indexCongruenceIdeal_ne_bot P r level
@[simp] theorem indexCongruencePlace_asIdeal
    (P : BasePrime) (r : Rank) (level : Nat) :
    (indexCongruencePlace P r level).asIdeal =
      IndexCongruenceIdeal P r level :=
  rfl
noncomputable abbrev IndexCongruenceAdicCompletion
    (P : BasePrime) (r : Rank) (level : Nat) :=
  (indexCongruencePlace P r level).adicCompletion (FunctionField P)
noncomputable abbrev IndexCongruenceAdicIntegers
    (P : BasePrime) (r : Rank) (level : Nat) :=
  (indexCongruencePlace P r level).adicCompletionIntegers (FunctionField P)
noncomputable def arithmeticFiniteAdeleAtIndexPlace
    (P : BasePrime) (r : Rank) (level : Nat) :
    ArithmeticFiniteAdeleRing P →+*
      IndexCongruenceAdicCompletion P r level :=
  arithmeticFiniteAdeleAt P (indexCongruencePlace P r level)
noncomputable def arithmeticFiniteAdeleSupportedAtIndexPlace
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : IndexCongruenceAdicCompletion P r level) :
    ArithmeticFiniteAdeleRing P := by
  classical
  refine ⟨Pi.single (indexCongruencePlace P r level) x, ?_⟩
  rw [Filter.eventually_cofinite]
  apply Set.Finite.subset
    (Set.finite_singleton (indexCongruencePlace P r level))
  intro v hv
  simp only [Set.mem_singleton_iff]
  by_contra hne
  apply hv
  rw [Pi.single_eq_of_ne hne]
  exact (v.adicCompletionIntegers (FunctionField P)).zero_mem
@[simp] theorem arithmeticFiniteAdeleAtIndexPlace_supported
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : IndexCongruenceAdicCompletion P r level) :
    arithmeticFiniteAdeleAtIndexPlace P r level
        (arithmeticFiniteAdeleSupportedAtIndexPlace P r level x) = x := by
  classical
  simp [arithmeticFiniteAdeleAtIndexPlace, arithmeticFiniteAdeleAt,
    arithmeticFiniteAdeleSupportedAtIndexPlace]
  exact Pi.single_eq_same (indexCongruencePlace P r level) x
theorem arithmeticFiniteAdeleAt_supportedAtIndexPlace_of_ne
    (P : BasePrime) (r : Rank) (level : Nat)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (hv : v ≠ indexCongruencePlace P r level)
    (x : IndexCongruenceAdicCompletion P r level) :
    arithmeticFiniteAdeleAt P v
        (arithmeticFiniteAdeleSupportedAtIndexPlace P r level x) = 0 := by
  classical
  change Pi.single (indexCongruencePlace P r level) x v = 0
  rw [Pi.single_eq_of_ne hv]
theorem arithmeticFiniteAdeleSupportedAtIndexPlace_mem_integral_iff
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : IndexCongruenceAdicCompletion P r level) :
    arithmeticFiniteAdeleSupportedAtIndexPlace P r level x ∈
        ArithmeticIntegralFiniteAdeles P ↔
      x ∈ IndexCongruenceAdicIntegers P r level := by
  classical
  constructor
  · intro hx
    have hselected := hx (indexCongruencePlace P r level)
    change Pi.single (indexCongruencePlace P r level) x
        (indexCongruencePlace P r level) ∈
      IndexCongruenceAdicIntegers P r level at hselected
    rw [Pi.single_eq_same] at hselected
    exact hselected
  · intro hx v
    by_cases hv : v = indexCongruencePlace P r level
    · subst v
      change Pi.single (indexCongruencePlace P r level) x
          (indexCongruencePlace P r level) ∈
        IndexCongruenceAdicIntegers P r level
      rw [Pi.single_eq_same]
      exact hx
    · change Pi.single (indexCongruencePlace P r level) x v ∈
        v.adicCompletionIntegers (FunctionField P)
      rw [Pi.single_eq_of_ne hv]
      exact (v.adicCompletionIntegers (FunctionField P)).zero_mem
noncomputable def arithmeticFiniteAdeleSupportedAtIndexPlaceNonUnitalRingHom
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexCongruenceAdicCompletion P r level →ₙ+*
      ArithmeticFiniteAdeleRing P where
  toFun := arithmeticFiniteAdeleSupportedAtIndexPlace P r level
  map_zero' := by
    apply IsDedekindDomain.FiniteAdeleRing.ext
    intro v
    classical
    change Pi.single (indexCongruencePlace P r level) 0 v = 0
    by_cases hv : v = indexCongruencePlace P r level
    · subst v
      rw [Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne hv]
  map_add' x y := by
    apply IsDedekindDomain.FiniteAdeleRing.ext
    intro v
    classical
    change Pi.single (indexCongruencePlace P r level) (x + y) v =
      Pi.single (indexCongruencePlace P r level) x v +
        Pi.single (indexCongruencePlace P r level) y v
    by_cases hv : v = indexCongruencePlace P r level
    · subst v
      simp only [Pi.single_eq_same]
    · simp only [Pi.single_eq_of_ne hv, add_zero]
  map_mul' x y := by
    apply IsDedekindDomain.FiniteAdeleRing.ext
    intro v
    classical
    change Pi.single (indexCongruencePlace P r level) (x * y) v =
      Pi.single (indexCongruencePlace P r level) x v *
        Pi.single (indexCongruencePlace P r level) y v
    by_cases hv : v = indexCongruencePlace P r level
    · subst v
      simp only [Pi.single_eq_same]
    · simp only [Pi.single_eq_of_ne hv, mul_zero]
noncomputable def arithmeticFiniteAdeleSupportedAtIndexPlaceLinearMap
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexCongruenceAdicCompletion P r level →ₗ[FunctionField P]
      ArithmeticFiniteAdeleRing P where
  toFun := arithmeticFiniteAdeleSupportedAtIndexPlace P r level
  map_add' := map_add
    (arithmeticFiniteAdeleSupportedAtIndexPlaceNonUnitalRingHom P r level)
  map_smul' c x := by
    apply IsDedekindDomain.FiniteAdeleRing.ext
    intro v
    classical
    change Pi.single (indexCongruencePlace P r level) (c • x) v =
      algebraMap (FunctionField P)
        (v.adicCompletion (FunctionField P)) c *
          Pi.single (indexCongruencePlace P r level) x v
    by_cases hv : v = indexCongruencePlace P r level
    · subst v
      simp only [Pi.single_eq_same, Algebra.smul_def]
    · simp only [Pi.single_eq_of_ne hv, mul_zero]
@[simp] theorem arithmeticFiniteAdeleAtIndexPlace_diagonal
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : FunctionField P) :
    arithmeticFiniteAdeleAtIndexPlace P r level
        (functionFieldToArithmeticFiniteAdeles P x) =
      algebraMap (FunctionField P)
        (IndexCongruenceAdicCompletion P r level) x :=
  rfl
noncomputable def arithmeticFiniteAdeleAtIndexPlaceAlgHom
    (P : BasePrime) (r : Rank) (level : Nat) :
    ArithmeticFiniteAdeleRing P →ₐ[FunctionField P]
      IndexCongruenceAdicCompletion P r level where
  __ := arithmeticFiniteAdeleAtIndexPlace P r level
  commutes' x := arithmeticFiniteAdeleAtIndexPlace_diagonal P r level x
noncomputable abbrev IndexAdicCyclicAlgebra
    (P : BasePrime) (r : Rank) (level : Nat) :=
  TensorProduct (FunctionField P)
    (IndexCongruenceAdicCompletion P r level) (CyclicAlgebra P r)
noncomputable def arithmeticFiniteAdeleCyclicAlgebraAtIndexPlace
    (P : BasePrime) (r : Rank) (level : Nat) :
    ArithmeticFiniteAdeleCyclicAlgebra P r →ₐ[FunctionField P]
      IndexAdicCyclicAlgebra P r level :=
  Algebra.TensorProduct.map
    (arithmeticFiniteAdeleAtIndexPlaceAlgHom P r level)
    (AlgHom.id (FunctionField P) (CyclicAlgebra P r))
noncomputable def arithmeticFiniteAdeleCyclicSupportedAtIndexPlace
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexAdicCyclicAlgebra P r level →ₗ[FunctionField P]
      ArithmeticFiniteAdeleCyclicAlgebra P r :=
  TensorProduct.map
    (arithmeticFiniteAdeleSupportedAtIndexPlaceLinearMap P r level)
    LinearMap.id
@[simp] theorem arithmeticFiniteAdeleCyclicAlgebraAtIndexPlace_tmul
    (P : BasePrime) (r : Rank) (level : Nat)
    (a : ArithmeticFiniteAdeleRing P) (x : CyclicAlgebra P r) :
    arithmeticFiniteAdeleCyclicAlgebraAtIndexPlace P r level
        (TensorProduct.tmul (FunctionField P) a x) =
      TensorProduct.tmul (FunctionField P)
        (arithmeticFiniteAdeleAtIndexPlace P r level a) x := by
  simp [arithmeticFiniteAdeleCyclicAlgebraAtIndexPlace,
    arithmeticFiniteAdeleAtIndexPlaceAlgHom]
  rfl
@[simp] theorem arithmeticFiniteAdeleCyclicSupportedAtIndexPlace_tmul
    (P : BasePrime) (r : Rank) (level : Nat)
    (a : IndexCongruenceAdicCompletion P r level)
    (x : CyclicAlgebra P r) :
    arithmeticFiniteAdeleCyclicSupportedAtIndexPlace P r level
        (TensorProduct.tmul (FunctionField P) a x) =
      TensorProduct.tmul (FunctionField P)
        (arithmeticFiniteAdeleSupportedAtIndexPlace P r level a) x := by
  simp [arithmeticFiniteAdeleCyclicSupportedAtIndexPlace,
    arithmeticFiniteAdeleSupportedAtIndexPlaceLinearMap]
  rfl
theorem arithmeticFiniteAdeleCyclicSplitting_supportedAtIndexPlace_of_ne
    (P : BasePrime) (r : Rank) (level : Nat)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (hv : v ≠ indexCongruencePlace P r level)
    (x : IndexAdicCyclicAlgebra P r level) :
    (arithmeticFiniteAdeleCyclicSplittingMap P r
        (arithmeticFiniteAdeleCyclicSupportedAtIndexPlace P r level x)).map
          (arithmeticFiniteAdeleSplittingRingAt P r v) = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
      rw [show arithmeticFiniteAdeleCyclicSupportedAtIndexPlace P r level
            (x + y) =
          arithmeticFiniteAdeleCyclicSupportedAtIndexPlace P r level x +
            arithmeticFiniteAdeleCyclicSupportedAtIndexPlace P r level y from
        map_add (arithmeticFiniteAdeleCyclicSupportedAtIndexPlace P r level) x y]
      rw [show arithmeticFiniteAdeleCyclicSplittingMap P r
            (arithmeticFiniteAdeleCyclicSupportedAtIndexPlace P r level x +
              arithmeticFiniteAdeleCyclicSupportedAtIndexPlace P r level y) =
          arithmeticFiniteAdeleCyclicSplittingMap P r
              (arithmeticFiniteAdeleCyclicSupportedAtIndexPlace P r level x) +
            arithmeticFiniteAdeleCyclicSplittingMap P r
              (arithmeticFiniteAdeleCyclicSupportedAtIndexPlace P r level y) from
        map_add (arithmeticFiniteAdeleCyclicSplittingMap P r) _ _]
      rw [Matrix.map_add _ (fun a b =>
        map_add (arithmeticFiniteAdeleSplittingRingAt P r v) a b),
        hx, hy, add_zero]
  | tmul a x =>
      rw [arithmeticFiniteAdeleCyclicSupportedAtIndexPlace_tmul,
        arithmeticFiniteAdeleCyclicSplittingMap,
        Algebra.TensorProduct.lift_tmul, Matrix.map_mul]
      have ha := arithmeticFiniteAdeleAt_supportedAtIndexPlace_of_ne
        P r level v hv a
      have hscalar :
          ((Algebra.ofId (ArithmeticFiniteAdeleRing P)
            (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
              (ArithmeticFiniteAdeleSplittingRing P r)))
                (arithmeticFiniteAdeleSupportedAtIndexPlace P r level a)).map
              (arithmeticFiniteAdeleSplittingRingAt P r v) = 0 := by
        ext i j
        by_cases hij : i = j
        · subst j
          simp [arithmeticFiniteAdeleSplittingRingAt,
            arithmeticFiniteAdeleAtAlgHom,
            Matrix.algebraMap_matrix_apply, ha]
          change arithmeticFiniteAdeleAt P v
            (arithmeticFiniteAdeleSupportedAtIndexPlace P r level a) ⊗ₜ[FunctionField P] 1 = 0
          rw [ha, TensorProduct.zero_tmul]
        · simp [arithmeticFiniteAdeleSplittingRingAt,
            arithmeticFiniteAdeleAtAlgHom,
            Matrix.algebraMap_matrix_apply, hij]
      rw [hscalar, zero_mul]
@[simp] theorem arithmeticFiniteAdeleCyclicAlgebraAtIndexPlace_supported
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : IndexAdicCyclicAlgebra P r level) :
    arithmeticFiniteAdeleCyclicAlgebraAtIndexPlace P r level
        (arithmeticFiniteAdeleCyclicSupportedAtIndexPlace P r level x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp [arithmeticFiniteAdeleCyclicSupportedAtIndexPlace]
  | add x y hx hy => simp [map_add, hx, hy]
  | tmul a x =>
      rw [arithmeticFiniteAdeleCyclicSupportedAtIndexPlace_tmul,
        arithmeticFiniteAdeleCyclicAlgebraAtIndexPlace_tmul,
        arithmeticFiniteAdeleAtIndexPlace_supported]
noncomputable def indexAdicCyclicBasis
    (P : BasePrime) (r : Rank) (level : Nat) :
    Module.Basis (Fin r.matrixRank × Fin r.matrixRank)
      (IndexCongruenceAdicCompletion P r level)
      (IndexAdicCyclicAlgebra P r level) :=
  (functionFieldCyclicBasis P r).baseChange
    (IndexCongruenceAdicCompletion P r level)
noncomputable def IndexAdicCyclicIntegralLattice
    (P : BasePrime) (r : Rank) (level : Nat) :
    Set (IndexAdicCyclicAlgebra P r level) :=
  {x | ∀ p, (indexAdicCyclicBasis P r level).equivFun x p ∈
    IndexCongruenceAdicIntegers P r level}
theorem indexAdicCyclicBasis_equivFun_diagonal
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : CyclicAlgebra P r)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    (indexAdicCyclicBasis P r level).equivFun
        (TensorProduct.tmul (FunctionField P) 1 x) p =
      algebraMap (FunctionField P)
        (IndexCongruenceAdicCompletion P r level)
          ((functionFieldCyclicBasis P r).equivFun x p) := by
  rw [Module.Basis.equivFun_apply, Module.Basis.equivFun_apply,
    indexAdicCyclicBasis, Module.Basis.baseChange_repr_tmul]
  rw [Algebra.smul_def, mul_one]
theorem indexAdicCyclic_diagonal_mem_integralLattice
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : CyclicAlgebra P r) (hx : x ∈ arithmeticCyclicSpan P r) :
    TensorProduct.tmul (FunctionField P) 1 x ∈
      IndexAdicCyclicIntegralLattice P r level := by
  intro p
  obtain ⟨a, ha⟩ :=
    exists_arithmetic_coordinate_of_mem_arithmeticCyclicSpan P r x hx p
  rw [indexAdicCyclicBasis_equivFun_diagonal, ← ha]
  exact IsDedekindDomain.HeightOneSpectrum.coe_algebraMap_mem
    (ArithmeticRing P) (FunctionField P)
    (indexCongruencePlace P r level) a
theorem one_mem_indexAdicCyclicIntegralLattice
    (P : BasePrime) (r : Rank) (level : Nat) :
    (1 : IndexAdicCyclicAlgebra P r level) ∈
      IndexAdicCyclicIntegralLattice P r level := by
  exact indexAdicCyclic_diagonal_mem_integralLattice P r level 1
    (one_mem_arithmeticCyclicSpan P r)
theorem IndexAdicCyclicIntegralLattice.sub_mem
    (P : BasePrime) (r : Rank) (level : Nat)
    {x y : IndexAdicCyclicAlgebra P r level}
    (hx : x ∈ IndexAdicCyclicIntegralLattice P r level)
    (hy : y ∈ IndexAdicCyclicIntegralLattice P r level) :
    x - y ∈ IndexAdicCyclicIntegralLattice P r level := by
  intro p
  have hcoord := congrArg
    (fun f : (Fin r.matrixRank × Fin r.matrixRank) →
      IndexCongruenceAdicCompletion P r level => f p)
    ((indexAdicCyclicBasis P r level).equivFun.map_sub x y)
  change (indexAdicCyclicBasis P r level).equivFun (x - y) p =
      (indexAdicCyclicBasis P r level).equivFun x p -
        (indexAdicCyclicBasis P r level).equivFun y p at hcoord
  rw [hcoord]
  exact (indexCongruencePlace P r level).adicCompletionIntegers
    (FunctionField P) |>.sub_mem (hx p) (hy p)
theorem ArithmeticFiniteAdeleCyclicIntegralLattice.add_mem
    (P : BasePrime) (r : Rank)
    {x y : ArithmeticFiniteAdeleCyclicAlgebra P r}
    (hx : x ∈ ArithmeticFiniteAdeleCyclicIntegralLattice P r)
    (hy : y ∈ ArithmeticFiniteAdeleCyclicIntegralLattice P r) :
    x + y ∈ ArithmeticFiniteAdeleCyclicIntegralLattice P r := by
  intro p
  rw [(arithmeticFiniteAdeleCyclicBasis P r).equivFun.map_add]
  exact (ArithmeticIntegralFiniteAdeles P).add_mem (hx p) (hy p)
theorem ArithmeticFiniteAdeleCyclicIntegralLattice.sub_mem
    (P : BasePrime) (r : Rank)
    {x y : ArithmeticFiniteAdeleCyclicAlgebra P r}
    (hx : x ∈ ArithmeticFiniteAdeleCyclicIntegralLattice P r)
    (hy : y ∈ ArithmeticFiniteAdeleCyclicIntegralLattice P r) :
    x - y ∈ ArithmeticFiniteAdeleCyclicIntegralLattice P r := by
  intro p
  have hcoord := congrArg
    (fun f : (Fin r.matrixRank × Fin r.matrixRank) →
      ArithmeticFiniteAdeleRing P => f p)
    ((arithmeticFiniteAdeleCyclicBasis P r).equivFun.map_sub x y)
  change (arithmeticFiniteAdeleCyclicBasis P r).equivFun (x - y) p =
      (arithmeticFiniteAdeleCyclicBasis P r).equivFun x p -
        (arithmeticFiniteAdeleCyclicBasis P r).equivFun y p at hcoord
  rw [hcoord]
  exact (ArithmeticIntegralFiniteAdeles P).sub_mem (hx p) (hy p)
theorem arithmeticFiniteAdeleCyclicSupportedAtIndexPlace_eq_sum
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : IndexAdicCyclicAlgebra P r level) :
    arithmeticFiniteAdeleCyclicSupportedAtIndexPlace P r level x =
      ∑ p, TensorProduct.tmul (FunctionField P)
        (arithmeticFiniteAdeleSupportedAtIndexPlace P r level
          ((indexAdicCyclicBasis P r level).equivFun x p))
        (functionFieldCyclicBasis P r p) := by
  conv_lhs => rw [← (indexAdicCyclicBasis P r level).sum_equivFun x]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro p _
  have hterm : (indexAdicCyclicBasis P r level).equivFun x p •
      indexAdicCyclicBasis P r level p =
      TensorProduct.tmul (FunctionField P)
        ((indexAdicCyclicBasis P r level).equivFun x p)
        (functionFieldCyclicBasis P r p) := by
    simp [indexAdicCyclicBasis, Module.Basis.baseChange_apply,
      TensorProduct.smul_tmul']
  rw [hterm, arithmeticFiniteAdeleCyclicSupportedAtIndexPlace_tmul]
theorem arithmeticFiniteAdeleCyclicBasis_repr_tmul_basis
    (P : BasePrime) (r : Rank)
    (a : ArithmeticFiniteAdeleRing P)
    (q p : Fin r.matrixRank × Fin r.matrixRank) :
    (arithmeticFiniteAdeleCyclicBasis P r).repr
        (TensorProduct.tmul (FunctionField P) a
          (functionFieldCyclicBasis P r q)) p =
      if q = p then a else 0 := by
  rw [arithmeticFiniteAdeleCyclicBasis,
    Module.Basis.baseChange_repr_tmul]
  rw [(functionFieldCyclicBasis P r).repr_self]
  by_cases h : q = p <;> simp [h]
theorem arithmeticFiniteAdeleCyclicBasis_equivFun_supportedAtIndexPlace
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : IndexAdicCyclicAlgebra P r level)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    (arithmeticFiniteAdeleCyclicBasis P r).equivFun
        (arithmeticFiniteAdeleCyclicSupportedAtIndexPlace P r level x) p =
      arithmeticFiniteAdeleSupportedAtIndexPlace P r level
        ((indexAdicCyclicBasis P r level).equivFun x p) := by
  rw [Module.Basis.equivFun_apply,
    arithmeticFiniteAdeleCyclicSupportedAtIndexPlace_eq_sum]
  have hsum := map_sum
    (arithmeticFiniteAdeleCyclicBasis P r).repr
    (fun q => TensorProduct.tmul (FunctionField P)
      (arithmeticFiniteAdeleSupportedAtIndexPlace P r level
        ((indexAdicCyclicBasis P r level).equivFun x q))
      (functionFieldCyclicBasis P r q)) Finset.univ
  rw [hsum]
  change Finsupp.applyAddHom p
      (∑ q, (arithmeticFiniteAdeleCyclicBasis P r).repr
        (TensorProduct.tmul (FunctionField P)
          (arithmeticFiniteAdeleSupportedAtIndexPlace P r level
            ((indexAdicCyclicBasis P r level).equivFun x q))
          (functionFieldCyclicBasis P r q))) = _
  rw [map_sum, Finset.sum_eq_single p]
  · exact arithmeticFiniteAdeleCyclicBasis_repr_tmul_basis P r _ p p
      |>.trans (by simp)
  · intro q _ hqp
    change ((arithmeticFiniteAdeleCyclicBasis P r).repr
      (TensorProduct.tmul (FunctionField P)
        (arithmeticFiniteAdeleSupportedAtIndexPlace P r level
          ((indexAdicCyclicBasis P r level).equivFun x q))
        (functionFieldCyclicBasis P r q))) p = 0
    rw [arithmeticFiniteAdeleCyclicBasis_repr_tmul_basis]
    simp [hqp]
  · simp
theorem arithmeticFiniteAdeleCyclicSupportedAtIndexPlace_mem_integral_iff
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : IndexAdicCyclicAlgebra P r level) :
    arithmeticFiniteAdeleCyclicSupportedAtIndexPlace P r level x ∈
        ArithmeticFiniteAdeleCyclicIntegralLattice P r ↔
      x ∈ IndexAdicCyclicIntegralLattice P r level := by
  simp only [ArithmeticFiniteAdeleCyclicIntegralLattice,
    IndexAdicCyclicIntegralLattice, Set.mem_setOf_eq]
  simp_rw [arithmeticFiniteAdeleCyclicBasis_equivFun_supportedAtIndexPlace,
    arithmeticFiniteAdeleSupportedAtIndexPlace_mem_integral_iff]
theorem one_mem_arithmeticFiniteAdeleCyclicIntegralLattice
    (P : BasePrime) (r : Rank) :
    (1 : ArithmeticFiniteAdeleCyclicAlgebra P r) ∈
      ArithmeticFiniteAdeleCyclicIntegralLattice P r := by
  exact cyclicAlgebraToArithmeticFiniteAdeles_mem_integralLattice
    P r 1 (one_mem_arithmeticCyclicSpan P r)
theorem arithmeticFiniteAdeleCyclicSupportedAtIndexPlace_mul
    (P : BasePrime) (r : Rank) (level : Nat)
    (x y : IndexAdicCyclicAlgebra P r level) :
    arithmeticFiniteAdeleCyclicSupportedAtIndexPlace P r level (x * y) =
      arithmeticFiniteAdeleCyclicSupportedAtIndexPlace P r level x *
        arithmeticFiniteAdeleCyclicSupportedAtIndexPlace P r level y := by
  induction x using TensorProduct.induction_on with
  | zero => simp [arithmeticFiniteAdeleCyclicSupportedAtIndexPlace]
  | add x z hx hz => simp [add_mul, map_add, hx, hz]
  | tmul a x =>
      induction y using TensorProduct.induction_on with
      | zero => simp [arithmeticFiniteAdeleCyclicSupportedAtIndexPlace]
      | add y z hy hz => simp [mul_add, map_add, hy, hz]
      | tmul b y =>
          simp [Algebra.TensorProduct.tmul_mul_tmul,
            show arithmeticFiniteAdeleSupportedAtIndexPlace P r level
                (a * b) =
              arithmeticFiniteAdeleSupportedAtIndexPlace P r level a *
                arithmeticFiniteAdeleSupportedAtIndexPlace P r level b from
              map_mul
                (arithmeticFiniteAdeleSupportedAtIndexPlaceNonUnitalRingHom
                  P r level) a b]
noncomputable def arithmeticFiniteAdeleCyclicIndexIdempotent
    (P : BasePrime) (r : Rank) (level : Nat) :
    ArithmeticFiniteAdeleCyclicAlgebra P r :=
  arithmeticFiniteAdeleCyclicSupportedAtIndexPlace P r level 1
theorem arithmeticFiniteAdeleCyclicIndexIdempotent_mul_self
    (P : BasePrime) (r : Rank) (level : Nat) :
    arithmeticFiniteAdeleCyclicIndexIdempotent P r level *
        arithmeticFiniteAdeleCyclicIndexIdempotent P r level =
      arithmeticFiniteAdeleCyclicIndexIdempotent P r level := by
  rw [arithmeticFiniteAdeleCyclicIndexIdempotent,
    ← arithmeticFiniteAdeleCyclicSupportedAtIndexPlace_mul]
  simp
theorem arithmeticFiniteAdeleCyclicIndexIdempotent_mul_supported
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : IndexAdicCyclicAlgebra P r level) :
    arithmeticFiniteAdeleCyclicIndexIdempotent P r level *
        arithmeticFiniteAdeleCyclicSupportedAtIndexPlace P r level x =
      arithmeticFiniteAdeleCyclicSupportedAtIndexPlace P r level x := by
  rw [arithmeticFiniteAdeleCyclicIndexIdempotent,
    ← arithmeticFiniteAdeleCyclicSupportedAtIndexPlace_mul]
  simp
theorem arithmeticFiniteAdeleCyclicSupported_mul_indexIdempotent
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : IndexAdicCyclicAlgebra P r level) :
    arithmeticFiniteAdeleCyclicSupportedAtIndexPlace P r level x *
        arithmeticFiniteAdeleCyclicIndexIdempotent P r level =
      arithmeticFiniteAdeleCyclicSupportedAtIndexPlace P r level x := by
  rw [arithmeticFiniteAdeleCyclicIndexIdempotent,
    ← arithmeticFiniteAdeleCyclicSupportedAtIndexPlace_mul]
  simp
noncomputable def arithmeticFiniteAdeleCyclicPatchAtIndexPlace
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : IndexAdicCyclicAlgebra P r level) :
    ArithmeticFiniteAdeleCyclicAlgebra P r :=
  1 - arithmeticFiniteAdeleCyclicIndexIdempotent P r level +
    arithmeticFiniteAdeleCyclicSupportedAtIndexPlace P r level x
theorem arithmeticFiniteAdeleCyclicPatchAtIndexPlace_mem_integral
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : IndexAdicCyclicAlgebra P r level)
    (hx : x ∈ IndexAdicCyclicIntegralLattice P r level) :
    arithmeticFiniteAdeleCyclicPatchAtIndexPlace P r level x ∈
      ArithmeticFiniteAdeleCyclicIntegralLattice P r := by
  apply ArithmeticFiniteAdeleCyclicIntegralLattice.add_mem P r
  · apply ArithmeticFiniteAdeleCyclicIntegralLattice.sub_mem P r
    · exact one_mem_arithmeticFiniteAdeleCyclicIntegralLattice P r
    · exact
        (arithmeticFiniteAdeleCyclicSupportedAtIndexPlace_mem_integral_iff
          P r level 1).mpr
            (one_mem_indexAdicCyclicIntegralLattice P r level)
  · exact
      (arithmeticFiniteAdeleCyclicSupportedAtIndexPlace_mem_integral_iff
        P r level x).mpr hx
theorem arithmeticFiniteAdeleCyclicPatchAtIndexPlace_mul
    (P : BasePrime) (r : Rank) (level : Nat)
    (x y : IndexAdicCyclicAlgebra P r level) :
    arithmeticFiniteAdeleCyclicPatchAtIndexPlace P r level x *
        arithmeticFiniteAdeleCyclicPatchAtIndexPlace P r level y =
      arithmeticFiniteAdeleCyclicPatchAtIndexPlace P r level (x * y) := by
  change
    (1 - arithmeticFiniteAdeleCyclicIndexIdempotent P r level +
        arithmeticFiniteAdeleCyclicSupportedAtIndexPlace P r level x) *
      (1 - arithmeticFiniteAdeleCyclicIndexIdempotent P r level +
        arithmeticFiniteAdeleCyclicSupportedAtIndexPlace P r level y) =
    1 - arithmeticFiniteAdeleCyclicIndexIdempotent P r level +
      arithmeticFiniteAdeleCyclicSupportedAtIndexPlace P r level (x * y)
  noncomm_ring
    [arithmeticFiniteAdeleCyclicIndexIdempotent_mul_self P r level,
      arithmeticFiniteAdeleCyclicIndexIdempotent_mul_supported P r level x,
      arithmeticFiniteAdeleCyclicIndexIdempotent_mul_supported P r level y,
      arithmeticFiniteAdeleCyclicSupported_mul_indexIdempotent P r level x,
      arithmeticFiniteAdeleCyclicSupported_mul_indexIdempotent P r level y,
      arithmeticFiniteAdeleCyclicSupportedAtIndexPlace_mul P r level x y]
theorem arithmeticFiniteAdeleCyclicSplitting_patchAtIndexPlace_of_ne
    (P : BasePrime) (r : Rank) (level : Nat)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (hv : v ≠ indexCongruencePlace P r level)
    (x : IndexAdicCyclicAlgebra P r level) :
    (arithmeticFiniteAdeleCyclicSplittingMap P r
        (arithmeticFiniteAdeleCyclicPatchAtIndexPlace P r level x)).map
          (arithmeticFiniteAdeleSplittingRingAt P r v) = 1 := by
  let h : ArithmeticFiniteAdeleCyclicAlgebra P r →+*
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (ArithmeticAdicSplittingRing P r v) :=
    (arithmeticFiniteAdeleSplittingRingAt P r v).toRingHom.mapMatrix.comp
      (arithmeticFiniteAdeleCyclicSplittingMap P r).toRingHom
  change h (arithmeticFiniteAdeleCyclicPatchAtIndexPlace P r level x) = 1
  have he : h (arithmeticFiniteAdeleCyclicIndexIdempotent P r level) = 0 := by
    exact arithmeticFiniteAdeleCyclicSplitting_supportedAtIndexPlace_of_ne
      P r level v hv 1
  have hx : h
      (arithmeticFiniteAdeleCyclicSupportedAtIndexPlace P r level x) = 0 := by
    exact arithmeticFiniteAdeleCyclicSplitting_supportedAtIndexPlace_of_ne
      P r level v hv x
  change h (1 - arithmeticFiniteAdeleCyclicIndexIdempotent P r level +
    arithmeticFiniteAdeleCyclicSupportedAtIndexPlace P r level x) = 1
  calc
    h (1 - arithmeticFiniteAdeleCyclicIndexIdempotent P r level +
        arithmeticFiniteAdeleCyclicSupportedAtIndexPlace P r level x) =
      h (1 - arithmeticFiniteAdeleCyclicIndexIdempotent P r level) +
        h (arithmeticFiniteAdeleCyclicSupportedAtIndexPlace P r level x) :=
      h.map_add _ _
    _ = (h 1 - h (arithmeticFiniteAdeleCyclicIndexIdempotent P r level)) +
        h (arithmeticFiniteAdeleCyclicSupportedAtIndexPlace P r level x) := by
      rw [h.map_sub]
    _ = 1 := by rw [h.map_one, he, hx]; simp
noncomputable def arithmeticFiniteAdeleCyclicUnitSupportedAtIndexPlace
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : (IndexAdicCyclicAlgebra P r level)ˣ) :
    (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ where
  val := arithmeticFiniteAdeleCyclicPatchAtIndexPlace P r level
    (u : IndexAdicCyclicAlgebra P r level)
  inv := arithmeticFiniteAdeleCyclicPatchAtIndexPlace P r level
    ((u⁻¹ : (IndexAdicCyclicAlgebra P r level)ˣ) :
      IndexAdicCyclicAlgebra P r level)
  val_inv := by
    rw [arithmeticFiniteAdeleCyclicPatchAtIndexPlace_mul]
    have hu : (u : IndexAdicCyclicAlgebra P r level) *
        ((u⁻¹ : (IndexAdicCyclicAlgebra P r level)ˣ) :
          IndexAdicCyclicAlgebra P r level) = 1 := by
      exact congrArg Units.val (mul_inv_cancel u)
    rw [hu]
    simp [arithmeticFiniteAdeleCyclicPatchAtIndexPlace,
      arithmeticFiniteAdeleCyclicIndexIdempotent]
  inv_val := by
    rw [arithmeticFiniteAdeleCyclicPatchAtIndexPlace_mul]
    have hu :
        ((u⁻¹ : (IndexAdicCyclicAlgebra P r level)ˣ) :
          IndexAdicCyclicAlgebra P r level) *
          (u : IndexAdicCyclicAlgebra P r level) = 1 := by
      exact congrArg Units.val (inv_mul_cancel u)
    rw [hu]
    simp [arithmeticFiniteAdeleCyclicPatchAtIndexPlace,
      arithmeticFiniteAdeleCyclicIndexIdempotent]
theorem arithmeticFiniteAdeleCyclicBaseReducedNorm_supportedAtIndexPlace_of_ne
    (P : BasePrime) (r : Rank) (level : Nat)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (hv : v ≠ indexCongruencePlace P r level)
    (u : (IndexAdicCyclicAlgebra P r level)ˣ) :
    arithmeticFiniteAdeleAt P v
        (arithmeticFiniteAdeleCyclicBaseReducedNorm P r
          (arithmeticFiniteAdeleCyclicUnitSupportedAtIndexPlace P r level u)) =
      1 := by
  apply Algebra.TensorProduct.includeLeft_injective
    (R := FunctionField P)
    (S := v.adicCompletion (FunctionField P))
    (A := v.adicCompletion (FunctionField P))
    (B := SplittingFunctionField P r)
    (algebraMap (FunctionField P) (SplittingFunctionField P r)).injective
  change algebraMap (v.adicCompletion (FunctionField P))
      (ArithmeticAdicSplittingRing P r v)
        (arithmeticFiniteAdeleAt P v
          (arithmeticFiniteAdeleCyclicBaseReducedNorm P r
            (arithmeticFiniteAdeleCyclicUnitSupportedAtIndexPlace
              P r level u))) =
    algebraMap (v.adicCompletion (FunctionField P))
      (ArithmeticAdicSplittingRing P r v) 1
  rw [arithmeticFiniteAdeleCyclicBaseReducedNorm_atPlace]
  change Matrix.det
      ((arithmeticFiniteAdeleCyclicSplittingMap P r
        (arithmeticFiniteAdeleCyclicPatchAtIndexPlace P r level
          (u : IndexAdicCyclicAlgebra P r level))).map
            (arithmeticFiniteAdeleSplittingRingAt P r v)) =
    algebraMap (v.adicCompletion (FunctionField P))
      (ArithmeticAdicSplittingRing P r v) 1
  rw [arithmeticFiniteAdeleCyclicSplitting_patchAtIndexPlace_of_ne
    P r level v hv, Matrix.det_one, map_one]
noncomputable def arithmeticFiniteAdeleCyclicUnitToIndexPlace
    (P : BasePrime) (r : Rank) (level : Nat) :
    (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ →*
      (IndexAdicCyclicAlgebra P r level)ˣ :=
  Units.map
    (arithmeticFiniteAdeleCyclicAlgebraAtIndexPlace
      P r level).toRingHom.toMonoidHom
@[simp] theorem arithmeticFiniteAdeleCyclicUnitToIndexPlace_supported
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : (IndexAdicCyclicAlgebra P r level)ˣ) :
    arithmeticFiniteAdeleCyclicUnitToIndexPlace P r level
        (arithmeticFiniteAdeleCyclicUnitSupportedAtIndexPlace P r level u) =
      u := by
  apply Units.ext
  simp [arithmeticFiniteAdeleCyclicUnitToIndexPlace,
    arithmeticFiniteAdeleCyclicUnitSupportedAtIndexPlace,
    arithmeticFiniteAdeleCyclicPatchAtIndexPlace,
    arithmeticFiniteAdeleCyclicIndexIdempotent]
@[simp] theorem arithmeticFiniteAdeleCyclicAlgebraAtIndexPlace_patch
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : IndexAdicCyclicAlgebra P r level) :
    arithmeticFiniteAdeleCyclicAlgebraAtIndexPlace P r level
        (arithmeticFiniteAdeleCyclicPatchAtIndexPlace P r level x) = x := by
  simp [arithmeticFiniteAdeleCyclicPatchAtIndexPlace,
    arithmeticFiniteAdeleCyclicIndexIdempotent]
theorem indexAdicCyclicBasis_equivFun_atIndexPlace
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : ArithmeticFiniteAdeleCyclicAlgebra P r)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    (indexAdicCyclicBasis P r level).equivFun
        (arithmeticFiniteAdeleCyclicAlgebraAtIndexPlace P r level x) p =
      arithmeticFiniteAdeleAtIndexPlace P r level
        ((arithmeticFiniteAdeleCyclicBasis P r).equivFun x p) := by
  induction x using TensorProduct.induction_on with
  | zero =>
      rw [map_zero]
      have hleft := congrArg
        (fun f : (Fin r.matrixRank × Fin r.matrixRank) →
          IndexCongruenceAdicCompletion P r level => f p)
        ((indexAdicCyclicBasis P r level).equivFun.map_zero)
      have hright := congrArg
        (fun f : (Fin r.matrixRank × Fin r.matrixRank) →
          ArithmeticFiniteAdeleRing P => f p)
        ((arithmeticFiniteAdeleCyclicBasis P r).equivFun.map_zero)
      change (indexAdicCyclicBasis P r level).equivFun 0 p = 0 at hleft
      change (arithmeticFiniteAdeleCyclicBasis P r).equivFun 0 p = 0 at hright
      rw [hleft, hright, map_zero]
  | add x y hx hy =>
      rw [map_add]
      have hleft := congrArg
        (fun f : (Fin r.matrixRank × Fin r.matrixRank) →
          IndexCongruenceAdicCompletion P r level => f p)
        ((indexAdicCyclicBasis P r level).equivFun.map_add
          (arithmeticFiniteAdeleCyclicAlgebraAtIndexPlace P r level x)
          (arithmeticFiniteAdeleCyclicAlgebraAtIndexPlace P r level y))
      have hright := congrArg
        (fun f : (Fin r.matrixRank × Fin r.matrixRank) →
          ArithmeticFiniteAdeleRing P => f p)
        ((arithmeticFiniteAdeleCyclicBasis P r).equivFun.map_add x y)
      change (indexAdicCyclicBasis P r level).equivFun
          (arithmeticFiniteAdeleCyclicAlgebraAtIndexPlace P r level x +
            arithmeticFiniteAdeleCyclicAlgebraAtIndexPlace P r level y) p =
        (indexAdicCyclicBasis P r level).equivFun
            (arithmeticFiniteAdeleCyclicAlgebraAtIndexPlace P r level x) p +
          (indexAdicCyclicBasis P r level).equivFun
            (arithmeticFiniteAdeleCyclicAlgebraAtIndexPlace P r level y) p
        at hleft
      change (arithmeticFiniteAdeleCyclicBasis P r).equivFun (x + y) p =
        (arithmeticFiniteAdeleCyclicBasis P r).equivFun x p +
          (arithmeticFiniteAdeleCyclicBasis P r).equivFun y p at hright
      rw [hleft, hright, map_add, hx, hy]
  | tmul a x =>
      rw [arithmeticFiniteAdeleCyclicAlgebraAtIndexPlace_tmul]
      simp [Module.Basis.equivFun_apply, indexAdicCyclicBasis,
        arithmeticFiniteAdeleCyclicBasis,
        Module.Basis.baseChange_repr_tmul]
      exact ((arithmeticFiniteAdeleAtIndexPlaceAlgHom
        P r level).toLinearMap.map_smul _ _).symm
@[simp] theorem arithmeticFiniteAdeleCyclicAlgebraAtIndexPlace_diagonal
    (P : BasePrime) (r : Rank) (level : Nat) (x : CyclicAlgebra P r) :
    arithmeticFiniteAdeleCyclicAlgebraAtIndexPlace P r level
        (cyclicAlgebraToArithmeticFiniteAdeles P r x) =
      TensorProduct.tmul (FunctionField P) 1 x := by
  simp [cyclicAlgebraToArithmeticFiniteAdeles_apply]
noncomputable abbrev IndexCongruenceLocalRing
    (P : BasePrime) (r : Rank) (level : Nat) :=
  Localization.AtPrime (IndexCongruenceIdeal P r level)
@[simp] theorem indexCompletedBaseArithmeticEval_constantCoeff
    (P : BasePrime) (r : Rank) (level : Nat) (a : ArithmeticRing P) :
    PowerSeries.constantCoeff
        (indexCompletedBaseArithmeticEval P r level a) =
      indexArithmeticEval P r level a := by
  rw [indexCompletedBaseArithmeticEval, RingHom.comp_apply,
    indexCompletedArithmeticEval_constantCoeff,
    indexConstantArithmeticEval_arithmeticBaseChange]
noncomputable def indexCompletedBasePolynomialTaylorHom
    (P : BasePrime) (r : Rank) (level : Nat) :
    PolynomialRing P →+* PowerSeries (ResidueField P r level) :=
  Polynomial.coeToPowerSeries.ringHom.comp
    ((Polynomial.taylorAlgHom (indexPlaceY P r level)).toRingHom.comp
      (Polynomial.mapRingHom
        (algebraMap (BaseField P) (ResidueField P r level))))
theorem indexCompletedBasePolynomialEval_eq_taylor
    (P : BasePrime) (r : Rank) (level : Nat) :
    indexCompletedBasePolynomialEval P r level =
      indexCompletedBasePolynomialTaylorHom P r level := by
  ext a
  · simp [indexCompletedBasePolynomialEval,
      indexCompletedBasePolynomialTaylorHom,
      indexCompletedPolynomialEval, add_comm]
  · simp [indexCompletedBasePolynomialEval,
      indexCompletedBasePolynomialTaylorHom,
      indexCompletedPolynomialEval, add_comm]
theorem indexCompletedBasePolynomialEval_injective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Injective (indexCompletedBasePolynomialEval P r level) := by
  rw [indexCompletedBasePolynomialEval_eq_taylor]
  exact (Polynomial.coe_injective (ResidueField P r level)).comp
    ((Polynomial.taylor_injective (indexPlaceY P r level)).comp
      (Polynomial.map_injective
        (algebraMap (BaseField P) (ResidueField P r level))
        (algebraMap (BaseField P) (ResidueField P r level)).injective))
theorem indexCompletedBaseArithmeticEval_injective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Injective (indexCompletedBaseArithmeticEval P r level) := by
  apply IsLocalization.injective_of_map_algebraMap_zero (ArithmeticRing P)
    (M := Submonoid.powers
      (Polynomial.X * (1 + Polynomial.X) : PolynomialRing P))
    (indexCompletedBaseArithmeticEval P r level)
  intro f hf
  rw [indexCompletedBaseArithmeticEval_algebraMap] at hf
  have hf0 : f = 0 := by
    apply indexCompletedBasePolynomialEval_injective P r level
    simpa using hf
  rw [hf0, map_zero]
abbrev IndexCongruenceLocalField
    (P : BasePrime) (r : Rank) (level : Nat) :=
  LaurentSeries (ResidueField P r level)
noncomputable def indexArithmeticToCongruenceLocalField
    (P : BasePrime) (r : Rank) (level : Nat) :
    ArithmeticRing P →+* IndexCongruenceLocalField P r level :=
  (HahnSeries.ofPowerSeries ℤ (ResidueField P r level)).comp
    (indexCompletedBaseArithmeticEval P r level)
theorem indexArithmeticToCongruenceLocalField_injective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Injective
      (indexArithmeticToCongruenceLocalField P r level) :=
  (HahnSeries.ofPowerSeries_injective (Γ := ℤ)
      (R := ResidueField P r level)).comp
    (indexCompletedBaseArithmeticEval_injective P r level)
noncomputable def functionFieldToIndexCongruenceLocalField
    (P : BasePrime) (r : Rank) (level : Nat) :
    FunctionField P →+* IndexCongruenceLocalField P r level :=
  IsFractionRing.lift
    (indexArithmeticToCongruenceLocalField_injective P r level)
@[simp] theorem functionFieldToIndexCongruenceLocalField_algebraMap
    (P : BasePrime) (r : Rank) (level : Nat) (a : ArithmeticRing P) :
    functionFieldToIndexCongruenceLocalField P r level
        (algebraMap (ArithmeticRing P) (FunctionField P) a) =
      indexArithmeticToCongruenceLocalField P r level a :=
  IsFractionRing.lift_algebraMap
    (indexArithmeticToCongruenceLocalField_injective P r level) a
noncomputable instance indexCongruenceLocalFieldFunctionFieldAlgebra
    (P : BasePrime) (r : Rank) (level : Nat) :
    Algebra (FunctionField P) (IndexCongruenceLocalField P r level) :=
  (functionFieldToIndexCongruenceLocalField P r level).toAlgebra
noncomputable def indexCompletedPolynomialTaylorHom
    (P : BasePrime) (r : Rank) (level : Nat) :
    ConstantPolynomialRing P r →+*
      PowerSeries (ResidueField P r level) :=
  Polynomial.coeToPowerSeries.ringHom.comp
    ((Polynomial.taylorAlgHom (indexPlaceY P r level)).toRingHom.comp
      (Polynomial.mapRingHom
        (indexConstantEmbedding P r level).toRingHom))
theorem indexCompletedPolynomialEval_eq_taylor
    (P : BasePrime) (r : Rank) (level : Nat) :
    indexCompletedPolynomialEval P r level =
      indexCompletedPolynomialTaylorHom P r level := by
  ext a <;>
    simp [indexCompletedPolynomialEval,
      indexCompletedPolynomialTaylorHom, add_comm]
theorem indexCompletedPolynomialEval_injective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Injective (indexCompletedPolynomialEval P r level) := by
  rw [indexCompletedPolynomialEval_eq_taylor]
  exact (Polynomial.coe_injective (ResidueField P r level)).comp
    ((Polynomial.taylor_injective (indexPlaceY P r level)).comp
      (Polynomial.map_injective
        (indexConstantEmbedding P r level).toRingHom
        (indexConstantEmbedding P r level).injective))
noncomputable def indexConstantPolynomialToCongruenceLocalField
    (P : BasePrime) (r : Rank) (level : Nat) :
    ConstantPolynomialRing P r →+*
      IndexCongruenceLocalField P r level :=
  (HahnSeries.ofPowerSeries ℤ (ResidueField P r level)).comp
    (indexCompletedPolynomialEval P r level)
theorem indexConstantPolynomialToCongruenceLocalField_injective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Injective
      (indexConstantPolynomialToCongruenceLocalField P r level) :=
  (HahnSeries.ofPowerSeries_injective (Γ := ℤ)
      (R := ResidueField P r level)).comp
    (indexCompletedPolynomialEval_injective P r level)
noncomputable def splittingFunctionFieldToIndexCongruenceLocalField
    (P : BasePrime) (r : Rank) (level : Nat) :
    SplittingFunctionField P r →+*
      IndexCongruenceLocalField P r level :=
  IsFractionRing.lift
    (indexConstantPolynomialToCongruenceLocalField_injective P r level)
@[simp] theorem splittingFunctionFieldToIndexCongruenceLocalField_algebraMap
    (P : BasePrime) (r : Rank) (level : Nat)
    (f : ConstantPolynomialRing P r) :
    splittingFunctionFieldToIndexCongruenceLocalField P r level
        (algebraMap (ConstantPolynomialRing P r)
          (SplittingFunctionField P r) f) =
      indexConstantPolynomialToCongruenceLocalField P r level f :=
  IsFractionRing.lift_algebraMap
    (indexConstantPolynomialToCongruenceLocalField_injective P r level) f
@[simp] theorem splittingFunctionFieldToIndexCongruenceLocalField_C
    (P : BasePrime) (r : Rank) (level : Nat) (a : ConstantExtension P r) :
    splittingFunctionFieldToIndexCongruenceLocalField P r level
        (RatFunc.C a) =
      HahnSeries.single 0 (indexConstantEmbedding P r level a) := by
  rw [show (RatFunc.C a : SplittingFunctionField P r) =
      algebraMap (ConstantPolynomialRing P r)
          (SplittingFunctionField P r) (Polynomial.C a) by simp,
    splittingFunctionFieldToIndexCongruenceLocalField_algebraMap]
  simp [indexConstantPolynomialToCongruenceLocalField,
    indexCompletedPolynomialEval]
@[simp] theorem splittingFunctionFieldToIndexCongruenceLocalField_X
    (P : BasePrime) (r : Rank) (level : Nat) :
    splittingFunctionFieldToIndexCongruenceLocalField P r level
        (RatFunc.X : SplittingFunctionField P r) =
      HahnSeries.single 0 (indexPlaceY P r level) +
        HahnSeries.single 1 1 := by
  rw [show (RatFunc.X : SplittingFunctionField P r) =
      algebraMap (ConstantPolynomialRing P r)
          (SplittingFunctionField P r) Polynomial.X by simp,
    splittingFunctionFieldToIndexCongruenceLocalField_algebraMap]
  simp [indexConstantPolynomialToCongruenceLocalField,
    indexCompletedPolynomialEval]
theorem splittingFunctionFieldToIndexCongruenceLocalField_arithmetic
    (P : BasePrime) (r : Rank) (level : Nat) :
    (splittingFunctionFieldToIndexCongruenceLocalField P r level).comp
        (arithmeticRingToSplittingFunctionField P r) =
      indexArithmeticToCongruenceLocalField P r level := by
  apply IsLocalization.ringHom_ext
    (Submonoid.powers
      (Polynomial.X * (1 + Polynomial.X) : PolynomialRing P))
  apply Polynomial.ringHom_ext
  · intro a
    simp [arithmeticRingToSplittingFunctionField,
      arithmeticRingToFunctionField, functionFieldEmbedding_C,
      indexArithmeticToCongruenceLocalField,
      indexCompletedBaseArithmeticEval,
      indexCompletedArithmeticEval,
      arithmeticToConstantArithmetic,
      indexCompletedPolynomialEval]
  · simp [arithmeticRingToSplittingFunctionField,
      arithmeticRingToFunctionField, functionFieldEmbedding_X,
      indexArithmeticToCongruenceLocalField,
      indexCompletedBaseArithmeticEval,
      indexCompletedArithmeticEval,
      arithmeticToConstantArithmetic,
      indexCompletedPolynomialEval]
theorem splittingFunctionFieldToIndexCongruenceLocalField_functionFieldEmbedding
    (P : BasePrime) (r : Rank) (level : Nat) (x : FunctionField P) :
    splittingFunctionFieldToIndexCongruenceLocalField P r level
        (functionFieldEmbedding P r x) =
      functionFieldToIndexCongruenceLocalField P r level x := by
  have h :
      (splittingFunctionFieldToIndexCongruenceLocalField P r level).comp
          (functionFieldEmbedding P r) =
        functionFieldToIndexCongruenceLocalField P r level := by
    apply IsFractionRing.ringHom_ext (A := ArithmeticRing P)
    intro a
    rw [functionFieldToIndexCongruenceLocalField_algebraMap]
    change splittingFunctionFieldToIndexCongruenceLocalField P r level
        (arithmeticRingToSplittingFunctionField P r a) =
      indexArithmeticToCongruenceLocalField P r level a
    exact DFunLike.congr_fun
      (splittingFunctionFieldToIndexCongruenceLocalField_arithmetic
        P r level) a
  exact DFunLike.congr_fun h x
theorem splittingFunctionFieldToIndexCongruenceLocalField_constantArithmetic
    (P : BasePrime) (r : Rank) (level : Nat) :
    (splittingFunctionFieldToIndexCongruenceLocalField P r level).comp
        (constantArithmeticToSplittingFunctionField P r) =
      (HahnSeries.ofPowerSeries ℤ
        (ResidueField P r level)).comp
          (indexCompletedArithmeticEval P r level) := by
  apply IsLocalization.ringHom_ext
    (Submonoid.powers
      (Polynomial.X * (1 + Polynomial.X) :
        ConstantPolynomialRing P r))
  apply RingHom.ext
  intro f
  rw [RingHom.comp_apply, RingHom.comp_apply,
    constantArithmeticToSplittingFunctionField_algebraMap,
    splittingFunctionFieldToIndexCongruenceLocalField_algebraMap]
  change indexConstantPolynomialToCongruenceLocalField P r level f =
    HahnSeries.ofPowerSeries ℤ (ResidueField P r level)
      (indexCompletedArithmeticEval P r level
        (algebraMap (ConstantPolynomialRing P r)
          (ConstantArithmeticRing P r) f))
  rw [indexCompletedArithmeticEval_algebraMap]
  rfl
theorem indexCompletedBaseArithmeticEval_isUnit_of_not_mem
    (P : BasePrime) (r : Rank) (level : Nat) (a : ArithmeticRing P)
    (ha : a ∉ IndexCongruenceIdeal P r level) :
    IsUnit (indexCompletedBaseArithmeticEval P r level a) := by
  rw [PowerSeries.isUnit_iff_constantCoeff,
    indexCompletedBaseArithmeticEval_constantCoeff, isUnit_iff_ne_zero]
  exact ha
noncomputable def indexCongruenceLocalRingToCompletion
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexCongruenceLocalRing P r level →+*
      PowerSeries (ResidueField P r level) :=
  IsLocalization.lift
    (fun a : (IndexCongruenceIdeal P r level).primeCompl =>
      indexCompletedBaseArithmeticEval_isUnit_of_not_mem
        P r level a.1 a.2)
@[simp] theorem indexCongruenceLocalRingToCompletion_algebraMap
    (P : BasePrime) (r : Rank) (level : Nat) (a : ArithmeticRing P) :
    indexCongruenceLocalRingToCompletion P r level
        (algebraMap (ArithmeticRing P)
          (IndexCongruenceLocalRing P r level) a) =
      indexCompletedBaseArithmeticEval P r level a := by
  exact IsLocalization.lift_eq _ _
noncomputable def indexValuationSubringToCompletion
    (P : BasePrime) (r : Rank) (level : Nat) :
    IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime (FunctionField P)
        (indexCongruencePlace P r level) →+*
      PowerSeries (ResidueField P r level) :=
  IsLocalization.lift
    (fun a : (indexCongruencePlace P r level).asIdeal.primeCompl ↦
      indexCompletedBaseArithmeticEval_isUnit_of_not_mem
        P r level a.1 a.2)
@[simp] theorem indexValuationSubringToCompletion_algebraMap
    (P : BasePrime) (r : Rank) (level : Nat) (a : ArithmeticRing P) :
    indexValuationSubringToCompletion P r level
        (algebraMap (ArithmeticRing P)
          (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime (FunctionField P)
            (indexCongruencePlace P r level)) a) =
      indexCompletedBaseArithmeticEval P r level a := by
  exact IsLocalization.lift_eq _ _
theorem functionFieldToIndexCongruenceLocalField_on_valuationSubring
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime (FunctionField P)
      (indexCongruencePlace P r level)) :
    functionFieldToIndexCongruenceLocalField P r level x.1 =
      HahnSeries.ofPowerSeries ℤ (ResidueField P r level)
        (indexValuationSubringToCompletion P r level x) := by
  have h :
      (functionFieldToIndexCongruenceLocalField P r level).comp
          (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime
            (FunctionField P)
            (indexCongruencePlace P r level)).subtype =
        (HahnSeries.ofPowerSeries ℤ
            (ResidueField P r level)).comp
          (indexValuationSubringToCompletion P r level) := by
    apply IsLocalization.ringHom_ext
      (indexCongruencePlace P r level).asIdeal.primeCompl
    apply RingHom.ext
    intro a
    simp only [RingHom.comp_apply]
    rw [show
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime
          (FunctionField P) (indexCongruencePlace P r level)).subtype
          (algebraMap (ArithmeticRing P)
            (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime
              (FunctionField P) (indexCongruencePlace P r level)) a) =
          algebraMap (ArithmeticRing P) (FunctionField P) a by
        exact (IsScalarTower.algebraMap_apply (ArithmeticRing P)
          (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime
            (FunctionField P) (indexCongruencePlace P r level))
          (FunctionField P) a).symm]
    rw [functionFieldToIndexCongruenceLocalField_algebraMap,
      indexValuationSubringToCompletion_algebraMap]
    rfl
  exact DFunLike.congr_fun h x
noncomputable def indexLaurentPullbackValuation
    (P : BasePrime) (r : Rank) (level : Nat) :
    Valuation (FunctionField P) (WithZero (Multiplicative ℤ)) :=
  Valuation.comap (functionFieldToIndexCongruenceLocalField P r level)
    (Valued.v : Valuation (IndexCongruenceLocalField P r level) _)
noncomputable def indexLaurentPullbackValuationSubring
    (P : BasePrime) (r : Rank) (level : Nat) :
    ValuationSubring (FunctionField P) :=
  (indexLaurentPullbackValuation P r level).valuationSubring
theorem valuationSubringAtIndexPlace_le_indexLaurentPullback
    (P : BasePrime) (r : Rank) (level : Nat) :
    IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime (FunctionField P)
        (indexCongruencePlace P r level) ≤
      indexLaurentPullbackValuationSubring P r level := by
  intro x hx
  change functionFieldToIndexCongruenceLocalField P r level x ∈
    (Valued.v : Valuation (IndexCongruenceLocalField P r level) _).valuationSubring
  rw [Valuation.mem_valuationSubring_iff,
    LaurentSeries.val_le_one_iff_eq_coe]
  exact ⟨indexValuationSubringToCompletion P r level ⟨x, hx⟩,
    (functionFieldToIndexCongruenceLocalField_on_valuationSubring
      P r level ⟨x, hx⟩).symm⟩
noncomputable def indexGlobalUniformizer
    (P : BasePrime) (r : Rank) (level : Nat) : FunctionField P :=
  algebraMap (ArithmeticRing P) (FunctionField P)
    (algebraMap (PolynomialRing P) (ArithmeticRing P)
      (indexPlacePolynomial P r level))
theorem indexGlobalUniformizer_ne_zero
    (P : BasePrime) (r : Rank) (level : Nat) :
    indexGlobalUniformizer P r level ≠ 0 := by
  rw [indexGlobalUniformizer,
    map_ne_zero_iff _
      (IsFractionRing.injective (ArithmeticRing P) (FunctionField P))]
  exact indexPlacePolynomial_arithmetic_ne_zero P r level
theorem functionFieldToIndexCongruenceLocalField_indexGlobalUniformizer
    (P : BasePrime) (r : Rank) (level : Nat) :
    functionFieldToIndexCongruenceLocalField P r level
        (indexGlobalUniformizer P r level) =
      HahnSeries.ofPowerSeries ℤ (ResidueField P r level)
        (indexCompletedUniformizer P r level) := by
  rw [indexGlobalUniformizer,
    functionFieldToIndexCongruenceLocalField_algebraMap]
  change HahnSeries.ofPowerSeries ℤ (ResidueField P r level)
      (indexCompletedBaseArithmeticEval P r level
        (algebraMap (PolynomialRing P) (ArithmeticRing P)
          (indexPlacePolynomial P r level))) = _
  rw [indexCompletedBaseArithmeticEval_algebraMap,
    indexCompletedBasePolynomialEval_indexPlacePolynomial]
theorem inv_indexGlobalUniformizer_not_mem_indexLaurentPullback
    (P : BasePrime) (r : Rank) (level : Nat) :
    (indexGlobalUniformizer P r level)⁻¹ ∉
      indexLaurentPullbackValuationSubring P r level := by
  intro hmem
  change Valued.v
      (functionFieldToIndexCongruenceLocalField P r level
        (indexGlobalUniformizer P r level)⁻¹) ≤ 1 at hmem
  obtain ⟨F, hF⟩ :=
    (LaurentSeries.val_le_one_iff_eq_coe _ _).mp hmem
  have hprod :
      HahnSeries.ofPowerSeries ℤ (ResidueField P r level)
          (indexCompletedUniformizer P r level) *
        HahnSeries.ofPowerSeries ℤ (ResidueField P r level) F = 1 := by
    rw [hF,
      ← functionFieldToIndexCongruenceLocalField_indexGlobalUniformizer]
    rw [← map_mul, mul_inv_cancel₀
      (indexGlobalUniformizer_ne_zero P r level), map_one]
  have hmul : indexCompletedUniformizer P r level * F = 1 := by
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
    simpa only [map_mul, map_one] using hprod
  have hu : IsUnit (indexCompletedUniformizer P r level) :=
    isUnit_iff_exists_inv.mpr ⟨F, hmul⟩
  rw [PowerSeries.isUnit_iff_constantCoeff,
    indexCompletedUniformizer_eq_X_mul_unitFactor] at hu
  simpa using hu
theorem indexLaurentPullbackValuationSubring_ne_top
    (P : BasePrime) (r : Rank) (level : Nat) :
    indexLaurentPullbackValuationSubring P r level ≠ ⊤ := by
  intro htop
  apply inv_indexGlobalUniformizer_not_mem_indexLaurentPullback P r level
  rw [htop]
  trivial
theorem valuationSubringAtIndexPlace_eq_indexLaurentPullback
    (P : BasePrime) (r : Rank) (level : Nat) :
    IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime
        (FunctionField P) (indexCongruencePlace P r level) =
      indexLaurentPullbackValuationSubring P r level :=
  ValuationSubring.eq_of_le_of_ne_top _
    (valuationSubringAtIndexPlace_le_indexLaurentPullback P r level)
    (indexLaurentPullbackValuationSubring_ne_top P r level)
theorem indexCongruenceValuation_isEquiv_indexLaurentPullback
    (P : BasePrime) (r : Rank) (level : Nat) :
    ((indexCongruencePlace P r level).valuation (FunctionField P)).IsEquiv
      (indexLaurentPullbackValuation P r level) := by
  rw [Valuation.isEquiv_iff_valuationSubring,
    ← IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring,
    valuationSubringAtIndexPlace_eq_indexLaurentPullback]
  rfl
noncomputable abbrev IndexLaurentPullbackCompletion
    (P : BasePrime) (r : Rank) (level : Nat) :=
  (indexLaurentPullbackValuation P r level).Completion
noncomputable def indexAdicCompletionEquivLaurentPullbackCompletion
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexCongruenceAdicCompletion P r level ≃ᵤ
      IndexLaurentPullbackCompletion P r level :=
  (IsDedekindDomain.HeightOneSpectrum.adicCompletion.uniformEquiv
    (FunctionField P) (indexCongruencePlace P r level)).trans
    (UniformSpace.Completion.mapEquiv
      (indexCongruenceValuation_isEquiv_indexLaurentPullback
        P r level).uniformEquiv)
noncomputable def indexAdicCompletionRingEquivLaurentPullbackCompletion
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexCongruenceAdicCompletion P r level ≃+*
      IndexLaurentPullbackCompletion P r level :=
  (IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv
    (FunctionField P) (indexCongruencePlace P r level)).trans
    (UniformSpace.Completion.mapRingEquiv
    (WithVal.congr
      ((indexCongruencePlace P r level).valuation (FunctionField P))
      (indexLaurentPullbackValuation P r level)
      (RingEquiv.refl (FunctionField P)))
    (indexCongruenceValuation_isEquiv_indexLaurentPullback
      P r level).uniformContinuous_congr.continuous
    (indexCongruenceValuation_isEquiv_indexLaurentPullback
      P r level).symm.uniformContinuous_congr.continuous)
theorem indexAdicCompletionRingEquiv_eq_uniformEquiv
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : IndexCongruenceAdicCompletion P r level) :
    indexAdicCompletionRingEquivLaurentPullbackCompletion P r level x =
      indexAdicCompletionEquivLaurentPullbackCompletion P r level x :=
  rfl
@[simp] theorem indexAdicCompletionEquivLaurentPullbackCompletion_algebraMap
    (P : BasePrime) (r : Rank) (level : Nat) (x : FunctionField P) :
    indexAdicCompletionEquivLaurentPullbackCompletion P r level
        (algebraMap (FunctionField P)
          (IndexCongruenceAdicCompletion P r level) x) =
      ((WithVal.toVal (indexLaurentPullbackValuation P r level) x :
        WithVal (indexLaurentPullbackValuation P r level)) :
          IndexLaurentPullbackCompletion P r level) := by
  exact UniformSpace.Completion.mapEquiv_coe
    (indexCongruenceValuation_isEquiv_indexLaurentPullback
      P r level).uniformEquiv
    (WithVal.toVal
      ((indexCongruencePlace P r level).valuation (FunctionField P)) x)
theorem indexAdicCompletionEquivLaurentPullbackCompletion_le_one_iff
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : IndexCongruenceAdicCompletion P r level) :
    Valued.v x ≤ 1 ↔
      Valued.v
        (indexAdicCompletionEquivLaurentPullbackCompletion P r level x) ≤ 1 :=
  (indexCongruenceValuation_isEquiv_indexLaurentPullback
    P r level).valuedCompletion_le_one_iff (x := x.toCompletion)
noncomputable abbrev IndexLaurentPullbackCompletionIntegers
    (P : BasePrime) (r : Rank) (level : Nat) :=
  (Valued.v : Valuation
    (IndexLaurentPullbackCompletion P r level) _).valuationSubring
noncomputable def indexAdicIntegersRingEquivLaurentPullbackIntegers
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexCongruenceAdicIntegers P r level ≃+*
      IndexLaurentPullbackCompletionIntegers P r level where
  toFun x :=
    ⟨indexAdicCompletionRingEquivLaurentPullbackCompletion P r level x,
      (indexAdicCompletionEquivLaurentPullbackCompletion_le_one_iff
        P r level x).mp x.property⟩
  invFun y := by
    let x :=
      (indexAdicCompletionRingEquivLaurentPullbackCompletion
        P r level).symm y.1
    refine ⟨x, ?_⟩
    apply (indexAdicCompletionEquivLaurentPullbackCompletion_le_one_iff
      P r level x).mpr
    rw [← indexAdicCompletionRingEquiv_eq_uniformEquiv]
    change Valued.v
      (indexAdicCompletionRingEquivLaurentPullbackCompletion P r level
        ((indexAdicCompletionRingEquivLaurentPullbackCompletion
          P r level).symm y.1)) ≤ 1
    rw [(indexAdicCompletionRingEquivLaurentPullbackCompletion
      P r level).apply_symm_apply]
    exact y.property
  left_inv x := by
    apply Subtype.ext
    exact (indexAdicCompletionRingEquivLaurentPullbackCompletion
      P r level).symm_apply_apply x
  right_inv y := by
    apply Subtype.ext
    exact (indexAdicCompletionRingEquivLaurentPullbackCompletion
      P r level).apply_symm_apply y
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul
      (indexAdicCompletionRingEquivLaurentPullbackCompletion P r level) x.1 y.1
  map_add' x y := by
    apply Subtype.ext
    exact map_add
      (indexAdicCompletionRingEquivLaurentPullbackCompletion P r level) x.1 y.1
section SelectedPlaceTopology
open scoped PowerSeries.WithPiTopology Topology WithZeroTopology Multiplicative
open MonoidWithZeroHom.ValueGroup₀
open Filter
theorem isOpen_arithmeticIntegralFiniteAdeles
    (P : BasePrime) :
    IsOpen (ArithmeticIntegralFiniteAdeles P :
      Set (ArithmeticFiniteAdeleRing P)) := by
  exact RestrictedProduct.isOpen_forall_mem fun v =>
    Valued.isOpen_valuationSubring
      (v.adicCompletion (FunctionField P))
theorem isOpen_arithmeticFiniteAdeleCyclicIntegralLattice
    (P : BasePrime) (r : Rank) :
    IsOpen (ArithmeticFiniteAdeleCyclicIntegralLattice P r) := by
  rw [show ArithmeticFiniteAdeleCyclicIntegralLattice P r =
      ⋂ p, (fun x =>
        (arithmeticFiniteAdeleCyclicBasis P r).equivFun x p) ⁻¹'
          (ArithmeticIntegralFiniteAdeles P :
            Set (ArithmeticFiniteAdeleRing P)) by
    ext x
    simp [ArithmeticFiniteAdeleCyclicIntegralLattice]]
  exact isOpen_iInter_of_finite fun p =>
    (isOpen_arithmeticIntegralFiniteAdeles P).preimage
      ((continuous_apply p).comp continuous_induced_dom)
theorem isOpen_arithmeticFiniteAdeleCyclicIntegralNormOneSet
    (P : BasePrime) (r : Rank) :
    IsOpen (ArithmeticFiniteAdeleCyclicIntegralNormOneSet P r) := by
  change IsOpen
    ({u : ArithmeticFiniteAdeleCyclicNormOne P r |
        ((u : (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ) :
          ArithmeticFiniteAdeleCyclicAlgebra P r) ∈
        ArithmeticFiniteAdeleCyclicIntegralLattice P r} ∩
      {u : ArithmeticFiniteAdeleCyclicNormOne P r |
        (((u : (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ)⁻¹ :
          (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ) :
          ArithmeticFiniteAdeleCyclicAlgebra P r) ∈
        ArithmeticFiniteAdeleCyclicIntegralLattice P r})
  exact
    ((isOpen_arithmeticFiniteAdeleCyclicIntegralLattice P r).preimage
      (Units.continuous_val.comp continuous_subtype_val)).inter
    ((isOpen_arithmeticFiniteAdeleCyclicIntegralLattice P r).preimage
      (Units.continuous_coe_inv.comp continuous_subtype_val))
local instance selectedPlaceResidueFieldTopologicalSpace
    (P : BasePrime) (r : Rank) (level : Nat) :
    TopologicalSpace (ResidueField P r level) := ⊥
local instance selectedPlaceResidueFieldDiscreteTopology
    (P : BasePrime) (r : Rank) (level : Nat) :
    DiscreteTopology (ResidueField P r level) := ⟨rfl⟩
theorem tendsto_indexCompletedBaseArithmeticEval_in_localField
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : PowerSeries (ResidueField P r level))
    (a : Nat → ArithmeticRing P)
    (ha : ∀ n k, k < n →
      PowerSeries.coeff k
          (indexCompletedBaseArithmeticEval P r level (a n)) =
        PowerSeries.coeff k s) :
    Filter.Tendsto
      (fun n ↦ HahnSeries.ofPowerSeries ℤ
        (ResidueField P r level)
        (indexCompletedBaseArithmeticEval P r level (a n)))
      Filter.atTop
      (𝓝 (HahnSeries.ofPowerSeries ℤ
        (ResidueField P r level) s)) := by
  rw [Filter.tendsto_def]
  intro U hU
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.mp hU
  obtain ⟨N, hN⟩ := WithZero.exists_exp_neg_natCast_lt
    (show embedding γ.1 ≠ 0 by simp)
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  apply hγ
  change Valued.v.restrict
      (HahnSeries.ofPowerSeries ℤ (ResidueField P r level)
          (indexCompletedBaseArithmeticEval P r level (a n)) -
        HahnSeries.ofPowerSeries ℤ (ResidueField P r level) s) < γ.1
  rw [Valuation.restrict_lt_iff_lt_embedding]
  rw [← map_sub]
  apply lt_of_le_of_lt
    ((LaurentSeries.valuation_le_iff_coeff_lt_eq_zero
      (ResidueField P r level)).mpr ?_) hN
  intro z hz
  cases z with
  | ofNat k =>
      have hkN : k < N := Int.ofNat_lt.mp hz
      calc
        _ = PowerSeries.coeff k
            (indexCompletedBaseArithmeticEval P r level (a n) - s) :=
          HahnSeries.ofPowerSeries_apply_coeff _ k
        _ = 0 := by
          rw [map_sub,
            ha n k (hkN.trans_le hn), sub_self]
  | negSucc k =>
      simp [HahnSeries.ofPowerSeries_apply,
        HahnSeries.embDomain_notin_image_support]
theorem ofPowerSeries_mem_closure_range_functionFieldToIndexCongruenceLocalField
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : PowerSeries (ResidueField P r level)) :
    HahnSeries.ofPowerSeries ℤ (ResidueField P r level) s ∈
      closure (Set.range
        (functionFieldToIndexCongruenceLocalField P r level)) := by
  choose a ha using fun n =>
    exists_indexCompletedBaseArithmeticEval_finite_coeff_lift
      P r level s n
  apply mem_closure_of_tendsto
    (f := fun n : Nat =>
      functionFieldToIndexCongruenceLocalField P r level
        (algebraMap (ArithmeticRing P) (FunctionField P) (a n)))
    (b := (Filter.atTop : Filter Nat))
  · simpa [functionFieldToIndexCongruenceLocalField_algebraMap,
      indexArithmeticToCongruenceLocalField] using
      tendsto_indexCompletedBaseArithmeticEval_in_localField
        P r level s a ha
  · exact Filter.Eventually.of_forall fun n => Set.mem_range_self _
theorem denseRange_functionFieldToIndexCongruenceLocalField
    (P : BasePrime) (r : Rank) (level : Nat) :
    DenseRange
      (functionFieldToIndexCongruenceLocalField P r level) := by
  intro z
  let K : Subfield (IndexCongruenceLocalField P r level) :=
    (functionFieldToIndexCongruenceLocalField P r level).fieldRange.topologicalClosure
  change z ∈ K
  obtain ⟨x, y, _, rfl⟩ :=
    IsFractionRing.div_surjective
      (PowerSeries (ResidueField P r level)) z
  apply K.div_mem
  · exact ofPowerSeries_mem_closure_range_functionFieldToIndexCongruenceLocalField
      P r level x
  · exact ofPowerSeries_mem_closure_range_functionFieldToIndexCongruenceLocalField
      P r level y
noncomputable def indexLaurentPullbackValuedEmbedding
    (P : BasePrime) (r : Rank) (level : Nat) :
    WithVal (indexLaurentPullbackValuation P r level) →+*
      IndexCongruenceLocalField P r level :=
  (functionFieldToIndexCongruenceLocalField P r level).comp
    (WithVal.equiv (indexLaurentPullbackValuation P r level)).toRingHom
@[simp] theorem indexLaurentPullbackValuedEmbedding_apply
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : WithVal (indexLaurentPullbackValuation P r level)) :
    indexLaurentPullbackValuedEmbedding P r level x =
      functionFieldToIndexCongruenceLocalField P r level x.ofVal :=
  rfl
@[simp] theorem indexLaurentPullbackValuedEmbedding_valuation
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : WithVal (indexLaurentPullbackValuation P r level)) :
    Valued.v (indexLaurentPullbackValuedEmbedding P r level x) =
      Valued.v x :=
  rfl
theorem indexLaurentPullbackValuation_surjective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Surjective (indexLaurentPullbackValuation P r level) := by
  intro γ
  by_cases hγ : γ = 0
  · use 0
    simp [hγ]
  · obtain ⟨z, hz⟩ :=
      LaurentSeries.valuation_surjective
        (ResidueField P r level) γ
    obtain ⟨x, hx⟩ :=
      (denseRange_functionFieldToIndexCongruenceLocalField P r level).mem_nhds
        (Valued.locally_const (hz.symm ▸ hγ))
    use x
    exact hx.trans hz
theorem denseRange_indexLaurentPullbackValuedEmbedding
    (P : BasePrime) (r : Rank) (level : Nat) :
    DenseRange (indexLaurentPullbackValuedEmbedding P r level) := by
  apply (denseRange_functionFieldToIndexCongruenceLocalField P r level).mono
  rintro _ ⟨x, rfl⟩
  exact ⟨WithVal.toVal (indexLaurentPullbackValuation P r level) x, rfl⟩
theorem indexLaurentPullbackWithVal_valuation_surjective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Surjective
      (Valued.v :
        WithVal (indexLaurentPullbackValuation P r level) →
          WithZero (Multiplicative ℤ)) := by
  intro γ
  obtain ⟨x, hx⟩ := indexLaurentPullbackValuation_surjective P r level γ
  exact ⟨WithVal.toVal (indexLaurentPullbackValuation P r level) x,
    by simpa using hx⟩
theorem isUniformInducing_indexLaurentPullbackValuedEmbedding
    (P : BasePrime) (r : Rank) (level : Nat) :
    IsUniformInducing (indexLaurentPullbackValuedEmbedding P r level) := by
  let v := indexLaurentPullbackValuation P r level
  let e := indexLaurentPullbackValuedEmbedding P r level
  have hsource : Function.Surjective
      (Valued.v : WithVal v → WithZero (Multiplicative ℤ)) := by
    simpa [v] using
      indexLaurentPullbackWithVal_valuation_surjective P r level
  apply ((Valued.hasBasis_uniformity (WithVal v)
      (WithZero (Multiplicative ℤ))).isUniformInducing_iff
    (Valued.hasBasis_uniformity (IndexCongruenceLocalField P r level)
      (WithZero (Multiplicative ℤ)))).mpr
  constructor
  · intro γ _
    obtain ⟨x, hx⟩ := hsource (embedding γ.1)
    let δ := Units.mk0 (Valued.v.restrict x) (by
      intro hx0
      have hxzero : x = 0 := by
        exact (Valuation.zero_iff Valued.v).mp
          ((Valuation.restrict_eq_zero_iff (v := Valued.v)).mp hx0)
      subst x
      have hγ0 : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := by simp
      exact hγ0 (hx.symm.trans (map_zero Valued.v)))
    refine ⟨δ, trivial, ?_⟩
    intro a b hab
    simp only [Set.mem_setOf_eq] at hab ⊢
    rw [Valuation.restrict_lt_iff_lt_embedding] at hab ⊢
    rw [← map_sub, indexLaurentPullbackValuedEmbedding_valuation]
    change Valued.v (b - a) <
      MonoidWithZeroHom.ValueGroup₀.embedding (Valued.v.restrict x) at hab
    rw [Valuation.embedding_restrict, hx] at hab
    exact hab
  · intro δ _
    obtain ⟨z, hz⟩ := LaurentSeries.valuation_surjective
      (ResidueField P r level) (embedding δ.1)
    let γ := Units.mk0 (Valued.v.restrict z) (by
      intro hz0
      have hzzero : z = 0 := by
        exact (Valuation.zero_iff Valued.v).mp
          ((Valuation.restrict_eq_zero_iff (v := Valued.v)).mp hz0)
      subst z
      have hδ0 : MonoidWithZeroHom.ValueGroup₀.embedding δ.1 ≠ 0 := by simp
      exact hδ0 (hz.symm.trans (map_zero Valued.v)))
    refine ⟨γ, trivial, ?_⟩
    intro a b hab
    simp only [Set.mem_setOf_eq] at hab ⊢
    rw [Valuation.restrict_lt_iff_lt_embedding] at hab ⊢
    rw [← map_sub, indexLaurentPullbackValuedEmbedding_valuation] at hab
    change Valued.v (b - a) <
      MonoidWithZeroHom.ValueGroup₀.embedding (Valued.v.restrict z) at hab
    rw [Valuation.embedding_restrict, hz] at hab
    exact hab
noncomputable def indexLaurentLocalFieldCompletionPkg
    (P : BasePrime) (r : Rank) (level : Nat) :
    AbstractCompletion
      (WithVal (indexLaurentPullbackValuation P r level)) where
  space := IndexCongruenceLocalField P r level
  coe := indexLaurentPullbackValuedEmbedding P r level
  uniformStruct := inferInstance
  complete := inferInstance
  separation := inferInstance
  isUniformInducing :=
    isUniformInducing_indexLaurentPullbackValuedEmbedding P r level
  dense := denseRange_indexLaurentPullbackValuedEmbedding P r level
noncomputable def indexLaurentPullbackCompletionEquivLocalField
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexLaurentPullbackCompletion P r level ≃ᵤ
      IndexCongruenceLocalField P r level :=
  AbstractCompletion.compareEquiv UniformSpace.Completion.cPkg
    (indexLaurentLocalFieldCompletionPkg P r level)
@[simp] theorem indexLaurentPullbackCompletionEquivLocalField_coe
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : WithVal (indexLaurentPullbackValuation P r level)) :
    indexLaurentPullbackCompletionEquivLocalField P r level x =
      indexLaurentPullbackValuedEmbedding P r level x :=
  AbstractCompletion.compare_coe UniformSpace.Completion.cPkg
    (indexLaurentLocalFieldCompletionPkg P r level) x
noncomputable def indexLaurentPullbackCompletionRingEquivLocalField
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexLaurentPullbackCompletion P r level ≃+*
      IndexCongruenceLocalField P r level := by
  let f := indexLaurentPullbackValuedEmbedding P r level
  let hf : Continuous f :=
    (isUniformInducing_indexLaurentPullbackValuedEmbedding
      P r level).uniformContinuous.continuous
  let F := UniformSpace.Completion.extensionHom f hf
  apply RingEquiv.ofBijective F
  have hF : (F : IndexLaurentPullbackCompletion P r level →
      IndexCongruenceLocalField P r level) =
      indexLaurentPullbackCompletionEquivLocalField P r level := rfl
  rw [hF]
  exact (indexLaurentPullbackCompletionEquivLocalField P r level).bijective
theorem indexLaurentPullbackCompletionRingEquiv_eq_uniformEquiv
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : IndexLaurentPullbackCompletion P r level) :
    indexLaurentPullbackCompletionRingEquivLocalField P r level x =
      indexLaurentPullbackCompletionEquivLocalField P r level x :=
  rfl
theorem indexLaurentPullbackCompletionEquivLocalField_valuation
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : IndexLaurentPullbackCompletion P r level) :
    Valued.v
        (indexLaurentPullbackCompletionEquivLocalField P r level x) =
      Valued.v x := by
  let v := indexLaurentPullbackValuation P r level
  have htarget : Continuous
      (Valued.v : IndexCongruenceLocalField P r level →
        WithZero (Multiplicative ℤ)) :=
    Valued.continuous_valuation_of_surjective
      (LaurentSeries.valuation_surjective (ResidueField P r level))
  have hsourceSurj : Function.Surjective
      (Valued.v : IndexLaurentPullbackCompletion P r level →
        WithZero (Multiplicative ℤ)) :=
    (Valued.valuedCompletion_surjective_iff
      (K := WithVal v) (Γ₀ := WithZero (Multiplicative ℤ))).mpr
      (by simpa [v] using
        indexLaurentPullbackWithVal_valuation_surjective P r level)
  have hsource : Continuous
      (Valued.v : IndexLaurentPullbackCompletion P r level →
        WithZero (Multiplicative ℤ)) :=
    Valued.continuous_valuation_of_surjective hsourceSurj
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
      exact isClosed_eq
        (htarget.comp
          (indexLaurentPullbackCompletionEquivLocalField
            P r level).continuous)
        hsource
  | ih a =>
      rw [indexLaurentPullbackCompletionEquivLocalField_coe,
        indexLaurentPullbackValuedEmbedding_valuation,
        Valued.valuedCompletion_apply]
theorem indexLaurentPullbackCompletionEquivLocalField_le_one_iff
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : IndexLaurentPullbackCompletion P r level) :
    Valued.v x ≤ 1 ↔
      Valued.v
        (indexLaurentPullbackCompletionEquivLocalField P r level x) ≤ 1 := by
  rw [indexLaurentPullbackCompletionEquivLocalField_valuation]
noncomputable def indexAdicCompletionRingEquivLocalField
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexCongruenceAdicCompletion P r level ≃+*
      IndexCongruenceLocalField P r level :=
  (indexAdicCompletionRingEquivLaurentPullbackCompletion P r level).trans
    (indexLaurentPullbackCompletionRingEquivLocalField P r level)
noncomputable def indexAdicCompletionEquivLocalField
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexCongruenceAdicCompletion P r level ≃ᵤ
      IndexCongruenceLocalField P r level :=
  (indexAdicCompletionEquivLaurentPullbackCompletion P r level).trans
    (indexLaurentPullbackCompletionEquivLocalField P r level)
theorem indexAdicCompletionRingEquivLocalField_eq_uniformEquiv
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : IndexCongruenceAdicCompletion P r level) :
    indexAdicCompletionRingEquivLocalField P r level x =
      indexAdicCompletionEquivLocalField P r level x :=
  rfl
@[simp] theorem indexAdicCompletionRingEquivLocalField_algebraMap
    (P : BasePrime) (r : Rank) (level : Nat) (x : FunctionField P) :
    indexAdicCompletionRingEquivLocalField P r level
        (algebraMap (FunctionField P)
          (IndexCongruenceAdicCompletion P r level) x) =
      functionFieldToIndexCongruenceLocalField P r level x := by
  rw [indexAdicCompletionRingEquivLocalField,
    RingEquiv.trans_apply,
    indexAdicCompletionRingEquiv_eq_uniformEquiv,
    indexAdicCompletionEquivLaurentPullbackCompletion_algebraMap,
    indexLaurentPullbackCompletionRingEquiv_eq_uniformEquiv,
    indexLaurentPullbackCompletionEquivLocalField_coe]
  rfl
noncomputable def indexAdicCompletionAlgEquivLocalField
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexCongruenceAdicCompletion P r level ≃ₐ[FunctionField P]
      IndexCongruenceLocalField P r level where
  __ := indexAdicCompletionRingEquivLocalField P r level
  commutes' x :=
    indexAdicCompletionRingEquivLocalField_algebraMap P r level x
noncomputable def cyclicAlgebraToIndexLocalMatrix
    (P : BasePrime) (r : Rank) (level : Nat) :
    CyclicAlgebra P r →ₐ[FunctionField P]
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (IndexCongruenceLocalField P r level) where
  toFun x := x.1.map
    (splittingFunctionFieldToIndexCongruenceLocalField P r level)
  map_one' := by
    apply Matrix.ext
    intro i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [Matrix.one_apply, hij]
  map_mul' x y := Matrix.map_mul
  map_zero' := by
    apply Matrix.ext
    intro i j
    simp
  map_add' x y := by
    apply Matrix.ext
    intro i j
    simp
  commutes' x := by
    change
      (algebraMap (FunctionField P)
        (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (SplittingFunctionField P r)) x).map
          (splittingFunctionFieldToIndexCongruenceLocalField P r level) =
        algebraMap (FunctionField P)
          (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (IndexCongruenceLocalField P r level)) x
    apply Matrix.map_algebraMap
    · exact map_zero
        (splittingFunctionFieldToIndexCongruenceLocalField P r level)
    · exact
        splittingFunctionFieldToIndexCongruenceLocalField_functionFieldEmbedding
          P r level x
noncomputable def indexAdicCompletionToIndexLocalMatrix
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexCongruenceAdicCompletion P r level →ₐ[FunctionField P]
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (IndexCongruenceLocalField P r level) :=
  ((Algebra.ofId (IndexCongruenceLocalField P r level)
    (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (IndexCongruenceLocalField P r level))).restrictScalars
        (FunctionField P)).comp
    (indexAdicCompletionAlgEquivLocalField P r level).toAlgHom
noncomputable def indexAdicCyclicAlgebraToIndexLocalMatrix
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexAdicCyclicAlgebra P r level →ₐ[FunctionField P]
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (IndexCongruenceLocalField P r level) :=
  Algebra.TensorProduct.lift
    (indexAdicCompletionToIndexLocalMatrix P r level)
    (cyclicAlgebraToIndexLocalMatrix P r level)
    (fun a x => by
      change Commute
        (algebraMap (IndexCongruenceLocalField P r level)
          (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (IndexCongruenceLocalField P r level))
          (indexAdicCompletionAlgEquivLocalField P r level a))
        ((x.1.map
          (splittingFunctionFieldToIndexCongruenceLocalField
            P r level)) :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (IndexCongruenceLocalField P r level))
      exact Algebra.commutes _ _)
@[simp] theorem indexAdicCyclicAlgebraToIndexLocalMatrix_tmul
    (P : BasePrime) (r : Rank) (level : Nat)
    (a : IndexCongruenceAdicCompletion P r level)
    (x : CyclicAlgebra P r) :
    indexAdicCyclicAlgebraToIndexLocalMatrix P r level
        (TensorProduct.tmul (FunctionField P) a x) =
      (indexAdicCompletionAlgEquivLocalField P r level a) •
        cyclicAlgebraToIndexLocalMatrix P r level x := by
  rw [indexAdicCyclicAlgebraToIndexLocalMatrix,
    Algebra.TensorProduct.lift_tmul]
  rw [Algebra.smul_def]
  rfl
noncomputable def indexLocalCyclicBasisVector
    (P : BasePrime) (r : Rank) (level : Nat)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (IndexCongruenceLocalField P r level) :=
  (completedIndexCyclicBasisVector P r level p).map
    (HahnSeries.ofPowerSeries ℤ (ResidueField P r level))
theorem indexLocalCyclicBasisVector_det_isUnit
    (P : BasePrime) (r : Rank) (level : Nat) :
    IsUnit ((Matrix.stdBasis (IndexCongruenceLocalField P r level)
      (Fin r.matrixRank) (Fin r.matrixRank)).det
        (indexLocalCyclicBasisVector P r level)) := by
  let f := HahnSeries.ofPowerSeries ℤ (ResidueField P r level)
  have hunit :=
    (completedIndexCyclicBasisVector_det_isUnit P r level).map f
  have hmap :
      f ((Matrix.stdBasis (PowerSeries (ResidueField P r level))
        (Fin r.matrixRank) (Fin r.matrixRank)).det
          (completedIndexCyclicBasisVector P r level)) =
        (Matrix.stdBasis (IndexCongruenceLocalField P r level)
          (Fin r.matrixRank) (Fin r.matrixRank)).det
            (indexLocalCyclicBasisVector P r level) := by
    simp only [Module.Basis.det_apply]
    rw [RingHom.map_det]
    apply congrArg Matrix.det
    apply Matrix.ext
    intro p q
    rw [RingHom.mapMatrix_apply, Matrix.map_apply,
      Module.Basis.toMatrix_apply, Module.Basis.toMatrix_apply]
    rw [show (Matrix.stdBasis (PowerSeries (ResidueField P r level))
        (Fin r.matrixRank) (Fin r.matrixRank)).repr
          (completedIndexCyclicBasisVector P r level q) p =
        completedIndexCyclicBasisVector P r level q p.1 p.2 by
          simp [Matrix.stdBasis]]
    rw [show (Matrix.stdBasis (IndexCongruenceLocalField P r level)
        (Fin r.matrixRank) (Fin r.matrixRank)).repr
          (indexLocalCyclicBasisVector P r level q) p =
        indexLocalCyclicBasisVector P r level q p.1 p.2 by
          simp [Matrix.stdBasis]]
    rfl
  rwa [hmap] at hunit
noncomputable def indexLocalCyclicBasis
    (P : BasePrime) (r : Rank) (level : Nat) :
    Module.Basis (Fin r.matrixRank × Fin r.matrixRank)
      (IndexCongruenceLocalField P r level)
      (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (IndexCongruenceLocalField P r level)) := by
  let hbasis := (Module.Basis.is_basis_iff_det
    (Matrix.stdBasis (IndexCongruenceLocalField P r level)
      (Fin r.matrixRank) (Fin r.matrixRank))).mpr
        (indexLocalCyclicBasisVector_det_isUnit P r level)
  exact Module.Basis.mk hbasis.1 hbasis.2.ge
@[simp] theorem indexLocalCyclicBasis_apply
    (P : BasePrime) (r : Rank) (level : Nat)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    indexLocalCyclicBasis P r level p =
      indexLocalCyclicBasisVector P r level p := by
  simp [indexLocalCyclicBasis]
noncomputable abbrev IndexLocalCyclicAlgebra
    (P : BasePrime) (r : Rank) (level : Nat) :=
  TensorProduct (FunctionField P)
    (IndexCongruenceLocalField P r level) (CyclicAlgebra P r)
noncomputable def indexAdicCyclicAlgebraToIndexLocalCyclicAlgebra
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexAdicCyclicAlgebra P r level →ₐ[FunctionField P]
      IndexLocalCyclicAlgebra P r level :=
  Algebra.TensorProduct.map
    (indexAdicCompletionAlgEquivLocalField P r level).toAlgHom
    (AlgHom.id (FunctionField P) (CyclicAlgebra P r))
theorem indexAdicCyclicAlgebraToIndexLocalCyclicAlgebra_bijective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Bijective
      (indexAdicCyclicAlgebraToIndexLocalCyclicAlgebra P r level) :=
  Algebra.TensorProduct.map_bijective
    (indexAdicCompletionAlgEquivLocalField P r level).bijective
    Function.bijective_id
noncomputable def indexAdicCyclicAlgebraEquivIndexLocalCyclicAlgebra
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexAdicCyclicAlgebra P r level ≃ₐ[FunctionField P]
      IndexLocalCyclicAlgebra P r level :=
  AlgEquiv.ofBijective
    (indexAdicCyclicAlgebraToIndexLocalCyclicAlgebra P r level)
    (indexAdicCyclicAlgebraToIndexLocalCyclicAlgebra_bijective P r level)
noncomputable def indexLocalCyclicAlgebraToMatrix
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexLocalCyclicAlgebra P r level
      →ₐ[IndexCongruenceLocalField P r level]
        Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (IndexCongruenceLocalField P r level) :=
  Algebra.TensorProduct.lift
    (Algebra.ofId (IndexCongruenceLocalField P r level)
      (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (IndexCongruenceLocalField P r level)))
    (cyclicAlgebraToIndexLocalMatrix P r level)
    (fun a x => by
      change Commute
        (algebraMap (IndexCongruenceLocalField P r level)
          (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (IndexCongruenceLocalField P r level)) a)
        (cyclicAlgebraToIndexLocalMatrix P r level x)
      exact Algebra.commutes _ _)
@[simp] theorem indexLocalCyclicAlgebraToMatrix_tmul
    (P : BasePrime) (r : Rank) (level : Nat)
    (a : IndexCongruenceLocalField P r level)
    (x : CyclicAlgebra P r) :
    indexLocalCyclicAlgebraToMatrix P r level
        (TensorProduct.tmul (FunctionField P) a x) =
      a • cyclicAlgebraToIndexLocalMatrix P r level x := by
  rw [indexLocalCyclicAlgebraToMatrix, Algebra.TensorProduct.lift_tmul,
    Algebra.smul_def]
  rfl
@[simp] theorem indexLocalCyclicAlgebraToMatrix_includeRight
    (P : BasePrime) (r : Rank) (level : Nat) (x : CyclicAlgebra P r) :
    indexLocalCyclicAlgebraToMatrix P r level
        (Algebra.TensorProduct.includeRight x) =
      cyclicAlgebraToIndexLocalMatrix P r level x := by
  rw [Algebra.TensorProduct.includeRight_apply,
    indexLocalCyclicAlgebraToMatrix_tmul, one_smul]
theorem cyclicAlgebraToIndexLocalMatrix_basis
    (P : BasePrime) (r : Rank) (level : Nat)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    cyclicAlgebraToIndexLocalMatrix P r level
        (functionFieldCyclicBasis P r p) =
      indexLocalCyclicBasisVector P r level p := by
  change ((functionFieldCyclicBasis P r p : CyclicAlgebra P r).1).map
      (splittingFunctionFieldToIndexCongruenceLocalField P r level) = _
  rw [functionFieldCyclicBasis_apply]
  change (splittingCyclicBasisVector P r p).map
      (splittingFunctionFieldToIndexCongruenceLocalField P r level) = _
  rw [← orderIndexCyclicBasisVector_to_global P r p,
    Matrix.map_map]
  change (orderIndexCyclicBasisVector P r p).map
      (fun x => splittingFunctionFieldToIndexCongruenceLocalField P r level
        (constantArithmeticToSplittingFunctionField P r x)) =
    ((orderIndexCyclicBasisVector P r p).map
      (indexCompletedArithmeticEval P r level)).map
        (HahnSeries.ofPowerSeries ℤ (ResidueField P r level))
  rw [Matrix.map_map]
  congr 1
  funext x
  exact DFunLike.congr_fun
    (splittingFunctionFieldToIndexCongruenceLocalField_constantArithmetic
      P r level) x
@[simp] theorem indexAdicCyclicAlgebraToIndexLocalMatrix_basis
    (P : BasePrime) (r : Rank) (level : Nat)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    indexAdicCyclicAlgebraToIndexLocalMatrix P r level
        (indexAdicCyclicBasis P r level p) =
      indexLocalCyclicBasis P r level p := by
  rw [indexAdicCyclicBasis, Module.Basis.baseChange_apply,
    indexAdicCyclicAlgebraToIndexLocalMatrix_tmul, map_one, one_smul,
    cyclicAlgebraToIndexLocalMatrix_basis,
    indexLocalCyclicBasis_apply]
theorem indexLocalCyclicBasis_sum_completed_equivFun
    (P : BasePrime) (r : Rank) (level : Nat)
    (M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (PowerSeries (ResidueField P r level))) :
    (∑ p, HahnSeries.ofPowerSeries ℤ (ResidueField P r level)
        ((completedIndexCyclicBasis P r level).equivFun M p) •
          indexLocalCyclicBasis P r level p) =
      M.map (HahnSeries.ofPowerSeries ℤ (ResidueField P r level)) := by
  have hsum := (completedIndexCyclicBasis P r level).sum_equivFun M
  apply Matrix.ext
  intro i j
  have hij := congrArg
    (fun N : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (PowerSeries (ResidueField P r level)) =>
        HahnSeries.ofPowerSeries ℤ (ResidueField P r level) (N i j)) hsum
  simpa [indexLocalCyclicBasis_apply, indexLocalCyclicBasisVector,
    completedIndexCyclicBasis_apply, Matrix.sum_apply] using hij
theorem indexCyclicBasis_sum_completed_equivFun_constantCoeff
    (P : BasePrime) (r : Rank) (level : Nat)
    (M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (PowerSeries (ResidueField P r level))) :
    (∑ p, PowerSeries.constantCoeff
        ((completedIndexCyclicBasis P r level).equivFun M p) •
          indexCyclicBasis P r level p) =
      M.map PowerSeries.constantCoeff := by
  have hsum := (completedIndexCyclicBasis P r level).sum_equivFun M
  apply Matrix.ext
  intro i j
  have hij := congrArg
    (fun N : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (PowerSeries (ResidueField P r level)) =>
        PowerSeries.constantCoeff (N i j)) hsum
  have hred (p : Fin r.matrixRank × Fin r.matrixRank) :
      PowerSeries.constantCoeff
          (completedIndexCyclicBasisVector P r level p i j) =
        indexCyclicBasisVector P r level p i j :=
    congrFun (congrFun
      (completedIndexCyclicBasisVector_reduction P r level p) i) j
  simpa [indexCyclicBasis_apply, completedIndexCyclicBasis_apply,
    Matrix.sum_apply, hred] using hij
noncomputable def indexLocalCyclicScalarExtensionBasis
    (P : BasePrime) (r : Rank) (level : Nat) :
    Module.Basis (Fin r.matrixRank × Fin r.matrixRank)
      (IndexCongruenceLocalField P r level)
      (IndexLocalCyclicAlgebra P r level) :=
  (functionFieldCyclicBasis P r).baseChange
    (IndexCongruenceLocalField P r level)
@[simp] theorem indexLocalCyclicAlgebraToMatrix_basis
    (P : BasePrime) (r : Rank) (level : Nat)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    indexLocalCyclicAlgebraToMatrix P r level
        (indexLocalCyclicScalarExtensionBasis P r level p) =
      indexLocalCyclicBasis P r level p := by
  rw [indexLocalCyclicScalarExtensionBasis, Module.Basis.baseChange_apply,
    indexLocalCyclicAlgebraToMatrix_tmul,
    cyclicAlgebraToIndexLocalMatrix_basis,
    indexLocalCyclicBasis_apply, one_smul]
theorem indexLocalCyclicAlgebraToMatrix_bijective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Bijective (indexLocalCyclicAlgebraToMatrix P r level) := by
  let e := (indexLocalCyclicScalarExtensionBasis P r level).equiv
    (indexLocalCyclicBasis P r level) (Equiv.refl _)
  have heq : (indexLocalCyclicAlgebraToMatrix P r level).toLinearMap =
      e.toLinearMap := by
    apply (indexLocalCyclicScalarExtensionBasis P r level).ext
    intro p
    change indexLocalCyclicAlgebraToMatrix P r level
        (indexLocalCyclicScalarExtensionBasis P r level p) =
      e (indexLocalCyclicScalarExtensionBasis P r level p)
    rw [indexLocalCyclicAlgebraToMatrix_basis]
    exact (Module.Basis.equiv_apply
      (indexLocalCyclicScalarExtensionBasis P r level) p
      (indexLocalCyclicBasis P r level) (Equiv.refl _)).symm
  rw [show (indexLocalCyclicAlgebraToMatrix P r level : _ → _) = e by
    funext x
    exact DFunLike.congr_fun heq x]
  exact e.bijective
noncomputable def indexLocalCyclicAlgebraEquivMatrix
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexLocalCyclicAlgebra P r level
      ≃ₐ[IndexCongruenceLocalField P r level]
        Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (IndexCongruenceLocalField P r level) :=
  AlgEquiv.ofBijective (indexLocalCyclicAlgebraToMatrix P r level)
    (indexLocalCyclicAlgebraToMatrix_bijective P r level)
noncomputable def cyclicAlgebraToIndexLocalCoordinates
    (P : BasePrime) (r : Rank) (level : Nat) :
    CyclicAlgebra P r →
      ((Fin r.matrixRank × Fin r.matrixRank) →
        IndexCongruenceLocalField P r level) :=
  fun x p => functionFieldToIndexCongruenceLocalField P r level
    ((functionFieldCyclicBasis P r).equivFun x p)
theorem indexAdicCyclicAlgebraToIndexLocalMatrix_factorization
    (P : BasePrime) (r : Rank) (level : Nat) :
    indexAdicCyclicAlgebraToIndexLocalMatrix P r level =
      ((indexLocalCyclicAlgebraToMatrix P r level).restrictScalars
        (FunctionField P)).comp
          (indexAdicCyclicAlgebraToIndexLocalCyclicAlgebra P r level) := by
  apply Algebra.TensorProduct.ext
  · ext a
    simp [indexAdicCyclicAlgebraToIndexLocalMatrix,
      indexAdicCompletionToIndexLocalMatrix,
      indexAdicCyclicAlgebraToIndexLocalCyclicAlgebra,
      indexLocalCyclicAlgebraToMatrix]
  · ext x
    simp [indexAdicCyclicAlgebraToIndexLocalMatrix,
      indexAdicCyclicAlgebraToIndexLocalCyclicAlgebra,
      indexLocalCyclicAlgebraToMatrix]
theorem indexAdicCyclicAlgebraToIndexLocalMatrix_bijective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Bijective
      (indexAdicCyclicAlgebraToIndexLocalMatrix P r level) := by
  rw [indexAdicCyclicAlgebraToIndexLocalMatrix_factorization]
  exact (indexLocalCyclicAlgebraToMatrix_bijective P r level).comp
    (indexAdicCyclicAlgebraToIndexLocalCyclicAlgebra_bijective P r level)
noncomputable def indexAdicCyclicAlgebraEquivIndexLocalMatrix
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexAdicCyclicAlgebra P r level ≃ₐ[FunctionField P]
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (IndexCongruenceLocalField P r level) :=
  AlgEquiv.ofBijective
    (indexAdicCyclicAlgebraToIndexLocalMatrix P r level)
    (indexAdicCyclicAlgebraToIndexLocalMatrix_bijective P r level)
noncomputable def indexLocalCyclicAlgebraUnitEquivGL
    (P : BasePrime) (r : Rank) (level : Nat) :
    (IndexLocalCyclicAlgebra P r level)ˣ ≃*
      Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (IndexCongruenceLocalField P r level) :=
  Units.mapEquiv
    (indexLocalCyclicAlgebraEquivMatrix P r level).toMulEquiv
noncomputable def indexLocalCyclicAlgebraReducedNorm
    (P : BasePrime) (r : Rank) (level : Nat) :
    (IndexLocalCyclicAlgebra P r level)ˣ →*
      (IndexCongruenceLocalField P r level)ˣ :=
  Matrix.GeneralLinearGroup.det.comp
    (indexLocalCyclicAlgebraUnitEquivGL P r level).toMonoidHom
noncomputable def IndexLocalCyclicAlgebraNormOne
    (P : BasePrime) (r : Rank) (level : Nat) :
    Subgroup (IndexLocalCyclicAlgebra P r level)ˣ :=
  (indexLocalCyclicAlgebraReducedNorm P r level).ker
noncomputable def indexLocalCyclicAlgebraNormOneEquivSL
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexLocalCyclicAlgebraNormOne P r level ≃*
      Matrix.SpecialLinearGroup (Fin r.matrixRank)
        (IndexCongruenceLocalField P r level) where
  toFun u :=
    ⟨((indexLocalCyclicAlgebraUnitEquivGL P r level u :
        Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (IndexCongruenceLocalField P r level)) :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (IndexCongruenceLocalField P r level)),
      congrArg Units.val u.property⟩
  invFun s :=
    ⟨(indexLocalCyclicAlgebraUnitEquivGL P r level).symm
        (Matrix.SpecialLinearGroup.toGL s), by
      change indexLocalCyclicAlgebraReducedNorm P r level
        ((indexLocalCyclicAlgebraUnitEquivGL P r level).symm
          (Matrix.SpecialLinearGroup.toGL s)) = 1
      rw [indexLocalCyclicAlgebraReducedNorm]
      simp⟩
  left_inv u := by
    apply Subtype.ext
    apply (indexLocalCyclicAlgebraUnitEquivGL P r level).injective
    apply Units.ext
    simp
    rfl
  right_inv s := by
    apply Matrix.SpecialLinearGroup.toGL_injective
    apply Units.ext
    simp
    rfl
  map_mul' u v := by
    apply Matrix.SpecialLinearGroup.toGL_injective
    apply Units.ext
    simp
    rfl
theorem indexAdicCompletionRingEquivLocalField_le_one_iff
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : IndexCongruenceAdicCompletion P r level) :
    Valued.v x ≤ 1 ↔
      Valued.v (indexAdicCompletionRingEquivLocalField P r level x) ≤ 1 := by
  simpa [indexAdicCompletionRingEquivLocalField, RingEquiv.trans_apply,
    indexAdicCompletionRingEquiv_eq_uniformEquiv,
    indexLaurentPullbackCompletionRingEquiv_eq_uniformEquiv] using
    (indexAdicCompletionEquivLaurentPullbackCompletion_le_one_iff
      P r level x).trans
      (indexLaurentPullbackCompletionEquivLocalField_le_one_iff
        P r level
        (indexAdicCompletionEquivLaurentPullbackCompletion P r level x))
noncomputable abbrev IndexCongruenceLocalIntegers
    (P : BasePrime) (r : Rank) (level : Nat) :=
  (Valued.v : Valuation (IndexCongruenceLocalField P r level) _).valuationSubring
noncomputable def indexAdicIntegersRingEquivLocalIntegers
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexCongruenceAdicIntegers P r level ≃+*
      IndexCongruenceLocalIntegers P r level where
  toFun x :=
    ⟨indexAdicCompletionRingEquivLocalField P r level x,
      (indexAdicCompletionRingEquivLocalField_le_one_iff
        P r level x).mp x.property⟩
  invFun y := by
    let x := (indexAdicCompletionRingEquivLocalField P r level).symm y.1
    refine ⟨x, ?_⟩
    apply (indexAdicCompletionRingEquivLocalField_le_one_iff
      P r level x).mpr
    change Valued.v
      (indexAdicCompletionRingEquivLocalField P r level
        ((indexAdicCompletionRingEquivLocalField P r level).symm y.1)) ≤ 1
    rw [(indexAdicCompletionRingEquivLocalField P r level).apply_symm_apply]
    exact y.property
  left_inv x := by
    apply Subtype.ext
    exact (indexAdicCompletionRingEquivLocalField P r level).symm_apply_apply x
  right_inv y := by
    apply Subtype.ext
    exact (indexAdicCompletionRingEquivLocalField P r level).apply_symm_apply y
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul (indexAdicCompletionRingEquivLocalField P r level) x.1 y.1
  map_add' x y := by
    apply Subtype.ext
    exact map_add (indexAdicCompletionRingEquivLocalField P r level) x.1 y.1
noncomputable def indexCongruenceLocalIntegersRingEquivPowerSeries
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexCongruenceLocalIntegers P r level ≃+*
      PowerSeries (ResidueField P r level) := by
  let f : PowerSeries (ResidueField P r level) →+*
      IndexCongruenceLocalIntegers P r level :=
    (HahnSeries.ofPowerSeries ℤ (ResidueField P r level)).codRestrict
      (IndexCongruenceLocalIntegers P r level) (fun s => by
        rw [Valuation.mem_valuationSubring_iff,
          LaurentSeries.val_le_one_iff_eq_coe]
        exact ⟨s, rfl⟩)
  exact (RingEquiv.ofBijective f ⟨
    fun x y hxy =>
      HahnSeries.ofPowerSeries_injective
        (congr_arg Subtype.val hxy),
    fun z => by
      have hz := z.property
      rw [Valuation.mem_valuationSubring_iff,
        LaurentSeries.val_le_one_iff_eq_coe] at hz
      obtain ⟨s, hs⟩ := hz
      exact ⟨s, Subtype.ext hs⟩⟩).symm
noncomputable def indexAdicIntegersRingEquivPowerSeries
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexCongruenceAdicIntegers P r level ≃+*
      PowerSeries (ResidueField P r level) :=
  (indexAdicIntegersRingEquivLocalIntegers P r level).trans
    (indexCongruenceLocalIntegersRingEquivPowerSeries P r level)
noncomputable def indexCompletedMatrixToIndexAdicCyclicAlgebra
    (P : BasePrime) (r : Rank) (level : Nat)
    (M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (PowerSeries (ResidueField P r level))) :
    IndexAdicCyclicAlgebra P r level :=
  (indexAdicCyclicBasis P r level).equivFun.symm
    (fun p =>
      (((indexAdicIntegersRingEquivPowerSeries P r level).symm
        ((completedIndexCyclicBasis P r level).equivFun M p) :
          IndexCongruenceAdicIntegers P r level) :
            IndexCongruenceAdicCompletion P r level))
@[simp] theorem indexAdicCyclicBasis_equivFun_completedMatrixLift
    (P : BasePrime) (r : Rank) (level : Nat)
    (M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (PowerSeries (ResidueField P r level)))
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    (indexAdicCyclicBasis P r level).equivFun
        (indexCompletedMatrixToIndexAdicCyclicAlgebra P r level M) p =
      (((indexAdicIntegersRingEquivPowerSeries P r level).symm
        ((completedIndexCyclicBasis P r level).equivFun M p) :
          IndexCongruenceAdicIntegers P r level) :
            IndexCongruenceAdicCompletion P r level) := by
  rw [indexCompletedMatrixToIndexAdicCyclicAlgebra]
  exact congrArg
    (fun f : (Fin r.matrixRank × Fin r.matrixRank) →
      IndexCongruenceAdicCompletion P r level => f p)
    ((indexAdicCyclicBasis P r level).equivFun.apply_symm_apply
      (fun q =>
        (((indexAdicIntegersRingEquivPowerSeries P r level).symm
          ((completedIndexCyclicBasis P r level).equivFun M q) :
            IndexCongruenceAdicIntegers P r level) :
              IndexCongruenceAdicCompletion P r level)))
theorem indexCompletedMatrixToIndexAdicCyclicAlgebra_mem_integral
    (P : BasePrime) (r : Rank) (level : Nat)
    (M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (PowerSeries (ResidueField P r level))) :
    indexCompletedMatrixToIndexAdicCyclicAlgebra P r level M ∈
      IndexAdicCyclicIntegralLattice P r level := by
  intro p
  rw [indexAdicCyclicBasis_equivFun_completedMatrixLift]
  exact ((indexAdicIntegersRingEquivPowerSeries P r level).symm
    ((completedIndexCyclicBasis P r level).equivFun M p)).property
noncomputable abbrev IndexAdicCyclicIntegralElement
    (P : BasePrime) (r : Rank) (level : Nat) :=
  ↥(IndexAdicCyclicIntegralLattice P r level)
noncomputable def indexAdicCyclicIntegralReductionCoordinates
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : IndexAdicCyclicIntegralElement P r level) :
    Fin r.matrixRank × Fin r.matrixRank → ResidueField P r level :=
  fun p => PowerSeries.constantCoeff
    (indexAdicIntegersRingEquivPowerSeries P r level
      ⟨(indexAdicCyclicBasis P r level).equivFun x.1 p,
        x.property p⟩)
noncomputable def indexAdicCyclicIntegralReduction
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexAdicCyclicIntegralElement P r level →
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (ResidueField P r level) :=
  fun x => (indexCyclicBasis P r level).equivFun.symm
    (indexAdicCyclicIntegralReductionCoordinates P r level x)
theorem indexAdicCyclicIntegralReduction_completedMatrixLift
    (P : BasePrime) (r : Rank) (level : Nat)
    (M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (PowerSeries (ResidueField P r level))) :
    indexAdicCyclicIntegralReduction P r level
        ⟨indexCompletedMatrixToIndexAdicCyclicAlgebra P r level M,
          indexCompletedMatrixToIndexAdicCyclicAlgebra_mem_integral
            P r level M⟩ =
      M.map PowerSeries.constantCoeff := by
  rw [indexAdicCyclicIntegralReduction,
    Module.Basis.equivFun_symm_apply,
    ← indexCyclicBasis_sum_completed_equivFun_constantCoeff P r level M]
  apply Finset.sum_congr rfl
  intro p _
  congr 1
  let z : IndexCongruenceAdicIntegers P r level :=
    ⟨(indexAdicCyclicBasis P r level).equivFun
      (indexCompletedMatrixToIndexAdicCyclicAlgebra P r level M) p,
      (indexCompletedMatrixToIndexAdicCyclicAlgebra_mem_integral
        P r level M) p⟩
  have hz : z =
      (indexAdicIntegersRingEquivPowerSeries P r level).symm
        ((completedIndexCyclicBasis P r level).equivFun M p) := by
    apply Subtype.ext
    exact indexAdicCyclicBasis_equivFun_completedMatrixLift P r level M p
  change PowerSeries.constantCoeff
      (indexAdicIntegersRingEquivPowerSeries P r level z) = _
  rw [hz, (indexAdicIntegersRingEquivPowerSeries
    P r level).apply_symm_apply]
theorem indexCongruenceLocalIntegersRingEquivPowerSeries_ofPowerSeries
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : PowerSeries (ResidueField P r level)) :
    indexCongruenceLocalIntegersRingEquivPowerSeries P r level
        ⟨HahnSeries.ofPowerSeries ℤ (ResidueField P r level) s, by
          rw [Valuation.mem_valuationSubring_iff,
            LaurentSeries.val_le_one_iff_eq_coe]
          exact ⟨s, rfl⟩⟩ = s := by
  apply (indexCongruenceLocalIntegersRingEquivPowerSeries
    P r level).symm.injective
  rw [(indexCongruenceLocalIntegersRingEquivPowerSeries
    P r level).symm_apply_apply]
  rfl
theorem indexAdicCompletionRingEquivLocalField_powerSeries_symm
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : PowerSeries (ResidueField P r level)) :
    indexAdicCompletionRingEquivLocalField P r level
        (((indexAdicIntegersRingEquivPowerSeries P r level).symm s :
          IndexCongruenceAdicIntegers P r level) :
            IndexCongruenceAdicCompletion P r level) =
      HahnSeries.ofPowerSeries ℤ (ResidueField P r level) s := by
  let z : IndexCongruenceAdicIntegers P r level :=
    (indexAdicIntegersRingEquivPowerSeries P r level).symm s
  let w : IndexCongruenceLocalIntegers P r level :=
    ⟨HahnSeries.ofPowerSeries ℤ (ResidueField P r level) s, by
      rw [Valuation.mem_valuationSubring_iff,
        LaurentSeries.val_le_one_iff_eq_coe]
      exact ⟨s, rfl⟩⟩
  have hz : indexCongruenceLocalIntegersRingEquivPowerSeries P r level
      (indexAdicIntegersRingEquivLocalIntegers P r level z) = s := by
    change indexAdicIntegersRingEquivPowerSeries P r level z = s
    exact (indexAdicIntegersRingEquivPowerSeries
      P r level).apply_symm_apply s
  have hw : indexCongruenceLocalIntegersRingEquivPowerSeries P r level w =
      s := by
    exact indexCongruenceLocalIntegersRingEquivPowerSeries_ofPowerSeries
      P r level s
  have hzw : indexAdicIntegersRingEquivLocalIntegers P r level z = w :=
    (indexCongruenceLocalIntegersRingEquivPowerSeries
      P r level).injective (hz.trans hw.symm)
  exact congrArg Subtype.val hzw
theorem indexAdicCyclicAlgebraToIndexLocalMatrix_completedMatrixLift
    (P : BasePrime) (r : Rank) (level : Nat)
    (M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (PowerSeries (ResidueField P r level))) :
    indexAdicCyclicAlgebraToIndexLocalMatrix P r level
        (indexCompletedMatrixToIndexAdicCyclicAlgebra P r level M) =
      M.map (HahnSeries.ofPowerSeries ℤ (ResidueField P r level)) := by
  rw [← indexLocalCyclicBasis_sum_completed_equivFun P r level M]
  conv_lhs =>
    rw [← (indexAdicCyclicBasis P r level).sum_equivFun
      (indexCompletedMatrixToIndexAdicCyclicAlgebra P r level M)]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro p _
  have hterm :
      (indexAdicCyclicBasis P r level).equivFun
          (indexCompletedMatrixToIndexAdicCyclicAlgebra P r level M) p •
        indexAdicCyclicBasis P r level p =
      TensorProduct.tmul (FunctionField P)
        ((indexAdicCyclicBasis P r level).equivFun
          (indexCompletedMatrixToIndexAdicCyclicAlgebra P r level M) p)
        (functionFieldCyclicBasis P r p) := by
    simp [indexAdicCyclicBasis, Module.Basis.baseChange_apply,
      TensorProduct.smul_tmul']
  rw [hterm, indexAdicCyclicAlgebraToIndexLocalMatrix_tmul,
    indexAdicCyclicBasis_equivFun_completedMatrixLift]
  change indexAdicCompletionRingEquivLocalField P r level
      (((indexAdicIntegersRingEquivPowerSeries P r level).symm
        ((completedIndexCyclicBasis P r level).equivFun M p) :
          IndexCongruenceAdicIntegers P r level) :
            IndexCongruenceAdicCompletion P r level) •
        cyclicAlgebraToIndexLocalMatrix P r level
          (functionFieldCyclicBasis P r p) = _
  rw [indexAdicCompletionRingEquivLocalField_powerSeries_symm,
    cyclicAlgebraToIndexLocalMatrix_basis,
    indexLocalCyclicBasis_apply]
theorem indexCongruenceLocalIntegers_constantCoeff_eq_zero_iff
    (P : BasePrime) (r : Rank) (level : Nat)
    (z : IndexCongruenceLocalIntegers P r level) :
    PowerSeries.constantCoeff
        (indexCongruenceLocalIntegersRingEquivPowerSeries P r level z) = 0 ↔
      Valued.v z.1 < 1 := by
  calc
    PowerSeries.constantCoeff
          (indexCongruenceLocalIntegersRingEquivPowerSeries P r level z) = 0 ↔
        ¬ IsUnit (PowerSeries.constantCoeff
          (indexCongruenceLocalIntegersRingEquivPowerSeries P r level z)) := by
      simp
    _ ↔ ¬ IsUnit
        (indexCongruenceLocalIntegersRingEquivPowerSeries P r level z) :=
      not_congr PowerSeries.isUnit_iff_constantCoeff.symm
    _ ↔ ¬ IsUnit z :=
      not_congr (isUnit_map_iff
        (indexCongruenceLocalIntegersRingEquivPowerSeries P r level) z)
    _ ↔ Valued.v z.1 < 1 :=
      Valuation.Integer.not_isUnit_iff_valuation_lt_one
noncomputable def arithmeticFiniteAdeleAtIndexLocalField
    (P : BasePrime) (r : Rank) (level : Nat) :
    ArithmeticFiniteAdeleRing P →+*
      IndexCongruenceLocalField P r level :=
  (indexAdicCompletionRingEquivLocalField P r level).toRingHom.comp
    (arithmeticFiniteAdeleAtIndexPlace P r level)
noncomputable def arithmeticFiniteAdeleSupportedAtIndexLocalField
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : IndexCongruenceLocalField P r level) :
    ArithmeticFiniteAdeleRing P :=
  arithmeticFiniteAdeleSupportedAtIndexPlace P r level
    ((indexAdicCompletionRingEquivLocalField P r level).symm x)
@[simp] theorem arithmeticFiniteAdeleAtIndexLocalField_supported
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : IndexCongruenceLocalField P r level) :
    arithmeticFiniteAdeleAtIndexLocalField P r level
        (arithmeticFiniteAdeleSupportedAtIndexLocalField P r level x) = x := by
  simp [arithmeticFiniteAdeleAtIndexLocalField,
    arithmeticFiniteAdeleSupportedAtIndexLocalField]
theorem continuous_arithmeticFiniteAdeleAtIndexLocalField
    (P : BasePrime) (r : Rank) (level : Nat) :
    Continuous (arithmeticFiniteAdeleAtIndexLocalField P r level) := by
  rw [show (arithmeticFiniteAdeleAtIndexLocalField P r level :
      ArithmeticFiniteAdeleRing P → IndexCongruenceLocalField P r level) =
      (indexAdicCompletionEquivLocalField P r level) ∘
        (fun a : ArithmeticFiniteAdeleRing P =>
          a (indexCongruencePlace P r level)) by
    funext a
    rw [Function.comp_apply, ←
      indexAdicCompletionRingEquivLocalField_eq_uniformEquiv]
    rfl]
  exact (indexAdicCompletionEquivLocalField P r level).continuous.comp
    (RestrictedProduct.continuous_eval (indexCongruencePlace P r level))
@[simp] theorem arithmeticFiniteAdeleAtIndexLocalField_diagonal
    (P : BasePrime) (r : Rank) (level : Nat) (x : FunctionField P) :
    arithmeticFiniteAdeleAtIndexLocalField P r level
        (functionFieldToArithmeticFiniteAdeles P x) =
      functionFieldToIndexCongruenceLocalField P r level x := by
  rw [arithmeticFiniteAdeleAtIndexLocalField, RingHom.comp_apply,
    arithmeticFiniteAdeleAtIndexPlace_diagonal]
  change indexAdicCompletionRingEquivLocalField P r level
      (algebraMap (FunctionField P)
        (IndexCongruenceAdicCompletion P r level) x) = _
  exact indexAdicCompletionRingEquivLocalField_algebraMap P r level x
noncomputable def ArithmeticFiniteAdelesIntegralAtIndex
    (P : BasePrime) (r : Rank) (level : Nat) :
    Subring (ArithmeticFiniteAdeleRing P) :=
  (IndexCongruenceLocalIntegers P r level).toSubring.comap
    (arithmeticFiniteAdeleAtIndexLocalField P r level)
noncomputable def arithmeticIntegralFiniteAdelesToIntegralAtIndex
    (P : BasePrime) (r : Rank) (level : Nat) :
    ArithmeticIntegralFiniteAdeles P →+*
      ArithmeticFiniteAdelesIntegralAtIndex P r level where
  toFun a := ⟨a.1, by
    change Valued.v
        (indexAdicCompletionRingEquivLocalField P r level
          (a.1 (indexCongruencePlace P r level))) ≤ 1
    apply (indexAdicCompletionRingEquivLocalField_le_one_iff
      P r level (a.1 (indexCongruencePlace P r level))).mp
    exact a.property (indexCongruencePlace P r level)⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl
  map_zero' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
theorem functionFieldToArithmeticFiniteAdeles_algebraMap_mem_integralAtIndex
    (P : BasePrime) (r : Rank) (level : Nat) (a : ArithmeticRing P) :
    functionFieldToArithmeticFiniteAdeles P
        (algebraMap (ArithmeticRing P) (FunctionField P) a) ∈
      ArithmeticFiniteAdelesIntegralAtIndex P r level := by
  change arithmeticFiniteAdeleAtIndexLocalField P r level
      (functionFieldToArithmeticFiniteAdeles P
        (algebraMap (ArithmeticRing P) (FunctionField P) a)) ∈
    IndexCongruenceLocalIntegers P r level
  rw [arithmeticFiniteAdeleAtIndexLocalField_diagonal,
    functionFieldToIndexCongruenceLocalField_algebraMap]
  rw [Valuation.mem_valuationSubring_iff,
    LaurentSeries.val_le_one_iff_eq_coe]
  exact ⟨indexCompletedBaseArithmeticEval P r level a, rfl⟩
noncomputable def arithmeticFiniteAdeleIntegralAtIndexToLocalIntegers
    (P : BasePrime) (r : Rank) (level : Nat) :
    ArithmeticFiniteAdelesIntegralAtIndex P r level →+*
      IndexCongruenceLocalIntegers P r level where
  toFun a := ⟨arithmeticFiniteAdeleAtIndexLocalField P r level a.1,
    a.property⟩
  map_one' := Subtype.ext (map_one
    (arithmeticFiniteAdeleAtIndexLocalField P r level))
  map_mul' a b := Subtype.ext (map_mul
    (arithmeticFiniteAdeleAtIndexLocalField P r level) a.1 b.1)
  map_zero' := Subtype.ext (map_zero
    (arithmeticFiniteAdeleAtIndexLocalField P r level))
  map_add' a b := Subtype.ext (map_add
    (arithmeticFiniteAdeleAtIndexLocalField P r level) a.1 b.1)
@[simp] theorem arithmeticFiniteAdeleIntegralAtIndexToLocalIntegers_diagonal
    (P : BasePrime) (r : Rank) (level : Nat) (a : ArithmeticRing P) :
    arithmeticFiniteAdeleIntegralAtIndexToLocalIntegers P r level
        ⟨functionFieldToArithmeticFiniteAdeles P
            (algebraMap (ArithmeticRing P) (FunctionField P) a),
          functionFieldToArithmeticFiniteAdeles_algebraMap_mem_integralAtIndex
            P r level a⟩ =
      ⟨HahnSeries.ofPowerSeries ℤ (ResidueField P r level)
          (indexCompletedBaseArithmeticEval P r level a), by
        rw [Valuation.mem_valuationSubring_iff,
          LaurentSeries.val_le_one_iff_eq_coe]
        exact ⟨indexCompletedBaseArithmeticEval P r level a, rfl⟩⟩ := by
  apply Subtype.ext
  change arithmeticFiniteAdeleAtIndexLocalField P r level
      (functionFieldToArithmeticFiniteAdeles P
        (algebraMap (ArithmeticRing P) (FunctionField P) a)) = _
  rw [arithmeticFiniteAdeleAtIndexLocalField_diagonal,
    functionFieldToIndexCongruenceLocalField_algebraMap]
  rfl
noncomputable def arithmeticFiniteAdeleIntegralAtIndexReduction
    (P : BasePrime) (r : Rank) (level : Nat) :
    ArithmeticFiniteAdelesIntegralAtIndex P r level →+*
      ResidueField P r level :=
  PowerSeries.constantCoeff.comp
    ((indexCongruenceLocalIntegersRingEquivPowerSeries P r level).toRingHom.comp
      (arithmeticFiniteAdeleIntegralAtIndexToLocalIntegers P r level))
theorem isOpen_ker_arithmeticFiniteAdeleIntegralAtIndexReduction
    (P : BasePrime) (r : Rank) (level : Nat) :
    IsOpen (RingHom.ker
      (arithmeticFiniteAdeleIntegralAtIndexReduction P r level) :
        Set (ArithmeticFiniteAdelesIntegralAtIndex P r level)) := by
  let f : ArithmeticFiniteAdelesIntegralAtIndex P r level →
      IndexCongruenceLocalField P r level := fun a =>
    arithmeticFiniteAdeleAtIndexLocalField P r level a.1
  have hf : Continuous f :=
    (continuous_arithmeticFiniteAdeleAtIndexLocalField P r level).comp
      continuous_subtype_val
  have hopen : IsOpen {x : IndexCongruenceLocalField P r level |
      Valued.v.restrict x < 1} :=
    Valued.isOpen_ball (IndexCongruenceLocalField P r level) 1
  rw [show (RingHom.ker
      (arithmeticFiniteAdeleIntegralAtIndexReduction P r level) :
        Set (ArithmeticFiniteAdelesIntegralAtIndex P r level)) =
      f ⁻¹' {x : IndexCongruenceLocalField P r level |
        Valued.v.restrict x < 1} by
    ext a
    change arithmeticFiniteAdeleIntegralAtIndexReduction P r level a = 0 ↔
      Valued.v.restrict (f a) < 1
    rw [Valuation.restrict_lt_one_iff]
    change PowerSeries.constantCoeff
        (indexCongruenceLocalIntegersRingEquivPowerSeries P r level
          (arithmeticFiniteAdeleIntegralAtIndexToLocalIntegers P r level a)) =
        0 ↔ _
    exact indexCongruenceLocalIntegers_constantCoeff_eq_zero_iff
      P r level
      (arithmeticFiniteAdeleIntegralAtIndexToLocalIntegers P r level a)]
  exact hopen.preimage hf
@[simp] theorem arithmeticFiniteAdeleIntegralAtIndexReduction_diagonal
    (P : BasePrime) (r : Rank) (level : Nat) (a : ArithmeticRing P) :
    arithmeticFiniteAdeleIntegralAtIndexReduction P r level
        ⟨functionFieldToArithmeticFiniteAdeles P
            (algebraMap (ArithmeticRing P) (FunctionField P) a),
          functionFieldToArithmeticFiniteAdeles_algebraMap_mem_integralAtIndex
            P r level a⟩ =
      indexArithmeticEval P r level a := by
  rw [arithmeticFiniteAdeleIntegralAtIndexReduction, RingHom.comp_apply,
    RingHom.comp_apply]
  change PowerSeries.constantCoeff
      (indexCongruenceLocalIntegersRingEquivPowerSeries P r level
        (arithmeticFiniteAdeleIntegralAtIndexToLocalIntegers P r level _)) = _
  rw [arithmeticFiniteAdeleIntegralAtIndexToLocalIntegers_diagonal,
    indexCongruenceLocalIntegersRingEquivPowerSeries_ofPowerSeries,
    indexCompletedBaseArithmeticEval_constantCoeff]
noncomputable def arithmeticIntegralFiniteAdeleReductionAtIndex
    (P : BasePrime) (r : Rank) (level : Nat) :
    ArithmeticIntegralFiniteAdeles P →+* ResidueField P r level :=
  (arithmeticFiniteAdeleIntegralAtIndexReduction P r level).comp
    (arithmeticIntegralFiniteAdelesToIntegralAtIndex P r level)
theorem arithmeticIntegralFiniteAdeleReductionAtIndex_eq_adic
    (P : BasePrime) (r : Rank) (level : Nat)
    (a : ArithmeticIntegralFiniteAdeles P) :
    arithmeticIntegralFiniteAdeleReductionAtIndex P r level a =
      PowerSeries.constantCoeff
        (indexAdicIntegersRingEquivPowerSeries P r level
          ⟨arithmeticFiniteAdeleAtIndexPlace P r level a.1,
            a.property (indexCongruencePlace P r level)⟩) := by
  rfl
@[simp] theorem arithmeticIntegralFiniteAdeleReductionAtIndex_diagonal
    (P : BasePrime) (r : Rank) (level : Nat) (a : ArithmeticRing P) :
    arithmeticIntegralFiniteAdeleReductionAtIndex P r level
        ⟨functionFieldToArithmeticFiniteAdeles P
            (algebraMap (ArithmeticRing P) (FunctionField P) a),
          functionFieldToArithmeticFiniteAdeles_algebraMap_mem_integral
            P a⟩ =
      indexArithmeticEval P r level a := by
  exact arithmeticFiniteAdeleIntegralAtIndexReduction_diagonal
    P r level a
theorem continuous_arithmeticIntegralFiniteAdelesToIntegralAtIndex
    (P : BasePrime) (r : Rank) (level : Nat) :
    Continuous
      (arithmeticIntegralFiniteAdelesToIntegralAtIndex P r level) := by
  exact Continuous.subtype_mk continuous_subtype_val _
theorem isOpen_ker_arithmeticIntegralFiniteAdeleReductionAtIndex
    (P : BasePrime) (r : Rank) (level : Nat) :
    IsOpen (RingHom.ker
      (arithmeticIntegralFiniteAdeleReductionAtIndex P r level) :
        Set (ArithmeticIntegralFiniteAdeles P)) := by
  rw [show (RingHom.ker
      (arithmeticIntegralFiniteAdeleReductionAtIndex P r level) :
        Set (ArithmeticIntegralFiniteAdeles P)) =
      (arithmeticIntegralFiniteAdelesToIntegralAtIndex P r level) ⁻¹'
        (RingHom.ker
          (arithmeticFiniteAdeleIntegralAtIndexReduction P r level) :
            Set (ArithmeticFiniteAdelesIntegralAtIndex P r level)) by
    ext a
    rfl]
  exact (isOpen_ker_arithmeticFiniteAdeleIntegralAtIndexReduction
    P r level).preimage
      (continuous_arithmeticIntegralFiniteAdelesToIntegralAtIndex
        P r level)
theorem continuous_ringHom_to_discrete_of_isOpen_ker
    {A B : Type*} [Ring A] [Ring B] [TopologicalSpace A]
    [IsTopologicalAddGroup A] [TopologicalSpace B] [DiscreteTopology B]
    (f : A →+* B) (hker : IsOpen (RingHom.ker f : Set A)) :
    Continuous f := by
  rw [continuous_discrete_rng]
  intro y
  by_cases hy : ∃ x, f x = y
  · obtain ⟨x, hx⟩ := hy
    rw [show f ⁻¹' {y} =
        (fun k : A => x + k) '' (RingHom.ker f : Set A) by
      ext z
      constructor
      · intro hz
        change f z = y at hz
        refine ⟨z - x, ?_, by abel⟩
        change f (z - x) = 0
        rw [map_sub, hz, hx, sub_self]
      · rintro ⟨k, hk, rfl⟩
        change f (x + k) = y
        change f k = 0 at hk
        rw [map_add, hx, hk, add_zero]]
    exact isOpenMap_add_left x _ hker
  · rw [show f ⁻¹' {y} = ∅ by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff,
        Set.mem_empty_iff_false, iff_false]
      exact fun hx => hy ⟨x, hx⟩]
    exact isOpen_empty
theorem continuous_arithmeticIntegralFiniteAdeleReductionAtIndex
    (P : BasePrime) (r : Rank) (level : Nat) :
    Continuous (arithmeticIntegralFiniteAdeleReductionAtIndex P r level) :=
  continuous_ringHom_to_discrete_of_isOpen_ker
    (arithmeticIntegralFiniteAdeleReductionAtIndex P r level)
    (isOpen_ker_arithmeticIntegralFiniteAdeleReductionAtIndex P r level)
noncomputable def arithmeticFiniteAdeleCyclicIntegralReductionCoordinates
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : ArithmeticFiniteAdeleCyclicIntegralElement P r) :
    Fin r.matrixRank × Fin r.matrixRank → ResidueField P r level :=
  fun p => arithmeticIntegralFiniteAdeleReductionAtIndex P r level
    ⟨(arithmeticFiniteAdeleCyclicBasis P r).equivFun x.1 p,
      x.property p⟩
noncomputable def arithmeticFiniteAdeleCyclicIntegralReduction
    (P : BasePrime) (r : Rank) (level : Nat) :
    ArithmeticFiniteAdeleCyclicIntegralElement P r →
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (ResidueField P r level) :=
  fun x => (indexCyclicBasis P r level).equivFun.symm
    (arithmeticFiniteAdeleCyclicIntegralReductionCoordinates
      P r level x)
@[simp] theorem indexCyclicBasis_equivFun_arithmeticFiniteAdeleCyclicReduction
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : ArithmeticFiniteAdeleCyclicIntegralElement P r) :
    (indexCyclicBasis P r level).equivFun
        (arithmeticFiniteAdeleCyclicIntegralReduction P r level x) =
      arithmeticFiniteAdeleCyclicIntegralReductionCoordinates
        P r level x :=
  (indexCyclicBasis P r level).equivFun.apply_symm_apply _
theorem arithmeticFiniteAdeleCyclicIntegralReduction_patchAtIndexPlace
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : IndexAdicCyclicAlgebra P r level)
    (hx : x ∈ IndexAdicCyclicIntegralLattice P r level) :
    arithmeticFiniteAdeleCyclicIntegralReduction P r level
        ⟨arithmeticFiniteAdeleCyclicPatchAtIndexPlace P r level x,
          arithmeticFiniteAdeleCyclicPatchAtIndexPlace_mem_integral
            P r level x hx⟩ =
      indexAdicCyclicIntegralReduction P r level ⟨x, hx⟩ := by
  apply (indexCyclicBasis P r level).equivFun.injective
  funext p
  have hleft := congrArg
    (fun f : (Fin r.matrixRank × Fin r.matrixRank) →
      ResidueField P r level => f p)
    (indexCyclicBasis_equivFun_arithmeticFiniteAdeleCyclicReduction
      P r level
      ⟨arithmeticFiniteAdeleCyclicPatchAtIndexPlace P r level x,
        arithmeticFiniteAdeleCyclicPatchAtIndexPlace_mem_integral
          P r level x hx⟩)
  have hright := congrArg
    (fun f : (Fin r.matrixRank × Fin r.matrixRank) →
      ResidueField P r level => f p)
    ((indexCyclicBasis P r level).equivFun.apply_symm_apply
      (indexAdicCyclicIntegralReductionCoordinates P r level ⟨x, hx⟩))
  change (indexCyclicBasis P r level).equivFun
      (arithmeticFiniteAdeleCyclicIntegralReduction P r level
        ⟨arithmeticFiniteAdeleCyclicPatchAtIndexPlace P r level x,
          arithmeticFiniteAdeleCyclicPatchAtIndexPlace_mem_integral
            P r level x hx⟩) p =
    arithmeticFiniteAdeleCyclicIntegralReductionCoordinates P r level
      ⟨arithmeticFiniteAdeleCyclicPatchAtIndexPlace P r level x,
        arithmeticFiniteAdeleCyclicPatchAtIndexPlace_mem_integral
          P r level x hx⟩ p at hleft
  change (indexCyclicBasis P r level).equivFun
      (indexAdicCyclicIntegralReduction P r level ⟨x, hx⟩) p =
    indexAdicCyclicIntegralReductionCoordinates P r level ⟨x, hx⟩ p
      at hright
  rw [hleft, hright]
  change arithmeticIntegralFiniteAdeleReductionAtIndex P r level
      ⟨(arithmeticFiniteAdeleCyclicBasis P r).equivFun
          (arithmeticFiniteAdeleCyclicPatchAtIndexPlace P r level x) p,
        _⟩ =
    PowerSeries.constantCoeff
      (indexAdicIntegersRingEquivPowerSeries P r level
        ⟨(indexAdicCyclicBasis P r level).equivFun x p, hx p⟩)
  rw [arithmeticIntegralFiniteAdeleReductionAtIndex_eq_adic]
  have hcoord := indexAdicCyclicBasis_equivFun_atIndexPlace
    P r level
      (arithmeticFiniteAdeleCyclicPatchAtIndexPlace P r level x) p
  rw [arithmeticFiniteAdeleCyclicAlgebraAtIndexPlace_patch] at hcoord
  have hpatch :=
    arithmeticFiniteAdeleCyclicPatchAtIndexPlace_mem_integral
      P r level x hx
  have hz :
      (⟨arithmeticFiniteAdeleAtIndexPlace P r level
          ((arithmeticFiniteAdeleCyclicBasis P r).equivFun
            (arithmeticFiniteAdeleCyclicPatchAtIndexPlace P r level x) p),
        (hpatch p) (indexCongruencePlace P r level)⟩ :
          IndexCongruenceAdicIntegers P r level) =
      ⟨(indexAdicCyclicBasis P r level).equivFun x p,
        hx p⟩ := by
    apply Subtype.ext
    exact hcoord.symm
  rw [hz]
theorem continuous_arithmeticFiniteAdeleCyclicIntegralReductionCoordinates
    (P : BasePrime) (r : Rank) (level : Nat) :
    Continuous
      (arithmeticFiniteAdeleCyclicIntegralReductionCoordinates
        P r level) := by
  apply continuous_pi
  intro p
  apply (continuous_arithmeticIntegralFiniteAdeleReductionAtIndex
    P r level).comp
  apply Continuous.subtype_mk
  exact ((continuous_apply p).comp continuous_induced_dom).comp
    continuous_subtype_val
theorem continuous_arithmeticFiniteAdeleCyclicIntegralReduction
    (P : BasePrime) (r : Rank) (level : Nat) :
    Continuous
      (arithmeticFiniteAdeleCyclicIntegralReduction P r level) := by
  exact (continuous_of_discreteTopology (f :=
      (indexCyclicBasis P r level).equivFun.symm)).comp
    (continuous_arithmeticFiniteAdeleCyclicIntegralReductionCoordinates
      P r level)
theorem isOpen_arithmeticFiniteAdeleCyclicIntegralReduction_fiber
    (P : BasePrime) (r : Rank) (level : Nat)
    (M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (ResidueField P r level)) :
    IsOpen ((arithmeticFiniteAdeleCyclicIntegralReduction P r level) ⁻¹'
      {M}) := by
  exact (isOpen_discrete {M}).preimage
    (continuous_arithmeticFiniteAdeleCyclicIntegralReduction P r level)
noncomputable def arithmeticFiniteAdeleCyclicCongruenceNeighborhood
    (P : BasePrime) (r : Rank) (level : Nat)
    (M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (ResidueField P r level)) :
    Set (ArithmeticFiniteAdeleCyclicAlgebra P r) :=
  Subtype.val ''
    ((arithmeticFiniteAdeleCyclicIntegralReduction P r level) ⁻¹' {M})
theorem isOpen_arithmeticFiniteAdeleCyclicCongruenceNeighborhood
    (P : BasePrime) (r : Rank) (level : Nat)
    (M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (ResidueField P r level)) :
    IsOpen (arithmeticFiniteAdeleCyclicCongruenceNeighborhood
      P r level M) := by
  exact (isOpen_arithmeticFiniteAdeleCyclicIntegralLattice P r
    ).isOpenMap_subtype_val _
    (isOpen_arithmeticFiniteAdeleCyclicIntegralReduction_fiber
      P r level M)
theorem mem_arithmeticFiniteAdeleCyclicCongruenceNeighborhood_iff
    (P : BasePrime) (r : Rank) (level : Nat)
    (M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (ResidueField P r level))
    (x : ArithmeticFiniteAdeleCyclicAlgebra P r) :
    x ∈ arithmeticFiniteAdeleCyclicCongruenceNeighborhood P r level M ↔
      ∃ hx : x ∈ ArithmeticFiniteAdeleCyclicIntegralLattice P r,
        arithmeticFiniteAdeleCyclicIntegralReduction P r level ⟨x, hx⟩ = M := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.property, ?_⟩
    simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hy
  · rintro ⟨hx, hred⟩
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hred
theorem arithmeticFiniteAdeleCyclicIntegralReductionCoordinates_diagonal
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : CyclicAlgebra P r) (hx : x ∈ arithmeticCyclicSpan P r)
    (p : Fin r.matrixRank × Fin r.matrixRank)
    (a : ArithmeticRing P)
    (ha : arithmeticRingToFunctionField P a =
      (functionFieldCyclicBasis P r).equivFun x p) :
    arithmeticFiniteAdeleCyclicIntegralReductionCoordinates P r level
        ⟨cyclicAlgebraToArithmeticFiniteAdeles P r x,
          cyclicAlgebraToArithmeticFiniteAdeles_mem_integralLattice
            P r x hx⟩ p =
      indexArithmeticEval P r level a := by
  let c : ArithmeticIntegralFiniteAdeles P :=
    ⟨(arithmeticFiniteAdeleCyclicBasis P r).equivFun
        (cyclicAlgebraToArithmeticFiniteAdeles P r x) p,
      (cyclicAlgebraToArithmeticFiniteAdeles_mem_integralLattice
        P r x hx) p⟩
  let d : ArithmeticIntegralFiniteAdeles P :=
    ⟨functionFieldToArithmeticFiniteAdeles P
        (algebraMap (ArithmeticRing P) (FunctionField P) a),
      functionFieldToArithmeticFiniteAdeles_algebraMap_mem_integral P a⟩
  have hcd : c = d := by
    apply Subtype.ext
    change (arithmeticFiniteAdeleCyclicBasis P r).equivFun
        (cyclicAlgebraToArithmeticFiniteAdeles P r x) p =
      functionFieldToArithmeticFiniteAdeles P
        (algebraMap (ArithmeticRing P) (FunctionField P) a)
    rw [arithmeticFiniteAdeleCyclicBasis_equivFun_diagonal, ← ha]
    have hbase : arithmeticRingToFunctionField P =
        algebraMap (ArithmeticRing P) (FunctionField P) := by
      apply IsLocalization.ringHom_ext
        (Submonoid.powers
          (Polynomial.X * (1 + Polynomial.X) : PolynomialRing P))
      apply RingHom.ext
      intro f
      simp only [RingHom.comp_apply]
      rw [arithmeticRingToFunctionField_algebraMap]
      exact IsScalarTower.algebraMap_apply
        (PolynomialRing P) (ArithmeticRing P) (FunctionField P) f
    rw [hbase]
  change arithmeticIntegralFiniteAdeleReductionAtIndex P r level c = _
  rw [hcd]
  exact arithmeticIntegralFiniteAdeleReductionAtIndex_diagonal
    P r level a
theorem arithmeticCyclicCoordinateMatrix_reduction
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : CyclicAlgebra P r) (hx : x ∈ arithmeticCyclicSpan P r) :
    (arithmeticCyclicCoordinateMatrix P r x hx).map
        (indexConstantArithmeticEval P r level) =
      arithmeticFiniteAdeleCyclicIntegralReduction P r level
        ⟨cyclicAlgebraToArithmeticFiniteAdeles P r x,
          cyclicAlgebraToArithmeticFiniteAdeles_mem_integralLattice
            P r x hx⟩ := by
  rw [arithmeticCyclicCoordinateMatrix]
  have hmapSum :
      ((∑ p, arithmeticToConstantArithmetic P r
          (arithmeticCyclicCoordinate P r x hx p) •
            orderIndexCyclicBasisVector P r p).map
          (indexConstantArithmeticEval P r level)) =
        ∑ p, (arithmeticToConstantArithmetic P r
          (arithmeticCyclicCoordinate P r x hx p) •
            orderIndexCyclicBasisVector P r p).map
          (indexConstantArithmeticEval P r level) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.sum_apply, map_sum]
  rw [hmapSum, arithmeticFiniteAdeleCyclicIntegralReduction,
    Module.Basis.equivFun_symm_apply]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Matrix.map_smul' _ _ _ (map_mul _),
    indexConstantArithmeticEval_arithmeticBaseChange,
    orderIndexCyclicBasisVector_reduction,
    ← indexCyclicBasis_apply]
  congr 1
  exact (arithmeticFiniteAdeleCyclicIntegralReductionCoordinates_diagonal
    P r level x hx p (arithmeticCyclicCoordinate P r x hx p)
      (arithmeticRingToFunctionField_arithmeticCyclicCoordinate
        P r x hx p)).symm
theorem arithmeticFiniteAdeleCyclicIntegralReduction_orderNormOneInnerForm
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : OrderNormOneInnerForm P r) :
    arithmeticFiniteAdeleCyclicIntegralReduction P r level
        ⟨cyclicAlgebraToArithmeticFiniteAdeles P r
            (orderNormOneInnerFormCyclicAlgebraPoint P r s),
          cyclicAlgebraToArithmeticFiniteAdeles_mem_integralLattice P r
            (orderNormOneInnerFormCyclicAlgebraPoint P r s)
            (orderNormOneInnerFormCyclicAlgebraPoint_mem_arithmeticCyclicSpan
              P r s)⟩ =
      (((s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
          (ConstantArithmeticRing P r)) :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (ConstantArithmeticRing P r)).map
            (indexConstantArithmeticEval P r level)) := by
  calc
    _ = (arithmeticCyclicCoordinateMatrix P r
          (orderNormOneInnerFormCyclicAlgebraPoint P r s)
          (orderNormOneInnerFormCyclicAlgebraPoint_mem_arithmeticCyclicSpan
            P r s)).map
          (indexConstantArithmeticEval P r level) :=
      (arithmeticCyclicCoordinateMatrix_reduction P r level
        (orderNormOneInnerFormCyclicAlgebraPoint P r s)
        (orderNormOneInnerFormCyclicAlgebraPoint_mem_arithmeticCyclicSpan
          P r s)).symm
    _ = _ := congrArg
      (fun M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (ConstantArithmeticRing P r) =>
          M.map (indexConstantArithmeticEval P r level))
      (arithmeticCyclicCoordinateMatrix_orderNormOneInnerForm P r s)
theorem orderNormOneInnerForm_mem_arithmeticFiniteAdeleCyclicCongruenceNeighborhood_iff
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : OrderNormOneInnerForm P r)
    (M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (ResidueField P r level)) :
    cyclicAlgebraToArithmeticFiniteAdeles P r
        (orderNormOneInnerFormCyclicAlgebraPoint P r s) ∈
      arithmeticFiniteAdeleCyclicCongruenceNeighborhood P r level M ↔
        (((s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
            (ConstantArithmeticRing P r)) :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (ConstantArithmeticRing P r)).map
              (indexConstantArithmeticEval P r level)) = M := by
  rw [mem_arithmeticFiniteAdeleCyclicCongruenceNeighborhood_iff]
  constructor
  · rintro ⟨hx, hred⟩
    have hpoint :
        (⟨cyclicAlgebraToArithmeticFiniteAdeles P r
            (orderNormOneInnerFormCyclicAlgebraPoint P r s), hx⟩ :
          ArithmeticFiniteAdeleCyclicIntegralElement P r) =
        ⟨cyclicAlgebraToArithmeticFiniteAdeles P r
            (orderNormOneInnerFormCyclicAlgebraPoint P r s),
          cyclicAlgebraToArithmeticFiniteAdeles_mem_integralLattice P r
            (orderNormOneInnerFormCyclicAlgebraPoint P r s)
            (orderNormOneInnerFormCyclicAlgebraPoint_mem_arithmeticCyclicSpan
              P r s)⟩ := by
      exact Subtype.ext rfl
    rw [hpoint,
      arithmeticFiniteAdeleCyclicIntegralReduction_orderNormOneInnerForm]
      at hred
    exact hred
  · intro hred
    refine ⟨cyclicAlgebraToArithmeticFiniteAdeles_mem_integralLattice P r
      (orderNormOneInnerFormCyclicAlgebraPoint P r s)
      (orderNormOneInnerFormCyclicAlgebraPoint_mem_arithmeticCyclicSpan
        P r s), ?_⟩
    rw [arithmeticFiniteAdeleCyclicIntegralReduction_orderNormOneInnerForm]
    exact hred
end SelectedPlaceTopology
theorem IndexCompletedNormOneInnerForm_eq_top
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexCompletedNormOneInnerForm P r level = ⊤ := by
  apply top_unique
  intro s _
  constructor <;> rw [IndexCompletedCyclicOrder_eq_top] <;>
    exact Set.mem_univ _
noncomputable def indexCompletedNormOneInnerFormEquivSL
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexCompletedNormOneInnerForm P r level ≃*
      Matrix.SpecialLinearGroup (Fin r.matrixRank)
        (PowerSeries (ResidueField P r level)) where
  toFun s := s
  invFun s := ⟨s, by
    rw [IndexCompletedNormOneInnerForm_eq_top]
    exact Subgroup.mem_top s⟩
  left_inv s := Subtype.ext rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
noncomputable def splittingCyclicScalarExtensionUnitEquivGL
    (P : BasePrime) (r : Rank) :
    (SplittingCyclicScalarExtension P r)ˣ ≃*
      Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (SplittingFunctionField P r) :=
  Units.mapEquiv
    (splittingCyclicScalarExtensionEquivMatrix P r).toMulEquiv
noncomputable def splittingCyclicScalarExtensionReducedNorm
    (P : BasePrime) (r : Rank) :
    (SplittingCyclicScalarExtension P r)ˣ →*
      (SplittingFunctionField P r)ˣ :=
  Matrix.GeneralLinearGroup.det.comp
    (splittingCyclicScalarExtensionUnitEquivGL P r).toMonoidHom
noncomputable def SplittingCyclicScalarExtensionNormOne
    (P : BasePrime) (r : Rank) :
    Subgroup (SplittingCyclicScalarExtension P r)ˣ :=
  (splittingCyclicScalarExtensionReducedNorm P r).ker
noncomputable def splittingCyclicScalarExtensionNormOneEquivSL
    (P : BasePrime) (r : Rank) :
    SplittingCyclicScalarExtensionNormOne P r ≃*
      Matrix.SpecialLinearGroup (Fin r.matrixRank)
        (SplittingFunctionField P r) where
  toFun u :=
    ⟨((splittingCyclicScalarExtensionUnitEquivGL P r u :
        Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (SplittingFunctionField P r)) :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r)),
      congrArg Units.val u.property⟩
  invFun s :=
    ⟨(splittingCyclicScalarExtensionUnitEquivGL P r).symm
        (Matrix.SpecialLinearGroup.toGL s), by
      change splittingCyclicScalarExtensionReducedNorm P r
        ((splittingCyclicScalarExtensionUnitEquivGL P r).symm
          (Matrix.SpecialLinearGroup.toGL s)) = 1
      rw [splittingCyclicScalarExtensionReducedNorm]
      simp⟩
  left_inv u := by
    apply Subtype.ext
    apply (splittingCyclicScalarExtensionUnitEquivGL P r).injective
    apply Units.ext
    simp
    rfl
  right_inv s := by
    apply Matrix.SpecialLinearGroup.toGL_injective
    apply Units.ext
    simp
    rfl
  map_mul' u v := by
    apply Matrix.SpecialLinearGroup.toGL_injective
    apply Units.ext
    simp
    rfl
noncomputable def cyclicAlgebraUnitToSplittingScalarExtension
    (P : BasePrime) (r : Rank) :
    (CyclicAlgebra P r)ˣ →*
      (SplittingCyclicScalarExtension P r)ˣ :=
  Units.map (Algebra.TensorProduct.includeRight
    (R := FunctionField P) (A := SplittingFunctionField P r)
      (B := CyclicAlgebra P r)).toRingHom
theorem splittingScalarExtensionUnitEquivGL_global_compatibility
    (P : BasePrime) (r : Rank) (u : (CyclicAlgebra P r)ˣ) :
    splittingCyclicScalarExtensionUnitEquivGL P r
        (cyclicAlgebraUnitToSplittingScalarExtension P r u) =
      cyclicAlgebraUnitToGlobalGL P r u := by
  apply Units.ext
  exact splittingCyclicScalarExtensionMap_includeRight P r u
noncomputable def cyclicAlgebraNormOneToSplittingNormOne
    (P : BasePrime) (r : Rank) :
    CyclicAlgebraNormOne P r →*
      SplittingCyclicScalarExtensionNormOne P r where
  toFun u :=
    ⟨cyclicAlgebraUnitToSplittingScalarExtension P r u, by
      change splittingCyclicScalarExtensionReducedNorm P r
        (cyclicAlgebraUnitToSplittingScalarExtension P r u) = 1
      change Matrix.GeneralLinearGroup.det
        (splittingCyclicScalarExtensionUnitEquivGL P r
          (cyclicAlgebraUnitToSplittingScalarExtension P r u)) = 1
      rw [splittingScalarExtensionUnitEquivGL_global_compatibility]
      have hu : (u : (CyclicAlgebra P r)ˣ) ∈
          CyclicAlgebraSplitNormOne P r := by
        rw [cyclicAlgebraSplitNormOne_eq_normOne]
        exact u.property
      exact hu⟩
  map_one' := Subtype.ext
    (map_one (cyclicAlgebraUnitToSplittingScalarExtension P r))
  map_mul' u v := Subtype.ext
    (map_mul (cyclicAlgebraUnitToSplittingScalarExtension P r)
      (u : (CyclicAlgebra P r)ˣ) (v : (CyclicAlgebra P r)ˣ))
noncomputable def cyclicAlgebraNormOneToSplittingSL
    (P : BasePrime) (r : Rank) :
    CyclicAlgebraNormOne P r →*
      Matrix.SpecialLinearGroup (Fin r.matrixRank)
        (SplittingFunctionField P r) :=
  (splittingCyclicScalarExtensionNormOneEquivSL P r).toMonoidHom.comp
    (cyclicAlgebraNormOneToSplittingNormOne P r)
abbrev IndexLocalNormOneInnerForm
    (P : BasePrime) (r : Rank) (level : Nat) :=
  Matrix.SpecialLinearGroup (Fin r.matrixRank)
    (IndexCongruenceLocalField P r level)
noncomputable def cyclicAlgebraNormOneToIndexLocal
    (P : BasePrime) (r : Rank) (level : Nat) :
    CyclicAlgebraNormOne P r →*
      IndexLocalNormOneInnerForm P r level :=
  (Matrix.SpecialLinearGroup.map (n := Fin r.matrixRank)
    (splittingFunctionFieldToIndexCongruenceLocalField P r level)).comp
      (cyclicAlgebraNormOneToSplittingSL P r)
noncomputable def cyclicAlgebraUnitToIndexLocalCyclicAlgebra
    (P : BasePrime) (r : Rank) (level : Nat) :
    (CyclicAlgebra P r)ˣ →*
      (IndexLocalCyclicAlgebra P r level)ˣ :=
  Units.map (Algebra.TensorProduct.includeRight
    (R := FunctionField P)
    (A := IndexCongruenceLocalField P r level)
    (B := CyclicAlgebra P r)).toRingHom
theorem indexLocalCyclicAlgebraUnitEquivGL_global_compatibility
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : (CyclicAlgebra P r)ˣ) :
    indexLocalCyclicAlgebraUnitEquivGL P r level
        (cyclicAlgebraUnitToIndexLocalCyclicAlgebra P r level u) =
      Units.map (cyclicAlgebraToIndexLocalMatrix P r level).toRingHom u := by
  apply Units.ext
  exact indexLocalCyclicAlgebraToMatrix_includeRight P r level u
noncomputable def cyclicAlgebraNormOneToIndexLocalNormOne
    (P : BasePrime) (r : Rank) (level : Nat) :
    CyclicAlgebraNormOne P r →*
      IndexLocalCyclicAlgebraNormOne P r level where
  toFun u :=
    ⟨cyclicAlgebraUnitToIndexLocalCyclicAlgebra P r level u, by
      change indexLocalCyclicAlgebraReducedNorm P r level
        (cyclicAlgebraUnitToIndexLocalCyclicAlgebra P r level u) = 1
      change Matrix.GeneralLinearGroup.det
        (indexLocalCyclicAlgebraUnitEquivGL P r level
          (cyclicAlgebraUnitToIndexLocalCyclicAlgebra P r level u)) = 1
      rw [indexLocalCyclicAlgebraUnitEquivGL_global_compatibility]
      apply Units.ext
      change Matrix.det
        ((splittingFunctionFieldToIndexCongruenceLocalField P r level).mapMatrix
          ((u : (CyclicAlgebra P r)ˣ).1.1)) = 1
      rw [← RingHom.map_det]
      have hu : (u : (CyclicAlgebra P r)ˣ) ∈
          CyclicAlgebraSplitNormOne P r := by
        rw [cyclicAlgebraSplitNormOne_eq_normOne]
        exact u.property
      have hdet : Matrix.det ((u : (CyclicAlgebra P r)ˣ).1.1) = 1 := by
        simpa [CyclicAlgebraSplitNormOne,
          cyclicAlgebraSplitReducedNorm,
          cyclicAlgebraUnitToGlobalGL] using congrArg Units.val hu
      rw [hdet, map_one]⟩
  map_one' := Subtype.ext
    (map_one (cyclicAlgebraUnitToIndexLocalCyclicAlgebra P r level))
  map_mul' u v := Subtype.ext
    (map_mul (cyclicAlgebraUnitToIndexLocalCyclicAlgebra P r level)
      (u : (CyclicAlgebra P r)ˣ) (v : (CyclicAlgebra P r)ˣ))
noncomputable def cyclicAlgebraUnitCommutatorNormOne
    (P : BasePrime) (r : Rank)
    (u v : (CyclicAlgebra P r)ˣ) : CyclicAlgebraNormOne P r :=
  ⟨⁅u, v⁆, by
    change cyclicAlgebraReducedNorm P r ⁅u, v⁆ = 1
    rw [map_commutatorElement]
    exact (Commute.all _ _).commutator_eq⟩
noncomputable def indexLocalGLCommutatorToSL
    (P : BasePrime) (r : Rank) (level : Nat)
    (a b : Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (IndexCongruenceLocalField P r level)) :
    IndexLocalNormOneInnerForm P r level :=
  ⟨(⁅a, b⁆ : Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (IndexCongruenceLocalField P r level)), by
    have hdet : Matrix.GeneralLinearGroup.det ⁅a, b⁆ = 1 := by
      rw [map_commutatorElement]
      exact (Commute.all _ _).commutator_eq
    exact congrArg Units.val hdet⟩
noncomputable def finiteSpecialLinearToIndexLocalNormOne
    (P : BasePrime) (r : Rank) (level : Nat)
    (g : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (ResidueField P r level)) :
    IndexLocalNormOneInnerForm P r level :=
  Matrix.SpecialLinearGroup.map (n := Fin r.matrixRank)
    (HahnSeries.ofPowerSeries ℤ (ResidueField P r level))
      ((orderIndexNormOneCompletedInnerFormLift P r level g :
        IndexCompletedNormOneInnerForm P r level) :
          Matrix.SpecialLinearGroup (Fin r.matrixRank)
            (PowerSeries (ResidueField P r level)))
noncomputable def indexLocalNormOneFiniteTargetNeighborhood
    (P : BasePrime) (r : Rank) (level : Nat)
    (g : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (ResidueField P r level)) :
    Set (IndexLocalNormOneInnerForm P r level) :=
  {s | ∀ i j,
    Valued.v.restrict
      (((s : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (IndexCongruenceLocalField P r level)) i j) -
        ((finiteSpecialLinearToIndexLocalNormOne P r level g :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (IndexCongruenceLocalField P r level)) i j)) < 1}
noncomputable def arithmeticFiniteAdeleAtIndexLocalFieldAlgHom
    (P : BasePrime) (r : Rank) (level : Nat) :
    ArithmeticFiniteAdeleRing P →ₐ[FunctionField P]
      IndexCongruenceLocalField P r level where
  __ := arithmeticFiniteAdeleAtIndexLocalField P r level
  commutes' x := arithmeticFiniteAdeleAtIndexLocalField_diagonal P r level x
noncomputable def arithmeticFiniteAdeleSplittingRingToIndexLocalField
    (P : BasePrime) (r : Rank) (level : Nat) :
    ArithmeticFiniteAdeleSplittingRing P r →ₐ[FunctionField P]
      IndexCongruenceLocalField P r level :=
  Algebra.TensorProduct.lift
    (arithmeticFiniteAdeleAtIndexLocalFieldAlgHom P r level)
    ({ __ := splittingFunctionFieldToIndexCongruenceLocalField P r level
       commutes' := fun x =>
        splittingFunctionFieldToIndexCongruenceLocalField_functionFieldEmbedding
          P r level x } :
      SplittingFunctionField P r →ₐ[FunctionField P]
        IndexCongruenceLocalField P r level)
    (fun _ _ => Commute.all _ _)
@[simp] theorem arithmeticFiniteAdeleSplittingRingToIndexLocalField_left
    (P : BasePrime) (r : Rank) (level : Nat)
    (a : ArithmeticFiniteAdeleRing P) :
    arithmeticFiniteAdeleSplittingRingToIndexLocalField P r level
        (algebraMap (ArithmeticFiniteAdeleRing P)
          (ArithmeticFiniteAdeleSplittingRing P r) a) =
      arithmeticFiniteAdeleAtIndexLocalField P r level a := by
  change arithmeticFiniteAdeleSplittingRingToIndexLocalField P r level
      (TensorProduct.tmul (FunctionField P) a 1) = _
  rw [arithmeticFiniteAdeleSplittingRingToIndexLocalField,
    Algebra.TensorProduct.lift_tmul]
  simp [arithmeticFiniteAdeleAtIndexLocalFieldAlgHom]
  rfl
@[simp] theorem arithmeticFiniteAdeleSplittingRingToIndexLocalField_right
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : SplittingFunctionField P r) :
    arithmeticFiniteAdeleSplittingRingToIndexLocalField P r level
        (splittingFunctionFieldToArithmeticFiniteAdeleSplittingRing P r x) =
      splittingFunctionFieldToIndexCongruenceLocalField P r level x := by
  change arithmeticFiniteAdeleSplittingRingToIndexLocalField P r level
      (TensorProduct.tmul (FunctionField P) 1 x) = _
  rw [arithmeticFiniteAdeleSplittingRingToIndexLocalField,
    Algebra.TensorProduct.lift_tmul]
  simp
noncomputable def arithmeticFiniteAdeleCyclicAlgebraToIndexLocal
    (P : BasePrime) (r : Rank) (level : Nat) :
    ArithmeticFiniteAdeleCyclicAlgebra P r →ₐ[FunctionField P]
      IndexLocalCyclicAlgebra P r level :=
  (indexAdicCyclicAlgebraToIndexLocalCyclicAlgebra P r level).comp
    (arithmeticFiniteAdeleCyclicAlgebraAtIndexPlace P r level)
theorem arithmeticFiniteAdeleCyclicSplitting_atIndex_compatibility
    (P : BasePrime) (r : Rank) (level : Nat) :
    ((indexLocalCyclicAlgebraToMatrix P r level).restrictScalars
      (FunctionField P)).comp
        (arithmeticFiniteAdeleCyclicAlgebraToIndexLocal P r level) =
      (arithmeticFiniteAdeleSplittingRingToIndexLocalField
        P r level).mapMatrix.comp
        ((arithmeticFiniteAdeleCyclicSplittingMap P r).restrictScalars
          (FunctionField P)) := by
  apply Algebra.TensorProduct.ext
  · apply DFunLike.ext _ _
    intro a
    apply Matrix.ext
    intro i j
    by_cases hij : i = j
    · subst j
      simp [arithmeticFiniteAdeleCyclicAlgebraToIndexLocal,
        arithmeticFiniteAdeleCyclicAlgebraAtIndexPlace,
        indexAdicCyclicAlgebraToIndexLocalCyclicAlgebra,
        indexLocalCyclicAlgebraToMatrix,
        arithmeticFiniteAdeleCyclicSplittingMap,
        Matrix.algebraMap_matrix_apply]
      rw [show TensorProduct.tmul (FunctionField P) a
          (1 : SplittingFunctionField P r) =
        algebraMap (ArithmeticFiniteAdeleRing P)
          (ArithmeticFiniteAdeleSplittingRing P r) a by rfl,
        arithmeticFiniteAdeleSplittingRingToIndexLocalField_left]
      rfl
    · simp [arithmeticFiniteAdeleCyclicAlgebraToIndexLocal,
      arithmeticFiniteAdeleCyclicAlgebraAtIndexPlace,
      indexAdicCyclicAlgebraToIndexLocalCyclicAlgebra,
      indexLocalCyclicAlgebraToMatrix,
      arithmeticFiniteAdeleCyclicSplittingMap,
      Matrix.algebraMap_matrix_apply, hij]
  · apply DFunLike.ext _ _
    intro x
    apply Matrix.ext
    intro i j
    simp [arithmeticFiniteAdeleCyclicAlgebraToIndexLocal,
      arithmeticFiniteAdeleCyclicAlgebraAtIndexPlace,
      indexAdicCyclicAlgebraToIndexLocalCyclicAlgebra,
      indexLocalCyclicAlgebraToMatrix,
      arithmeticFiniteAdeleCyclicSplittingMap,
      cyclicAlgebraToArithmeticFiniteAdeleSplittingMatrix,
      cyclicAlgebraToIndexLocalMatrix]
noncomputable def arithmeticFiniteAdeleCyclicUnitToIndexLocal
    (P : BasePrime) (r : Rank) (level : Nat) :
    (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ →*
      (IndexLocalCyclicAlgebra P r level)ˣ :=
  Units.map
    (arithmeticFiniteAdeleCyclicAlgebraToIndexLocal
      P r level).toRingHom.toMonoidHom
theorem arithmeticFiniteAdeleCyclicReducedNorm_atIndex
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ) :
    indexLocalCyclicAlgebraReducedNorm P r level
        (arithmeticFiniteAdeleCyclicUnitToIndexLocal P r level u) =
      Units.map
        (arithmeticFiniteAdeleSplittingRingToIndexLocalField
          P r level).toRingHom.toMonoidHom
        (arithmeticFiniteAdeleCyclicReducedNorm P r u) := by
  apply Units.ext
  change Matrix.det
      ((indexLocalCyclicAlgebraUnitEquivGL P r level
        (arithmeticFiniteAdeleCyclicUnitToIndexLocal P r level u) :
          Matrix.GeneralLinearGroup (Fin r.matrixRank)
            (IndexCongruenceLocalField P r level)) :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (IndexCongruenceLocalField P r level)) =
    arithmeticFiniteAdeleSplittingRingToIndexLocalField P r level
      (Matrix.det
        ((arithmeticFiniteAdeleCyclicUnitToGL P r u :
          Matrix.GeneralLinearGroup (Fin r.matrixRank)
            (ArithmeticFiniteAdeleSplittingRing P r)) :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (ArithmeticFiniteAdeleSplittingRing P r)))
  change Matrix.det
      (indexLocalCyclicAlgebraToMatrix P r level
        (arithmeticFiniteAdeleCyclicAlgebraToIndexLocal P r level
          (u : ArithmeticFiniteAdeleCyclicAlgebra P r))) =
    arithmeticFiniteAdeleSplittingRingToIndexLocalField P r level
      (Matrix.det
        (arithmeticFiniteAdeleCyclicSplittingMap P r
          (u : ArithmeticFiniteAdeleCyclicAlgebra P r)))
  have hcompat := DFunLike.congr_fun
    (arithmeticFiniteAdeleCyclicSplitting_atIndex_compatibility P r level)
    (u : ArithmeticFiniteAdeleCyclicAlgebra P r)
  have hcompat' :
      indexLocalCyclicAlgebraToMatrix P r level
          (arithmeticFiniteAdeleCyclicAlgebraToIndexLocal P r level
            (u : ArithmeticFiniteAdeleCyclicAlgebra P r)) =
        (arithmeticFiniteAdeleCyclicSplittingMap P r
          (u : ArithmeticFiniteAdeleCyclicAlgebra P r)).map
            (arithmeticFiniteAdeleSplittingRingToIndexLocalField
              P r level) := by
    simpa using hcompat
  rw [hcompat']
  exact
    ((arithmeticFiniteAdeleSplittingRingToIndexLocalField
      P r level).map_det
        (arithmeticFiniteAdeleCyclicSplittingMap P r
          (u : ArithmeticFiniteAdeleCyclicAlgebra P r))).symm
theorem arithmeticFiniteAdeleCyclicBaseReducedNorm_atIndex
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ) :
    indexLocalCyclicAlgebraReducedNorm P r level
        (arithmeticFiniteAdeleCyclicUnitToIndexLocal P r level u) =
      Units.map (arithmeticFiniteAdeleAtIndexLocalField P r level)
        (arithmeticFiniteAdeleCyclicBaseReducedNorm P r u) := by
  rw [arithmeticFiniteAdeleCyclicReducedNorm_atIndex,
    arithmeticFiniteAdeleCyclicReducedNorm_eq_baseChange]
  apply Units.ext
  exact arithmeticFiniteAdeleSplittingRingToIndexLocalField_left P r level
    (arithmeticFiniteAdeleCyclicBaseReducedNorm P r u)
@[simp] theorem arithmeticFiniteAdeleCyclicUnitToIndexLocal_supported
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : (IndexAdicCyclicAlgebra P r level)ˣ) :
    arithmeticFiniteAdeleCyclicUnitToIndexLocal P r level
        (arithmeticFiniteAdeleCyclicUnitSupportedAtIndexPlace P r level u) =
      Units.map
        (indexAdicCyclicAlgebraToIndexLocalCyclicAlgebra
          P r level).toRingHom.toMonoidHom u := by
  apply Units.ext
  change indexAdicCyclicAlgebraToIndexLocalCyclicAlgebra P r level
      (arithmeticFiniteAdeleCyclicAlgebraAtIndexPlace P r level
        (arithmeticFiniteAdeleCyclicPatchAtIndexPlace P r level
          (u : IndexAdicCyclicAlgebra P r level))) =
    indexAdicCyclicAlgebraToIndexLocalCyclicAlgebra P r level
      (u : IndexAdicCyclicAlgebra P r level)
  rw [arithmeticFiniteAdeleCyclicAlgebraAtIndexPlace_patch]
theorem arithmeticFiniteAdeleCyclicBaseReducedNorm_supportedAtIndexPlace
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : (IndexAdicCyclicAlgebra P r level)ˣ)
    (hu : indexLocalCyclicAlgebraReducedNorm P r level
      (arithmeticFiniteAdeleCyclicUnitToIndexLocal P r level
        (arithmeticFiniteAdeleCyclicUnitSupportedAtIndexPlace
          P r level u)) = 1) :
    arithmeticFiniteAdeleAtIndexPlace P r level
        (arithmeticFiniteAdeleCyclicBaseReducedNorm P r
          (arithmeticFiniteAdeleCyclicUnitSupportedAtIndexPlace P r level u)) =
      1 := by
  have hcompat := arithmeticFiniteAdeleCyclicBaseReducedNorm_atIndex
    P r level
      (arithmeticFiniteAdeleCyclicUnitSupportedAtIndexPlace P r level u)
  rw [hu] at hcompat
  have hval := congrArg Units.val hcompat
  apply (indexAdicCompletionRingEquivLocalField P r level).injective
  simpa [arithmeticFiniteAdeleAtIndexLocalField] using hval.symm
theorem arithmeticFiniteAdeleCyclicBaseReducedNorm_supported_eq_one
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : (IndexAdicCyclicAlgebra P r level)ˣ)
    (hu : indexLocalCyclicAlgebraReducedNorm P r level
      (arithmeticFiniteAdeleCyclicUnitToIndexLocal P r level
        (arithmeticFiniteAdeleCyclicUnitSupportedAtIndexPlace
          P r level u)) = 1) :
    arithmeticFiniteAdeleCyclicBaseReducedNorm P r
        (arithmeticFiniteAdeleCyclicUnitSupportedAtIndexPlace P r level u) =
      1 := by
  apply Units.ext
  apply IsDedekindDomain.FiniteAdeleRing.ext
  intro v
  by_cases hv : v = indexCongruencePlace P r level
  · subst v
    exact arithmeticFiniteAdeleCyclicBaseReducedNorm_supportedAtIndexPlace
      P r level u hu
  · exact
      arithmeticFiniteAdeleCyclicBaseReducedNorm_supportedAtIndexPlace_of_ne
        P r level v hv u
noncomputable def arithmeticFiniteAdeleNormOneSupportedAtIndexPlace
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : (IndexAdicCyclicAlgebra P r level)ˣ)
    (hu : indexLocalCyclicAlgebraReducedNorm P r level
      (arithmeticFiniteAdeleCyclicUnitToIndexLocal P r level
        (arithmeticFiniteAdeleCyclicUnitSupportedAtIndexPlace
          P r level u)) = 1) :
    ArithmeticFiniteAdeleCyclicNormOne P r :=
  ⟨arithmeticFiniteAdeleCyclicUnitSupportedAtIndexPlace P r level u,
    (arithmeticFiniteAdeleCyclicReducedNorm_eq_one_iff_base P r _).mpr
      (arithmeticFiniteAdeleCyclicBaseReducedNorm_supported_eq_one
        P r level u hu)⟩
theorem arithmeticFiniteAdeleNormOneSupportedAtIndexPlace_mem_integral
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : (IndexAdicCyclicAlgebra P r level)ˣ)
    (huNorm : indexLocalCyclicAlgebraReducedNorm P r level
      (arithmeticFiniteAdeleCyclicUnitToIndexLocal P r level
        (arithmeticFiniteAdeleCyclicUnitSupportedAtIndexPlace
          P r level u)) = 1)
    (hu : (u : IndexAdicCyclicAlgebra P r level) ∈
      IndexAdicCyclicIntegralLattice P r level)
    (huInv : ((u⁻¹ : (IndexAdicCyclicAlgebra P r level)ˣ) :
        IndexAdicCyclicAlgebra P r level) ∈
      IndexAdicCyclicIntegralLattice P r level) :
    arithmeticFiniteAdeleNormOneSupportedAtIndexPlace P r level u huNorm ∈
      ArithmeticFiniteAdeleCyclicIntegralNormOneSet P r := by
  constructor
  · change arithmeticFiniteAdeleCyclicPatchAtIndexPlace P r level
        (u : IndexAdicCyclicAlgebra P r level) ∈
      ArithmeticFiniteAdeleCyclicIntegralLattice P r
    exact arithmeticFiniteAdeleCyclicPatchAtIndexPlace_mem_integral
      P r level (u : IndexAdicCyclicAlgebra P r level) hu
  · change arithmeticFiniteAdeleCyclicPatchAtIndexPlace P r level
        ((u⁻¹ : (IndexAdicCyclicAlgebra P r level)ˣ) :
          IndexAdicCyclicAlgebra P r level) ∈
      ArithmeticFiniteAdeleCyclicIntegralLattice P r
    exact arithmeticFiniteAdeleCyclicPatchAtIndexPlace_mem_integral
      P r level
        ((u⁻¹ : (IndexAdicCyclicAlgebra P r level)ˣ) :
          IndexAdicCyclicAlgebra P r level) huInv
noncomputable def arithmeticFiniteAdeleNormOneToIndexLocalNormOne
    (P : BasePrime) (r : Rank) (level : Nat) :
    ArithmeticFiniteAdeleCyclicNormOne P r →*
      IndexLocalCyclicAlgebraNormOne P r level where
  toFun u := ⟨arithmeticFiniteAdeleCyclicUnitToIndexLocal P r level u, by
    change indexLocalCyclicAlgebraReducedNorm P r level
      (arithmeticFiniteAdeleCyclicUnitToIndexLocal P r level u) = 1
    rw [arithmeticFiniteAdeleCyclicReducedNorm_atIndex]
    rw [u.property, map_one]⟩
  map_one' := Subtype.ext
    (map_one (arithmeticFiniteAdeleCyclicUnitToIndexLocal P r level))
  map_mul' u v := Subtype.ext
    (map_mul (arithmeticFiniteAdeleCyclicUnitToIndexLocal P r level)
      (u : (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ)
      (v : (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ))
noncomputable def indexAdicCyclicAlgebraUnitEquivIndexLocal
    (P : BasePrime) (r : Rank) (level : Nat) :
    (IndexAdicCyclicAlgebra P r level)ˣ ≃*
      (IndexLocalCyclicAlgebra P r level)ˣ :=
  Units.mapEquiv
    (indexAdicCyclicAlgebraEquivIndexLocalCyclicAlgebra
      P r level).toMulEquiv
noncomputable def indexLocalCyclicAlgebraNormOneToArithmeticFiniteAdeleNormOne
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : IndexLocalCyclicAlgebraNormOne P r level) :
    ArithmeticFiniteAdeleCyclicNormOne P r :=
  arithmeticFiniteAdeleNormOneSupportedAtIndexPlace P r level
    ((indexAdicCyclicAlgebraUnitEquivIndexLocal P r level).symm u.1)
    (by
      rw [arithmeticFiniteAdeleCyclicUnitToIndexLocal_supported]
      rw [show Units.map
          (indexAdicCyclicAlgebraToIndexLocalCyclicAlgebra
            P r level).toRingHom.toMonoidHom
          ((indexAdicCyclicAlgebraUnitEquivIndexLocal
            P r level).symm u.1) = u.1 by
        exact (indexAdicCyclicAlgebraUnitEquivIndexLocal
          P r level).apply_symm_apply u.1]
      exact u.property)
@[simp] theorem arithmeticFiniteAdeleNormOneToIndexLocalNormOne_section
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : IndexLocalCyclicAlgebraNormOne P r level) :
    arithmeticFiniteAdeleNormOneToIndexLocalNormOne P r level
        (indexLocalCyclicAlgebraNormOneToArithmeticFiniteAdeleNormOne
          P r level u) = u := by
  apply Subtype.ext
  change arithmeticFiniteAdeleCyclicUnitToIndexLocal P r level
      (arithmeticFiniteAdeleCyclicUnitSupportedAtIndexPlace P r level
        ((indexAdicCyclicAlgebraUnitEquivIndexLocal P r level).symm u.1)) =
    u.1
  rw [arithmeticFiniteAdeleCyclicUnitToIndexLocal_supported]
  exact (indexAdicCyclicAlgebraUnitEquivIndexLocal
    P r level).apply_symm_apply u.1
@[simp] theorem arithmeticFiniteAdeleCyclicAlgebraToIndexLocal_diagonal
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : CyclicAlgebra P r) :
    arithmeticFiniteAdeleCyclicAlgebraToIndexLocal P r level
        (cyclicAlgebraToArithmeticFiniteAdeles P r x) =
      Algebra.TensorProduct.includeRight x := by
  simp [arithmeticFiniteAdeleCyclicAlgebraToIndexLocal,
    cyclicAlgebraToArithmeticFiniteAdeles_apply,
    arithmeticFiniteAdeleCyclicAlgebraAtIndexPlace,
    indexAdicCyclicAlgebraToIndexLocalCyclicAlgebra]
noncomputable abbrev CartwrightStegerSIntegralNormOne
    (P : BasePrime) (r : Rank) :=
  CartwrightStegerBaseNormOneOrderUnits P r
noncomputable def orderNormOneInnerFormEquivSIntegralNormOne
    (P : BasePrime) (r : Rank) :
    OrderNormOneInnerForm P r ≃*
      CartwrightStegerSIntegralNormOne P r :=
  orderNormOneInnerFormEquivBaseNormOneOrderUnits P r
noncomputable def sIntegralNormOneToCyclicAlgebraNormOne
    (P : BasePrime) (r : Rank) :
    CartwrightStegerSIntegralNormOne P r →*
      CyclicAlgebraNormOne P r :=
  (orderNormOneInnerFormToCyclicAlgebraNormOne P r).comp
    (orderNormOneInnerFormEquivSIntegralNormOne P r).symm.toMonoidHom
noncomputable def indexCompletedNormOneInnerFormToIndexLocal
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexCompletedNormOneInnerForm P r level →*
      IndexLocalNormOneInnerForm P r level :=
  (Matrix.SpecialLinearGroup.map (n := Fin r.matrixRank)
    (HahnSeries.ofPowerSeries ℤ (ResidueField P r level))).comp
      (IndexCompletedNormOneInnerForm P r level).subtype
noncomputable def indexLocalIntegralEntriesToPowerSeriesMatrix
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : IndexLocalNormOneInnerForm P r level)
    (hs : ∀ i j,
      ((s : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (IndexCongruenceLocalField P r level)) i j) ∈
          IndexCongruenceLocalIntegers P r level) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (PowerSeries (ResidueField P r level)) :=
  fun i j => indexCongruenceLocalIntegersRingEquivPowerSeries P r level
    ⟨((s : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (IndexCongruenceLocalField P r level)) i j), hs i j⟩
theorem indexLocalIntegralEntriesToPowerSeriesMatrix_map
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : IndexLocalNormOneInnerForm P r level)
    (hs : ∀ i j,
      ((s : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (IndexCongruenceLocalField P r level)) i j) ∈
          IndexCongruenceLocalIntegers P r level) :
    (indexLocalIntegralEntriesToPowerSeriesMatrix P r level s hs).map
        (HahnSeries.ofPowerSeries ℤ (ResidueField P r level)) =
      (s : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (IndexCongruenceLocalField P r level)) := by
  apply Matrix.ext
  intro i j
  let z : IndexCongruenceLocalIntegers P r level :=
    ⟨((s : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (IndexCongruenceLocalField P r level)) i j), hs i j⟩
  have hz := congrArg Subtype.val
    ((indexCongruenceLocalIntegersRingEquivPowerSeries
      P r level).symm_apply_apply z)
  exact hz
noncomputable def indexLocalNormOneToCompletedOfIntegralEntries
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : IndexLocalNormOneInnerForm P r level)
    (hs : ∀ i j,
      ((s : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (IndexCongruenceLocalField P r level)) i j) ∈
          IndexCongruenceLocalIntegers P r level) :
    IndexCompletedNormOneInnerForm P r level := by
  let M := indexLocalIntegralEntriesToPowerSeriesMatrix P r level s hs
  have hdet : Matrix.det M = 1 := by
    apply (HahnSeries.ofPowerSeries_injective (Γ := ℤ))
    rw [RingHom.map_det]
    change Matrix.det
      (M.map (HahnSeries.ofPowerSeries ℤ (ResidueField P r level))) =
        HahnSeries.ofPowerSeries ℤ (ResidueField P r level) 1
    rw [show M =
          indexLocalIntegralEntriesToPowerSeriesMatrix P r level s hs from rfl,
      indexLocalIntegralEntriesToPowerSeriesMatrix_map P r level s hs,
      s.property, map_one]
  exact (indexCompletedNormOneInnerFormEquivSL P r level).symm ⟨M, hdet⟩
noncomputable def indexAdicCyclicAlgebraUnitEquivIndexLocalGL
    (P : BasePrime) (r : Rank) (level : Nat) :
    (IndexAdicCyclicAlgebra P r level)ˣ ≃*
      Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (IndexCongruenceLocalField P r level) :=
  Units.mapEquiv
    (indexAdicCyclicAlgebraEquivIndexLocalMatrix P r level).toMulEquiv
noncomputable def indexCompletedNormOneInnerFormToIndexAdicCyclicUnit
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : IndexCompletedNormOneInnerForm P r level) :
    (IndexAdicCyclicAlgebra P r level)ˣ :=
  (indexAdicCyclicAlgebraUnitEquivIndexLocalGL P r level).symm
    (Matrix.SpecialLinearGroup.toGL
      (indexCompletedNormOneInnerFormToIndexLocal P r level s))
@[simp] theorem indexAdicCyclicAlgebraUnitEquivIndexLocalGL_completed
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : IndexCompletedNormOneInnerForm P r level) :
    indexAdicCyclicAlgebraUnitEquivIndexLocalGL P r level
        (indexCompletedNormOneInnerFormToIndexAdicCyclicUnit
          P r level s) =
      Matrix.SpecialLinearGroup.toGL
        (indexCompletedNormOneInnerFormToIndexLocal P r level s) := by
  exact (indexAdicCyclicAlgebraUnitEquivIndexLocalGL
    P r level).apply_symm_apply _
theorem indexCompletedNormOneInnerFormToIndexAdicCyclicUnit_val
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : IndexCompletedNormOneInnerForm P r level) :
    (indexCompletedNormOneInnerFormToIndexAdicCyclicUnit P r level s :
        IndexAdicCyclicAlgebra P r level) =
      indexCompletedMatrixToIndexAdicCyclicAlgebra P r level
        ((s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
          (PowerSeries (ResidueField P r level))) :
            Matrix (Fin r.matrixRank) (Fin r.matrixRank)
              (PowerSeries (ResidueField P r level))) := by
  apply (indexAdicCyclicAlgebraToIndexLocalMatrix_bijective
    P r level).1
  rw [indexAdicCyclicAlgebraToIndexLocalMatrix_completedMatrixLift]
  have h := congrArg Units.val
    (indexAdicCyclicAlgebraUnitEquivIndexLocalGL_completed
      P r level s)
  simpa [indexAdicCyclicAlgebraUnitEquivIndexLocalGL,
    indexAdicCyclicAlgebraEquivIndexLocalMatrix,
    indexCompletedNormOneInnerFormToIndexLocal] using h
theorem indexCompletedNormOneInnerFormToIndexAdicCyclicUnit_inv_val
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : IndexCompletedNormOneInnerForm P r level) :
    ((indexCompletedNormOneInnerFormToIndexAdicCyclicUnit
        P r level s)⁻¹ : (IndexAdicCyclicAlgebra P r level)ˣ) =
      indexCompletedNormOneInnerFormToIndexAdicCyclicUnit
        P r level s⁻¹ := by
  apply (indexAdicCyclicAlgebraUnitEquivIndexLocalGL P r level).injective
  simp [indexCompletedNormOneInnerFormToIndexAdicCyclicUnit,
    indexCompletedNormOneInnerFormToIndexLocal]
theorem indexLocalCyclicAlgebraUnitEquivGL_adic_compatibility
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : (IndexAdicCyclicAlgebra P r level)ˣ) :
    indexLocalCyclicAlgebraUnitEquivGL P r level
        (Units.map
          (indexAdicCyclicAlgebraToIndexLocalCyclicAlgebra
            P r level).toRingHom.toMonoidHom u) =
      indexAdicCyclicAlgebraUnitEquivIndexLocalGL P r level u := by
  apply Units.ext
  exact (DFunLike.congr_fun
    (indexAdicCyclicAlgebraToIndexLocalMatrix_factorization P r level)
      (u : IndexAdicCyclicAlgebra P r level)).symm
theorem indexCompletedNormOneInnerFormToIndexAdicCyclicUnit_normOne
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : IndexCompletedNormOneInnerForm P r level) :
    indexLocalCyclicAlgebraReducedNorm P r level
        (Units.map
          (indexAdicCyclicAlgebraToIndexLocalCyclicAlgebra
            P r level).toRingHom.toMonoidHom
          (indexCompletedNormOneInnerFormToIndexAdicCyclicUnit
            P r level s)) = 1 := by
  rw [indexLocalCyclicAlgebraReducedNorm,
    MonoidHom.comp_apply]
  change Matrix.GeneralLinearGroup.det
      (indexLocalCyclicAlgebraUnitEquivGL P r level
        (Units.map
          (indexAdicCyclicAlgebraToIndexLocalCyclicAlgebra
            P r level).toRingHom.toMonoidHom
          (indexCompletedNormOneInnerFormToIndexAdicCyclicUnit
            P r level s))) = 1
  rw [indexLocalCyclicAlgebraUnitEquivGL_adic_compatibility,
    indexAdicCyclicAlgebraUnitEquivIndexLocalGL_completed]
  apply Units.ext
  exact (indexCompletedNormOneInnerFormToIndexLocal P r level s).property
theorem indexCompletedNormOneInnerFormToIndexAdicCyclicUnit_integral
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : IndexCompletedNormOneInnerForm P r level) :
    (indexCompletedNormOneInnerFormToIndexAdicCyclicUnit P r level s :
        IndexAdicCyclicAlgebra P r level) ∈
        IndexAdicCyclicIntegralLattice P r level ∧
      (((indexCompletedNormOneInnerFormToIndexAdicCyclicUnit
          P r level s)⁻¹ : (IndexAdicCyclicAlgebra P r level)ˣ) :
        IndexAdicCyclicAlgebra P r level) ∈
          IndexAdicCyclicIntegralLattice P r level := by
  constructor
  · rw [indexCompletedNormOneInnerFormToIndexAdicCyclicUnit_val]
    exact indexCompletedMatrixToIndexAdicCyclicAlgebra_mem_integral
      P r level _
  · rw [indexCompletedNormOneInnerFormToIndexAdicCyclicUnit_inv_val,
      indexCompletedNormOneInnerFormToIndexAdicCyclicUnit_val]
    exact indexCompletedMatrixToIndexAdicCyclicAlgebra_mem_integral
      P r level _
noncomputable def indexCompletedNormOneInnerFormToArithmeticFiniteAdeleNormOne
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : IndexCompletedNormOneInnerForm P r level) :
    ArithmeticFiniteAdeleCyclicNormOne P r :=
  arithmeticFiniteAdeleNormOneSupportedAtIndexPlace P r level
    (indexCompletedNormOneInnerFormToIndexAdicCyclicUnit P r level s)
    (by
      rw [arithmeticFiniteAdeleCyclicUnitToIndexLocal_supported]
      exact indexCompletedNormOneInnerFormToIndexAdicCyclicUnit_normOne
        P r level s)
theorem indexCompletedNormOneInnerFormToArithmeticFiniteAdeleNormOne_integral
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : IndexCompletedNormOneInnerForm P r level) :
    indexCompletedNormOneInnerFormToArithmeticFiniteAdeleNormOne
        P r level s ∈
      ArithmeticFiniteAdeleCyclicIntegralNormOneSet P r := by
  have hint := indexCompletedNormOneInnerFormToIndexAdicCyclicUnit_integral
    P r level s
  apply arithmeticFiniteAdeleNormOneSupportedAtIndexPlace_mem_integral
  · exact hint.1
  · exact hint.2
theorem indexCompletedNormOneInnerFormToArithmeticFiniteAdeleNormOne_reduction
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : IndexCompletedNormOneInnerForm P r level) :
    arithmeticFiniteAdeleCyclicIntegralReduction P r level
        ⟨(indexCompletedNormOneInnerFormToArithmeticFiniteAdeleNormOne
            P r level s).1.1,
          (indexCompletedNormOneInnerFormToArithmeticFiniteAdeleNormOne_integral
            P r level s).1⟩ =
      ((indexCompletedNormOneReduction P r level s :
          Matrix.SpecialLinearGroup (Fin r.matrixRank)
            (ResidueField P r level)) :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (ResidueField P r level)) := by
  have hint := indexCompletedNormOneInnerFormToIndexAdicCyclicUnit_integral
    P r level s
  change arithmeticFiniteAdeleCyclicIntegralReduction P r level
      ⟨arithmeticFiniteAdeleCyclicPatchAtIndexPlace P r level
        (indexCompletedNormOneInnerFormToIndexAdicCyclicUnit
          P r level s), _⟩ = _
  rw [arithmeticFiniteAdeleCyclicIntegralReduction_patchAtIndexPlace
    P r level _ hint.1]
  let x : IndexAdicCyclicIntegralElement P r level :=
    ⟨indexCompletedNormOneInnerFormToIndexAdicCyclicUnit P r level s,
      hint.1⟩
  let y : IndexAdicCyclicIntegralElement P r level :=
    ⟨indexCompletedMatrixToIndexAdicCyclicAlgebra P r level
      ((s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
        (PowerSeries (ResidueField P r level))) :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (PowerSeries (ResidueField P r level))),
      indexCompletedMatrixToIndexAdicCyclicAlgebra_mem_integral
        P r level _⟩
  have hxy : x = y := by
    apply Subtype.ext
    exact indexCompletedNormOneInnerFormToIndexAdicCyclicUnit_val
      P r level s
  change indexAdicCyclicIntegralReduction P r level x = _
  rw [hxy]
  rw [indexAdicCyclicIntegralReduction_completedMatrixLift]
  rfl
noncomputable def finiteSpecialLinearToArithmeticFiniteAdeleNormOne
    (P : BasePrime) (r : Rank) (level : Nat)
    (g : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (ResidueField P r level)) :
    ArithmeticFiniteAdeleCyclicNormOne P r :=
  indexCompletedNormOneInnerFormToArithmeticFiniteAdeleNormOne P r level
    (orderIndexNormOneCompletedInnerFormLift P r level g)
theorem finiteSpecialLinearToArithmeticFiniteAdeleNormOne_integral
    (P : BasePrime) (r : Rank) (level : Nat)
    (g : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (ResidueField P r level)) :
    finiteSpecialLinearToArithmeticFiniteAdeleNormOne P r level g ∈
      ArithmeticFiniteAdeleCyclicIntegralNormOneSet P r :=
  indexCompletedNormOneInnerFormToArithmeticFiniteAdeleNormOne_integral
    P r level (orderIndexNormOneCompletedInnerFormLift P r level g)
theorem finiteSpecialLinearToArithmeticFiniteAdeleNormOne_reduction
    (P : BasePrime) (r : Rank) (level : Nat)
    (g : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (ResidueField P r level)) :
    arithmeticFiniteAdeleCyclicIntegralReduction P r level
        ⟨(finiteSpecialLinearToArithmeticFiniteAdeleNormOne
            P r level g).1.1,
          (finiteSpecialLinearToArithmeticFiniteAdeleNormOne_integral
            P r level g).1⟩ =
      (g : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (ResidueField P r level)) := by
  have hred :=
    indexCompletedNormOneInnerFormToArithmeticFiniteAdeleNormOne_reduction
      P r level (orderIndexNormOneCompletedInnerFormLift P r level g)
  have hlift := congrArg Subtype.val
    (indexCompletedNormOneReduction_lift P r level g)
  simpa [finiteSpecialLinearToArithmeticFiniteAdeleNormOne] using
    hred.trans hlift
noncomputable def arithmeticFiniteAdeleCyclicNormOneCongruenceNeighborhood
    (P : BasePrime) (r : Rank) (level : Nat)
    (g : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (ResidueField P r level)) :
    Set (ArithmeticFiniteAdeleCyclicNormOne P r) :=
  ArithmeticFiniteAdeleCyclicIntegralNormOneSet P r ∩
    {u | u.1.1 ∈ arithmeticFiniteAdeleCyclicCongruenceNeighborhood
      P r level (g : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (ResidueField P r level))}
theorem isOpen_arithmeticFiniteAdeleCyclicNormOneCongruenceNeighborhood
    (P : BasePrime) (r : Rank) (level : Nat)
    (g : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (ResidueField P r level)) :
    IsOpen (arithmeticFiniteAdeleCyclicNormOneCongruenceNeighborhood
      P r level g) := by
  exact (isOpen_arithmeticFiniteAdeleCyclicIntegralNormOneSet P r).inter
    ((isOpen_arithmeticFiniteAdeleCyclicCongruenceNeighborhood P r level
      (g : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (ResidueField P r level))).preimage
      (Units.continuous_val.comp continuous_subtype_val))
theorem arithmeticFiniteAdeleCyclicNormOneCongruenceNeighborhood_nonempty
    (P : BasePrime) (r : Rank) (level : Nat)
    (g : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (ResidueField P r level)) :
    (arithmeticFiniteAdeleCyclicNormOneCongruenceNeighborhood
      P r level g).Nonempty := by
  refine ⟨finiteSpecialLinearToArithmeticFiniteAdeleNormOne P r level g,
    finiteSpecialLinearToArithmeticFiniteAdeleNormOne_integral
      P r level g, ?_⟩
  change
    (finiteSpecialLinearToArithmeticFiniteAdeleNormOne P r level g).1.1 ∈
      arithmeticFiniteAdeleCyclicCongruenceNeighborhood P r level
        (g : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (ResidueField P r level))
  rw [mem_arithmeticFiniteAdeleCyclicCongruenceNeighborhood_iff]
  exact ⟨(finiteSpecialLinearToArithmeticFiniteAdeleNormOne_integral
      P r level g).1,
    finiteSpecialLinearToArithmeticFiniteAdeleNormOne_reduction
      P r level g⟩
theorem indexCompletedNormOneInnerFormToIndexLocal_injective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Injective
      (indexCompletedNormOneInnerFormToIndexLocal P r level) := by
  intro s t h
  apply Subtype.ext
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  have hij := congrArg (fun M => M i j) (congrArg Subtype.val h)
  exact HahnSeries.ofPowerSeries_injective hij
noncomputable abbrev IndexLocalIntegralNormOneInnerForm
    (P : BasePrime) (r : Rank) (level : Nat) :=
  (indexCompletedNormOneInnerFormToIndexLocal P r level).range
noncomputable def indexCompletedNormOneInnerFormEquivIndexLocalIntegral
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexCompletedNormOneInnerForm P r level ≃*
      IndexLocalIntegralNormOneInnerForm P r level :=
  MulEquiv.ofBijective
    (indexCompletedNormOneInnerFormToIndexLocal P r level).rangeRestrict
    ⟨(MonoidHom.rangeRestrict_injective_iff.mpr
      (indexCompletedNormOneInnerFormToIndexLocal_injective P r level)),
      MonoidHom.rangeRestrict_surjective _⟩
noncomputable def indexLocalIntegralNormOneReduction
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexLocalIntegralNormOneInnerForm P r level →*
      Matrix.SpecialLinearGroup (Fin r.matrixRank)
        (ResidueField P r level) :=
  (indexCompletedNormOneReduction P r level).comp
    (indexCompletedNormOneInnerFormEquivIndexLocalIntegral
      P r level).symm.toMonoidHom
noncomputable def sIntegralNormOneToIndexLocalIntegral
    (P : BasePrime) (r : Rank) (level : Nat) :
    CartwrightStegerSIntegralNormOne P r →*
      IndexLocalIntegralNormOneInnerForm P r level :=
  (indexCompletedNormOneInnerFormEquivIndexLocalIntegral
    P r level).toMonoidHom.comp
      (baseNormOneOrderUnitsToCompleted P r level)
noncomputable def sIntegralNormOneReductionToSL
    (P : BasePrime) (r : Rank) (level : Nat) :
    CartwrightStegerSIntegralNormOne P r →*
      Matrix.SpecialLinearGroup (Fin r.matrixRank)
        (ResidueField P r level) :=
  (indexLocalIntegralNormOneReduction P r level).comp
    (sIntegralNormOneToIndexLocalIntegral P r level)
theorem sIntegralNormOneReductionToSL_factor_completed
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : CartwrightStegerSIntegralNormOne P r) :
    sIntegralNormOneReductionToSL P r level u =
      indexCompletedNormOneReduction P r level
        (baseNormOneOrderUnitsToCompleted P r level u) := by
  simp [sIntegralNormOneReductionToSL,
    sIntegralNormOneToIndexLocalIntegral,
    indexLocalIntegralNormOneReduction]
theorem sIntegralNormOneReductionToSL_surjective_of_prasadStrongApproximation
    (P : BasePrime) (r : Rank) (level : Nat)
    (hPrasad : DenseRange
      (cyclicAlgebraNormOneToArithmeticFiniteAdeleNormOne P r)) :
    Function.Surjective (sIntegralNormOneReductionToSL P r level) := by
  intro g
  let U : Set (ArithmeticFiniteAdeleCyclicNormOne P r) :=
    arithmeticFiniteAdeleCyclicNormOneCongruenceNeighborhood
      P r level g
  have hUopen : IsOpen U :=
    isOpen_arithmeticFiniteAdeleCyclicNormOneCongruenceNeighborhood
      P r level g
  have hUne : U.Nonempty :=
    arithmeticFiniteAdeleCyclicNormOneCongruenceNeighborhood_nonempty
      P r level g
  obtain ⟨z, hzU, hzrange⟩ :=
    dense_iff_inter_open.mp hPrasad U hUopen hUne
  obtain ⟨u, rfl⟩ := hzrange
  have hint :
      cyclicAlgebraNormOneToArithmeticFiniteAdeleNormOne P r u ∈
        ArithmeticFiniteAdeleCyclicIntegralNormOneSet P r := hzU.1
  rw [cyclicAlgebraNormOne_preimage_integralNormOneSet] at hint
  obtain ⟨s, hs⟩ := hint
  have hcong := hzU.2
  rw [← hs] at hcong
  change cyclicAlgebraToArithmeticFiniteAdeles P r
      (orderNormOneInnerFormCyclicAlgebraPoint P r s) ∈
    arithmeticFiniteAdeleCyclicCongruenceNeighborhood P r level
      (g : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (ResidueField P r level)) at hcong
  have hred :=
    (orderNormOneInnerForm_mem_arithmeticFiniteAdeleCyclicCongruenceNeighborhood_iff
      P r level s
        (g : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (ResidueField P r level))).mp hcong
  refine ⟨orderNormOneInnerFormEquivBaseNormOneOrderUnits P r s, ?_⟩
  rw [sIntegralNormOneReductionToSL_factor_completed]
  change indexCompletedNormOneReduction P r level
      (orderNormOneInnerFormToCompleted P r level
        ((orderNormOneInnerFormEquivBaseNormOneOrderUnits P r).symm
          (orderNormOneInnerFormEquivBaseNormOneOrderUnits P r s))) = g
  rw [(orderNormOneInnerFormEquivBaseNormOneOrderUnits P r).symm_apply_apply]
  rw [indexCompletedNormOneReduction_global_compatibility]
  apply Subtype.ext
  exact hred
noncomputable def sIntegralNormOneReductionToPSL
    (P : BasePrime) (r : Rank) (level : Nat) :
    CartwrightStegerSIntegralNormOne P r →* PSL P r level :=
  (specialLinearToPSL P r level).comp
    (sIntegralNormOneReductionToSL P r level)
theorem sIntegralNormOneReductionToPSL_eq_baseReduction
    (P : BasePrime) (r : Rank) (level : Nat) :
    sIntegralNormOneReductionToPSL P r level =
      baseNormOneOrderUnitsReduction P r level := by
  ext u
  rw [sIntegralNormOneReductionToPSL, MonoidHom.comp_apply,
    sIntegralNormOneReductionToSL_factor_completed,
    baseNormOneOrderUnitsReduction_factor_completed]
theorem sIntegralNormOneReductionToPSL_surjective_iff_PSL_le_image
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Surjective (sIntegralNormOneReductionToPSL P r level) ↔
      PSL P r level ≤ IndexCartwrightStegerImage P r level := by
  rw [sIntegralNormOneReductionToPSL_eq_baseReduction,
    baseNormOneOrderUnitsReduction_surjective_iff_PSL_le_image]
theorem sIntegralNormOneReductionToPSL_surjective_of_prasadStrongApproximation
    (P : BasePrime) (r : Rank) (level : Nat)
    (hPrasad : DenseRange
      (cyclicAlgebraNormOneToArithmeticFiniteAdeleNormOne P r)) :
    Function.Surjective (sIntegralNormOneReductionToPSL P r level) := by
  intro y
  obtain ⟨g, rfl⟩ := specialLinearToPSL_surjective P r level y
  obtain ⟨u, hu⟩ :=
    sIntegralNormOneReductionToSL_surjective_of_prasadStrongApproximation
      P r level hPrasad g
  refine ⟨u, ?_⟩
  change specialLinearToPSL P r level
      (sIntegralNormOneReductionToSL P r level u) =
    specialLinearToPSL P r level g
  rw [hu]
theorem PSL_le_IndexCartwrightStegerImage_of_prasadStrongApproximation
    (P : BasePrime) (r : Rank) (level : Nat)
    (hPrasad : DenseRange
      (cyclicAlgebraNormOneToArithmeticFiniteAdeleNormOne P r)) :
    PSL P r level ≤ IndexCartwrightStegerImage P r level :=
  (sIntegralNormOneReductionToPSL_surjective_iff_PSL_le_image
    P r level).mp
      (sIntegralNormOneReductionToPSL_surjective_of_prasadStrongApproximation
        P r level hPrasad)
noncomputable def cyclicAlgebraNormOneToBuildingLocal
    (P : BasePrime) (r : Rank) :
    CyclicAlgebraNormOne P r →*
      BuildingCyclicScalarExtensionNormOne P r :=
  (cyclicAlgebraBuildingNormOneToLocal P r).comp
    (MulEquiv.subgroupCongr
      (cyclicAlgebraBuildingNormOne_eq_normOne P r).symm).toMonoidHom
noncomputable def orderNormOneInnerFormToBuildingLocal
    (P : BasePrime) (r : Rank) :
    OrderNormOneInnerForm P r →*
      BuildingCyclicScalarExtensionNormOne P r :=
  (cyclicAlgebraNormOneToBuildingLocal P r).comp
    (orderNormOneInnerFormToCyclicAlgebraNormOne P r)
noncomputable def baseNormOneOrderUnitsToBuildingLocal
    (P : BasePrime) (r : Rank) :
    CartwrightStegerBaseNormOneOrderUnits P r →*
      BuildingCyclicScalarExtensionNormOne P r :=
  (orderNormOneInnerFormToBuildingLocal P r).comp
    (orderNormOneInnerFormEquivBaseNormOneOrderUnits P r).symm.toMonoidHom
noncomputable def indexCartwrightStegerColorZeroEquivPSLOfLe
    (P : BasePrime) (r : Rank) (level : Nat)
    (hPSL : PSL P r level ≤ IndexCartwrightStegerImage P r level) :
    IndexCartwrightStegerColorZero P r level ≃* PSL P r level where
  toFun g :=
    ⟨(g : IndexCartwrightStegerImage P r level),
      (mem_IndexCartwrightStegerColorZero_iff_mem_PSL
        P r level (g : IndexCartwrightStegerImage P r level)).mp
          g.property⟩
  invFun s := by
    let g : IndexCartwrightStegerImage P r level :=
      ⟨s, hPSL s.property⟩
    exact ⟨g,
      (mem_IndexCartwrightStegerColorZero_iff_mem_PSL
        P r level g).mpr s.property⟩
  left_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv s := by
    apply Subtype.ext
    rfl
  map_mul' g h := by
    apply Subtype.ext
    rfl
noncomputable def
    indexCartwrightStegerColorZeroEquivPSLOfPrasadStrongApproximation
    (P : BasePrime) (r : Rank) (level : Nat)
    (hPrasad : DenseRange
      (cyclicAlgebraNormOneToArithmeticFiniteAdeleNormOne P r)) :
    IndexCartwrightStegerColorZero P r level ≃* PSL P r level :=
  indexCartwrightStegerColorZeroEquivPSLOfLe P r level
    (PSL_le_IndexCartwrightStegerImage_of_prasadStrongApproximation
      P r level hPrasad)
end QEC.Coding.HighDimensionalExpander.CartwrightSteger


