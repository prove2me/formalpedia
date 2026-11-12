-- Prove2me | Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadDenominatorCorrection
-- name    : QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadDenominatorCorrection
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T18:19:11.537743+00:00
-- url     : https://prove2.me/theorems/ff41e0ab-ebba-4cf1-963f-2608ae078cae
-- title:
--   Prasad Denominator Correction
-- statement:
--   Definitions and structural lemmas for Prasad Denominator Correction, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadDenominatorCorrection.lean

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadSpecialization
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CongruenceLifting_residueTransvectionSpecial_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_arithmeticFiniteAdeleCyclicUnitDenominatorPlaces_finite
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
noncomputable local instance arithmeticFinitePlaceDecidableEq (P : BasePrime) :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P)) :=
  Classical.decEq _
noncomputable def arithmeticFiniteAdeleSupportedAtPlace
    (P : BasePrime)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (x : v.adicCompletion (FunctionField P)) :
    ArithmeticFiniteAdeleRing P := by
  classical
  refine ⟨Pi.single v x, ?_⟩
  rw [Filter.eventually_cofinite]
  apply Set.Finite.subset (Set.finite_singleton v)
  intro w hw
  simp only [Set.mem_singleton_iff]
  by_contra hwv
  apply hw
  rw [Pi.single_eq_of_ne hwv]
  exact (w.adicCompletionIntegers (FunctionField P)).zero_mem
@[simp] theorem arithmeticFiniteAdeleAt_supportedAtPlace
    (P : BasePrime)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (x : v.adicCompletion (FunctionField P)) :
    arithmeticFiniteAdeleAt P v
        (arithmeticFiniteAdeleSupportedAtPlace P v x) = x := by
  classical
  change Pi.single v x v = x
  exact Pi.single_eq_same v x
noncomputable def arithmeticFiniteAdeleSupportedAtPlaceNonUnitalRingHom
    (P : BasePrime)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P)) :
    v.adicCompletion (FunctionField P) →ₙ+* ArithmeticFiniteAdeleRing P where
  toFun := arithmeticFiniteAdeleSupportedAtPlace P v
  map_zero' := by
    apply IsDedekindDomain.FiniteAdeleRing.ext
    intro w
    classical
    change Pi.single v 0 w = 0
    by_cases hwv : w = v
    · subst w
      simp
    · rw [Pi.single_eq_of_ne hwv]
  map_add' := by
    intro x y
    apply IsDedekindDomain.FiniteAdeleRing.ext
    intro w
    classical
    change Pi.single v (x + y) w = Pi.single v x w + Pi.single v y w
    by_cases hwv : w = v
    · subst w
      simp
    · simp [Pi.single_eq_of_ne hwv]
  map_mul' := by
    intro x y
    apply IsDedekindDomain.FiniteAdeleRing.ext
    intro w
    classical
    change Pi.single v (x * y) w = Pi.single v x w * Pi.single v y w
    by_cases hwv : w = v
    · subst w
      simp
    · simp [Pi.single_eq_of_ne hwv]
noncomputable def arithmeticFiniteAdeleSupportedAtPlaceLinearMap
    (P : BasePrime)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P)) :
    v.adicCompletion (FunctionField P) →ₗ[FunctionField P]
      ArithmeticFiniteAdeleRing P where
  toFun := arithmeticFiniteAdeleSupportedAtPlace P v
  map_add' := map_add
    (arithmeticFiniteAdeleSupportedAtPlaceNonUnitalRingHom P v)
  map_smul' a x := by
    apply IsDedekindDomain.FiniteAdeleRing.ext
    intro w
    classical
    change Pi.single v (a • x) w =
      algebraMap (FunctionField P)
        (w.adicCompletion (FunctionField P)) a * Pi.single v x w
    by_cases hwv : w = v
    · subst w
      simp only [Pi.single_eq_same, Algebra.smul_def]
    · simp only [Pi.single_eq_of_ne hwv, mul_zero]
noncomputable abbrev ArithmeticAdicCyclicAlgebra
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P)) :=
  TensorProduct (FunctionField P)
    (v.adicCompletion (FunctionField P)) (CyclicAlgebra P r)
noncomputable def arithmeticFiniteAdeleCyclicAlgebraAtPlace
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P)) :
    ArithmeticFiniteAdeleCyclicAlgebra P r →ₐ[FunctionField P]
      ArithmeticAdicCyclicAlgebra P r v :=
  Algebra.TensorProduct.map
    (arithmeticFiniteAdeleAtAlgHom P v)
    (AlgHom.id (FunctionField P) (CyclicAlgebra P r))
noncomputable def arithmeticFiniteAdeleCyclicSupportedAtPlace
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P)) :
    ArithmeticAdicCyclicAlgebra P r v →ₗ[FunctionField P]
      ArithmeticFiniteAdeleCyclicAlgebra P r :=
  TensorProduct.map
    (arithmeticFiniteAdeleSupportedAtPlaceLinearMap P v)
    LinearMap.id
@[simp] theorem arithmeticFiniteAdeleCyclicAlgebraAtPlace_tmul
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (a : ArithmeticFiniteAdeleRing P) (x : CyclicAlgebra P r) :
    arithmeticFiniteAdeleCyclicAlgebraAtPlace P r v
        (TensorProduct.tmul (FunctionField P) a x) =
      TensorProduct.tmul (FunctionField P)
        (arithmeticFiniteAdeleAt P v a) x := by
  simp [arithmeticFiniteAdeleCyclicAlgebraAtPlace,
    arithmeticFiniteAdeleAtAlgHom]
  rfl
@[simp] theorem arithmeticFiniteAdeleCyclicSupportedAtPlace_tmul
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (a : v.adicCompletion (FunctionField P)) (x : CyclicAlgebra P r) :
    arithmeticFiniteAdeleCyclicSupportedAtPlace P r v
        (TensorProduct.tmul (FunctionField P) a x) =
      TensorProduct.tmul (FunctionField P)
        (arithmeticFiniteAdeleSupportedAtPlace P v a) x := by
  simp [arithmeticFiniteAdeleCyclicSupportedAtPlace,
    arithmeticFiniteAdeleSupportedAtPlaceLinearMap]
  rfl
@[simp] theorem arithmeticFiniteAdeleCyclicAlgebraAtPlace_supported
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (x : ArithmeticAdicCyclicAlgebra P r v) :
    arithmeticFiniteAdeleCyclicAlgebraAtPlace P r v
        (arithmeticFiniteAdeleCyclicSupportedAtPlace P r v x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp [arithmeticFiniteAdeleCyclicSupportedAtPlace]
  | add x y hx hy => simp [map_add, hx, hy]
  | tmul a x =>
      rw [arithmeticFiniteAdeleCyclicSupportedAtPlace_tmul,
        arithmeticFiniteAdeleCyclicAlgebraAtPlace_tmul,
        arithmeticFiniteAdeleAt_supportedAtPlace]
noncomputable def arithmeticAdicCyclicBasis
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P)) :
    Module.Basis (Fin r.matrixRank × Fin r.matrixRank)
      (v.adicCompletion (FunctionField P))
      (ArithmeticAdicCyclicAlgebra P r v) :=
  (functionFieldCyclicBasis P r).baseChange
    (v.adicCompletion (FunctionField P))
noncomputable def ArithmeticAdicCyclicIntegralLattice
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P)) :
    Set (ArithmeticAdicCyclicAlgebra P r v) :=
  {x | ∀ p, (arithmeticAdicCyclicBasis P r v).equivFun x p ∈
    v.adicCompletionIntegers (FunctionField P)}
@[simp] theorem arithmeticFiniteAdeleCyclicAlgebraAtPlace_diagonal
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (x : CyclicAlgebra P r) :
    arithmeticFiniteAdeleCyclicAlgebraAtPlace P r v
        (cyclicAlgebraToArithmeticFiniteAdeles P r x) =
      TensorProduct.tmul (FunctionField P) 1 x := by
  simp [cyclicAlgebraToArithmeticFiniteAdeles_apply]
theorem arithmeticFiniteAdeleCyclicSupportedAtPlace_mul
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (x y : ArithmeticAdicCyclicAlgebra P r v) :
    arithmeticFiniteAdeleCyclicSupportedAtPlace P r v (x * y) =
      arithmeticFiniteAdeleCyclicSupportedAtPlace P r v x *
        arithmeticFiniteAdeleCyclicSupportedAtPlace P r v y := by
  induction x using TensorProduct.induction_on with
  | zero => simp [arithmeticFiniteAdeleCyclicSupportedAtPlace]
  | add x z hx hz => simp [add_mul, map_add, hx, hz]
  | tmul a x =>
      induction y using TensorProduct.induction_on with
      | zero => simp [arithmeticFiniteAdeleCyclicSupportedAtPlace]
      | add y z hy hz => simp [mul_add, map_add, hy, hz]
      | tmul b y =>
          simp [Algebra.TensorProduct.tmul_mul_tmul,
            show arithmeticFiniteAdeleSupportedAtPlace P v (a * b) =
                arithmeticFiniteAdeleSupportedAtPlace P v a *
                  arithmeticFiniteAdeleSupportedAtPlace P v b from
              map_mul
                (arithmeticFiniteAdeleSupportedAtPlaceNonUnitalRingHom P v)
                a b]
noncomputable def arithmeticFiniteAdeleCyclicPlaceIdempotent
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P)) :
    ArithmeticFiniteAdeleCyclicAlgebra P r :=
  arithmeticFiniteAdeleCyclicSupportedAtPlace P r v 1
theorem arithmeticFiniteAdeleCyclicPlaceIdempotent_mul_self
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P)) :
    arithmeticFiniteAdeleCyclicPlaceIdempotent P r v *
        arithmeticFiniteAdeleCyclicPlaceIdempotent P r v =
      arithmeticFiniteAdeleCyclicPlaceIdempotent P r v := by
  rw [arithmeticFiniteAdeleCyclicPlaceIdempotent,
    ← arithmeticFiniteAdeleCyclicSupportedAtPlace_mul]
  simp
theorem arithmeticFiniteAdeleCyclicPlaceIdempotent_mul_supported
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (x : ArithmeticAdicCyclicAlgebra P r v) :
    arithmeticFiniteAdeleCyclicPlaceIdempotent P r v *
        arithmeticFiniteAdeleCyclicSupportedAtPlace P r v x =
      arithmeticFiniteAdeleCyclicSupportedAtPlace P r v x := by
  rw [arithmeticFiniteAdeleCyclicPlaceIdempotent,
    ← arithmeticFiniteAdeleCyclicSupportedAtPlace_mul]
  simp
theorem arithmeticFiniteAdeleCyclicSupported_mul_placeIdempotent
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (x : ArithmeticAdicCyclicAlgebra P r v) :
    arithmeticFiniteAdeleCyclicSupportedAtPlace P r v x *
        arithmeticFiniteAdeleCyclicPlaceIdempotent P r v =
      arithmeticFiniteAdeleCyclicSupportedAtPlace P r v x := by
  rw [arithmeticFiniteAdeleCyclicPlaceIdempotent,
    ← arithmeticFiniteAdeleCyclicSupportedAtPlace_mul]
  simp
noncomputable def arithmeticFiniteAdeleCyclicPatchAtPlace
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (x : ArithmeticAdicCyclicAlgebra P r v) :
    ArithmeticFiniteAdeleCyclicAlgebra P r :=
  1 - arithmeticFiniteAdeleCyclicPlaceIdempotent P r v +
    arithmeticFiniteAdeleCyclicSupportedAtPlace P r v x
theorem arithmeticFiniteAdeleCyclicPatchAtPlace_mul
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (x y : ArithmeticAdicCyclicAlgebra P r v) :
    arithmeticFiniteAdeleCyclicPatchAtPlace P r v x *
        arithmeticFiniteAdeleCyclicPatchAtPlace P r v y =
      arithmeticFiniteAdeleCyclicPatchAtPlace P r v (x * y) := by
  change
    (1 - arithmeticFiniteAdeleCyclicPlaceIdempotent P r v +
        arithmeticFiniteAdeleCyclicSupportedAtPlace P r v x) *
      (1 - arithmeticFiniteAdeleCyclicPlaceIdempotent P r v +
        arithmeticFiniteAdeleCyclicSupportedAtPlace P r v y) =
    1 - arithmeticFiniteAdeleCyclicPlaceIdempotent P r v +
      arithmeticFiniteAdeleCyclicSupportedAtPlace P r v (x * y)
  noncomm_ring
    [arithmeticFiniteAdeleCyclicPlaceIdempotent_mul_self P r v,
      arithmeticFiniteAdeleCyclicPlaceIdempotent_mul_supported P r v x,
      arithmeticFiniteAdeleCyclicPlaceIdempotent_mul_supported P r v y,
      arithmeticFiniteAdeleCyclicSupported_mul_placeIdempotent P r v x,
      arithmeticFiniteAdeleCyclicSupported_mul_placeIdempotent P r v y,
      arithmeticFiniteAdeleCyclicSupportedAtPlace_mul P r v x y]
@[simp] theorem arithmeticFiniteAdeleCyclicAlgebraAtPlace_patch
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (x : ArithmeticAdicCyclicAlgebra P r v) :
    arithmeticFiniteAdeleCyclicAlgebraAtPlace P r v
        (arithmeticFiniteAdeleCyclicPatchAtPlace P r v x) = x := by
  simp [arithmeticFiniteAdeleCyclicPatchAtPlace,
    arithmeticFiniteAdeleCyclicPlaceIdempotent]
noncomputable def arithmeticFiniteAdeleCyclicUnitSupportedAtPlace
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (u : (ArithmeticAdicCyclicAlgebra P r v)ˣ) :
    (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ where
  val := arithmeticFiniteAdeleCyclicPatchAtPlace P r v u
  inv := arithmeticFiniteAdeleCyclicPatchAtPlace P r v
    ((u⁻¹ : (ArithmeticAdicCyclicAlgebra P r v)ˣ) :
      ArithmeticAdicCyclicAlgebra P r v)
  val_inv := by
    rw [arithmeticFiniteAdeleCyclicPatchAtPlace_mul]
    have hu : (u : ArithmeticAdicCyclicAlgebra P r v) *
        ((u⁻¹ : (ArithmeticAdicCyclicAlgebra P r v)ˣ) :
          ArithmeticAdicCyclicAlgebra P r v) = 1 := by
      exact congrArg Units.val (mul_inv_cancel u)
    rw [hu]
    simp [arithmeticFiniteAdeleCyclicPatchAtPlace,
      arithmeticFiniteAdeleCyclicPlaceIdempotent]
  inv_val := by
    rw [arithmeticFiniteAdeleCyclicPatchAtPlace_mul]
    have hu :
        ((u⁻¹ : (ArithmeticAdicCyclicAlgebra P r v)ˣ) :
          ArithmeticAdicCyclicAlgebra P r v) *
          (u : ArithmeticAdicCyclicAlgebra P r v) = 1 := by
      exact congrArg Units.val (inv_mul_cancel u)
    rw [hu]
    simp [arithmeticFiniteAdeleCyclicPatchAtPlace,
      arithmeticFiniteAdeleCyclicPlaceIdempotent]
noncomputable def arithmeticFiniteAdeleCyclicUnitAtPlace
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P)) :
    (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ →*
      (ArithmeticAdicCyclicAlgebra P r v)ˣ :=
  Units.map
    (arithmeticFiniteAdeleCyclicAlgebraAtPlace P r v).toRingHom.toMonoidHom
noncomputable def arithmeticFiniteAdeleCyclicUnitClearAtPlace
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (u : (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ) :
    (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ :=
  arithmeticFiniteAdeleCyclicUnitSupportedAtPlace P r v
      ((arithmeticFiniteAdeleCyclicUnitAtPlace P r v u)⁻¹) * u
noncomputable def arithmeticFiniteAdeleCyclicUnitClearAtPlaceList
    (P : BasePrime) (r : Rank) :
    List (IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P)) →
      (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ →
        (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ
  | [], u => u
  | v :: places, u =>
      arithmeticFiniteAdeleCyclicUnitClearAtPlaceList P r places
        (arithmeticFiniteAdeleCyclicUnitClearAtPlace P r v u)
noncomputable def arithmeticFiniteAdeleCyclicUnitDenominatorPlaceList
    (P : BasePrime) (r : Rank)
    (u : (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ) :
    List (IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P)) :=
  (arithmeticFiniteAdeleCyclicUnitDenominatorPlaces_finite P r u).toFinset.toList
end QEC.Coding.HighDimensionalExpander.CartwrightSteger


