-- Prove2me | Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicDivisionAlgebra
-- name    : QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicDivisionAlgebra
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T14:46:11.374547+00:00
-- url     : https://prove2.me/theorems/bcb4ebba-ed84-467a-af7c-3cee21dbc15d
-- title:
--   Cyclic Division Algebra
-- statement:
--   Definitions and structural lemmas for Cyclic Division Algebra, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/CyclicDivisionAlgebra.lean

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewCompatibility
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewReconstructionTheorem
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewUnits
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
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraToBuilding_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraToBuilding_cartwrightStegerBCyclicElement
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraToBuilding_cartwrightStegerGeneratorCyclicElement
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraToBuilding_constantCyclicElement
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraToBuilding_cyclicGeneratorCyclicElement
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraToBuilding_cyclicGeneratorInverseCyclicElement
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraToBuilding_cyclicMonomial
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_exists_skewLaurent_of_integralCyclicCoordinates
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_exists_skewLaurent_support_max
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
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewLaurentToGlobalMatrix_injective
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewLaurentToGlobalMatrix_single
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewLaurent_coeff_mul_at_support_max_ne_zero
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


set_option autoImplicit false
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem skewLaurent_mul_ne_zero
    (P : BasePrime) (r : Rank)
    {f g : CartwrightStegerSkewLaurentRing P r}
    (hf : f ≠ 0) (hg : g ≠ 0) :
    f * g ≠ 0 := by
  obtain ⟨a, ha, hmaxa⟩ := exists_skewLaurent_support_max P r hf
  obtain ⟨b, hb, hmaxb⟩ := exists_skewLaurent_support_max P r hg
  intro hzero
  have hcoeff := skewLaurent_coeff_mul_at_support_max_ne_zero P r
    ha hmaxa hb hmaxb
  rw [hzero] at hcoeff
  exact hcoeff rfl
noncomputable def cyclicCoordinateCommonDenominator
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r) :
    PolynomialRing P :=
  ∏ p : Fin r.matrixRank × Fin r.matrixRank,
    ((functionFieldCyclicBasis P r).repr x p).denom
theorem cyclicCoordinateCommonDenominator_ne_zero
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r) :
    cyclicCoordinateCommonDenominator P r x ≠ 0 := by
  rw [cyclicCoordinateCommonDenominator, Finset.prod_ne_zero_iff]
  intro p _
  exact RatFunc.denom_ne_zero _
theorem cyclicCoordinate_denom_dvd_commonDenominator
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    ((functionFieldCyclicBasis P r).repr x p).denom ∣
      cyclicCoordinateCommonDenominator P r x := by
  unfold cyclicCoordinateCommonDenominator
  exact Finset.dvd_prod_of_mem
    (fun q : Fin r.matrixRank × Fin r.matrixRank =>
      ((functionFieldCyclicBasis P r).repr x q).denom)
    (Finset.mem_univ p)
theorem exists_integralArithmetic_coordinate_commonDenominator_smul
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    ∃ a : IntegralArithmeticRing P,
      integralArithmeticToFunctionField P a =
        (functionFieldCyclicBasis P r).repr
          ((algebraMap (PolynomialRing P) (FunctionField P)
              (cyclicCoordinateCommonDenominator P r x)) • x) p := by
  let D := cyclicCoordinateCommonDenominator P r x
  let c := (functionFieldCyclicBasis P r).repr x p
  have hD : D ≠ 0 := cyclicCoordinateCommonDenominator_ne_zero P r x
  have hdvd : c.denom ∣ D :=
    cyclicCoordinate_denom_dvd_commonDenominator P r x p
  obtain ⟨q, hq⟩ := (RatFunc.denom_dvd hD).mp hdvd
  refine ⟨algebraMap (PolynomialRing P) (IntegralArithmeticRing P) q, ?_⟩
  rw [integralArithmeticToFunctionField_algebraMap]
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
  change algebraMap (PolynomialRing P) (FunctionField P) q =
    algebraMap (PolynomialRing P) (FunctionField P) D * c
  rw [hq]
  rw [div_eq_mul_inv, mul_left_comm,
    mul_inv_cancel₀ (RatFunc.algebraMap_ne_zero hD), mul_one]
theorem exists_skewLaurent_clearing_cyclic_denominators
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r) :
    ∃ D : PolynomialRing P, D ≠ 0 ∧
      ∃ f : CartwrightStegerSkewLaurentRing P r,
        skewLaurentToCyclicAlgebra P r f =
          (algebraMap (PolynomialRing P) (FunctionField P) D) • x := by
  let D := cyclicCoordinateCommonDenominator P r x
  have hD : D ≠ 0 := cyclicCoordinateCommonDenominator_ne_zero P r x
  have hcoords : ∀ p : Fin r.matrixRank × Fin r.matrixRank,
      ∃ a : IntegralArithmeticRing P,
        integralArithmeticToFunctionField P a =
          (functionFieldCyclicBasis P r).repr
            ((algebraMap (PolynomialRing P) (FunctionField P) D) • x) p := by
    intro p
    exact exists_integralArithmetic_coordinate_commonDenominator_smul P r x p
  obtain ⟨f, hf⟩ := exists_skewLaurent_of_integralCyclicCoordinates P r
    ((algebraMap (PolynomialRing P) (FunctionField P) D) • x) hcoords
  refine ⟨D, hD, f, ?_⟩
  apply Subtype.ext
  exact hf
theorem cyclicAlgebra_mul_ne_zero
    (P : BasePrime) (r : Rank)
    {x y : CyclicAlgebra P r} (hx : x ≠ 0) (hy : y ≠ 0) :
    x * y ≠ 0 := by
  obtain ⟨D, hD, f, hf⟩ :=
    exists_skewLaurent_clearing_cyclic_denominators P r x
  obtain ⟨E, hE, g, hg⟩ :=
    exists_skewLaurent_clearing_cyclic_denominators P r y
  have hDf : f ≠ 0 := by
    intro hf0
    rw [hf0, map_zero] at hf
    have hscalar :
        algebraMap (PolynomialRing P) (FunctionField P) D ≠ 0 :=
      RatFunc.algebraMap_ne_zero hD
    exact hx ((smul_eq_zero.mp hf.symm).resolve_left hscalar)
  have hEg : g ≠ 0 := by
    intro hg0
    rw [hg0, map_zero] at hg
    have hscalar :
        algebraMap (PolynomialRing P) (FunctionField P) E ≠ 0 :=
      RatFunc.algebraMap_ne_zero hE
    exact hy ((smul_eq_zero.mp hg.symm).resolve_left hscalar)
  intro hxy
  have hmap : skewLaurentToCyclicAlgebra P r (f * g) = 0 := by
    rw [map_mul, hf, hg]
    rw [smul_mul_smul_comm, hxy, smul_zero]
  have hfg : f * g = 0 := by
    apply skewLaurentToGlobalMatrix_injective P r
    simpa only [skewLaurentToCyclicAlgebra_coe, map_zero, ZeroMemClass.coe_zero]
      using congrArg Subtype.val hmap
  exact (skewLaurent_mul_ne_zero P r hDf hEg) hfg
@[implicit_reducible] noncomputable def cyclicAlgebraIsDomain
    (P : BasePrime) (r : Rank) : IsDomain (CyclicAlgebra P r) := by
  letI : NoZeroDivisors (CyclicAlgebra P r) :=
    ⟨fun h => Classical.byContradiction fun hn =>
      cyclicAlgebra_mul_ne_zero P r
        (fun hx => hn (Or.inl hx)) (fun hy => hn (Or.inr hy)) h⟩
  exact NoZeroDivisors.to_isDomain (CyclicAlgebra P r)
@[implicit_reducible] noncomputable def cyclicAlgebraDivisionRing
    (P : BasePrime) (r : Rank) : DivisionRing (CyclicAlgebra P r) := by
  letI : IsDomain (CyclicAlgebra P r) := cyclicAlgebraIsDomain P r
  letI : FiniteDimensional (FunctionField P) (CyclicAlgebra P r) :=
    (functionFieldCyclicBasis P r).finiteDimensional_of_finite
  exact divisionRingOfFiniteDimensional (FunctionField P) (CyclicAlgebra P r)
end QEC.Coding.HighDimensionalExpander.CartwrightSteger


