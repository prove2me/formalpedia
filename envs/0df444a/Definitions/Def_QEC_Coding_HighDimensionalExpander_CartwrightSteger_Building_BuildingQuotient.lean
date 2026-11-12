-- Prove2me | Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingQuotient
-- name    : QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingQuotient
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T15:49:36.765586+00:00
-- url     : https://prove2.me/theorems/3011003c-9571-45ae-a897-33ef3950bb86
-- title:
--   Building Quotient
-- statement:
--   Definitions and structural lemmas for Building Quotient, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingQuotient.lean

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_Relations
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
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_exists_orderUnitLattice_lift_of_buildingLattice
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
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_map_OrderSplitCartwrightStegerLattice_to_global
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_map_orderSplitCartwrightStegerClassGeneratorGL_to_global
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_map_orderUnitLattice_to_building
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_map_orderUnitLattice_to_global
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_mem_skewLaurentIntSupport
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_orderSplitBaseChangeGLHom_injective
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_orderUnitToBuildingPGL_generator
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_orderUnitToGlobalGL_generator
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_orderUnitToGlobalPGL_eq_compactNormalForm_of_building_eq
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


set_option autoImplicit false
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
noncomputable def orderSplitLatticeToGlobalMatrixGroup
    (P : BasePrime) (r : Rank) :
    OrderSplitCartwrightStegerLattice P r →*
      CartwrightStegerMatrixGroup P r where
  toFun x := ⟨orderSplitBaseChangeGLHom P r
      (x : Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (ConstantArithmeticRing P r)), by
    have hx : orderSplitBaseChangeGLHom P r
        (x : Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (ConstantArithmeticRing P r)) ∈
        (OrderSplitCartwrightStegerLattice P r).map
          (orderSplitBaseChangeGLHom P r) :=
      ⟨x, x.property, rfl⟩
    rw [map_OrderSplitCartwrightStegerLattice_to_global] at hx
    exact hx⟩
  map_one' := Subtype.ext (map_one (orderSplitBaseChangeGLHom P r))
  map_mul' x y := Subtype.ext
    (map_mul (orderSplitBaseChangeGLHom P r)
      (x : Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (ConstantArithmeticRing P r))
      (y : Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (ConstantArithmeticRing P r)))
theorem orderSplitLatticeToGlobalMatrixGroup_surjective
    (P : BasePrime) (r : Rank) :
    Function.Surjective (orderSplitLatticeToGlobalMatrixGroup P r) := by
  intro y
  have hy : (y : Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (SplittingFunctionField P r)) ∈
      (OrderSplitCartwrightStegerLattice P r).map
        (orderSplitBaseChangeGLHom P r) := by
    rw [map_OrderSplitCartwrightStegerLattice_to_global]
    exact y.property
  obtain ⟨x, hx, hxy⟩ := hy
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
theorem orderSplitLatticeToGlobalMatrixGroup_injective
    (P : BasePrime) (r : Rank) :
    Function.Injective (orderSplitLatticeToGlobalMatrixGroup P r) := by
  intro x y hxy
  apply Subtype.ext
  apply orderSplitBaseChangeGLHom_injective P r
  exact congrArg Subtype.val hxy
noncomputable def globalMatrixLatticeReduction
    (P : BasePrime) (r : Rank) (level : Nat) :
    CartwrightStegerMatrixGroup P r →* IndexCartwrightStegerImage P r level :=
  (orderSplitLatticeToGlobalMatrixGroup P r).liftOfSurjective
    (orderSplitLatticeToGlobalMatrixGroup_surjective P r)
    ⟨orderSplitLatticeReduction P r level, by
      intro x hx
      have hxOne : x = 1 :=
        orderSplitLatticeToGlobalMatrixGroup_injective P r
          ((MonoidHom.mem_ker.mp hx).trans (map_one _).symm)
      subst x
      exact Subgroup.one_mem _⟩
@[simp] theorem globalMatrixLatticeReduction_orderSplit
    (P : BasePrime) (r : Rank) (level : Nat)
    (x : OrderSplitCartwrightStegerLattice P r) :
    globalMatrixLatticeReduction P r level
        (orderSplitLatticeToGlobalMatrixGroup P r x) =
      orderSplitLatticeReduction P r level x := by
  simp [globalMatrixLatticeReduction]
noncomputable def orderUnitLatticeToGlobalMatrixGroup
    (P : BasePrime) (r : Rank) :
    CartwrightStegerOrderUnitLattice P r →*
      CartwrightStegerMatrixGroup P r where
  toFun u := ⟨orderUnitToGlobalGL P r
      (u : (CartwrightStegerOrder P r)ˣ), by
    have hu : orderUnitToGlobalGL P r
        (u : (CartwrightStegerOrder P r)ˣ) ∈
        (CartwrightStegerOrderUnitLattice P r).map
          (orderUnitToGlobalGL P r) := ⟨u, u.property, rfl⟩
    rw [map_orderUnitLattice_to_global] at hu
    exact hu⟩
  map_one' := Subtype.ext (map_one (orderUnitToGlobalGL P r))
  map_mul' u v := Subtype.ext (map_mul (orderUnitToGlobalGL P r)
    (u : (CartwrightStegerOrder P r)ˣ)
    (v : (CartwrightStegerOrder P r)ˣ))
theorem orderUnitLatticeToGlobalMatrixGroup_surjective
    (P : BasePrime) (r : Rank) :
    Function.Surjective (orderUnitLatticeToGlobalMatrixGroup P r) := by
  intro y
  have hy : (y : Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (SplittingFunctionField P r)) ∈
      (CartwrightStegerOrderUnitLattice P r).map
        (orderUnitToGlobalGL P r) := by
    rw [map_orderUnitLattice_to_global]
    exact y.property
  obtain ⟨u, hu, huy⟩ := hy
  exact ⟨⟨u, hu⟩, Subtype.ext huy⟩
noncomputable def orderUnitLatticeToBuildingLattice
    (P : BasePrime) (r : Rank) :
    CartwrightStegerOrderUnitLattice P r →*
      BuildingCartwrightStegerLattice P r where
  toFun u := ⟨orderUnitToBuildingPGL P r
      (u : (CartwrightStegerOrder P r)ˣ), by
    have hu : orderUnitToBuildingPGL P r
        (u : (CartwrightStegerOrder P r)ˣ) ∈
        (CartwrightStegerOrderUnitLattice P r).map
          (orderUnitToBuildingPGL P r) := ⟨u, u.property, rfl⟩
    rw [map_orderUnitLattice_to_building] at hu
    exact hu⟩
  map_one' := Subtype.ext (map_one (orderUnitToBuildingPGL P r))
  map_mul' u v := Subtype.ext (map_mul (orderUnitToBuildingPGL P r)
    (u : (CartwrightStegerOrder P r)ˣ)
    (v : (CartwrightStegerOrder P r)ˣ))
theorem orderUnitLatticeToBuildingLattice_surjective
    (P : BasePrime) (r : Rank) :
    Function.Surjective (orderUnitLatticeToBuildingLattice P r) := by
  intro g
  obtain ⟨u, hu, hug⟩ :=
    exists_orderUnitLattice_lift_of_buildingLattice P r g
  exact ⟨⟨u, hu⟩, Subtype.ext hug⟩
noncomputable def orderUnitLatticeReduction
    (P : BasePrime) (r : Rank) (level : Nat) :
    CartwrightStegerOrderUnitLattice P r →*
      IndexCartwrightStegerImage P r level :=
  (globalMatrixLatticeReduction P r level).comp
    (orderUnitLatticeToGlobalMatrixGroup P r)
theorem orderUnitLatticeReduction_surjective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Surjective (orderUnitLatticeReduction P r level) := by
  intro y
  obtain ⟨x, hx⟩ := orderSplitLatticeReduction_surjective P r level y
  obtain ⟨u, hu⟩ := orderUnitLatticeToGlobalMatrixGroup_surjective P r
    (orderSplitLatticeToGlobalMatrixGroup P r x)
  refine ⟨u, ?_⟩
  change globalMatrixLatticeReduction P r level
      (orderUnitLatticeToGlobalMatrixGroup P r u) = y
  rw [hu, globalMatrixLatticeReduction_orderSplit, hx]
theorem ker_orderUnitLatticeToBuildingLattice_le_reduction
    (P : BasePrime) (r : Rank) (level : Nat) :
    (orderUnitLatticeToBuildingLattice P r).ker ≤
      (orderUnitLatticeReduction P r level).ker := by
  intro u hu
  have huBuilding : orderUnitToBuildingPGL P r u = 1 := by
    exact congrArg Subtype.val (MonoidHom.mem_ker.mp hu)
  have huCompact : orderUnitToBuildingPGL P r u ∈
      SphericalHecke.maximalCompact (BaseField P) r.matrixRank := by
    rw [huBuilding]
    exact Subgroup.one_mem _
  have huGlobal : orderUnitToGlobalPGL P r u = 1 := by
    have hnormal :=
      orderUnitToGlobalPGL_eq_compactNormalForm_of_building_eq
        P r u huCompact 1 0 (by simpa using huBuilding)
    simpa [globalCompactNormalForm, constantUnitMatrix] using hnormal
  obtain ⟨x, hx⟩ := orderSplitLatticeToGlobalMatrixGroup_surjective P r
    (orderUnitLatticeToGlobalMatrixGroup P r u)
  have hxGlobal : Matrix.ProjGenLinGroup.mk
        (orderSplitBaseChangeGLHom P r x) =
      Matrix.ProjGenLinGroup.mk (orderSplitBaseChangeGLHom P r 1) := by
    rw [show orderSplitBaseChangeGLHom P r x =
        orderUnitToGlobalGL P r u from congrArg Subtype.val hx]
    simpa [orderUnitToGlobalPGL] using huGlobal
  have hxReduction :=
    orderSplitReductionPGLHom_eq_of_baseChange_projective_eq
      P r level x 1 hxGlobal
  rw [MonoidHom.mem_ker]
  change globalMatrixLatticeReduction P r level
      (orderUnitLatticeToGlobalMatrixGroup P r u) = 1
  rw [← hx, globalMatrixLatticeReduction_orderSplit]
  apply Subtype.ext
  change orderSplitReductionPGLHom P r level x = 1
  simpa using hxReduction
noncomputable def buildingLatticeReduction
    (P : BasePrime) (r : Rank) (level : Nat) :
    BuildingCartwrightStegerLattice P r →*
      IndexCartwrightStegerImage P r level :=
  (orderUnitLatticeToBuildingLattice P r).liftOfSurjective
    (orderUnitLatticeToBuildingLattice_surjective P r)
    ⟨orderUnitLatticeReduction P r level,
      ker_orderUnitLatticeToBuildingLattice_le_reduction P r level⟩
@[simp] theorem buildingLatticeReduction_orderUnit
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : CartwrightStegerOrderUnitLattice P r) :
    buildingLatticeReduction P r level
        (orderUnitLatticeToBuildingLattice P r u) =
      orderUnitLatticeReduction P r level u := by
  simp [buildingLatticeReduction]
theorem buildingLatticeReduction_surjective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Surjective (buildingLatticeReduction P r level) := by
  intro y
  obtain ⟨u, hu⟩ := orderUnitLatticeReduction_surjective P r level y
  exact ⟨orderUnitLatticeToBuildingLattice P r u, by
    rw [buildingLatticeReduction_orderUnit, hu]⟩
noncomputable def orderUnitLatticeGenerator
    (P : BasePrime) (r : Rank) (u : ConstantProjectiveClass P r) :
    CartwrightStegerOrderUnitLattice P r :=
  ⟨cartwrightStegerOrderUnitGenerator P r u,
    Subgroup.subset_closure ⟨u, rfl⟩⟩
noncomputable def orderSplitLatticeGenerator
    (P : BasePrime) (r : Rank) (u : ConstantProjectiveClass P r) :
    OrderSplitCartwrightStegerLattice P r :=
  ⟨orderSplitCartwrightStegerGeneratorGL P r
      (constantClassRepresentative P r u),
    Subgroup.subset_closure ⟨u, rfl⟩⟩
@[simp] theorem orderUnitLatticeGenerator_to_building
    (P : BasePrime) (r : Rank) (u : ConstantProjectiveClass P r) :
    orderUnitLatticeToBuildingLattice P r
        (orderUnitLatticeGenerator P r u) =
      buildingLatticeGenerator P r u := by
  apply Subtype.ext
  exact orderUnitToBuildingPGL_generator P r u
theorem orderUnitLatticeGenerator_to_global_eq_orderSplit
    (P : BasePrime) (r : Rank) (u : ConstantProjectiveClass P r) :
    orderUnitLatticeToGlobalMatrixGroup P r
        (orderUnitLatticeGenerator P r u) =
      orderSplitLatticeToGlobalMatrixGroup P r
        (orderSplitLatticeGenerator P r u) := by
  apply Subtype.ext
  change orderUnitToGlobalGL P r
      (cartwrightStegerOrderUnitGenerator P r u) =
    orderSplitBaseChangeGLHom P r
      (orderSplitCartwrightStegerGeneratorGL P r
        (constantClassRepresentative P r u))
  rw [orderUnitToGlobalGL_generator,
    map_orderSplitCartwrightStegerClassGeneratorGL_to_global]
@[simp] theorem orderUnitLatticeReduction_generator
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : ConstantProjectiveClass P r) :
    orderUnitLatticeReduction P r level
        (orderUnitLatticeGenerator P r u) =
      ⟨indexCartwrightStegerClassGenerator P r level u,
        indexCartwrightStegerGenerator_mem_image P r level u⟩ := by
  change globalMatrixLatticeReduction P r level
      (orderUnitLatticeToGlobalMatrixGroup P r
        (orderUnitLatticeGenerator P r u)) = _
  rw [orderUnitLatticeGenerator_to_global_eq_orderSplit,
    globalMatrixLatticeReduction_orderSplit]
  apply Subtype.ext
  exact orderSplitReductionPGLHom_classGenerator P r level u
@[simp] theorem buildingLatticeReduction_generator
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : ConstantProjectiveClass P r) :
    buildingLatticeReduction P r level
        (buildingLatticeGenerator P r u) =
      ⟨indexCartwrightStegerClassGenerator P r level u,
        indexCartwrightStegerGenerator_mem_image P r level u⟩ := by
  rw [← orderUnitLatticeGenerator_to_building,
    buildingLatticeReduction_orderUnit,
    orderUnitLatticeReduction_generator]
noncomputable def BuildingCartwrightStegerCongruenceSubgroup
    (P : BasePrime) (r : Rank) (level : Nat) :
    Subgroup (BuildingCartwrightStegerLattice P r) :=
  (buildingLatticeReduction P r level).ker
noncomputable instance buildingCartwrightStegerCongruenceSubgroupNormal
    (P : BasePrime) (r : Rank) (level : Nat) :
    (BuildingCartwrightStegerCongruenceSubgroup P r level).Normal := by
  dsimp [BuildingCartwrightStegerCongruenceSubgroup]
  infer_instance
noncomputable def buildingLatticeQuotientEquiv
    (P : BasePrime) (r : Rank) (level : Nat) :
    BuildingCartwrightStegerLattice P r ⧸
        BuildingCartwrightStegerCongruenceSubgroup P r level ≃*
      IndexCartwrightStegerImage P r level :=
  QuotientGroup.quotientKerEquivOfSurjective
    (buildingLatticeReduction P r level)
    (buildingLatticeReduction_surjective P r level)
end QEC.Coding.HighDimensionalExpander.CartwrightSteger


