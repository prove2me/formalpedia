-- Prove2me | Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_NormOneCompatibility
-- name    : QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_NormOneCompatibility
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T16:52:15.160304+00:00
-- url     : https://prove2.me/theorems/da585e2c-eb94-4d06-888c-9c36be6c890c
-- title:
--   Norm One Compatibility
-- statement:
--   Definitions and structural lemmas for Norm One Compatibility, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Norm/NormOneCompatibility.lean

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_SplitCoordinates
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
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraReducedNorm_baseChange_eq_splitReducedNorm
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
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_orderInnerFormToOrderUnits_surjective
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
noncomputable def CyclicAlgebraNormOne
    (P : BasePrime) (r : Rank) : Subgroup ((CyclicAlgebra P r)ˣ) :=
  (cyclicAlgebraReducedNorm P r).ker
theorem cyclicAlgebraSplitNormOne_eq_normOne
    (P : BasePrime) (r : Rank) :
    CyclicAlgebraSplitNormOne P r = CyclicAlgebraNormOne P r := by
  apply SetLike.ext
  intro u
  change cyclicAlgebraSplitReducedNorm P r u = 1 ↔
    cyclicAlgebraReducedNorm P r u = 1
  constructor
  · intro hu
    apply Units.map_injective (functionFieldEmbedding P r).injective
    calc
      Units.map (functionFieldEmbedding P r).toMonoidHom
          (cyclicAlgebraReducedNorm P r u) =
        cyclicAlgebraSplitReducedNorm P r u :=
          cyclicAlgebraReducedNorm_baseChange_eq_splitReducedNorm P r u
      _ = 1 := hu
      _ = Units.map (functionFieldEmbedding P r).toMonoidHom 1 := (map_one _).symm
  · intro hu
    calc
      cyclicAlgebraSplitReducedNorm P r u =
        Units.map (functionFieldEmbedding P r).toMonoidHom
          (cyclicAlgebraReducedNorm P r u) :=
            (cyclicAlgebraReducedNorm_baseChange_eq_splitReducedNorm P r u).symm
      _ = Units.map (functionFieldEmbedding P r).toMonoidHom 1 :=
        congrArg (Units.map (functionFieldEmbedding P r).toMonoidHom) hu
      _ = 1 := map_one _
noncomputable def cartwrightStegerOrderBaseReducedNorm
    (P : BasePrime) (r : Rank) :
    (CartwrightStegerOrder P r)ˣ →* (FunctionField P)ˣ :=
  (cyclicAlgebraReducedNorm P r).comp (orderUnitToCyclicUnit P r)
noncomputable def CartwrightStegerBaseNormOneOrderUnits
    (P : BasePrime) (r : Rank) :
    Subgroup ((CartwrightStegerOrder P r)ˣ) :=
  (cartwrightStegerOrderBaseReducedNorm P r).ker
theorem cartwrightStegerNormOneOrderUnits_eq_baseNormOne
    (P : BasePrime) (r : Rank) :
    CartwrightStegerNormOneOrderUnits P r =
      CartwrightStegerBaseNormOneOrderUnits P r := by
  apply SetLike.ext
  intro u
  change cartwrightStegerOrderReducedNorm P r u = 1 ↔
    cartwrightStegerOrderBaseReducedNorm P r u = 1
  change cyclicAlgebraSplitReducedNorm P r (orderUnitToCyclicUnit P r u) = 1 ↔
    cyclicAlgebraReducedNorm P r (orderUnitToCyclicUnit P r u) = 1
  constructor
  · intro hu
    apply Units.map_injective (functionFieldEmbedding P r).injective
    calc
      Units.map (functionFieldEmbedding P r).toMonoidHom
          (cyclicAlgebraReducedNorm P r (orderUnitToCyclicUnit P r u)) =
        cyclicAlgebraSplitReducedNorm P r (orderUnitToCyclicUnit P r u) :=
          cyclicAlgebraReducedNorm_baseChange_eq_splitReducedNorm P r _
      _ = 1 := hu
      _ = Units.map (functionFieldEmbedding P r).toMonoidHom 1 :=
        (map_one _).symm
  · intro hu
    calc
      cyclicAlgebraSplitReducedNorm P r (orderUnitToCyclicUnit P r u) =
        Units.map (functionFieldEmbedding P r).toMonoidHom
          (cyclicAlgebraReducedNorm P r (orderUnitToCyclicUnit P r u)) :=
            (cyclicAlgebraReducedNorm_baseChange_eq_splitReducedNorm P r _).symm
      _ = Units.map (functionFieldEmbedding P r).toMonoidHom 1 :=
        congrArg (Units.map (functionFieldEmbedding P r).toMonoidHom) hu
      _ = 1 := map_one _
noncomputable def orderNormOneInnerFormToBaseNormOneOrderUnits
    (P : BasePrime) (r : Rank) :
    OrderNormOneInnerForm P r →*
      CartwrightStegerBaseNormOneOrderUnits P r where
  toFun s := ⟨orderNormOneInnerFormToOrderUnits P r s, by
    rw [← cartwrightStegerNormOneOrderUnits_eq_baseNormOne]
    exact orderNormOneInnerFormToOrderUnits_mem_normOne P r s⟩
  map_one' := Subtype.ext (map_one (orderNormOneInnerFormToOrderUnits P r))
  map_mul' s t := Subtype.ext
    (map_mul (orderNormOneInnerFormToOrderUnits P r) s t)
theorem orderNormOneInnerFormToBaseNormOneOrderUnits_injective
    (P : BasePrime) (r : Rank) :
    Function.Injective (orderNormOneInnerFormToBaseNormOneOrderUnits P r) := by
  intro s t hst
  apply orderNormOneInnerFormToOrderUnits_injective P r
  exact congrArg Subtype.val hst
theorem orderNormOneInnerFormToBaseNormOneOrderUnits_surjective
    (P : BasePrime) (r : Rank) :
    Function.Surjective
      (orderNormOneInnerFormToBaseNormOneOrderUnits P r) := by
  intro u
  obtain ⟨g, hg⟩ := orderInnerFormToOrderUnits_surjective P r u
  have huOld : (u : (CartwrightStegerOrder P r)ˣ) ∈
      CartwrightStegerNormOneOrderUnits P r := by
    rw [cartwrightStegerNormOneOrderUnits_eq_baseNormOne]
    exact u.property
  have huDet : Matrix.GeneralLinearGroup.det
      (orderUnitToGlobalGL P r (u : (CartwrightStegerOrder P r)ˣ)) = 1 :=
    huOld
  have hgMap : Units.map
      (constantArithmeticToSplittingFunctionField P r).toMonoidHom
        (Matrix.GeneralLinearGroup.det
          (g : Matrix.GeneralLinearGroup (Fin r.matrixRank)
            (ConstantArithmeticRing P r))) = 1 := by
    calc
      _ = Matrix.GeneralLinearGroup.det
          (Matrix.GeneralLinearGroup.map
            (constantArithmeticToSplittingFunctionField P r)
            (g : Matrix.GeneralLinearGroup (Fin r.matrixRank)
              (ConstantArithmeticRing P r))) :=
        (Matrix.GeneralLinearGroup.map_det
          (constantArithmeticToSplittingFunctionField P r) _).symm
      _ = Matrix.GeneralLinearGroup.det
          (orderUnitToGlobalGL P r
            (orderInnerFormToOrderUnits P r g)) := by
        apply congrArg Matrix.GeneralLinearGroup.det
        rw [orderUnitToGlobalGL_orderInnerFormToOrderUnits]
        apply Units.ext
        rfl
      _ = Matrix.GeneralLinearGroup.det
          (orderUnitToGlobalGL P r
            (u : (CartwrightStegerOrder P r)ˣ)) := by rw [hg]
      _ = 1 := huDet
  have hgDet : Matrix.GeneralLinearGroup.det
      (g : Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (ConstantArithmeticRing P r)) = 1 := by
    apply Units.map_injective
      (constantArithmeticToSplittingFunctionField_injective P r)
    simpa using hgMap
  let gn : OrderInnerFormNormOne P r := ⟨g, hgDet⟩
  let s : OrderNormOneInnerForm P r :=
    (orderNormOneInnerFormEquivFullNormOne P r).symm gn
  refine ⟨s, ?_⟩
  apply Subtype.ext
  rw [← hg]
  apply Units.ext
  apply Subtype.ext
  change ((Matrix.SpecialLinearGroup.toGL
      ((s : OrderNormOneInnerForm P r) :
        Matrix.SpecialLinearGroup (Fin r.matrixRank)
          (ConstantArithmeticRing P r))) :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (ConstantArithmeticRing P r)).map
          (constantArithmeticToSplittingFunctionField P r) =
    (((g : OrderInnerFormUnits P r) :
      Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (ConstantArithmeticRing P r)) :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (ConstantArithmeticRing P r)).map
          (constantArithmeticToSplittingFunctionField P r)
  congr 1
noncomputable def orderNormOneInnerFormEquivBaseNormOneOrderUnits
    (P : BasePrime) (r : Rank) :
    OrderNormOneInnerForm P r ≃*
      CartwrightStegerBaseNormOneOrderUnits P r :=
  MulEquiv.ofBijective
    (orderNormOneInnerFormToBaseNormOneOrderUnits P r)
    ⟨orderNormOneInnerFormToBaseNormOneOrderUnits_injective P r,
      orderNormOneInnerFormToBaseNormOneOrderUnits_surjective P r⟩
noncomputable def orderNormOneInnerFormToCyclicAlgebraNormOne
    (P : BasePrime) (r : Rank) :
    OrderNormOneInnerForm P r →* CyclicAlgebraNormOne P r where
  toFun s := ⟨orderUnitToCyclicUnit P r
      (orderNormOneInnerFormToOrderUnits P r s), by
    change cyclicAlgebraReducedNorm P r
      (orderUnitToCyclicUnit P r
        (orderNormOneInnerFormToOrderUnits P r s)) = 1
    have hs : (orderUnitToCyclicUnit P r
        (orderNormOneInnerFormToOrderUnits P r s)) ∈
        CyclicAlgebraSplitNormOne P r :=
      (orderNormOneInnerFormToCyclicAlgebraSplitNormOne P r s).property
    rw [cyclicAlgebraSplitNormOne_eq_normOne] at hs
    exact hs⟩
  map_one' := Subtype.ext <| by simp
  map_mul' s t := Subtype.ext <| by simp
end QEC.Coding.HighDimensionalExpander.CartwrightSteger


