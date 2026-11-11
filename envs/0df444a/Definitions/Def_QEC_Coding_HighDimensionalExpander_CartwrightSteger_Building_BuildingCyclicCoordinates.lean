-- Prove2me | Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingCyclicCoordinates
-- name    : QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingCyclicCoordinates
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T03:48:34.589284+00:00
-- url     : https://prove2.me/theorems/6f84a205-0cfe-40c7-810d-8db59cae923c
-- title:
--   Building Cyclic Coordinates
-- statement:
--   Definitions and structural lemmas for Building Cyclic Coordinates, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingCyclicCoordinates.lean

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_ArithmeticIntersection
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_GlobalBuildingLattice
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityLattice
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_LocalLinkReduction
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CongruenceLifting_residueTransvectionSpecial_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingCompactCyclicSemidirectHom_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingGeneratorNeighborAtEquiv_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingIntegralUnitPGLHom_monomial
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingLatticeVertexMap_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerGeneratorCyclicElement_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerGeneratorCyclicUnit_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerGeneratorCyclicUnit_to_buildingGL
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerGeneratorCyclicUnit_to_buildingPGL
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerNormUnit_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantFrobenius_order
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrixHom_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrix_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraToBuilding_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraToBuilding_cartwrightStegerBCyclicElement
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraToBuilding_cartwrightStegerGeneratorCyclicElement
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraToBuilding_constantCyclicElement
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraToBuilding_cyclicGeneratorCyclicElement
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraToBuilding_cyclicGeneratorInverseCyclicElement
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraToBuilding_cyclicMonomial
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_frobeniusGL_coe
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
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_mem_skewLaurentIntSupport
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueBGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueConstantGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueXAdjoinRootEquiv_root
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueYAdjoinRootEquiv_root
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewLaurentMonomialUnit_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewLaurentToBuildingMatrix_single
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewLaurentToGlobalMatrix_single
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_toLin_constantRegularMatrix
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
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingCompactCyclicSemidirectHom_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingGeneratorNeighborAtEquiv_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingIntegralUnitPGLHom_monomial
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingLatticeVertexMap_one
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
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.mem_skewLaurentIntSupport
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueBGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueConstantGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueXAdjoinRootEquiv_root
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueYAdjoinRootEquiv_root
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurentMonomialUnit_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurentToBuildingMatrix_single
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
open scoped MatrixGroups
noncomputable def residueCyclicBasisVector
    (P : BasePrime) (r : Rank)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BaseField P) :=
  constantRegularMatrix P r (constantBasis P r p.1) *
    (frobeniusGL P r :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BaseField P)) ^
        (p.2 : ℕ)
theorem toLin_residueCyclicBasisVector_apply
    (P : BasePrime) (r : Rank)
    (p : Fin r.matrixRank × Fin r.matrixRank)
    (x : ConstantExtension P r) :
    Matrix.toLin (constantBasis P r) (constantBasis P r)
        (residueCyclicBasisVector P r p) x =
      (constantBasis P r p.1) *
        ((constantFrobenius P r) ^ (p.2 : ℕ)) x := by
  rw [residueCyclicBasisVector]
  rw [Matrix.toLin_mul_apply (constantBasis P r) (constantBasis P r)
    (constantBasis P r)]
  rw [toLin_constantRegularMatrix]
  change (constantBasis P r p.1) *
      Matrix.toLin (constantBasis P r) (constantBasis P r)
        ((frobeniusGL P r :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BaseField P)) ^
            (p.2 : ℕ)) x = _
  rw [Matrix.toLin_pow, frobeniusGL_coe, Matrix.toLin_toMatrix]
  simp [Module.End.coe_pow]
theorem residueCyclicBasisVector_linearIndependent
    (P : BasePrime) (r : Rank) :
    LinearIndependent (BaseField P) (residueCyclicBasisVector P r) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro a ha p
  have hfun : ∀ x : ConstantExtension P r,
      ∑ k : Fin r.matrixRank,
        (∑ j : Fin r.matrixRank,
          algebraMap (BaseField P) (ConstantExtension P r) (a (j, k)) *
            constantBasis P r j) *
          ((constantFrobenius P r) ^ (k : ℕ)) x = 0 := by
    intro x
    calc
      _ = ∑ k : Fin r.matrixRank, ∑ j : Fin r.matrixRank,
          a (j, k) •
            Matrix.toLin (constantBasis P r) (constantBasis P r)
              (residueCyclicBasisVector P r (j, k)) x := by
          apply Finset.sum_congr rfl
          intro k _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j _
          rw [toLin_residueCyclicBasisVector_apply]
          simp [Algebra.smul_def, mul_assoc]
      _ = Matrix.toLin (constantBasis P r) (constantBasis P r)
          (∑ q, a q • residueCyclicBasisVector P r q) x := by
          rw [Fintype.sum_prod_type, Finset.sum_comm]
          simp
      _ = 0 := by rw [ha]; simp
  let f : Fin r.matrixRank → ConstantExtension P r := fun k =>
    ∑ j : Fin r.matrixRank,
      algebraMap (BaseField P) (ConstantExtension P r) (a (j, k)) *
        constantBasis P r j
  have hfrob : ∀ k, f k = 0 := by
    have hrel : ∑ k : Fin r.matrixRank,
        f k • ((constantFrobenius P r) ^ (k : ℕ)).toAlgHom.toLinearMap = 0 := by
      apply LinearMap.ext
      intro x
      simpa [f, Algebra.smul_def] using hfun x
    have hinj : Function.Injective
        (fun k : Fin r.matrixRank =>
          ((constantFrobenius P r) ^ (k : ℕ)).toAlgHom) := by
      intro i j hij
      have hpowers : (constantFrobenius P r) ^ (i : ℕ) =
          (constantFrobenius P r) ^ (j : ℕ) := by
        apply AlgEquiv.ext
        intro x
        exact DFunLike.congr_fun hij x
      apply Fin.ext
      apply pow_injOn_Iio_orderOf (x := constantFrobenius P r)
      · simpa [constantFrobenius_order P r] using i.isLt
      · simpa [constantFrobenius_order P r] using j.isLt
      · exact hpowers
    have hli : LinearIndependent (ConstantExtension P r)
        (fun k : Fin r.matrixRank =>
          ((constantFrobenius P r) ^ (k : ℕ)).toAlgHom.toLinearMap) :=
      (linearIndependent_algHom_toLinearMap
        (BaseField P) (ConstantExtension P r) (ConstantExtension P r)).comp
          (fun k : Fin r.matrixRank =>
            ((constantFrobenius P r) ^ (k : ℕ)).toAlgHom) hinj
    exact Fintype.linearIndependent_iff.mp hli f hrel
  have hp := hfrob p.2
  have hp' : (∑ j : Fin r.matrixRank,
      a (j, p.2) • constantBasis P r j) = 0 := by
    simpa [f, Algebra.smul_def] using hp
  have hpcoord := congrArg (fun x => (constantBasis P r).repr x p.1) hp'
  simp only [map_sum, map_smul] at hpcoord
  simp_rw [(constantBasis P r).repr_self] at hpcoord
  simp only [Finsupp.smul_single, smul_eq_mul, mul_one, map_zero,
    Finsupp.zero_apply] at hpcoord
  have hsingle : (∑ c : Fin r.matrixRank,
      Finsupp.single c (a (c, p.2))) p.1 = a p := by
    simp [Finsupp.single_apply]
  rw [hsingle] at hpcoord
  exact hpcoord
noncomputable def residueCyclicBasis
    (P : BasePrime) (r : Rank) :
    Module.Basis (Fin r.matrixRank × Fin r.matrixRank) (BaseField P)
      (Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BaseField P)) :=
  Module.Basis.mk (residueCyclicBasisVector_linearIndependent P r)
    ((residueCyclicBasisVector_linearIndependent P r).span_eq_top_of_card_eq_finrank
      (by simp [Module.finrank_matrix])).ge
@[simp] theorem residueCyclicBasis_apply
    (P : BasePrime) (r : Rank)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    residueCyclicBasis P r p = residueCyclicBasisVector P r p := by
  simp [residueCyclicBasis]
noncomputable def buildingIntegralCyclicBasisVector
    (P : BasePrime) (r : Rank)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BuildingIntegerRing P) :=
  (constantRegularMatrix P r (constantBasis P r p.1)).map PowerSeries.C *
    ((buildingCyclicGeneratorIntegralGL P r :
      Matrix.GeneralLinearGroup (Fin r.matrixRank) (BuildingIntegerRing P)) :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BuildingIntegerRing P)) ^
          (p.2 : ℕ)
@[simp] theorem buildingIntegralCyclicBasisVector_reduction
    (P : BasePrime) (r : Rank)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    (buildingIntegralCyclicBasisVector P r p).map PowerSeries.constantCoeff =
      residueCyclicBasisVector P r p := by
  rw [buildingIntegralCyclicBasisVector, residueCyclicBasisVector,
    Matrix.map_mul, Matrix.map_pow]
  congr 1
  exact congrArg
    (fun M : Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BaseField P) =>
      M ^ (p.2 : ℕ))
    (congrArg Units.val
      (powerSeriesReductionGL_buildingCyclicGeneratorIntegralGL P r))
@[simp] theorem buildingIntegralCyclicBasisVector_toLocal
    (P : BasePrime) (r : Rank)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    (buildingIntegralCyclicBasisVector P r p).map
        (SphericalHecke.integerEmbedding (BaseField P)) =
      buildingCyclicBasisVector P r p := by
  rw [buildingIntegralCyclicBasisVector, buildingCyclicBasisVector,
    Matrix.map_mul, Matrix.map_pow]
  congr 1
  have hz := congrArg Units.val
    (buildingCyclicGeneratorIntegralGL_toLocal P r)
  change (↑(buildingCyclicGeneratorIntegralGL P r) :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BuildingIntegerRing P)).map
        (SphericalHecke.integerEmbedding (BaseField P)) =
      (buildingCyclicGeneratorGL P r :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BuildingLocalField P)) at hz
  rw [buildingCyclicGeneratorGL_coe] at hz
  exact congrArg
    (fun M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (BuildingLocalField P) => M ^ (p.2 : ℕ))
    hz
theorem buildingIntegralCyclicBasisVector_det_isUnit
    (P : BasePrime) (r : Rank) :
    IsUnit ((Matrix.stdBasis (BuildingIntegerRing P)
      (Fin r.matrixRank) (Fin r.matrixRank)).det
        (buildingIntegralCyclicBasisVector P r)) := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  have hmap : PowerSeries.constantCoeff
      ((Matrix.stdBasis (BuildingIntegerRing P)
        (Fin r.matrixRank) (Fin r.matrixRank)).det
          (buildingIntegralCyclicBasisVector P r)) =
      (Matrix.stdBasis (BaseField P)
        (Fin r.matrixRank) (Fin r.matrixRank)).det
          (residueCyclicBasisVector P r) := by
    simp only [Module.Basis.det_apply]
    rw [RingHom.map_det]
    congr 1
    apply Matrix.ext
    intro p q
    change PowerSeries.constantCoeff
        (buildingIntegralCyclicBasisVector P r q p.1 p.2) =
      residueCyclicBasisVector P r q p.1 p.2
    exact congrFun (congrFun
      (buildingIntegralCyclicBasisVector_reduction P r q) p.1) p.2
  rw [hmap]
  let hli := residueCyclicBasisVector_linearIndependent P r
  exact (Module.Basis.is_basis_iff_det
    (Matrix.stdBasis (BaseField P)
      (Fin r.matrixRank) (Fin r.matrixRank))).mp
        ⟨hli, hli.span_eq_top_of_card_eq_finrank
          (by simp [Module.finrank_matrix])⟩
noncomputable def buildingIntegralCyclicBasis
    (P : BasePrime) (r : Rank) :
    Module.Basis (Fin r.matrixRank × Fin r.matrixRank)
      (BuildingIntegerRing P)
      (Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BuildingIntegerRing P)) :=
  Module.Basis.mk
    ((Module.Basis.is_basis_iff_det
      (Matrix.stdBasis (BuildingIntegerRing P)
        (Fin r.matrixRank) (Fin r.matrixRank))).mpr
          (buildingIntegralCyclicBasisVector_det_isUnit P r)).1
    ((Module.Basis.is_basis_iff_det
      (Matrix.stdBasis (BuildingIntegerRing P)
        (Fin r.matrixRank) (Fin r.matrixRank))).mpr
          (buildingIntegralCyclicBasisVector_det_isUnit P r)).2.ge
@[simp] theorem buildingIntegralCyclicBasis_apply
    (P : BasePrime) (r : Rank)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    buildingIntegralCyclicBasis P r p =
      buildingIntegralCyclicBasisVector P r p := by
  simp [buildingIntegralCyclicBasis]
theorem buildingCyclicBasisVector_det_isUnit
    (P : BasePrime) (r : Rank) :
    IsUnit ((Matrix.stdBasis (BuildingLocalField P)
      (Fin r.matrixRank) (Fin r.matrixRank)).det
        (buildingCyclicBasisVector P r)) := by
  have hint := buildingIntegralCyclicBasisVector_det_isUnit P r
  have hmapped :
      SphericalHecke.integerEmbedding (BaseField P)
          ((Matrix.stdBasis (BuildingIntegerRing P)
            (Fin r.matrixRank) (Fin r.matrixRank)).det
              (buildingIntegralCyclicBasisVector P r)) =
        (Matrix.stdBasis (BuildingLocalField P)
          (Fin r.matrixRank) (Fin r.matrixRank)).det
            (buildingCyclicBasisVector P r) := by
    simp only [Module.Basis.det_apply]
    have hmatrix :
        (SphericalHecke.integerEmbedding (BaseField P)).mapMatrix
            ((Matrix.stdBasis (BuildingIntegerRing P)
              (Fin r.matrixRank) (Fin r.matrixRank)).toMatrix
                (buildingIntegralCyclicBasisVector P r)) =
          (Matrix.stdBasis (BuildingLocalField P)
            (Fin r.matrixRank) (Fin r.matrixRank)).toMatrix
              (buildingCyclicBasisVector P r) := by
      apply Matrix.ext
      intro p q
      change SphericalHecke.integerEmbedding (BaseField P)
          (buildingIntegralCyclicBasisVector P r q p.1 p.2) =
        buildingCyclicBasisVector P r q p.1 p.2
      exact congrFun (congrFun
        (buildingIntegralCyclicBasisVector_toLocal P r q) p.1) p.2
    rw [RingHom.map_det, hmatrix]
  rw [← hmapped]
  exact IsUnit.map (SphericalHecke.integerEmbedding (BaseField P)) hint
noncomputable def buildingLocalCyclicBasis
    (P : BasePrime) (r : Rank) :
    Module.Basis (Fin r.matrixRank × Fin r.matrixRank)
      (BuildingLocalField P)
      (Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BuildingLocalField P)) :=
  Module.Basis.mk
    ((Module.Basis.is_basis_iff_det
      (Matrix.stdBasis (BuildingLocalField P)
        (Fin r.matrixRank) (Fin r.matrixRank))).mpr
          (buildingCyclicBasisVector_det_isUnit P r)).1
    ((Module.Basis.is_basis_iff_det
      (Matrix.stdBasis (BuildingLocalField P)
        (Fin r.matrixRank) (Fin r.matrixRank))).mpr
          (buildingCyclicBasisVector_det_isUnit P r)).2.ge
end QEC.Coding.HighDimensionalExpander.CartwrightSteger


