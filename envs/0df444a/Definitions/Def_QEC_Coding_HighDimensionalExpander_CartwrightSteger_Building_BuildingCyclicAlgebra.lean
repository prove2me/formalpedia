-- Prove2me | Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingCyclicAlgebra
-- name    : QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingCyclicAlgebra
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T00:02:42.943734+00:00
-- url     : https://prove2.me/theorems/bd70c06f-154e-43b1-9fa6-e12130ccd127
-- title:
--   Building Cyclic Algebra
-- statement:
--   Definitions and structural lemmas for Building Cyclic Algebra, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingCyclicAlgebra.lean

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebraBasis
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingSkewRepresentation
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CongruenceLifting_residueTransvectionSpecial_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Rank_two_le_matrixRank
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingCompactCyclicSemidirectHom_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingCyclicGeneratorMatrix_mul_buildingConstantMatrix
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingGeneratorNeighborAtEquiv_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingIntegralUnitPGLHom_monomial
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingLatticeVertexMap_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerBMatrix_mem_cyclicAlgebra
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerNormUnit_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantMatrix_mem_cyclicAlgebra
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrixHom_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrix_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicGeneratorInverseMatrix_mem_cyclicAlgebra
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicGeneratorMatrix_mem_cyclicAlgebra
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicGeneratorMatrix_pow_mul_constantMatrix
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicGeneratorMatrix_pow_rank_add
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_frobeniusPowerEquiv_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_functionFieldCyclicBasis_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_globalIntegralUnitGLHom_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_globalIntegralUnitPGLHom_monomial
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexConstantGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexCyclicGeneratorGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_infinityConjugationCorrectionSum_bound_zero
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_infinityCyclicCoefficient_rank
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_infinityCyclicCoefficient_zero
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_mem_skewLaurentIntSupport
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueBGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueConstantGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueXAdjoinRootEquiv_root
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueYAdjoinRootEquiv_root
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewLaurentMonomialUnit_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewLaurentToBuildingMatrix_single
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
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingCompactCyclicSemidirectHom_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingGeneratorNeighborAtEquiv_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingIntegralUnitPGLHom_monomial
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingLatticeVertexMap_one
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerNormUnit_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantUnitMatrixHom_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantUnitMatrix_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.frobeniusPowerEquiv_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.functionFieldCyclicBasis_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.globalIntegralUnitGLHom_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.globalIntegralUnitPGLHom_monomial
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexConstantGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexCyclicGeneratorGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.infinityConjugationCorrectionSum_bound_zero
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.infinityCyclicCoefficient_rank
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.infinityCyclicCoefficient_zero
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
noncomputable instance buildingLocalFunctionFieldAlgebra
    (P : BasePrime) : Algebra (FunctionField P) (BuildingLocalField P) :=
  (functionFieldToBuildingLocalField P).toAlgebra
noncomputable def buildingCyclicBasisVector
    (P : BasePrime) (r : Rank)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BuildingLocalField P) :=
  buildingConstantMatrix P r (constantBasis P r p.1) *
    buildingCyclicGeneratorMatrix P r ^ (p.2 : ℕ)
noncomputable def cyclicAlgebraToBuildingLinear
    (P : BasePrime) (r : Rank) :
    CyclicAlgebra P r →ₗ[FunctionField P]
  Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BuildingLocalField P) :=
  (functionFieldCyclicBasis P r).constr
    (FunctionField P)
    (fun p => buildingCyclicBasisVector P r p)
@[simp] theorem cyclicAlgebraToBuildingLinear_basis
    (P : BasePrime) (r : Rank)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    cyclicAlgebraToBuildingLinear P r (functionFieldCyclicBasis P r p) =
      buildingCyclicBasisVector P r p := by
  exact (functionFieldCyclicBasis P r).constr_basis
    (FunctionField P) (fun q => buildingCyclicBasisVector P r q) p
@[simp] theorem functionFieldToBuildingLocalField_C
    (P : BasePrime) (a : BaseField P) :
    functionFieldToBuildingLocalField P (RatFunc.C a) =
      algebraMap (BaseField P) (BuildingLocalField P) a := by
  calc
    functionFieldToBuildingLocalField P (RatFunc.C a) =
        algebraMap (RatFunc (BaseField P)) (LaurentSeries (BaseField P))
          (RatFunc.C a) := rfl
    _ = HahnSeries.single 0 a := by
      have h := (RatFunc.coe_coe (F := BaseField P) (Polynomial.C a)).symm
      simp at h
      exact h
    _ = algebraMap (BaseField P) (BuildingLocalField P) a := by
      rw [LaurentSeries.algebraMap_apply]
      ext n
      simp [HahnSeries.C]
theorem buildingConstantMatrix_baseField_smul_functionField
    (P : BasePrime) (r : Rank) (a : BaseField P)
    (c : ConstantExtension P r) :
    buildingConstantMatrix P r (a • c) =
      (algebraMap (BaseField P) (FunctionField P) a) •
        buildingConstantMatrix P r c := by
  have hC : algebraMap (FunctionField P) (BuildingLocalField P)
      (algebraMap (BaseField P) (FunctionField P) a) =
      algebraMap (BaseField P) (BuildingLocalField P) a := by
    change functionFieldToBuildingLocalField P (RatFunc.C a) = _
    exact functionFieldToBuildingLocalField_C P a
  have hBaseMatrix : buildingConstantMatrix P r
      (algebraMap (BaseField P) (ConstantExtension P r) a) =
      algebraMap (BuildingLocalField P)
        (Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BuildingLocalField P))
        (algebraMap (BaseField P) (BuildingLocalField P) a) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [buildingConstantMatrix, Matrix.algebraMap_matrix_apply]
    · simp [buildingConstantMatrix, Matrix.algebraMap_matrix_apply, hij]
  have hFunctionMatrix :
      algebraMap (FunctionField P)
          (Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BuildingLocalField P))
          (algebraMap (BaseField P) (FunctionField P) a) =
        algebraMap (BuildingLocalField P)
          (Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BuildingLocalField P))
          (algebraMap (BaseField P) (BuildingLocalField P) a) := by
    rw [IsScalarTower.algebraMap_apply
      (FunctionField P) (BuildingLocalField P)
      (Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BuildingLocalField P)), hC]
  rw [Algebra.smul_def]
  rw [← buildingConstantMatrixEmbedding_apply,
    ← buildingConstantMatrixEmbedding_apply]
  rw [Algebra.smul_def
    (algebraMap (BaseField P) (FunctionField P) a)
    (buildingConstantMatrixEmbedding P r c)]
  change buildingConstantMatrixEmbedding P r
      (algebraMap (BaseField P) (ConstantExtension P r) a * c) =
    (algebraMap (FunctionField P)
      (Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BuildingLocalField P))
      (algebraMap (BaseField P) (FunctionField P) a)) *
        buildingConstantMatrixEmbedding P r c
  rw [map_mul, buildingConstantMatrixEmbedding_apply,
    buildingConstantMatrixEmbedding_apply, hBaseMatrix, hFunctionMatrix]
theorem cyclicAlgebraToBuildingLinear_constantMonomial
    (P : BasePrime) (r : Rank) (c : ConstantExtension P r)
    (k : ℕ) (hk : k < r.matrixRank) :
    cyclicAlgebraToBuildingLinear P r
        ⟨constantMatrix P r c * cyclicGeneratorMatrix P r ^ k,
          (CyclicAlgebra P r).mul_mem
            (constantMatrix_mem_cyclicAlgebra P r c)
            ((CyclicAlgebra P r).pow_mem
              (cyclicGeneratorMatrix_mem_cyclicAlgebra P r) k)⟩ =
      buildingConstantMatrix P r c *
        buildingCyclicGeneratorMatrix P r ^ k := by
  let kf : Fin r.matrixRank := ⟨k, hk⟩
  have hsource :
      (⟨constantMatrix P r c * cyclicGeneratorMatrix P r ^ k,
        (CyclicAlgebra P r).mul_mem
          (constantMatrix_mem_cyclicAlgebra P r c)
          ((CyclicAlgebra P r).pow_mem
            (cyclicGeneratorMatrix_mem_cyclicAlgebra P r) k)⟩ :
        CyclicAlgebra P r) =
      ∑ j, (algebraMap (BaseField P) (FunctionField P)
        ((constantBasis P r).repr c j)) •
          functionFieldCyclicBasis P r (j, kf) := by
    apply Subtype.ext
    change constantMatrix P r c * cyclicGeneratorMatrix P r ^ k =
      (CyclicAlgebra P r).val (∑ j,
        (algebraMap (BaseField P) (FunctionField P)
          ((constantBasis P r).repr c j)) •
            functionFieldCyclicBasis P r (j, kf))
    rw [map_sum]
    simp only [map_smul, functionFieldCyclicBasis_apply]
    conv_lhs => rw [← (constantBasis P r).sum_repr c]
    rw [← constantMatrixEmbedding_apply, map_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [constantMatrixEmbedding_apply,
      constantMatrix_baseField_smul_functionField]
    rw [smul_mul_assoc]
    rfl
  rw [hsource, map_sum]
  simp_rw [map_smul, cyclicAlgebraToBuildingLinear_basis]
  have hconst :
      (∑ j, (algebraMap (BaseField P) (FunctionField P)
        ((constantBasis P r).repr c j)) •
          buildingConstantMatrix P r (constantBasis P r j)) =
        buildingConstantMatrix P r c := by
    conv_rhs => rw [← (constantBasis P r).sum_repr c]
    rw [← buildingConstantMatrixEmbedding_apply, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    simpa only [buildingConstantMatrixEmbedding_apply] using
      (buildingConstantMatrix_baseField_smul_functionField P r
        ((constantBasis P r).repr c j) (constantBasis P r j)).symm
  change (∑ j, (algebraMap (BaseField P) (FunctionField P)
      ((constantBasis P r).repr c j)) •
        (buildingConstantMatrix P r (constantBasis P r j) *
          buildingCyclicGeneratorMatrix P r ^ k)) = _
  calc
    _ = (∑ j, (algebraMap (BaseField P) (FunctionField P)
          ((constantBasis P r).repr c j)) •
            buildingConstantMatrix P r (constantBasis P r j)) *
          buildingCyclicGeneratorMatrix P r ^ k := by
      simp_rw [← smul_mul_assoc]
      rw [Finset.sum_mul]
    _ = _ := congrArg
      (fun M => M * buildingCyclicGeneratorMatrix P r ^ k) hconst
theorem buildingCyclicGeneratorMatrix_pow_mul_buildingConstantMatrix
    (P : BasePrime) (r : Rank) (j : ℕ) (c : ConstantExtension P r) :
    buildingCyclicGeneratorMatrix P r ^ j * buildingConstantMatrix P r c =
      buildingConstantMatrix P r ((constantFrobenius P r ^ j) c) *
        buildingCyclicGeneratorMatrix P r ^ j := by
  induction j generalizing c with
  | zero => simp
  | succ j ih =>
      calc
        buildingCyclicGeneratorMatrix P r ^ (j + 1) *
              buildingConstantMatrix P r c =
            buildingCyclicGeneratorMatrix P r ^ j *
              (buildingCyclicGeneratorMatrix P r *
                buildingConstantMatrix P r c) := by
                  rw [pow_succ, mul_assoc]
        _ = buildingCyclicGeneratorMatrix P r ^ j *
              (buildingConstantMatrix P r (constantFrobenius P r c) *
                buildingCyclicGeneratorMatrix P r) := by
                  rw [buildingCyclicGeneratorMatrix_mul_buildingConstantMatrix]
        _ = (buildingCyclicGeneratorMatrix P r ^ j *
              buildingConstantMatrix P r (constantFrobenius P r c)) *
                buildingCyclicGeneratorMatrix P r := by rw [mul_assoc]
        _ = buildingConstantMatrix P r
              ((constantFrobenius P r ^ j) (constantFrobenius P r c)) *
                buildingCyclicGeneratorMatrix P r ^ j *
                  buildingCyclicGeneratorMatrix P r := by rw [ih]
        _ = buildingConstantMatrix P r
              ((constantFrobenius P r ^ (j + 1)) c) *
                buildingCyclicGeneratorMatrix P r ^ (j + 1) := by
                  rw [pow_succ, AlgEquiv.mul_apply, pow_succ, mul_assoc]
theorem buildingCyclicGeneratorMatrix_pow_rank_add
    (P : BasePrime) (r : Rank) (n : ℕ) :
    buildingCyclicGeneratorMatrix P r ^ (r.matrixRank + n) =
      (1 + buildingLocalY P) •
        buildingCyclicGeneratorMatrix P r ^ n := by
  rw [pow_add, buildingCyclicGeneratorMatrix_pow_matrixRank]
  rw [smul_mul_assoc, one_mul]
@[simp] theorem functionFieldToBuildingLocalField_X
    (P : BasePrime) :
    functionFieldToBuildingLocalField P RatFunc.X = buildingLocalY P := by
  change ((RatFunc.X : RatFunc (BaseField P)) :
      LaurentSeries (BaseField P)) =
    ((PowerSeries.X : PowerSeries (BaseField P)) :
      LaurentSeries (BaseField P))
  rw [RatFunc.coe_X, PowerSeries.coe_X]
noncomputable def cyclicMonomial
    (P : BasePrime) (r : Rank) (c : ConstantExtension P r) (k : ℕ) :
    CyclicAlgebra P r :=
  ⟨constantMatrix P r c * cyclicGeneratorMatrix P r ^ k,
    (CyclicAlgebra P r).mul_mem
      (constantMatrix_mem_cyclicAlgebra P r c)
      ((CyclicAlgebra P r).pow_mem
        (cyclicGeneratorMatrix_mem_cyclicAlgebra P r) k)⟩
@[simp] theorem cyclicMonomial_coe
    (P : BasePrime) (r : Rank) (c : ConstantExtension P r) (k : ℕ) :
    (cyclicMonomial P r c k :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r)) =
      constantMatrix P r c * cyclicGeneratorMatrix P r ^ k := rfl
theorem cyclicAlgebraToBuildingLinear_cyclicMonomial
    (P : BasePrime) (r : Rank) (c : ConstantExtension P r)
    (k : ℕ) (hk : k < r.matrixRank) :
    cyclicAlgebraToBuildingLinear P r (cyclicMonomial P r c k) =
      buildingConstantMatrix P r c *
        buildingCyclicGeneratorMatrix P r ^ k := by
  exact cyclicAlgebraToBuildingLinear_constantMonomial P r c k hk
theorem cyclicMonomial_mul
    (P : BasePrime) (r : Rank) (c d : ConstantExtension P r)
    (k l : ℕ) :
    cyclicMonomial P r c k * cyclicMonomial P r d l =
      cyclicMonomial P r
        (c * (constantFrobenius P r ^ k) d) (k + l) := by
  apply Subtype.ext
  change
    (constantMatrix P r c * cyclicGeneratorMatrix P r ^ k) *
        (constantMatrix P r d * cyclicGeneratorMatrix P r ^ l) =
      constantMatrix P r (c * (constantFrobenius P r ^ k) d) *
        cyclicGeneratorMatrix P r ^ (k + l)
  calc
    _ = constantMatrix P r c *
        (cyclicGeneratorMatrix P r ^ k * constantMatrix P r d) *
          cyclicGeneratorMatrix P r ^ l := by group
    _ = constantMatrix P r c *
        (constantMatrix P r ((constantFrobenius P r ^ k) d) *
          cyclicGeneratorMatrix P r ^ k) *
          cyclicGeneratorMatrix P r ^ l := by
            rw [cyclicGeneratorMatrix_pow_mul_constantMatrix]
    _ = (constantMatrix P r c *
        constantMatrix P r ((constantFrobenius P r ^ k) d)) *
          (cyclicGeneratorMatrix P r ^ k *
            cyclicGeneratorMatrix P r ^ l) := by group
    _ = _ := by
      change (constantMatrixEmbedding P r c *
          constantMatrixEmbedding P r ((constantFrobenius P r ^ k) d)) *
          (cyclicGeneratorMatrix P r ^ k * cyclicGeneratorMatrix P r ^ l) = _
      rw [← map_mul, ← pow_add]
      rfl
theorem buildingCyclicMonomial_mul
    (P : BasePrime) (r : Rank) (c d : ConstantExtension P r)
    (k l : ℕ) :
    (buildingConstantMatrix P r c *
        buildingCyclicGeneratorMatrix P r ^ k) *
      (buildingConstantMatrix P r d *
        buildingCyclicGeneratorMatrix P r ^ l) =
      buildingConstantMatrix P r
          (c * (constantFrobenius P r ^ k) d) *
        buildingCyclicGeneratorMatrix P r ^ (k + l) := by
  calc
    _ = buildingConstantMatrix P r c *
        (buildingCyclicGeneratorMatrix P r ^ k *
          buildingConstantMatrix P r d) *
            buildingCyclicGeneratorMatrix P r ^ l := by group
    _ = buildingConstantMatrix P r c *
        (buildingConstantMatrix P r ((constantFrobenius P r ^ k) d) *
          buildingCyclicGeneratorMatrix P r ^ k) *
            buildingCyclicGeneratorMatrix P r ^ l := by
              rw [buildingCyclicGeneratorMatrix_pow_mul_buildingConstantMatrix]
    _ = (buildingConstantMatrix P r c *
        buildingConstantMatrix P r ((constantFrobenius P r ^ k) d)) *
          (buildingCyclicGeneratorMatrix P r ^ k *
            buildingCyclicGeneratorMatrix P r ^ l) := by group
    _ = _ := by
      change (buildingConstantMatrixEmbedding P r c *
          buildingConstantMatrixEmbedding P r
            ((constantFrobenius P r ^ k) d)) *
          (buildingCyclicGeneratorMatrix P r ^ k *
            buildingCyclicGeneratorMatrix P r ^ l) = _
      rw [← map_mul, ← pow_add]
      rfl
theorem oneAddX_smul_buildingMatrix
    (P : BasePrime) (r : Rank)
    (M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (BuildingLocalField P)) :
    ((1 + RatFunc.X : FunctionField P) • M) =
      (1 + buildingLocalY P) • M := by
  rw [Algebra.smul_def, Algebra.smul_def]
  rw [IsScalarTower.algebraMap_apply
    (FunctionField P) (BuildingLocalField P)
    (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (BuildingLocalField P))]
  have hX :
      algebraMap (FunctionField P) (BuildingLocalField P) RatFunc.X =
        buildingLocalY P := functionFieldToBuildingLocalField_X P
  rw [map_add, map_one, hX]
theorem cyclicMonomial_rank_add
    (P : BasePrime) (r : Rank) (c : ConstantExtension P r) (n : ℕ) :
    cyclicMonomial P r c (r.matrixRank + n) =
      (1 + RatFunc.X : FunctionField P) • cyclicMonomial P r c n := by
  apply Subtype.ext
  change constantMatrix P r c *
      cyclicGeneratorMatrix P r ^ (r.matrixRank + n) =
    (CyclicAlgebra P r).val
      ((1 + RatFunc.X : FunctionField P) • cyclicMonomial P r c n)
  rw [cyclicGeneratorMatrix_pow_rank_add, Matrix.mul_smul]
  rw [map_smul]
  change onePlusY P r •
      (constantMatrix P r c * cyclicGeneratorMatrix P r ^ n) =
    (1 + RatFunc.X : FunctionField P) •
      (constantMatrix P r c * cyclicGeneratorMatrix P r ^ n)
  rw [onePlusY_eq_functionField_smul_one]
  simp only [Algebra.smul_def, map_add, map_one]
  congr 1
  rw [IsScalarTower.algebraMap_apply
    (FunctionField P) (SplittingFunctionField P r)
    (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r))]
  simp
theorem cyclicAlgebraToBuildingLinear_cyclicMonomial_mul
    (P : BasePrime) (r : Rank) (c d : ConstantExtension P r)
    (k l : ℕ) (hk : k < r.matrixRank) (hl : l < r.matrixRank) :
    cyclicAlgebraToBuildingLinear P r
        (cyclicMonomial P r c k * cyclicMonomial P r d l) =
      cyclicAlgebraToBuildingLinear P r (cyclicMonomial P r c k) *
        cyclicAlgebraToBuildingLinear P r (cyclicMonomial P r d l) := by
  let e : ConstantExtension P r :=
    c * (constantFrobenius P r ^ k) d
  rw [cyclicMonomial_mul]
  by_cases hsum : k + l < r.matrixRank
  · rw [cyclicAlgebraToBuildingLinear_cyclicMonomial P r e (k + l) hsum]
    rw [cyclicAlgebraToBuildingLinear_cyclicMonomial P r c k hk,
      cyclicAlgebraToBuildingLinear_cyclicMonomial P r d l hl]
    exact (buildingCyclicMonomial_mul P r c d k l).symm
  · have hrank : 0 < r.matrixRank :=
      lt_of_lt_of_le (by omega) (Rank.two_le_matrixRank r)
    let j := k + l - r.matrixRank
    have hj : j < r.matrixRank := by omega
    have hsumEq : k + l = r.matrixRank + j := by omega
    rw [hsumEq, cyclicMonomial_rank_add, map_smul,
      cyclicAlgebraToBuildingLinear_cyclicMonomial P r e j hj,
      oneAddX_smul_buildingMatrix]
    rw [cyclicAlgebraToBuildingLinear_cyclicMonomial P r c k hk,
      cyclicAlgebraToBuildingLinear_cyclicMonomial P r d l hl,
      buildingCyclicMonomial_mul]
    rw [hsumEq, buildingCyclicGeneratorMatrix_pow_rank_add,
      Matrix.mul_smul]
theorem functionFieldCyclicBasis_eq_cyclicMonomial
    (P : BasePrime) (r : Rank)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    functionFieldCyclicBasis P r p =
      cyclicMonomial P r (constantBasis P r p.1) p.2 := by
  apply Subtype.ext
  rw [functionFieldCyclicBasis_apply]
  rfl
noncomputable def cyclicAlgebraMappedMul
    (P : BasePrime) (r : Rank) :
    CyclicAlgebra P r →ₗ[FunctionField P]
      CyclicAlgebra P r →ₗ[FunctionField P]
        Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (BuildingLocalField P) :=
  LinearMap.mk₂ (FunctionField P)
    (fun x y => cyclicAlgebraToBuildingLinear P r (x * y))
    (by intro x y z; simp [add_mul])
    (by intro a x y; simp)
    (by intro x y z; simp [mul_add])
    (by intro a x y; simp)
noncomputable def cyclicAlgebraBuildingMul
    (P : BasePrime) (r : Rank) :
    CyclicAlgebra P r →ₗ[FunctionField P]
      CyclicAlgebra P r →ₗ[FunctionField P]
        Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (BuildingLocalField P) :=
  LinearMap.mk₂ (FunctionField P)
    (fun x y => cyclicAlgebraToBuildingLinear P r x *
      cyclicAlgebraToBuildingLinear P r y)
    (by intro x y z; simp [add_mul])
    (by intro a x y; simp)
    (by intro x y z; simp [mul_add])
    (by intro a x y; simp)
theorem cyclicAlgebraToBuildingLinear_map_mul
    (P : BasePrime) (r : Rank) (x y : CyclicAlgebra P r) :
    cyclicAlgebraToBuildingLinear P r (x * y) =
      cyclicAlgebraToBuildingLinear P r x *
        cyclicAlgebraToBuildingLinear P r y := by
  have hmaps : cyclicAlgebraMappedMul P r = cyclicAlgebraBuildingMul P r := by
    apply (functionFieldCyclicBasis P r).ext
    intro p
    apply (functionFieldCyclicBasis P r).ext
    intro q
    simp only [cyclicAlgebraMappedMul, cyclicAlgebraBuildingMul,
      LinearMap.mk₂_apply]
    rw [functionFieldCyclicBasis_eq_cyclicMonomial,
      functionFieldCyclicBasis_eq_cyclicMonomial]
    exact cyclicAlgebraToBuildingLinear_cyclicMonomial_mul P r
      (constantBasis P r p.1) (constantBasis P r q.1)
      p.2 q.2 p.2.isLt q.2.isLt
  exact DFunLike.congr_fun (DFunLike.congr_fun hmaps x) y
theorem cyclicMonomial_one
    (P : BasePrime) (r : Rank) :
    cyclicMonomial P r 1 0 = 1 := by
  apply Subtype.ext
  simp [← constantMatrixEmbedding_apply]
theorem cyclicAlgebraToBuildingLinear_map_one
    (P : BasePrime) (r : Rank) :
    cyclicAlgebraToBuildingLinear P r 1 = 1 := by
  rw [← cyclicMonomial_one P r]
  rw [cyclicAlgebraToBuildingLinear_cyclicMonomial P r 1 0
    (lt_of_lt_of_le (by omega) (Rank.two_le_matrixRank r))]
  simp [← buildingConstantMatrixEmbedding_apply]
noncomputable def cyclicAlgebraToBuilding
    (P : BasePrime) (r : Rank) :
    CyclicAlgebra P r →ₐ[FunctionField P]
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (BuildingLocalField P) where
  toFun := cyclicAlgebraToBuildingLinear P r
  map_zero' := (cyclicAlgebraToBuildingLinear P r).map_zero
  map_add' := (cyclicAlgebraToBuildingLinear P r).map_add
  map_one' := cyclicAlgebraToBuildingLinear_map_one P r
  map_mul' := cyclicAlgebraToBuildingLinear_map_mul P r
  commutes' a := by
    rw [Algebra.algebraMap_eq_smul_one,
      map_smul, cyclicAlgebraToBuildingLinear_map_one]
    rw [Algebra.smul_def, mul_one]
noncomputable def constantCyclicElement
    (P : BasePrime) (r : Rank) (c : ConstantExtension P r) :
    CyclicAlgebra P r :=
  ⟨constantMatrix P r c, constantMatrix_mem_cyclicAlgebra P r c⟩
noncomputable def cyclicGeneratorCyclicElement
    (P : BasePrime) (r : Rank) : CyclicAlgebra P r :=
  ⟨cyclicGeneratorMatrix P r,
    cyclicGeneratorMatrix_mem_cyclicAlgebra P r⟩
noncomputable def cyclicGeneratorInverseCyclicElement
    (P : BasePrime) (r : Rank) : CyclicAlgebra P r :=
  ⟨cyclicGeneratorInverseMatrix P r,
    cyclicGeneratorInverseMatrix_mem_cyclicAlgebra P r⟩
noncomputable def cartwrightStegerBCyclicElement
    (P : BasePrime) (r : Rank) : CyclicAlgebra P r :=
  ⟨cartwrightStegerBMatrix P r,
    cartwrightStegerBMatrix_mem_cyclicAlgebra P r⟩
noncomputable def cartwrightStegerGeneratorCyclicElement
    (P : BasePrime) (r : Rank) (u : ConstantProjectiveClass P r) :
    CyclicAlgebra P r :=
  constantCyclicElement P r (constantClassRepresentative P r u) *
    cartwrightStegerBCyclicElement P r *
      constantCyclicElement P r
        ((constantClassRepresentative P r u)⁻¹)
end QEC.Coding.HighDimensionalExpander.CartwrightSteger


