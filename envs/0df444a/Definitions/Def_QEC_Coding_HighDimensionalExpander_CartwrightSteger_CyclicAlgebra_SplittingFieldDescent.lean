-- Prove2me | Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_SplittingFieldDescent
-- name    : QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_SplittingFieldDescent
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T03:40:30.201163+00:00
-- url     : https://prove2.me/theorems/d685f5aa-06d4-417f-9c04-92927b314004
-- title:
--   Splitting Field Descent
-- statement:
--   Definitions and structural lemmas for Splitting Field Descent, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/SplittingFieldDescent.lean

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebraBasis
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Algebra_RatFuncCoefficientEquiv
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CongruenceLifting_residueTransvectionSpecial_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingCompactCyclicSemidirectHom_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingGeneratorNeighborAtEquiv_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingLatticeVertexMap_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerNormUnit_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrixHom_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrix_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicGenerator_mul_constantMatrix
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_exists_eq_algebraMap_of_constantFrobenius_eq
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_frobeniusPowerEquiv_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_functionFieldCyclicBasis_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexConstantGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexCyclicGeneratorGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_infinityConjugationCorrectionSum_bound_zero
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_infinityCyclicCoefficient_rank
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_infinityCyclicCoefficient_zero
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueBGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueConstantGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueXAdjoinRootEquiv_root
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueYAdjoinRootEquiv_root
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
import Theorems.Thm_RatFunc_denom_coefficientRingEquiv
import Theorems.Thm_RatFunc_num_coefficientRingEquiv
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.CongruenceLifting.residueTransvectionSpecial_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingCompactCyclicSemidirectHom_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingGeneratorNeighborAtEquiv_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingLatticeVertexMap_one
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerNormUnit_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantUnitMatrixHom_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantUnitMatrix_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.frobeniusPowerEquiv_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.functionFieldCyclicBasis_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexConstantGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexCyclicGeneratorGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.infinityConjugationCorrectionSum_bound_zero
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.infinityCyclicCoefficient_rank
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.infinityCyclicCoefficient_zero
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueBGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueConstantGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueXAdjoinRootEquiv_root
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueYAdjoinRootEquiv_root
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
noncomputable def splittingFunctionFieldFrobeniusRingEquiv
    (P : BasePrime) (r : Rank) :
    SplittingFunctionField P r ≃+* SplittingFunctionField P r :=
  RatFunc.coefficientRingEquiv (constantFrobenius P r).toRingEquiv
theorem splittingFunctionFieldFrobeniusRingEquiv_functionFieldEmbedding
    (P : BasePrime) (r : Rank) (x : FunctionField P) :
    splittingFunctionFieldFrobeniusRingEquiv P r
        (functionFieldEmbedding P r x) =
      functionFieldEmbedding P r x := by
  let lhs : FunctionField P →+* SplittingFunctionField P r :=
    (splittingFunctionFieldFrobeniusRingEquiv P r).toRingHom.comp
      (functionFieldEmbedding P r)
  have heq : lhs = functionFieldEmbedding P r := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors (PolynomialRing P))
      (RingHom.ext fun a => ?_)
    simp only [lhs, RingHom.coe_comp, Function.comp_apply]
    rw [show algebraMap (PolynomialRing P) (FunctionField P) a =
        algebraMap (PolynomialRing P) (FunctionField P) a /
          algebraMap (PolynomialRing P) (FunctionField P) 1 by simp]
    unfold functionFieldEmbedding
    dsimp only
    rw [RatFunc.coe_mapRingHom_eq_coe_map, RatFunc.map_apply_div]
    change RatFunc.coefficientRingEquiv
        (constantFrobenius P r).toRingEquiv _ = _
    rw [RatFunc.coefficientRingEquiv_apply_div]
    simp only [map_one]
    rw [div_one, div_one]
    congr 1
    ext i
    simp
  exact DFunLike.congr_fun heq x
noncomputable def splittingFunctionFieldFrobenius
    (P : BasePrime) (r : Rank) :
    SplittingFunctionField P r ≃ₐ[FunctionField P]
      SplittingFunctionField P r :=
  { splittingFunctionFieldFrobeniusRingEquiv P r with
    commutes' := splittingFunctionFieldFrobeniusRingEquiv_functionFieldEmbedding
      P r }
theorem exists_eq_functionFieldEmbedding_of_frobenius_eq
    (P : BasePrime) (r : Rank) (x : SplittingFunctionField P r)
    (hx : splittingFunctionFieldFrobenius P r x = x) :
    ∃ a : FunctionField P, functionFieldEmbedding P r a = x := by
  have hnumMap := RatFunc.num_coefficientRingEquiv
    (constantFrobenius P r).toRingEquiv x
  have hdenMap := RatFunc.denom_coefficientRingEquiv
    (constantFrobenius P r).toRingEquiv x
  change RatFunc.coefficientRingEquiv
      (constantFrobenius P r).toRingEquiv x = x at hx
  rw [hx] at hnumMap hdenMap
  have hnumCoeff (i : ℕ) :
      constantFrobenius P r (x.num.coeff i) = x.num.coeff i := by
    have h := congrArg
      (fun p : Polynomial (ConstantExtension P r) ↦ p.coeff i) hnumMap
    simpa using h.symm
  have hdenCoeff (i : ℕ) :
      constantFrobenius P r (x.denom.coeff i) = x.denom.coeff i := by
    have h := congrArg
      (fun p : Polynomial (ConstantExtension P r) ↦ p.coeff i) hdenMap
    simpa using h.symm
  choose pn hpn using fun i =>
    exists_eq_algebraMap_of_constantFrobenius_eq P r
      (x.num.coeff i) (hnumCoeff i)
  choose qn hqn using fun i =>
    exists_eq_algebraMap_of_constantFrobenius_eq P r
      (x.denom.coeff i) (hdenCoeff i)
  have hnumLifts : x.num ∈ Polynomial.lifts
      (algebraMap (BaseField P) (ConstantExtension P r)) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    exact ⟨pn i, hpn i⟩
  have hdenLifts : x.denom ∈ Polynomial.lifts
      (algebraMap (BaseField P) (ConstantExtension P r)) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    exact ⟨qn i, hqn i⟩
  obtain ⟨p, hp, -⟩ := Polynomial.exists_support_eq_of_mem_lifts hnumLifts
  obtain ⟨q, hq, -⟩ := Polynomial.exists_support_eq_of_mem_lifts hdenLifts
  refine ⟨algebraMap (PolynomialRing P) (FunctionField P) p /
      algebraMap (PolynomialRing P) (FunctionField P) q, ?_⟩
  rw [show x = algebraMap (Polynomial (ConstantExtension P r))
        (SplittingFunctionField P r) x.num /
      algebraMap (Polynomial (ConstantExtension P r))
        (SplittingFunctionField P r) x.denom by
    exact x.num_div_denom.symm]
  unfold functionFieldEmbedding
  dsimp only
  rw [RatFunc.coe_mapRingHom_eq_coe_map, RatFunc.map_apply_div]
  change Polynomial.mapRingHom
      (algebraMap (BaseField P) (ConstantExtension P r)) p = x.num at hp
  change Polynomial.mapRingHom
      (algebraMap (BaseField P) (ConstantExtension P r)) q = x.denom at hq
  rw [hp, hq]
theorem splittingFunctionFieldFrobenius_mapMatrix_constantMatrix
    (P : BasePrime) (r : Rank) (c : ConstantExtension P r) :
    (splittingFunctionFieldFrobenius P r).toRingHom.mapMatrix
        (constantMatrix P r c) =
      constantMatrix P r (constantFrobenius P r c) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [constantMatrix, splittingFunctionFieldFrobenius,
      splittingFunctionFieldFrobeniusRingEquiv]
    congr 2
    have hc : Function.Commute (constantFrobenius P r)
        (constantFrobenius P r).symm := fun x => by simp
    exact hc.iterate_right i.val c
  · simp [constantMatrix, hij]
theorem splittingFunctionFieldFrobenius_mapMatrix_cyclicGenerator
    (P : BasePrime) (r : Rank) :
    (splittingFunctionFieldFrobenius P r).toRingHom.mapMatrix
        (cyclicGeneratorMatrix P r) =
      cyclicGeneratorMatrix P r := by
  cases r with
  | three =>
      ext i j
      change splittingFunctionFieldFrobenius P .three
          (cyclicGeneratorMatrix P .three i j) =
        cyclicGeneratorMatrix P .three i j
      fin_cases i <;> fin_cases j <;>
        simp [cyclicGeneratorMatrix, onePlusY,
          splittingFunctionFieldFrobenius,
          splittingFunctionFieldFrobeniusRingEquiv]
  | four =>
      ext i j
      change splittingFunctionFieldFrobenius P .four
          (cyclicGeneratorMatrix P .four i j) =
        cyclicGeneratorMatrix P .four i j
      fin_cases i <;> fin_cases j <;>
        simp [cyclicGeneratorMatrix, onePlusY,
          splittingFunctionFieldFrobenius,
          splittingFunctionFieldFrobeniusRingEquiv]
theorem splittingFunctionFieldFrobenius_mapMatrix_cyclicGeneratorInverse
    (P : BasePrime) (r : Rank) :
    (splittingFunctionFieldFrobenius P r).toRingHom.mapMatrix
        (cyclicGeneratorInverseMatrix P r) =
      cyclicGeneratorInverseMatrix P r := by
  let f : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r) →+*
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r) :=
    (splittingFunctionFieldFrobenius P r).toRingHom.mapMatrix
  have hright := congrArg f (cyclicGenerator_mul_inverse P r)
  have hleft := congrArg f (cyclicGenerator_inverse_mul P r)
  rw [map_mul, map_one,
    splittingFunctionFieldFrobenius_mapMatrix_cyclicGenerator] at hright hleft
  calc
    f (cyclicGeneratorInverseMatrix P r) =
        1 * f (cyclicGeneratorInverseMatrix P r) := by rw [one_mul]
    _ = (cyclicGeneratorInverseMatrix P r * cyclicGeneratorMatrix P r) *
          f (cyclicGeneratorInverseMatrix P r) := by
      rw [cyclicGenerator_inverse_mul]
    _ = cyclicGeneratorInverseMatrix P r *
          (cyclicGeneratorMatrix P r * f (cyclicGeneratorInverseMatrix P r)) := by
      rw [mul_assoc]
    _ = cyclicGeneratorInverseMatrix P r := by rw [hright, mul_one]
theorem splittingFunctionFieldFrobenius_mapMatrix_functionFieldScalar
    (P : BasePrime) (r : Rank) (a : FunctionField P) :
    (splittingFunctionFieldFrobenius P r).toRingHom.mapMatrix
        (a • (1 : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (SplittingFunctionField P r))) =
      a • (1 : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r)) := by
  ext i j
  by_cases hij : i = j
  · subst j
    have hai : (a • (1 : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r))) i i = functionFieldEmbedding P r a := by
      simp only [Algebra.smul_def, Matrix.mul_apply, Matrix.one_apply,
        mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true]
      rw [IsScalarTower.algebraMap_apply
        (FunctionField P) (SplittingFunctionField P r)
        (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (SplittingFunctionField P r))]
      rw [Matrix.algebraMap_matrix_apply, if_pos rfl]
      rfl
    change splittingFunctionFieldFrobenius P r
        ((a • (1 : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (SplittingFunctionField P r))) i i) = _
    rw [hai]
    exact splittingFunctionFieldFrobeniusRingEquiv_functionFieldEmbedding P r a
  · simp [hij]
theorem splittingFunctionFieldFrobenius_mapMatrix_eq_cyclicGenerator_conj
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r) :
    (splittingFunctionFieldFrobenius P r).toRingHom.mapMatrix
        (x : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (SplittingFunctionField P r)) =
      cyclicGeneratorMatrix P r * (x : Matrix (Fin r.matrixRank)
          (Fin r.matrixRank) (SplittingFunctionField P r)) *
        cyclicGeneratorInverseMatrix P r := by
  let f : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r) →+*
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r) :=
    (splittingFunctionFieldFrobenius P r).toRingHom.mapMatrix
  apply Algebra.adjoin_induction
    (R := FunctionField P)
    (s := Set.range (constantMatrix P r) ∪
      {cyclicGeneratorMatrix P r, cyclicGeneratorInverseMatrix P r})
    (p := fun M _ => f M = cyclicGeneratorMatrix P r * M *
      cyclicGeneratorInverseMatrix P r)
  · intro M hM
    rcases hM with hM | hM
    · obtain ⟨c, rfl⟩ := hM
      rw [splittingFunctionFieldFrobenius_mapMatrix_constantMatrix,
        cyclicGenerator_mul_constantMatrix, mul_assoc,
        cyclicGenerator_mul_inverse, mul_one]
    · rcases hM with (rfl | hM)
      · rw [splittingFunctionFieldFrobenius_mapMatrix_cyclicGenerator,
          mul_assoc, cyclicGenerator_mul_inverse, mul_one]
      · rw [Set.mem_singleton_iff] at hM
        subst M
        rw [splittingFunctionFieldFrobenius_mapMatrix_cyclicGeneratorInverse,
          cyclicGenerator_mul_inverse, one_mul]
  · intro a
    rw [Algebra.algebraMap_eq_smul_one]
    change f (a • (1 : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r))) = _
    change (splittingFunctionFieldFrobenius P r).toRingHom.mapMatrix
      (a • (1 : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r))) = _
    rw [splittingFunctionFieldFrobenius_mapMatrix_functionFieldScalar]
    calc
      a • (1 : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (SplittingFunctionField P r)) =
        a • (cyclicGeneratorMatrix P r *
          cyclicGeneratorInverseMatrix P r) := by
            rw [cyclicGenerator_mul_inverse]
      _ = cyclicGeneratorMatrix P r *
          (a • (1 : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (SplittingFunctionField P r))) *
            cyclicGeneratorInverseMatrix P r := by
        simp only [smul_mul_assoc, mul_smul_comm]
        rw [mul_one]
  · intro M N _ _ hM hN
    rw [map_add, hM, hN, mul_add, add_mul]
  · intro M N _ _ hM hN
    rw [map_mul, hM, hN]
    calc
      (cyclicGeneratorMatrix P r * M * cyclicGeneratorInverseMatrix P r) *
          (cyclicGeneratorMatrix P r * N * cyclicGeneratorInverseMatrix P r) =
        cyclicGeneratorMatrix P r * M *
          (cyclicGeneratorInverseMatrix P r * cyclicGeneratorMatrix P r) *
            N * cyclicGeneratorInverseMatrix P r := by noncomm_ring
      _ = cyclicGeneratorMatrix P r * (M * N) *
          cyclicGeneratorInverseMatrix P r := by
        rw [cyclicGenerator_inverse_mul]
        simp [mul_assoc]
  · exact x.property
theorem splittingFunctionFieldFrobenius_cyclicAlgebra_det
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r) :
    splittingFunctionFieldFrobenius P r
        (Matrix.det (x : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (SplittingFunctionField P r))) =
      Matrix.det (x : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r)) := by
  change (splittingFunctionFieldFrobenius P r).toRingHom
      (Matrix.det (x : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r))) = _
  rw [RingHom.map_det,
    splittingFunctionFieldFrobenius_mapMatrix_eq_cyclicGenerator_conj,
    Matrix.det_mul, Matrix.det_mul]
  have hdet : Matrix.det (cyclicGeneratorMatrix P r) *
      Matrix.det (cyclicGeneratorInverseMatrix P r) = 1 := by
    rw [← Matrix.det_mul, cyclicGenerator_mul_inverse, Matrix.det_one]
  calc
    Matrix.det (cyclicGeneratorMatrix P r) *
          Matrix.det (x : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (SplittingFunctionField P r)) *
        Matrix.det (cyclicGeneratorInverseMatrix P r) =
      Matrix.det (x : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r)) *
        (Matrix.det (cyclicGeneratorMatrix P r) *
          Matrix.det (cyclicGeneratorInverseMatrix P r)) := by ring
    _ = _ := by rw [hdet, mul_one]
noncomputable def cyclicAlgebraReducedNormValue
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r) : FunctionField P :=
  Classical.choose (exists_eq_functionFieldEmbedding_of_frobenius_eq P r
    (Matrix.det (x : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r)))
    (splittingFunctionFieldFrobenius_cyclicAlgebra_det P r x))
theorem functionFieldEmbedding_cyclicAlgebraReducedNormValue
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r) :
    functionFieldEmbedding P r (cyclicAlgebraReducedNormValue P r x) =
      Matrix.det (x : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r)) :=
  Classical.choose_spec (exists_eq_functionFieldEmbedding_of_frobenius_eq P r
    (Matrix.det (x : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r)))
    (splittingFunctionFieldFrobenius_cyclicAlgebra_det P r x))
@[simp] theorem cyclicAlgebraReducedNormValue_one
    (P : BasePrime) (r : Rank) :
    cyclicAlgebraReducedNormValue P r 1 = 1 := by
  apply (functionFieldEmbedding P r).injective
  rw [functionFieldEmbedding_cyclicAlgebraReducedNormValue]
  simp
theorem cyclicAlgebraReducedNormValue_mul
    (P : BasePrime) (r : Rank) (x y : CyclicAlgebra P r) :
    cyclicAlgebraReducedNormValue P r (x * y) =
      cyclicAlgebraReducedNormValue P r x *
        cyclicAlgebraReducedNormValue P r y := by
  apply (functionFieldEmbedding P r).injective
  rw [map_mul]
  rw [functionFieldEmbedding_cyclicAlgebraReducedNormValue,
    functionFieldEmbedding_cyclicAlgebraReducedNormValue,
    functionFieldEmbedding_cyclicAlgebraReducedNormValue]
  exact Matrix.det_mul _ _
noncomputable def cyclicAlgebraReducedNormMonoidHom
    (P : BasePrime) (r : Rank) :
    CyclicAlgebra P r →* FunctionField P where
  toFun := cyclicAlgebraReducedNormValue P r
  map_one' := cyclicAlgebraReducedNormValue_one P r
  map_mul' := cyclicAlgebraReducedNormValue_mul P r
noncomputable def cyclicAlgebraReducedNorm
    (P : BasePrime) (r : Rank) :
    (CyclicAlgebra P r)ˣ →* (FunctionField P)ˣ :=
  Units.map (cyclicAlgebraReducedNormMonoidHom P r)
end QEC.Coding.HighDimensionalExpander.CartwrightSteger


