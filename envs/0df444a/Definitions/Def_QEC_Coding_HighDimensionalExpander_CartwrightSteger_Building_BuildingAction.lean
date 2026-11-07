-- Prove2me | Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingAction
-- name    : QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingAction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T12:50:21.122009+00:00
-- url     : https://prove2.me/theorems/e0a3ab37-81ca-4a51-87a1-06dfc32c6183
-- title:
--   Building Action
-- statement:
--   Definitions and structural lemmas for Building Action, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingAction.lean

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Reduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_FrobeniusCharpoly
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_BuildingAdjacency
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CongruenceLifting_residueTransvectionSpecial_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Rank_two_le_matrixRank
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerNormUnit_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrix_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_exists_eq_algebraMap_of_map_frobeniusDifferenceRange_le
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_frobeniusGL_charpoly
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_frobeniusGL_pow_matrixRank
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_frobeniusPowerEquiv_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexConstantGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexCyclicGeneratorGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_natCard_constantProjectiveClass
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_range_toLin_constant_conjugate_one_sub_frobeniusGL_inv
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_range_toLin_mul_generalLinear
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueBGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueConstantGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueXAdjoinRootEquiv_root
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueYAdjoinRootEquiv_root
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankFour_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankFour_three
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankFour_two
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankThree_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankThree_two
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_MatrixOrderLowerBound_add
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coe_uniformizerUnit
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coloredAdjacencyDegree_rankFour_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coloredAdjacencyDegree_rankThree_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_diagonalGeneralLinear_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_dominantCoweight_eq_fundamental_one_of_sum_eq_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_dominantDoubleCoset_fundamental
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_integerEmbedding_injective
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_integralGeneralLinearToLocal_inv_orderLowerBound
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_left_mul_mem_dominantDoubleCoset
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_localUnitOrder_mul
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_mk_mem_dominantDoubleCoset
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_mk_powerSeriesGeneralLinearToLocal_mem_maximalCompact
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_powerSeriesGeneralLinearToInteger_inverse
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_powerSeriesReductionGL_constantGeneralLinearLift
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_powerSeries_integer_local_triangle
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_projective_mk_mem_maximalCompact_iff_integral
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFourFundamentalHeckeAlgEquiv_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFourSecondCompoundGeneralLinear_inv_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankThreeFundamentalHeckeAlgEquiv_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_right_mul_mem_dominantDoubleCoset
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_smithDominantCoweight_exponent_sum
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_smithExponent_sum_eq_det_localUnitOrder_of_orderLowerBound_zero
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.CongruenceLifting.residueTransvectionSpecial_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerNormUnit_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantUnitMatrix_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.frobeniusPowerEquiv_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexConstantGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexCyclicGeneratorGL_coe
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


set_option autoImplicit false
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
noncomputable def buildingRootIdeal (P : BasePrime) :
    Ideal (BuildingIntegerRing P) :=
  Ideal.span {PowerSeries.X}
noncomputable def buildingRootPolynomial
    (P : BasePrime) (r : Rank) :
    Polynomial (BuildingIntegerRing P) :=
  Polynomial.X ^ r.matrixRank -
    Polynomial.C (1 + PowerSeries.X)
theorem buildingRootPolynomial_monic
    (P : BasePrime) (r : Rank) :
    (buildingRootPolynomial P r).Monic := by
  exact Polynomial.monic_X_pow_sub_C (1 + PowerSeries.X)
    (by cases r <;> simp [Rank.matrixRank])
theorem buildingRootPolynomial_eval_one_mem
    (P : BasePrime) (r : Rank) :
    (buildingRootPolynomial P r).eval 1 ∈ buildingRootIdeal P := by
  have hx : PowerSeries.X ∈ buildingRootIdeal P :=
    Ideal.subset_span (Set.mem_singleton PowerSeries.X)
  simpa [buildingRootPolynomial] using (buildingRootIdeal P).neg_mem hx
theorem buildingRankCast_ne_zero
    (P : BasePrime) (r : Rank) :
    (r.matrixRank : BaseField P) ≠ 0 := by
  change (r.matrixRank : ZMod P.q) ≠ 0
  intro hzero
  have hdiv : P.q ∣ r.matrixRank :=
    (ZMod.natCast_eq_zero_iff r.matrixRank P.q).mp hzero
  exact (Nat.not_dvd_of_pos_of_lt
    (lt_of_lt_of_le (by norm_num) (Rank.two_le_matrixRank r))
    (lt_of_le_of_lt (by cases r <;> simp [Rank.matrixRank]) P.five_le)) hdiv
theorem buildingRootPolynomial_derivative_eval_one_isUnit
    (P : BasePrime) (r : Rank) :
    IsUnit
      ((buildingRootPolynomial P r).derivative.eval 1) := by
  have heq :
      (buildingRootPolynomial P r).derivative.eval 1 =
        (r.matrixRank : BuildingIntegerRing P) := by
    rw [buildingRootPolynomial, Polynomial.derivative_sub,
      Polynomial.derivative_X_pow, Polynomial.derivative_C, sub_zero]
    simp
  rw [heq]
  rw [PowerSeries.isUnit_iff_constantCoeff]
  rw [isUnit_iff_ne_zero]
  simpa using buildingRankCast_ne_zero P r
theorem buildingRootPolynomial_derivative_quotient_isUnit
    (P : BasePrime) (r : Rank) :
    IsUnit
      (Ideal.Quotient.mk (buildingRootIdeal P)
        ((buildingRootPolynomial P r).derivative.eval 1)) :=
  (buildingRootPolynomial_derivative_eval_one_isUnit P r).map _
theorem exists_buildingOnePlusYRoot
    (P : BasePrime) (r : Rank) :
    ∃ a : BuildingIntegerRing P,
      (buildingRootPolynomial P r).IsRoot a ∧
        a - 1 ∈ buildingRootIdeal P := by
  letI : HenselianRing (BuildingIntegerRing P) (buildingRootIdeal P) := by
    rw [buildingRootIdeal]
    infer_instance
  exact HenselianRing.is_henselian
      (buildingRootPolynomial P r)
      (buildingRootPolynomial_monic P r)
      1
      (buildingRootPolynomial_eval_one_mem P r)
      (buildingRootPolynomial_derivative_quotient_isUnit P r)
noncomputable def buildingOnePlusYRoot
    (P : BasePrime) (r : Rank) : BuildingIntegerRing P :=
  Classical.choose (exists_buildingOnePlusYRoot P r)
theorem buildingOnePlusYRoot_isRoot
    (P : BasePrime) (r : Rank) :
    (buildingRootPolynomial P r).IsRoot
      (buildingOnePlusYRoot P r) :=
  (Classical.choose_spec (exists_buildingOnePlusYRoot P r)).1
theorem buildingOnePlusYRoot_pow_matrixRank
    (P : BasePrime) (r : Rank) :
    buildingOnePlusYRoot P r ^ r.matrixRank =
      1 + PowerSeries.X := by
  have h := buildingOnePlusYRoot_isRoot P r
  rw [Polynomial.IsRoot, buildingRootPolynomial,
    Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C] at h
  exact sub_eq_zero.mp h
theorem buildingOnePlusYRoot_isUnit
    (P : BasePrime) (r : Rank) :
    IsUnit (buildingOnePlusYRoot P r) := by
  rw [← isUnit_pow_iff
    (by cases r <;> norm_num [Rank.matrixRank] : r.matrixRank ≠ 0)]
  rw [buildingOnePlusYRoot_pow_matrixRank]
  rw [PowerSeries.isUnit_iff_constantCoeff]
  simp
noncomputable def buildingOnePlusYRootUnit
    (P : BasePrime) (r : Rank) : (BuildingIntegerRing P)ˣ :=
  (buildingOnePlusYRoot_isUnit P r).unit
@[simp] theorem buildingOnePlusYRootUnit_coe
    (P : BasePrime) (r : Rank) :
    (buildingOnePlusYRootUnit P r : BuildingIntegerRing P) =
      buildingOnePlusYRoot P r :=
  IsUnit.unit_spec (buildingOnePlusYRoot_isUnit P r)
@[simp]
theorem buildingOnePlusYRoot_constantCoeff
    (P : BasePrime) (r : Rank) :
    PowerSeries.constantCoeff (buildingOnePlusYRoot P r) = 1 := by
  have hmem :=
    (Classical.choose_spec (exists_buildingOnePlusYRoot P r)).2
  change buildingOnePlusYRoot P r - 1 ∈
    Ideal.span ({PowerSeries.X} : Set (BuildingIntegerRing P)) at hmem
  rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff] at hmem
  exact sub_eq_zero.mp (by simpa using hmem)
noncomputable def buildingOnePlusYRootField
    (P : BasePrime) (r : Rank) : BuildingLocalField P :=
  (buildingOnePlusYRoot P r : BuildingLocalField P)
noncomputable def buildingLocalY (P : BasePrime) : BuildingLocalField P :=
  ((PowerSeries.X : BuildingIntegerRing P) : BuildingLocalField P)
theorem buildingOnePlusYRootField_pow_matrixRank
    (P : BasePrime) (r : Rank) :
    buildingOnePlusYRootField P r ^ r.matrixRank =
      1 + buildingLocalY P := by
  rw [buildingOnePlusYRootField, buildingLocalY,
    ← PowerSeries.coe_pow, buildingOnePlusYRoot_pow_matrixRank]
  simp
theorem one_add_buildingLocalY_ne_zero
    (P : BasePrime) : 1 + buildingLocalY P ≠ 0 := by
  intro hzero
  have hcoeff := congrArg
    (fun f : BuildingLocalField P => f.coeff 0) hzero
  simp [buildingLocalY] at hcoeff
theorem buildingOnePlusYRootField_ne_zero
    (P : BasePrime) (r : Rank) :
    buildingOnePlusYRootField P r ≠ 0 := by
  intro hzero
  have hpow := buildingOnePlusYRootField_pow_matrixRank P r
  rw [hzero, zero_pow (by cases r <;> simp [Rank.matrixRank])] at hpow
  exact one_add_buildingLocalY_ne_zero P hpow.symm
noncomputable def buildingFrobeniusMatrix
    (P : BasePrime) (r : Rank) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BuildingLocalField P) :=
  (frobeniusGL P r :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BaseField P)).map
    (algebraMap (BaseField P) (BuildingLocalField P))
noncomputable def buildingFrobeniusGL
    (P : BasePrime) (r : Rank) :
    Matrix.GeneralLinearGroup (Fin r.matrixRank) (BuildingLocalField P) :=
  Matrix.GeneralLinearGroup.map
    (algebraMap (BaseField P) (BuildingLocalField P))
    (frobeniusGL P r)
@[simp] theorem buildingFrobeniusGL_coe
    (P : BasePrime) (r : Rank) :
    (buildingFrobeniusGL P r :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BuildingLocalField P)) =
      buildingFrobeniusMatrix P r :=
  rfl
theorem buildingFrobeniusMatrix_pow_matrixRank
    (P : BasePrime) (r : Rank) :
    buildingFrobeniusMatrix P r ^ r.matrixRank = 1 := by
  have hbase :
      (frobeniusGL P r :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BaseField P)) ^
          r.matrixRank = 1 := by
    rw [← Units.val_pow_eq_pow_val]
    exact congrArg Units.val (frobeniusGL_pow_matrixRank P r)
  rw [buildingFrobeniusMatrix, ← Matrix.map_pow, hbase]
  simp
theorem buildingFrobeniusMatrix_charpoly
    (P : BasePrime) (r : Rank) :
    (buildingFrobeniusMatrix P r).charpoly =
      Polynomial.X ^ r.matrixRank - 1 := by
  rw [buildingFrobeniusMatrix, Matrix.charpoly_map,
    frobeniusGL_charpoly]
  simp
noncomputable def buildingConstantMatrix
    (P : BasePrime) (r : Rank) (c : ConstantExtension P r) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BuildingLocalField P) :=
  (constantRegularMatrix P r c).map
    (algebraMap (BaseField P) (BuildingLocalField P))
noncomputable def buildingCyclicGeneratorMatrix
    (P : BasePrime) (r : Rank) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BuildingLocalField P) :=
  buildingOnePlusYRootField P r • buildingFrobeniusMatrix P r
noncomputable def buildingCyclicGeneratorGL
    (P : BasePrime) (r : Rank) :
    Matrix.GeneralLinearGroup (Fin r.matrixRank) (BuildingLocalField P) :=
  Matrix.GeneralLinearGroup.scalar (Fin r.matrixRank)
      (Units.mk0 (buildingOnePlusYRootField P r)
        (buildingOnePlusYRootField_ne_zero P r)) *
    buildingFrobeniusGL P r
noncomputable def buildingCyclicGeneratorIntegralGL
    (P : BasePrime) (r : Rank) :
    Matrix.GeneralLinearGroup (Fin r.matrixRank) (BuildingIntegerRing P) :=
  Matrix.GeneralLinearGroup.scalar (Fin r.matrixRank)
      (buildingOnePlusYRootUnit P r) *
    SphericalHecke.constantGeneralLinearLift (BaseField P) r.matrixRank
      (frobeniusGL P r)
theorem buildingCyclicGeneratorIntegralGL_toLocal
    (P : BasePrime) (r : Rank) :
    SphericalHecke.powerSeriesGeneralLinearToLocal (BaseField P) r.matrixRank
        (buildingCyclicGeneratorIntegralGL P r) =
      buildingCyclicGeneratorGL P r := by
  have hfrob :
      SphericalHecke.powerSeriesGeneralLinearToLocal
          (BaseField P) r.matrixRank
          (SphericalHecke.constantGeneralLinearLift
            (BaseField P) r.matrixRank (frobeniusGL P r)) =
        buildingFrobeniusGL P r := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    change HahnSeries.ofPowerSeries Int (BaseField P)
        (PowerSeries.C ((frobeniusGL P r) i j)) =
      algebraMap (BaseField P) (BuildingLocalField P)
        ((frobeniusGL P r) i j)
    rw [HahnSeries.ofPowerSeries_C,
      LaurentSeries.algebraMap_apply]
  rw [buildingCyclicGeneratorIntegralGL,
    SphericalHecke.powerSeriesGeneralLinearToLocal, map_mul]
  change Matrix.GeneralLinearGroup.map _
      (Matrix.GeneralLinearGroup.scalar (Fin r.matrixRank)
        (buildingOnePlusYRootUnit P r)) *
      SphericalHecke.powerSeriesGeneralLinearToLocal
        (BaseField P) r.matrixRank
        (SphericalHecke.constantGeneralLinearLift
          (BaseField P) r.matrixRank (frobeniusGL P r)) = _
  rw [hfrob]
  rw [buildingCyclicGeneratorGL]
  congr 1
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  by_cases hij : i = j
  · subst j
    simp [SphericalHecke.integerEmbedding, buildingOnePlusYRootField]
  · simp [SphericalHecke.integerEmbedding, hij]
theorem powerSeriesReductionGL_buildingCyclicGeneratorIntegralGL
    (P : BasePrime) (r : Rank) :
    SphericalHecke.powerSeriesReductionGL (BaseField P) r.matrixRank
        (buildingCyclicGeneratorIntegralGL P r) =
      frobeniusGL P r := by
  rw [buildingCyclicGeneratorIntegralGL, map_mul,
    SphericalHecke.powerSeriesReductionGL_constantGeneralLinearLift]
  change Matrix.GeneralLinearGroup.map PowerSeries.constantCoeff
      (Matrix.GeneralLinearGroup.scalar (Fin r.matrixRank)
        (buildingOnePlusYRootUnit P r)) * frobeniusGL P r = _
  have hscalar : Matrix.GeneralLinearGroup.map PowerSeries.constantCoeff
      (Matrix.GeneralLinearGroup.scalar (Fin r.matrixRank)
        (buildingOnePlusYRootUnit P r)) = 1 := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    by_cases hij : i = j
    · subst j
      simp [buildingOnePlusYRootUnit_coe]
    · simp [hij]
  rw [hscalar, one_mul]
@[simp] theorem buildingCyclicGeneratorGL_coe
    (P : BasePrime) (r : Rank) :
    (buildingCyclicGeneratorGL P r :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (BuildingLocalField P)) =
      buildingCyclicGeneratorMatrix P r := by
  rw [buildingCyclicGeneratorGL, buildingCyclicGeneratorMatrix,
    Units.val_mul, buildingFrobeniusGL_coe]
  change Matrix.scalar (Fin r.matrixRank)
      (buildingOnePlusYRootField P r) * buildingFrobeniusMatrix P r = _
  rw [Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
theorem buildingCyclicGeneratorMatrix_pow_matrixRank
    (P : BasePrime) (r : Rank) :
    buildingCyclicGeneratorMatrix P r ^ r.matrixRank =
      (1 + buildingLocalY P) •
        (1 : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (BuildingLocalField P)) := by
  rw [buildingCyclicGeneratorMatrix, smul_pow,
    buildingFrobeniusMatrix_pow_matrixRank,
    buildingOnePlusYRootField_pow_matrixRank]
theorem buildingLocalY_ne_zero (P : BasePrime) :
    buildingLocalY P ≠ 0 := by
  intro hzero
  have hcoeff := congrArg
    (fun f : BuildingLocalField P => f.coeff 1) hzero
  simp [buildingLocalY] at hcoeff
noncomputable def buildingBMatrix
    (P : BasePrime) (r : Rank) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BuildingLocalField P) :=
  1 - ((buildingCyclicGeneratorGL P r)⁻¹ :
    Matrix.GeneralLinearGroup (Fin r.matrixRank) (BuildingLocalField P))
noncomputable def buildingBIntegralMatrix
    (P : BasePrime) (r : Rank) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BuildingIntegerRing P) :=
  1 - ((buildingCyclicGeneratorIntegralGL P r)⁻¹ :
    Matrix.GeneralLinearGroup (Fin r.matrixRank) (BuildingIntegerRing P))
theorem buildingBIntegralMatrix_toLocal
    (P : BasePrime) (r : Rank) :
    (SphericalHecke.integerEmbedding (BaseField P)).mapMatrix
        (buildingBIntegralMatrix P r) =
      buildingBMatrix P r := by
  rw [buildingBIntegralMatrix, buildingBMatrix, map_sub, map_one]
  change (1 : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (BuildingLocalField P)) -
      (((SphericalHecke.powerSeriesGeneralLinearToLocal
        (BaseField P) r.matrixRank
        (buildingCyclicGeneratorIntegralGL P r))⁻¹ :
          Matrix.GeneralLinearGroup (Fin r.matrixRank)
            (BuildingLocalField P)) :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (BuildingLocalField P)) = _
  rw [buildingCyclicGeneratorIntegralGL_toLocal]
theorem buildingBIntegralMatrix_reduction
    (P : BasePrime) (r : Rank) :
    (buildingBIntegralMatrix P r).map PowerSeries.constantCoeff =
      1 - ((frobeniusGL P r)⁻¹ :
        Matrix.GeneralLinearGroup (Fin r.matrixRank) (BaseField P)) := by
  rw [buildingBIntegralMatrix,
    Matrix.map_sub PowerSeries.constantCoeff (by intros; simp),
    Matrix.map_one PowerSeries.constantCoeff (by simp) (by simp)]
  change (1 : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (BaseField P)) -
      (((SphericalHecke.powerSeriesReductionGL
        (BaseField P) r.matrixRank
        (buildingCyclicGeneratorIntegralGL P r))⁻¹ :
          Matrix.GeneralLinearGroup (Fin r.matrixRank) (BaseField P)) :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BaseField P)) = _
  rw [powerSeriesReductionGL_buildingCyclicGeneratorIntegralGL]
theorem buildingBMatrix_isUnit
    (P : BasePrime) (r : Rank) :
    IsUnit (buildingBMatrix P r) := by
  apply isUnit_one_sub_inv_of_pow_eq_one_add_smul_one
    (buildingCyclicGeneratorGL P r) r.matrixRank
    (buildingLocalY P) (buildingLocalY_ne_zero P)
  simpa only [buildingCyclicGeneratorGL_coe] using
    buildingCyclicGeneratorMatrix_pow_matrixRank P r
noncomputable def buildingBGL
    (P : BasePrime) (r : Rank) :
    Matrix.GeneralLinearGroup (Fin r.matrixRank) (BuildingLocalField P) :=
  (buildingBMatrix_isUnit P r).unit
@[simp] theorem buildingBGL_coe
    (P : BasePrime) (r : Rank) :
    (buildingBGL P r :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BuildingLocalField P)) =
      buildingBMatrix P r :=
  IsUnit.unit_spec (buildingBMatrix_isUnit P r)
theorem buildingBMatrix_det (P : BasePrime) (r : Rank) :
    Matrix.det (buildingBMatrix P r) =
      buildingLocalY P / (1 + buildingLocalY P) := by
  let F : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (BuildingLocalField P) := buildingFrobeniusMatrix P r
  let Fg : Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (BuildingLocalField P) := buildingFrobeniusGL P r
  let a : BuildingLocalField P := buildingOnePlusYRootField P r
  let au : (BuildingLocalField P)ˣ :=
    Units.mk0 a (buildingOnePlusYRootField_ne_zero P r)
  let c : BuildingLocalField P := (au⁻¹ : (BuildingLocalField P)ˣ)
  have hchar : F.charpoly = Polynomial.X ^ r.matrixRank - 1 :=
    buildingFrobeniusMatrix_charpoly P r
  have hdetF : Matrix.det F =
      (-1 : BuildingLocalField P) ^ r.matrixRank * (-1) := by
    rw [Matrix.det_eq_sign_charpoly_coeff, hchar]
    cases r <;> norm_num [Rank.matrixRank]
  have hdetFne : Matrix.det F ≠ 0 := by
    dsimp [F]
    exact Units.ne_zero (Matrix.GeneralLinearGroup.det (buildingFrobeniusGL P r))
  have heval := Matrix.eval_charpoly F c
  rw [hchar] at heval
  have hscalar : Matrix.scalar (Fin r.matrixRank) c =
      c • (1 : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (BuildingLocalField P)) := by
    exact (Matrix.smul_one_eq_diagonal c).symm
  have hdetCsubF : Matrix.det
      (c • (1 : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (BuildingLocalField P)) - F) = c ^ r.matrixRank - 1 := by
    rw [← hscalar]
    exact heval.symm.trans (by simp)
  have hdetFsubC : Matrix.det
      (F - c • (1 : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (BuildingLocalField P))) =
      (-1 : BuildingLocalField P) ^ r.matrixRank *
        (c ^ r.matrixRank - 1) := by
    rw [show F - c • (1 : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (BuildingLocalField P)) =
        -(c • (1 : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (BuildingLocalField P)) - F) by abel]
    rw [Matrix.det_neg, Fintype.card_fin, hdetCsubF]
  have hfactor : buildingBMatrix P r =
      ((Fg⁻¹ : Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (BuildingLocalField P)) :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (BuildingLocalField P)) *
        (F - c • (1 : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (BuildingLocalField P))) := by
    have hscalarInv :
        (((Matrix.GeneralLinearGroup.scalar (Fin r.matrixRank) au)⁻¹ :
          Matrix.GeneralLinearGroup (Fin r.matrixRank)
            (BuildingLocalField P)) :
              Matrix (Fin r.matrixRank) (Fin r.matrixRank)
                (BuildingLocalField P)) =
          c • (1 : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (BuildingLocalField P)) := by
      change Matrix.diagonal (fun _ => c) = c • (1 : Matrix
        (Fin r.matrixRank) (Fin r.matrixRank) (BuildingLocalField P))
      exact (Matrix.smul_one_eq_diagonal c).symm
    change 1 - (((Matrix.GeneralLinearGroup.scalar (Fin r.matrixRank) au *
      Fg)⁻¹ : Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (BuildingLocalField P)) :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (BuildingLocalField P)) = _
    rw [mul_inv_rev, Units.val_mul, hscalarInv, Matrix.mul_sub]
    have hFg :
        ((Fg⁻¹ : Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (BuildingLocalField P)) :
            Matrix (Fin r.matrixRank) (Fin r.matrixRank)
              (BuildingLocalField P)) * F = 1 := by
      change ((Fg⁻¹ * Fg : Matrix.GeneralLinearGroup
        (Fin r.matrixRank) (BuildingLocalField P)) :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (BuildingLocalField P)) = 1
      simp
    rw [hFg]
  have hdetFgInv : Matrix.det
      (((Fg⁻¹ : Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (BuildingLocalField P)) :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (BuildingLocalField P))) = (Matrix.det F)⁻¹ := by
    change ((Matrix.GeneralLinearGroup.det Fg⁻¹ :
      (BuildingLocalField P)ˣ) : BuildingLocalField P) = _
    rw [map_inv, Units.val_inv_eq_inv_val]
    congr 1
  rw [hfactor, Matrix.det_mul, hdetFgInv, hdetF, hdetFsubC]
  dsimp [c, au, a]
  change ((-1 : BuildingLocalField P) ^ r.matrixRank * (-1))⁻¹ *
      ((-1 : BuildingLocalField P) ^ r.matrixRank *
        (((buildingOnePlusYRootField P r)⁻¹) ^ r.matrixRank - 1)) = _
  rw [inv_pow, buildingOnePlusYRootField_pow_matrixRank]
  cases r <;> norm_num [Rank.matrixRank] <;>
    field_simp [one_add_buildingLocalY_ne_zero P] <;> ring
theorem one_add_buildingLocalY_order
    (P : BasePrime) :
    (1 + buildingLocalY P).order = 0 := by
  have hlt :
      (1 : BuildingLocalField P).orderTop <
        (buildingLocalY P).orderTop := by
    simp [buildingLocalY]
  have htop := HahnSeries.orderTop_add_eq_left hlt
  have hne := one_add_buildingLocalY_ne_zero P
  have hcoe :
      (((1 + buildingLocalY P).order : Int) : WithTop Int) =
        (0 : WithTop Int) := by
    calc
      _ = (1 + buildingLocalY P).orderTop :=
        HahnSeries.order_eq_orderTop_of_ne_zero hne
      _ = (1 : BuildingLocalField P).orderTop := htop
      _ = 0 := by simp
  exact WithTop.coe_eq_coe.mp hcoe
theorem buildingBGL_det_localUnitOrder
    (P : BasePrime) (r : Rank) :
    SphericalHecke.localUnitOrder
      (Matrix.GeneralLinearGroup.det (buildingBGL P r)) = 1 := by
  let den : (BuildingLocalField P)ˣ :=
    Units.mk0 (1 + buildingLocalY P) (one_add_buildingLocalY_ne_zero P)
  have hdet : Matrix.GeneralLinearGroup.det (buildingBGL P r) =
      SphericalHecke.uniformizerUnit (BaseField P) * den⁻¹ := by
    apply Units.ext
    change Matrix.det (buildingBMatrix P r) = _
    rw [buildingBMatrix_det]
    simp [den, buildingLocalY, SphericalHecke.coe_uniformizerUnit,
      div_eq_mul_inv]
  rw [hdet, SphericalHecke.localUnitOrder_mul,
    SphericalHecke.localUnitOrder_inv]
  have huniformizer : SphericalHecke.localUnitOrder
      (SphericalHecke.uniformizerUnit (BaseField P)) = 1 := by
    simpa using SphericalHecke.localUnitOrder_uniformizerUnit_pow
      (k := BaseField P) 1
  have hden : SphericalHecke.localUnitOrder den = 0 := by
    exact one_add_buildingLocalY_order P
  rw [huniformizer, hden]
  norm_num
theorem buildingBMatrix_orderLowerBound_zero
    (P : BasePrime) (r : Rank) :
    SphericalHecke.MatrixOrderLowerBound 0 (buildingBMatrix P r) := by
  have hzInv :=
    SphericalHecke.integralGeneralLinearToLocal_inv_orderLowerBound
      (SphericalHecke.powerSeriesGeneralLinearToInteger
        (BaseField P) r.matrixRank
        (buildingCyclicGeneratorIntegralGL P r))
  rw [SphericalHecke.powerSeries_integer_local_triangle,
    buildingCyclicGeneratorIntegralGL_toLocal] at hzInv
  have hone : SphericalHecke.MatrixOrderLowerBound 0
      (1 : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (BuildingLocalField P)) := by
    intro i j
    by_cases hij : i = j
    · subst j
      simp
    · rw [Matrix.one_apply_ne hij, HahnSeries.orderTop_zero]
      exact le_top
  have hneg : SphericalHecke.MatrixOrderLowerBound 0
      (-((buildingCyclicGeneratorGL P r)⁻¹ :
        Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (BuildingLocalField P)) :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (BuildingLocalField P)) := by
    intro i j
    change 0 ≤ (-(((buildingCyclicGeneratorGL P r)⁻¹ :
      Matrix.GeneralLinearGroup (Fin r.matrixRank) (BuildingLocalField P)) :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (BuildingLocalField P)) i j).orderTop
    rw [HahnSeries.orderTop_neg]
    exact hzInv i j
  simpa [buildingBMatrix, sub_eq_add_neg] using hone.add hneg
theorem buildingB_smithDominantCoweight_eq_fundamental
    (P : BasePrime) (r : Rank) :
    SphericalHecke.smithDominantCoweight (buildingBGL P r) =
      SphericalHecke.fundamentalDominantCoweight r.matrixRank 1 := by
  let weight :=
    SphericalHecke.smithDominantCoweight (buildingBGL P r)
  have hsmith :
      (∑ i, (SphericalHecke.smithExponent
        (buildingBGL P r) i : ℤ)) = 1 := by
    rw [SphericalHecke.smithExponent_sum_eq_det_localUnitOrder_of_orderLowerBound_zero
      (buildingBGL P r)]
    · exact buildingBGL_det_localUnitOrder P r
    · simpa only [buildingBGL_coe] using
        buildingBMatrix_orderLowerBound_zero P r
  have hsumInt : (∑ i, (weight.exponent i : ℤ)) = 1 := by
    rw [show weight = SphericalHecke.smithDominantCoweight
      (buildingBGL P r) by rfl,
      SphericalHecke.smithDominantCoweight_exponent_sum]
    exact hsmith
  have hsumNat : ∑ i, weight.exponent i = 1 := by
    exact_mod_cast hsumInt
  change weight =
    SphericalHecke.fundamentalDominantCoweight r.matrixRank 1
  exact SphericalHecke.dominantCoweight_eq_fundamental_one_of_sum_eq_one
    (lt_of_lt_of_le (by norm_num) (Rank.two_le_matrixRank r)) weight hsumNat
theorem buildingB_mem_fundamentalDoubleCoset
    (P : BasePrime) (r : Rank) :
    Matrix.ProjGenLinGroup.mk (buildingBGL P r) ∈
      SphericalHecke.fundamentalDoubleCoset
        (BaseField P) r.matrixRank 1 := by
  rw [← SphericalHecke.dominantDoubleCoset_fundamental]
  rw [← buildingB_smithDominantCoweight_eq_fundamental P r]
  exact SphericalHecke.mk_mem_dominantDoubleCoset (buildingBGL P r)
noncomputable def buildingConstantIntegralGL
    (P : BasePrime) (r : Rank)
    (u : (ConstantExtension P r)ˣ) :
    Matrix.GeneralLinearGroup (Fin r.matrixRank) (BuildingIntegerRing P) :=
  SphericalHecke.constantGeneralLinearLift
    (BaseField P) r.matrixRank
    (Units.map (constantRegularMatrix P r).toMonoidHom u)
noncomputable def buildingConstantGL
    (P : BasePrime) (r : Rank)
    (u : (ConstantExtension P r)ˣ) :
    Matrix.GeneralLinearGroup (Fin r.matrixRank) (BuildingLocalField P) :=
  Matrix.GeneralLinearGroup.map
      (algebraMap (BaseField P) (BuildingLocalField P))
    (Units.map (constantRegularMatrix P r).toMonoidHom u)
theorem buildingConstantGL_eq_constantLift_toLocal
    (P : BasePrime) (r : Rank)
    (u : (ConstantExtension P r)ˣ) :
    buildingConstantGL P r u =
      SphericalHecke.powerSeriesGeneralLinearToLocal
        (BaseField P) r.matrixRank
        (buildingConstantIntegralGL P r u) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  change algebraMap (BaseField P) (BuildingLocalField P)
      ((constantRegularMatrix P r) (u : ConstantExtension P r) i j) =
    HahnSeries.ofPowerSeries Int (BaseField P)
      (PowerSeries.C
        ((constantRegularMatrix P r) (u : ConstantExtension P r) i j))
  rw [HahnSeries.ofPowerSeries_C]
  rw [LaurentSeries.algebraMap_apply]
theorem buildingConstant_mem_maximalCompact
    (P : BasePrime) (r : Rank)
    (u : (ConstantExtension P r)ˣ) :
    Matrix.ProjGenLinGroup.mk (buildingConstantGL P r u) ∈
      SphericalHecke.maximalCompact (BaseField P) r.matrixRank := by
  rw [buildingConstantGL_eq_constantLift_toLocal]
  exact SphericalHecke.mk_powerSeriesGeneralLinearToLocal_mem_maximalCompact _
@[simp] theorem buildingConstantGL_coe
    (P : BasePrime) (r : Rank)
    (u : (ConstantExtension P r)ˣ) :
    (buildingConstantGL P r u :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BuildingLocalField P)) =
      buildingConstantMatrix P r u :=
  rfl
noncomputable def buildingCartwrightStegerGeneratorGL
    (P : BasePrime) (r : Rank)
    (u : (ConstantExtension P r)ˣ) :
    Matrix.GeneralLinearGroup (Fin r.matrixRank) (BuildingLocalField P) :=
  buildingConstantGL P r u * buildingBGL P r *
    (buildingConstantGL P r u)⁻¹
theorem buildingCartwrightStegerGeneratorGL_det
    (P : BasePrime) (r : Rank)
    (u : (ConstantExtension P r)ˣ) :
    Matrix.GeneralLinearGroup.det
        (buildingCartwrightStegerGeneratorGL P r u) =
      Matrix.GeneralLinearGroup.det (buildingBGL P r) := by
  simp [buildingCartwrightStegerGeneratorGL, map_mul]
theorem buildingCartwrightStegerGeneratorGL_det_localUnitOrder
    (P : BasePrime) (r : Rank)
    (u : (ConstantExtension P r)ˣ) :
    SphericalHecke.localUnitOrder
        (Matrix.GeneralLinearGroup.det
          (buildingCartwrightStegerGeneratorGL P r u)) = 1 := by
  rw [buildingCartwrightStegerGeneratorGL_det,
    buildingBGL_det_localUnitOrder]
noncomputable def buildingCartwrightStegerGeneratorIntegralMatrix
    (P : BasePrime) (r : Rank)
    (u : (ConstantExtension P r)ˣ) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BuildingIntegerRing P) :=
  (buildingConstantIntegralGL P r u :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BuildingIntegerRing P)) *
    buildingBIntegralMatrix P r *
  ((buildingConstantIntegralGL P r u)⁻¹ :
      Matrix.GeneralLinearGroup (Fin r.matrixRank) (BuildingIntegerRing P))
theorem buildingCartwrightStegerGeneratorIntegralMatrix_reduction
    (P : BasePrime) (r : Rank)
    (u : (ConstantExtension P r)ˣ) :
    (buildingCartwrightStegerGeneratorIntegralMatrix P r u).map
        PowerSeries.constantCoeff =
      (constantRegularMatrix P r (u : ConstantExtension P r)) *
        (1 - ((frobeniusGL P r)⁻¹ :
          Matrix.GeneralLinearGroup (Fin r.matrixRank) (BaseField P))) *
      (constantRegularMatrix P r
        ((u : ConstantExtension P r)⁻¹)) := by
  rw [buildingCartwrightStegerGeneratorIntegralMatrix,
    Matrix.map_mul, Matrix.map_mul,
    buildingBIntegralMatrix_reduction]
  change
    ((SphericalHecke.powerSeriesReductionGL (BaseField P) r.matrixRank)
      (buildingConstantIntegralGL P r u) :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BaseField P)) * _ *
    (((SphericalHecke.powerSeriesReductionGL (BaseField P) r.matrixRank)
      (buildingConstantIntegralGL P r u))⁻¹ :
        Matrix.GeneralLinearGroup (Fin r.matrixRank) (BaseField P)) = _
  rw [buildingConstantIntegralGL,
    SphericalHecke.powerSeriesReductionGL_constantGeneralLinearLift]
  simp
theorem buildingCartwrightStegerGeneratorIntegralMatrix_toLocal
    (P : BasePrime) (r : Rank)
    (u : (ConstantExtension P r)ˣ) :
    (SphericalHecke.integerEmbedding (BaseField P)).mapMatrix
        (buildingCartwrightStegerGeneratorIntegralMatrix P r u) =
      (buildingCartwrightStegerGeneratorGL P r u :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BuildingLocalField P)) := by
  rw [buildingCartwrightStegerGeneratorIntegralMatrix,
    map_mul, map_mul, buildingBIntegralMatrix_toLocal]
  change
    (SphericalHecke.powerSeriesGeneralLinearToLocal
      (BaseField P) r.matrixRank (buildingConstantIntegralGL P r u) :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BuildingLocalField P)) *
      buildingBMatrix P r *
    ((SphericalHecke.powerSeriesGeneralLinearToLocal
      (BaseField P) r.matrixRank (buildingConstantIntegralGL P r u))⁻¹ :
        Matrix.GeneralLinearGroup (Fin r.matrixRank) (BuildingLocalField P)) = _
  rw [← buildingConstantGL_eq_constantLift_toLocal]
  simp [buildingCartwrightStegerGeneratorGL]
theorem generatorReductionRange_eq_of_vertex_eq
    (P : BasePrime) (r : Rank)
    (u v : (ConstantExtension P r)ˣ)
    (hvertex :
      (QuotientGroup.mk
          (Matrix.ProjGenLinGroup.mk
            (buildingCartwrightStegerGeneratorGL P r u)) :
        SphericalHecke.BuildingVertex (BaseField P) r.matrixRank) =
        QuotientGroup.mk
          (Matrix.ProjGenLinGroup.mk
            (buildingCartwrightStegerGeneratorGL P r v))) :
    LinearMap.range
        (Matrix.toLin (constantBasis P r) (constantBasis P r)
          ((buildingCartwrightStegerGeneratorIntegralMatrix P r u).map
            PowerSeries.constantCoeff)) =
      LinearMap.range
        (Matrix.toLin (constantBasis P r) (constantBasis P r)
          ((buildingCartwrightStegerGeneratorIntegralMatrix P r v).map
            PowerSeries.constantCoeff)) := by
  let Au := buildingCartwrightStegerGeneratorGL P r u
  let Av := buildingCartwrightStegerGeneratorGL P r v
  let R : Matrix.GeneralLinearGroup
      (Fin r.matrixRank) (BuildingLocalField P) := Au⁻¹ * Av
  have hcompact : Matrix.ProjGenLinGroup.mk R ∈
      SphericalHecke.maximalCompact (BaseField P) r.matrixRank := by
    have hrel := QuotientGroup.eq.mp hvertex
    simpa [R, Au, Av, map_mul, map_inv] using hrel
  have hdetR : SphericalHecke.localUnitOrder
      (Matrix.GeneralLinearGroup.det R) = 0 := by
    simp [R, Au, Av, map_mul, map_inv,
      SphericalHecke.localUnitOrder_mul,
      SphericalHecke.localUnitOrder_inv,
      buildingCartwrightStegerGeneratorGL_det_localUnitOrder]
  have hd : 0 < r.matrixRank :=
    lt_of_lt_of_le (by omega) (Rank.two_le_matrixRank r)
  have hRintegral : R ∈ SphericalHecke.integralGeneralLinearSet
      (BaseField P) r.matrixRank :=
    (SphericalHecke.projective_mk_mem_maximalCompact_iff_integral
      (BaseField P) r.matrixRank hd R hdetR).mp hcompact
  rw [← SphericalHecke.range_integralGeneralLinearToLocal] at hRintegral
  obtain ⟨D, hD⟩ := hRintegral
  let C := SphericalHecke.integerGeneralLinearToPowerSeries
    (BaseField P) r.matrixRank D
  have hC : SphericalHecke.powerSeriesGeneralLinearToLocal
      (BaseField P) r.matrixRank C = R := by
    rw [← SphericalHecke.powerSeries_integer_local_triangle]
    rw [SphericalHecke.powerSeriesGeneralLinearToInteger_inverse]
    exact hD
  have hmatrix : buildingCartwrightStegerGeneratorIntegralMatrix P r v =
      buildingCartwrightStegerGeneratorIntegralMatrix P r u *
        (C : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (BuildingIntegerRing P)) := by
    apply Matrix.map_injective
      (SphericalHecke.integerEmbedding_injective (BaseField P))
    change
      (buildingCartwrightStegerGeneratorIntegralMatrix P r v).map
          (SphericalHecke.integerEmbedding (BaseField P)) =
        (buildingCartwrightStegerGeneratorIntegralMatrix P r u *
          (C : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (BuildingIntegerRing P))).map
          (SphericalHecke.integerEmbedding (BaseField P))
    rw [Matrix.map_mul]
    have hu :=
      buildingCartwrightStegerGeneratorIntegralMatrix_toLocal P r u
    have hv :=
      buildingCartwrightStegerGeneratorIntegralMatrix_toLocal P r v
    change (buildingCartwrightStegerGeneratorIntegralMatrix P r u).map
      (SphericalHecke.integerEmbedding (BaseField P)) =
        (Au : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (BuildingLocalField P)) at hu
    change (buildingCartwrightStegerGeneratorIntegralMatrix P r v).map
      (SphericalHecke.integerEmbedding (BaseField P)) =
        (Av : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (BuildingLocalField P)) at hv
    have hc := congrArg Units.val hC
    change (C : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (BuildingIntegerRing P)).map
        (SphericalHecke.integerEmbedding (BaseField P)) =
      (R : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (BuildingLocalField P)) at hc
    rw [hv, hu, hc]
    simp [R]
  rw [hmatrix, Matrix.map_mul]
  exact (range_toLin_mul_generalLinear P r
    ((buildingCartwrightStegerGeneratorIntegralMatrix P r u).map
      PowerSeries.constantCoeff)
    (SphericalHecke.powerSeriesReductionGL
      (BaseField P) r.matrixRank C)).symm
noncomputable def buildingCartwrightStegerGenerator
    (P : BasePrime) (r : Rank)
    (u : ConstantProjectiveClass P r) :
    Matrix.ProjGenLinGroup (Fin r.matrixRank) (BuildingLocalField P) :=
  Matrix.ProjGenLinGroup.mk
    (buildingCartwrightStegerGeneratorGL P r
      (constantClassRepresentative P r u))
theorem buildingCartwrightStegerGenerator_mem_fundamentalDoubleCoset
    (P : BasePrime) (r : Rank) (u : ConstantProjectiveClass P r) :
    buildingCartwrightStegerGenerator P r u ∈
      SphericalHecke.fundamentalDoubleCoset
        (BaseField P) r.matrixRank 1 := by
  let c := Matrix.ProjGenLinGroup.mk
    (buildingConstantGL P r (constantClassRepresentative P r u))
  have hc : c ∈ SphericalHecke.maximalCompact
      (BaseField P) r.matrixRank :=
    buildingConstant_mem_maximalCompact P r
      (constantClassRepresentative P r u)
  rw [← SphericalHecke.dominantDoubleCoset_fundamental]
  have hb : Matrix.ProjGenLinGroup.mk (buildingBGL P r) ∈
      SphericalHecke.dominantDoubleCoset (BaseField P)
        (SphericalHecke.fundamentalDominantCoweight r.matrixRank 1) := by
    rw [SphericalHecke.dominantDoubleCoset_fundamental]
    exact buildingB_mem_fundamentalDoubleCoset P r
  have hleft := SphericalHecke.left_mul_mem_dominantDoubleCoset
    (BaseField P)
    (SphericalHecke.fundamentalDominantCoweight r.matrixRank 1) hc hb
  have hconj := SphericalHecke.right_mul_mem_dominantDoubleCoset
    (BaseField P)
    (SphericalHecke.fundamentalDominantCoweight r.matrixRank 1)
    ((SphericalHecke.maximalCompact (BaseField P) r.matrixRank).inv_mem hc)
    hleft
  simpa [buildingCartwrightStegerGenerator,
    buildingCartwrightStegerGeneratorGL, c, map_mul, map_inv] using hconj
noncomputable def buildingGeneratorNeighbor
    (P : BasePrime) (r : Rank) (u : ConstantProjectiveClass P r) :
    {q // q ∈ SphericalHecke.fundamentalNeighborCosets
      (BaseField P) r.matrixRank 1} := by
  refine ⟨QuotientGroup.mk (buildingCartwrightStegerGenerator P r u), ?_⟩
  rw [SphericalHecke.mem_fundamentalNeighborCosets]
  exact ⟨buildingCartwrightStegerGenerator P r u,
    buildingCartwrightStegerGenerator_mem_fundamentalDoubleCoset P r u, rfl⟩
theorem natCard_constantProjectiveClass_eq_coloredAdjacencyDegree_one
    (P : BasePrime) (r : Rank) :
    Nat.card (ConstantProjectiveClass P r) =
      SphericalHecke.coloredAdjacencyDegree
        (BaseField P) r.matrixRank 1 := by
  rw [natCard_constantProjectiveClass]
  cases r with
  | three =>
      simp only [Rank.matrixRank]
      rw [SphericalHecke.coloredAdjacencyDegree_rankThree_one]
      simp [Finset.sum_range_succ]
      ring
  | four =>
      simp only [Rank.matrixRank]
      rw [SphericalHecke.coloredAdjacencyDegree_rankFour_one]
      simp [Finset.sum_range_succ]
      ring
theorem card_buildingGeneratorNeighbor_domain_eq_codomain
    (P : BasePrime) (r : Rank) :
    Fintype.card (ConstantProjectiveClass P r) =
      Fintype.card
        {q // q ∈ SphericalHecke.fundamentalNeighborCosets
          (BaseField P) r.matrixRank 1} := by
  rw [← Nat.card_eq_fintype_card,
    natCard_constantProjectiveClass_eq_coloredAdjacencyDegree_one]
  simp [SphericalHecke.coloredAdjacencyDegree]
theorem buildingGeneratorNeighbor_injective
    (P : BasePrime) (r : Rank) :
    Function.Injective (buildingGeneratorNeighbor P r) := by
  intro x y hxy
  let u := constantClassRepresentative P r x
  let v := constantClassRepresentative P r y
  have hvertex :
      (QuotientGroup.mk
          (Matrix.ProjGenLinGroup.mk
            (buildingCartwrightStegerGeneratorGL P r u)) :
        SphericalHecke.BuildingVertex (BaseField P) r.matrixRank) =
      QuotientGroup.mk
        (Matrix.ProjGenLinGroup.mk
          (buildingCartwrightStegerGeneratorGL P r v)) := by
    have hval := congrArg Subtype.val hxy
    exact hval
  have hrange := generatorReductionRange_eq_of_vertex_eq P r u v hvertex
  rw [buildingCartwrightStegerGeneratorIntegralMatrix_reduction,
    buildingCartwrightStegerGeneratorIntegralMatrix_reduction,
    range_toLin_constant_conjugate_one_sub_frobeniusGL_inv,
    range_toLin_constant_conjugate_one_sub_frobeniusGL_inv] at hrange
  let a : ConstantExtension P r :=
    (u : ConstantExtension P r) * (v : ConstantExtension P r)⁻¹
  have hstable : (frobeniusDifferenceRange P r).map
      (constantMultiplicationLinearMap P r a) ≤
      frobeniusDifferenceRange P r := by
    rintro _ ⟨z, hz, rfl⟩
    have huz : (u : ConstantExtension P r) * z ∈
        (frobeniusDifferenceRange P r).map
          (constantMultiplicationLinearMap P r u) := by
      exact Submodule.mem_map_of_mem hz
    rw [hrange] at huz
    obtain ⟨w, hw, huw⟩ := huz
    have haw : a * z = w := by
      change ((u : ConstantExtension P r) *
        (v : ConstantExtension P r)⁻¹) * z = w
      change (v : ConstantExtension P r) * w =
        (u : ConstantExtension P r) * z at huw
      apply (mul_left_cancel₀ (Units.ne_zero v))
      simpa [mul_assoc, mul_left_comm, mul_comm] using huw.symm
    simpa [haw] using hw
  obtain ⟨c, hc⟩ :=
    exists_eq_algebraMap_of_map_frobeniusDifferenceRange_le
      P r a hstable
  have hc_ne : c ≠ 0 := by
    intro hc0
    have ha0 : a = 0 := by simpa [hc0] using hc
    exact (mul_ne_zero (Units.ne_zero u)
      (inv_ne_zero (Units.ne_zero v))) ha0
  let cu : (BaseField P)ˣ := Units.mk0 c hc_ne
  have hquotient :
      (QuotientGroup.mk u : ConstantProjectiveClass P r) =
        QuotientGroup.mk v := by
    apply QuotientGroup.eq_iff_div_mem.mpr
    change u / v ∈ baseScalarUnits P r
    refine ⟨cu, ?_⟩
    apply Units.ext
    simpa [a, cu, baseScalarUnitHom, div_eq_mul_inv] using hc.symm
  exact (QuotientGroup.out_eq' x).symm.trans
    (hquotient.trans (QuotientGroup.out_eq' y))
theorem buildingGeneratorNeighbor_bijective
    (P : BasePrime) (r : Rank) :
    Function.Bijective (buildingGeneratorNeighbor P r) := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  exact ⟨buildingGeneratorNeighbor_injective P r,
    card_buildingGeneratorNeighbor_domain_eq_codomain P r⟩
noncomputable def buildingGeneratorNeighborEquiv
    (P : BasePrime) (r : Rank) :
    ConstantProjectiveClass P r ≃
      {q // q ∈ SphericalHecke.fundamentalNeighborCosets
        (BaseField P) r.matrixRank 1} :=
  Equiv.ofBijective (buildingGeneratorNeighbor P r)
    (buildingGeneratorNeighbor_bijective P r)
noncomputable def BuildingCartwrightStegerLattice
    (P : BasePrime) (r : Rank) :
    Subgroup
      (Matrix.ProjGenLinGroup (Fin r.matrixRank) (BuildingLocalField P)) :=
  Subgroup.closure
    (Set.range (buildingCartwrightStegerGenerator P r))
noncomputable def buildingLatticeGenerator
    (P : BasePrime) (r : Rank) (u : ConstantProjectiveClass P r) :
    BuildingCartwrightStegerLattice P r :=
  ⟨buildingCartwrightStegerGenerator P r u,
    Subgroup.subset_closure (Set.mem_range_self u)⟩
@[simp]
theorem buildingLatticeGenerator_coe
    (P : BasePrime) (r : Rank) (u : ConstantProjectiveClass P r) :
    (buildingLatticeGenerator P r u :
      Matrix.ProjGenLinGroup (Fin r.matrixRank) (BuildingLocalField P)) =
      buildingCartwrightStegerGenerator P r u :=
  rfl
abbrev CartwrightStegerBuildingVertex
    (P : BasePrime) (r : Rank) :=
  SphericalHecke.BuildingVertex (BaseField P) r.matrixRank
noncomputable def buildingLatticeVertexMap
    (P : BasePrime) (r : Rank) :
    BuildingCartwrightStegerLattice P r →
      CartwrightStegerBuildingVertex P r :=
  fun g => QuotientGroup.mk
    (g : Matrix.ProjGenLinGroup (Fin r.matrixRank) (BuildingLocalField P))
noncomputable def buildingGeneratorNeighborAtEquiv
    (P : BasePrime) (r : Rank)
    (g : BuildingCartwrightStegerLattice P r) :
    ConstantProjectiveClass P r ≃
      {q // SphericalHecke.ColoredBuildingAdjacent
        (BaseField P) r.matrixRank 1
        (buildingLatticeVertexMap P r g) q} := by
  let eBase := (buildingGeneratorNeighborEquiv P r).trans
    (SphericalHecke.fundamentalNeighborAdjacentBaseEquiv
      (BaseField P) r.matrixRank 1)
  let gl : Matrix.ProjGenLinGroup (Fin r.matrixRank)
      (BuildingLocalField P) := g
  have hcenter :
      gl •
          (QuotientGroup.mk 1 : CartwrightStegerBuildingVertex P r) =
        buildingLatticeVertexMap P r g := by
    rw [MulAction.Quotient.smul_mk]
    simp [gl, smul_eq_mul, buildingLatticeVertexMap]
  exact {
    toFun := fun u => ⟨gl • (eBase u).1, by
      rw [← hcenter]
      exact (SphericalHecke.coloredBuildingAdjacent_smul_iff
        (BaseField P) r.matrixRank 1 gl _ _).2 (eBase u).2⟩
    invFun := fun q => eBase.symm ⟨gl⁻¹ • q.1, by
      have hq : SphericalHecke.ColoredBuildingAdjacent
          (BaseField P) r.matrixRank 1
          (gl • (QuotientGroup.mk 1 : CartwrightStegerBuildingVertex P r))
          q.1 := by simpa [hcenter] using q.2
      have hback := (SphericalHecke.coloredBuildingAdjacent_smul_iff
        (BaseField P) r.matrixRank 1 gl⁻¹ _ _).2 hq
      simpa using hback⟩
    left_inv := fun u => by
      apply eBase.injective
      apply Subtype.ext
      simp
    right_inv := fun q => by
      apply Subtype.ext
      simp
  }
end QEC.Coding.HighDimensionalExpander.CartwrightSteger


