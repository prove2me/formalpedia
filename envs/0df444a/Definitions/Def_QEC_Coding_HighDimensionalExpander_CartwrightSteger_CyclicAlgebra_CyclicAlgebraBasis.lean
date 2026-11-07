-- Prove2me | Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebraBasis
-- name    : QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebraBasis
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T23:55:20.7164+00:00
-- url     : https://prove2.me/theorems/c7330d76-293b-4027-8497-38720262cec1
-- title:
--   Cyclic Algebra Basis
-- statement:
--   Definitions and structural lemmas for Cyclic Algebra Basis, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/CyclicAlgebraBasis.lean

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityLattice
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Core
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CongruenceLifting_residueTransvectionSpecial_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Rank_two_le_matrixRank
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingCompactCyclicSemidirectHom_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingGeneratorNeighborAtEquiv_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingLatticeVertexMap_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerNormUnit_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantMatrix_mem_cyclicAlgebra
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrixHom_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrix_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicGeneratorInverseMatrix_eq_inv_smul_pow_pred
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicGeneratorInverseMatrix_mem_cyclicAlgebra
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicGeneratorMatrix_mem_cyclicAlgebra
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicGeneratorMatrix_pow_mul_constantMatrix
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicGeneratorMatrix_pow_rank_add
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_frobeniusPowerEquiv_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_functionFieldEmbedding_injective
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
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.CongruenceLifting.residueTransvectionSpecial_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingCompactCyclicSemidirectHom_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingGeneratorNeighborAtEquiv_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingLatticeVertexMap_one
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerNormUnit_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantUnitMatrixHom_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantUnitMatrix_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.frobeniusPowerEquiv_apply
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


set_option autoImplicit false
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
noncomputable def functionFieldCyclicBasisVector
    (P : BasePrime) (r : Rank)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    CyclicAlgebra P r :=
  ⟨splittingCyclicBasisVector P r p,
    (CyclicAlgebra P r).mul_mem
      (constantMatrix_mem_cyclicAlgebra P r (constantBasis P r p.1))
      ((CyclicAlgebra P r).pow_mem
        (cyclicGeneratorMatrix_mem_cyclicAlgebra P r) p.2)⟩
@[simp] theorem functionFieldCyclicBasisVector_coe
    (P : BasePrime) (r : Rank)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    (functionFieldCyclicBasisVector P r p :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r)) =
      splittingCyclicBasisVector P r p := rfl
theorem functionFieldCyclicBasisVector_linearIndependent
    (P : BasePrime) (r : Rank) :
    LinearIndependent (FunctionField P)
      (functionFieldCyclicBasisVector P r) := by
  apply LinearIndependent.of_comp (CyclicAlgebra P r).val.toLinearMap
  exact
    (splittingCyclicBasisVector_linearIndependent P r).restrict_scalars
      (show Function.Injective (fun a : FunctionField P =>
          a • (1 : SplittingFunctionField P r)) by
        intro a b h
        have hab : a = b := by simpa [Algebra.smul_def] using h
        apply functionFieldEmbedding_injective P r
        exact congrArg (functionFieldEmbedding P r) hab)
noncomputable def functionFieldCyclicSpan
    (P : BasePrime) (r : Rank) :
    Submodule (FunctionField P) (CyclicAlgebra P r) :=
  Submodule.span (FunctionField P)
    (Set.range (functionFieldCyclicBasisVector P r))
theorem functionFieldEmbedding_C
    (P : BasePrime) (r : Rank) (a : BaseField P) :
    functionFieldEmbedding P r (RatFunc.C a) =
      RatFunc.C (algebraMap (BaseField P) (ConstantExtension P r) a) := by
  rw [show (RatFunc.C a : FunctionField P) =
      algebraMap (PolynomialRing P) (FunctionField P) (Polynomial.C a) /
        algebraMap (PolynomialRing P) (FunctionField P) 1 by simp,
    show (RatFunc.C (algebraMap (BaseField P) (ConstantExtension P r) a) :
        SplittingFunctionField P r) =
      algebraMap (Polynomial (ConstantExtension P r))
          (SplittingFunctionField P r)
          (Polynomial.C (algebraMap (BaseField P) (ConstantExtension P r) a)) /
        algebraMap (Polynomial (ConstantExtension P r))
          (SplittingFunctionField P r) 1 by simp]
  unfold functionFieldEmbedding
  dsimp only
  rw [RatFunc.coe_mapRingHom_eq_coe_map]
  rw [RatFunc.map_apply_div]
  simp
theorem constantMatrix_baseField_smul_functionField
    (P : BasePrime) (r : Rank) (a : BaseField P)
    (c : ConstantExtension P r) :
    constantMatrix P r (a • c) =
      (algebraMap (BaseField P) (FunctionField P) a) •
        constantMatrix P r c := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [constantMatrix, Algebra.smul_def]
    left
    have hfix (n : ℕ) :
        ((⇑(constantFrobenius P r).symm)^[n])
            (algebraMap (BaseField P) (ConstantExtension P r) a) =
          algebraMap (BaseField P) (ConstantExtension P r) a := by
      induction n with
      | zero => rfl
      | succ n ih =>
          rw [Function.iterate_succ_apply,
            (constantFrobenius P r).symm.commutes a, ih]
    rw [hfix i]
    exact (functionFieldEmbedding_C P r a).symm
  · simp [constantMatrix, hij, Algebra.smul_def]
theorem constantCyclicMonomial_eq_sum_basis
    (P : BasePrime) (r : Rank) (c : ConstantExtension P r)
    (k : ℕ) (hk : k < r.matrixRank) :
    (⟨constantMatrix P r c * cyclicGeneratorMatrix P r ^ k,
      (CyclicAlgebra P r).mul_mem
        (constantMatrix_mem_cyclicAlgebra P r c)
        ((CyclicAlgebra P r).pow_mem
          (cyclicGeneratorMatrix_mem_cyclicAlgebra P r) k)⟩ :
      CyclicAlgebra P r) =
      ∑ j, algebraMap (BaseField P) (FunctionField P)
          ((constantBasis P r).repr c j) •
            functionFieldCyclicBasisVector P r (j, ⟨k, hk⟩) := by
  apply Subtype.ext
  change constantMatrix P r c * cyclicGeneratorMatrix P r ^ k =
    (CyclicAlgebra P r).val
      (∑ j, algebraMap (BaseField P) (FunctionField P)
        ((constantBasis P r).repr c j) •
          functionFieldCyclicBasisVector P r (j, ⟨k, hk⟩))
  rw [map_sum]
  simp only [map_smul]
  conv_lhs => rw [← (constantBasis P r).sum_repr c]
  rw [← constantMatrixEmbedding_apply, map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [constantMatrixEmbedding_apply,
    constantMatrix_baseField_smul_functionField, smul_mul_assoc]
  rfl
theorem constantCyclicMonomial_mem_functionFieldCyclicSpan
    (P : BasePrime) (r : Rank) (c : ConstantExtension P r)
    (k : ℕ) (hk : k < r.matrixRank) :
    ⟨constantMatrix P r c * cyclicGeneratorMatrix P r ^ k,
      (CyclicAlgebra P r).mul_mem
        (constantMatrix_mem_cyclicAlgebra P r c)
        ((CyclicAlgebra P r).pow_mem
          (cyclicGeneratorMatrix_mem_cyclicAlgebra P r) k)⟩ ∈
      functionFieldCyclicSpan P r := by
  rw [constantCyclicMonomial_eq_sum_basis P r c k hk]
  apply Submodule.sum_mem
  intro j _
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨(j, ⟨k, hk⟩), rfl⟩
theorem onePlusY_eq_functionField_smul_one
    (P : BasePrime) (r : Rank) :
    onePlusY P r =
      (algebraMap (FunctionField P) (SplittingFunctionField P r)
        (1 + RatFunc.X)) • (1 : SplittingFunctionField P r) := by
  change 1 + RatFunc.X = functionFieldEmbedding P r (1 + RatFunc.X) * 1
  rw [map_add, map_one, functionFieldEmbedding_X]
  simp
theorem constantCyclicMonomial_mul_eq
    (P : BasePrime) (r : Rank)
    (c d : ConstantExtension P r) (k l : ℕ) :
    (constantMatrix P r c * cyclicGeneratorMatrix P r ^ k) *
        (constantMatrix P r d * cyclicGeneratorMatrix P r ^ l) =
      constantMatrix P r (c * (constantFrobenius P r ^ k) d) *
        cyclicGeneratorMatrix P r ^ (k + l) := by
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
          (cyclicGeneratorMatrix P r ^ k *
            cyclicGeneratorMatrix P r ^ l) = _
      rw [← map_mul, ← pow_add]
      rfl
theorem constantCyclicMonomial_mul_mem_functionFieldCyclicSpan
    (P : BasePrime) (r : Rank)
    (c d : ConstantExtension P r)
    (k l : ℕ) (hk : k < r.matrixRank) (hl : l < r.matrixRank) :
    (⟨constantMatrix P r c * cyclicGeneratorMatrix P r ^ k,
        (CyclicAlgebra P r).mul_mem
          (constantMatrix_mem_cyclicAlgebra P r c)
          ((CyclicAlgebra P r).pow_mem
            (cyclicGeneratorMatrix_mem_cyclicAlgebra P r) k)⟩ :
      CyclicAlgebra P r) *
      ⟨constantMatrix P r d * cyclicGeneratorMatrix P r ^ l,
        (CyclicAlgebra P r).mul_mem
          (constantMatrix_mem_cyclicAlgebra P r d)
          ((CyclicAlgebra P r).pow_mem
            (cyclicGeneratorMatrix_mem_cyclicAlgebra P r) l)⟩ ∈
        functionFieldCyclicSpan P r := by
  let e : ConstantExtension P r :=
    c * (constantFrobenius P r ^ k) d
  have hproduct :
      (constantMatrix P r c * cyclicGeneratorMatrix P r ^ k) *
          (constantMatrix P r d * cyclicGeneratorMatrix P r ^ l) =
        constantMatrix P r e * cyclicGeneratorMatrix P r ^ (k + l) :=
    constantCyclicMonomial_mul_eq P r c d k l
  by_cases hsum : k + l < r.matrixRank
  · have hmem := constantCyclicMonomial_mem_functionFieldCyclicSpan
      P r e (k + l) hsum
    have heq :
        (⟨constantMatrix P r c * cyclicGeneratorMatrix P r ^ k,
            (CyclicAlgebra P r).mul_mem
              (constantMatrix_mem_cyclicAlgebra P r c)
              ((CyclicAlgebra P r).pow_mem
                (cyclicGeneratorMatrix_mem_cyclicAlgebra P r) k)⟩ :
          CyclicAlgebra P r) *
          ⟨constantMatrix P r d * cyclicGeneratorMatrix P r ^ l,
            (CyclicAlgebra P r).mul_mem
              (constantMatrix_mem_cyclicAlgebra P r d)
              ((CyclicAlgebra P r).pow_mem
                (cyclicGeneratorMatrix_mem_cyclicAlgebra P r) l)⟩ =
        ⟨constantMatrix P r e * cyclicGeneratorMatrix P r ^ (k + l),
          (CyclicAlgebra P r).mul_mem
            (constantMatrix_mem_cyclicAlgebra P r e)
            ((CyclicAlgebra P r).pow_mem
              (cyclicGeneratorMatrix_mem_cyclicAlgebra P r) (k + l))⟩ := by
      apply Subtype.ext
      exact hproduct
    rw [heq]
    exact hmem
  · have hrank : 0 < r.matrixRank :=
      lt_of_lt_of_le (by omega) (Rank.two_le_matrixRank r)
    let j := k + l - r.matrixRank
    have hj : j < r.matrixRank := by omega
    have hsumEq : k + l = r.matrixRank + j := by omega
    let a : FunctionField P := 1 + RatFunc.X
    have hmatrix : constantMatrix P r e *
          cyclicGeneratorMatrix P r ^ (k + l) =
        a • (constantMatrix P r e * cyclicGeneratorMatrix P r ^ j) := by
      rw [hsumEq, cyclicGeneratorMatrix_pow_rank_add]
      rw [Matrix.mul_smul]
      rw [onePlusY_eq_functionField_smul_one]
      simp only [a, Algebra.smul_def, map_add, map_one]
      congr 1
      rw [IsScalarTower.algebraMap_apply
        (FunctionField P) (SplittingFunctionField P r)
        (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (SplittingFunctionField P r))]
      simp
    have hmem := constantCyclicMonomial_mem_functionFieldCyclicSpan
      P r e j hj
    have hscalarMem := (functionFieldCyclicSpan P r).smul_mem a hmem
    have heq :
        (⟨constantMatrix P r c * cyclicGeneratorMatrix P r ^ k,
            (CyclicAlgebra P r).mul_mem
              (constantMatrix_mem_cyclicAlgebra P r c)
              ((CyclicAlgebra P r).pow_mem
                (cyclicGeneratorMatrix_mem_cyclicAlgebra P r) k)⟩ :
          CyclicAlgebra P r) *
          ⟨constantMatrix P r d * cyclicGeneratorMatrix P r ^ l,
            (CyclicAlgebra P r).mul_mem
              (constantMatrix_mem_cyclicAlgebra P r d)
              ((CyclicAlgebra P r).pow_mem
                (cyclicGeneratorMatrix_mem_cyclicAlgebra P r) l)⟩ =
        a • ⟨constantMatrix P r e * cyclicGeneratorMatrix P r ^ j,
          (CyclicAlgebra P r).mul_mem
            (constantMatrix_mem_cyclicAlgebra P r e)
            ((CyclicAlgebra P r).pow_mem
              (cyclicGeneratorMatrix_mem_cyclicAlgebra P r) j)⟩ := by
      apply Subtype.ext
      exact hproduct.trans hmatrix
    rw [heq]
    exact hscalarMem
theorem functionFieldCyclicSpan_mul_mem
    (P : BasePrime) (r : Rank) (x y : CyclicAlgebra P r)
    (hx : x ∈ functionFieldCyclicSpan P r)
    (hy : y ∈ functionFieldCyclicSpan P r) :
    x * y ∈ functionFieldCyclicSpan P r := by
  let S := functionFieldCyclicSpan P r
  refine Submodule.span_induction
    (p := fun x _ => ∀ y, y ∈ S → x * y ∈ S)
    ?basisX ?zeroX ?addX ?smulX hx y hy
  · intro x hxRange
    obtain ⟨p, rfl⟩ := hxRange
    intro y hy
    refine Submodule.span_induction
      (p := fun y _ => functionFieldCyclicBasisVector P r p * y ∈ S)
      ?basisY ?zeroY ?addY ?smulY hy
    · intro y hyRange
      obtain ⟨q, rfl⟩ := hyRange
      exact constantCyclicMonomial_mul_mem_functionFieldCyclicSpan
        P r (constantBasis P r p.1) (constantBasis P r q.1)
        p.2 q.2 p.2.isLt q.2.isLt
    · simp [S]
    · intro a b _ _ ha hb
      rw [mul_add]
      exact S.add_mem ha hb
    · intro a z _ hz
      rw [mul_smul_comm]
      exact S.smul_mem a hz
  · intro y _
    simp [S]
  · intro a b _ _ ha hb y hy
    rw [add_mul]
    exact S.add_mem (ha y hy) (hb y hy)
  · intro a z _ hz y hy
    rw [smul_mul_assoc]
    exact S.smul_mem a (hz y hy)
theorem one_mem_functionFieldCyclicSpan
    (P : BasePrime) (r : Rank) :
    (1 : CyclicAlgebra P r) ∈ functionFieldCyclicSpan P r := by
  have h := constantCyclicMonomial_mem_functionFieldCyclicSpan
    P r 1 0 (lt_of_lt_of_le (by omega) (Rank.two_le_matrixRank r))
  have hone :
      (1 : CyclicAlgebra P r) =
        ⟨constantMatrix P r 1 * cyclicGeneratorMatrix P r ^ 0,
          (CyclicAlgebra P r).mul_mem
            (constantMatrix_mem_cyclicAlgebra P r 1)
            ((CyclicAlgebra P r).pow_mem
              (cyclicGeneratorMatrix_mem_cyclicAlgebra P r) 0)⟩ := by
    apply Subtype.ext
    simp [← constantMatrixEmbedding_apply]
  rw [hone]
  exact h
noncomputable def functionFieldCyclicSpanSubalgebra
    (P : BasePrime) (r : Rank) :
    Subalgebra (FunctionField P) (CyclicAlgebra P r) where
  carrier := functionFieldCyclicSpan P r
  zero_mem' := (functionFieldCyclicSpan P r).zero_mem
  one_mem' := one_mem_functionFieldCyclicSpan P r
  add_mem' := (functionFieldCyclicSpan P r).add_mem
  mul_mem' := by
    intro a b ha hb
    exact functionFieldCyclicSpan_mul_mem P r a b ha hb
  algebraMap_mem' a := by
    have h := (functionFieldCyclicSpan P r).smul_mem a
      (one_mem_functionFieldCyclicSpan P r)
    simpa [Algebra.smul_def] using h
theorem constantMatrix_mem_functionFieldCyclicSpan
    (P : BasePrime) (r : Rank) (c : ConstantExtension P r) :
    (⟨constantMatrix P r c, constantMatrix_mem_cyclicAlgebra P r c⟩ :
      CyclicAlgebra P r) ∈ functionFieldCyclicSpan P r := by
  have h := constantCyclicMonomial_mem_functionFieldCyclicSpan P r c 0
    (lt_of_lt_of_le (by omega) (Rank.two_le_matrixRank r))
  have heq :
      (⟨constantMatrix P r c, constantMatrix_mem_cyclicAlgebra P r c⟩ :
        CyclicAlgebra P r) =
      ⟨constantMatrix P r c * cyclicGeneratorMatrix P r ^ 0,
        (CyclicAlgebra P r).mul_mem
          (constantMatrix_mem_cyclicAlgebra P r c)
          ((CyclicAlgebra P r).pow_mem
            (cyclicGeneratorMatrix_mem_cyclicAlgebra P r) 0)⟩ := by
    apply Subtype.ext
    simp
  rw [heq]
  exact h
theorem cyclicGeneratorMatrix_mem_functionFieldCyclicSpan
    (P : BasePrime) (r : Rank) :
    (⟨cyclicGeneratorMatrix P r,
        cyclicGeneratorMatrix_mem_cyclicAlgebra P r⟩ : CyclicAlgebra P r) ∈
      functionFieldCyclicSpan P r := by
  have h := constantCyclicMonomial_mem_functionFieldCyclicSpan P r 1 1
    (lt_of_lt_of_le (by omega) (Rank.two_le_matrixRank r))
  have heq :
      (⟨cyclicGeneratorMatrix P r,
        cyclicGeneratorMatrix_mem_cyclicAlgebra P r⟩ : CyclicAlgebra P r) =
      ⟨constantMatrix P r 1 * cyclicGeneratorMatrix P r ^ 1,
        (CyclicAlgebra P r).mul_mem
          (constantMatrix_mem_cyclicAlgebra P r 1)
          ((CyclicAlgebra P r).pow_mem
            (cyclicGeneratorMatrix_mem_cyclicAlgebra P r) 1)⟩ := by
    apply Subtype.ext
    simp [← constantMatrixEmbedding_apply]
  rw [heq]
  exact h
theorem functionFieldEmbedding_onePlusY
    (P : BasePrime) (r : Rank) :
    functionFieldEmbedding P r (1 + RatFunc.X) = onePlusY P r := by
  rw [map_add, map_one, functionFieldEmbedding_X]
  rfl
theorem onePlusYInv_smul_eq_functionField_smul
    (P : BasePrime) (r : Rank)
    (M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r)) :
    (onePlusY P r)⁻¹ • M =
      ((1 + RatFunc.X : FunctionField P)⁻¹) • M := by
  have hscalar : functionFieldEmbedding P r
      ((1 + RatFunc.X : FunctionField P)⁻¹) = (onePlusY P r)⁻¹ := by
    rw [map_inv₀, functionFieldEmbedding_onePlusY]
  simp only [Algebra.smul_def]
  congr 1
  rw [IsScalarTower.algebraMap_apply
    (FunctionField P) (SplittingFunctionField P r)
    (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r))]
  change (algebraMap (SplittingFunctionField P r)
      (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r))) (onePlusY P r)⁻¹ =
    (algebraMap (SplittingFunctionField P r)
      (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r)))
      (functionFieldEmbedding P r ((1 + RatFunc.X : FunctionField P)⁻¹))
  rw [hscalar]
theorem cyclicGeneratorInverseMatrix_mem_functionFieldCyclicSpan
    (P : BasePrime) (r : Rank) :
    (⟨cyclicGeneratorInverseMatrix P r,
        cyclicGeneratorInverseMatrix_mem_cyclicAlgebra P r⟩ :
      CyclicAlgebra P r) ∈ functionFieldCyclicSpan P r := by
  have hrank : 0 < r.matrixRank :=
    lt_of_lt_of_le (by omega) (Rank.two_le_matrixRank r)
  have hpred : r.matrixRank - 1 < r.matrixRank := by omega
  have h := constantCyclicMonomial_mem_functionFieldCyclicSpan P r 1
    (r.matrixRank - 1) hpred
  let a : FunctionField P := (1 + RatFunc.X)⁻¹
  have hsmul := (functionFieldCyclicSpan P r).smul_mem a h
  have heq :
      (⟨cyclicGeneratorInverseMatrix P r,
        cyclicGeneratorInverseMatrix_mem_cyclicAlgebra P r⟩ :
        CyclicAlgebra P r) =
      a • ⟨constantMatrix P r 1 *
          cyclicGeneratorMatrix P r ^ (r.matrixRank - 1),
        (CyclicAlgebra P r).mul_mem
          (constantMatrix_mem_cyclicAlgebra P r 1)
          ((CyclicAlgebra P r).pow_mem
            (cyclicGeneratorMatrix_mem_cyclicAlgebra P r)
            (r.matrixRank - 1))⟩ := by
    apply Subtype.ext
    change cyclicGeneratorInverseMatrix P r =
      a • (constantMatrix P r 1 *
        cyclicGeneratorMatrix P r ^ (r.matrixRank - 1))
    calc
      cyclicGeneratorInverseMatrix P r =
          (onePlusY P r)⁻¹ •
            cyclicGeneratorMatrix P r ^ (r.matrixRank - 1) :=
        cyclicGeneratorInverseMatrix_eq_inv_smul_pow_pred P r
      _ = a • cyclicGeneratorMatrix P r ^ (r.matrixRank - 1) := by
        simpa only [a] using onePlusYInv_smul_eq_functionField_smul P r
          (cyclicGeneratorMatrix P r ^ (r.matrixRank - 1))
      _ = _ := by simp [a, ← constantMatrixEmbedding_apply]
  simpa only [heq] using hsmul
theorem functionFieldCyclicSpan_eq_top
    (P : BasePrime) (r : Rank) :
    functionFieldCyclicSpan P r = ⊤ := by
  apply top_unique
  intro x _
  apply Algebra.adjoin_induction
    (R := FunctionField P)
    (s := Set.range (constantMatrix P r) ∪
      {cyclicGeneratorMatrix P r, cyclicGeneratorInverseMatrix P r})
    (p := fun M hM =>
      (⟨M, hM⟩ : CyclicAlgebra P r) ∈ functionFieldCyclicSpan P r)
  · intro M hM
    rcases hM with hM | hM
    · obtain ⟨c, rfl⟩ := hM
      exact constantMatrix_mem_functionFieldCyclicSpan P r c
    · rcases hM with (rfl | hM)
      · exact cyclicGeneratorMatrix_mem_functionFieldCyclicSpan P r
      · rw [Set.mem_singleton_iff] at hM
        subst M
        exact cyclicGeneratorInverseMatrix_mem_functionFieldCyclicSpan P r
  · intro a
    exact (functionFieldCyclicSpanSubalgebra P r).algebraMap_mem a
  · intro M N hM hN hMi hNi
    exact (functionFieldCyclicSpanSubalgebra P r).add_mem hMi hNi
  · intro M N hM hN hMi hNi
    exact (functionFieldCyclicSpanSubalgebra P r).mul_mem hMi hNi
noncomputable def functionFieldCyclicBasis
    (P : BasePrime) (r : Rank) :
    Module.Basis (Fin r.matrixRank × Fin r.matrixRank)
      (FunctionField P) (CyclicAlgebra P r) :=
  Module.Basis.mk (functionFieldCyclicBasisVector_linearIndependent P r)
    (by
      change (⊤ : Submodule (FunctionField P) (CyclicAlgebra P r)) ≤
        functionFieldCyclicSpan P r
      rw [functionFieldCyclicSpan_eq_top])
end QEC.Coding.HighDimensionalExpander.CartwrightSteger


