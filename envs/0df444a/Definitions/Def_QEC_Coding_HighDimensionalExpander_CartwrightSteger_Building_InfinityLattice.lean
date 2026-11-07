-- Prove2me | Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityLattice
-- name    : QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityLattice
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T13:30:10.342752+00:00
-- url     : https://prove2.me/theorems/96eac7ca-c2cb-4220-a879-cc1493e0b206
-- title:
--   Infinity Lattice
-- statement:
--   Definitions and structural lemmas for Infinity Lattice, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityLattice.lean

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.FieldTheory.RatFunc.Valuation
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CongruenceLifting_residueTransvectionSpecial_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingCompactCyclicSemidirectHom_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingGeneratorNeighborAtEquiv_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingLatticeVertexMap_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerNormUnit_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantFrobenius_order
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrixHom_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrix_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_frobeniusPowerEquiv_apply
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
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_MatrixOrderLowerBound_add
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_MatrixOrderLowerBound_mul
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
noncomputable local instance _p2m_local_instance_a53544448f_18 (P : BasePrime) (r : Rank) :
    DecidableEq (SplittingFunctionField P r) := Classical.decEq _
noncomputable def InfinityCoefficientRing (P : BasePrime) (r : Rank) :=
  Algebra.adjoin (ConstantExtension P r)
    ({(splittingY P r)⁻¹} : Set (SplittingFunctionField P r))
noncomputable def infinityUniformizer (P : BasePrime) (r : Rank) :
    InfinityCoefficientRing P r :=
  ⟨(splittingY P r)⁻¹,
    Algebra.subset_adjoin (Set.mem_singleton ((splittingY P r)⁻¹))⟩
@[simp]
theorem infinityUniformizer_val (P : BasePrime) (r : Rank) :
    (infinityUniformizer P r : SplittingFunctionField P r) =
      (splittingY P r)⁻¹ :=
  rfl
def infinityCyclicBasisSet (P : BasePrime) (r : Rank) :
    Set (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r)) :=
  {X | ∃ (c : ConstantExtension P r) (k : ℕ),
    k < r.matrixRank ∧
      X = constantMatrix P r c * cyclicGeneratorMatrix P r ^ k}
theorem infinityCyclicBasisSet_eq_range
    (P : BasePrime) (r : Rank) :
    infinityCyclicBasisSet P r =
      Set.range (fun p : ConstantExtension P r × Fin r.matrixRank =>
        constantMatrix P r p.1 *
          cyclicGeneratorMatrix P r ^ (p.2 : ℕ)) := by
  ext X
  constructor
  · rintro ⟨c, k, hk, rfl⟩
    exact ⟨(c, ⟨k, hk⟩), rfl⟩
  · rintro ⟨⟨c, k⟩, rfl⟩
    exact ⟨c, k, k.isLt, rfl⟩
theorem infinityCyclicBasisSet_finite
    (P : BasePrime) (r : Rank) :
    (infinityCyclicBasisSet P r).Finite := by
  rw [infinityCyclicBasisSet_eq_range]
  exact Set.finite_range _
noncomputable def constantConjugateAlgHom
    (P : BasePrime) (r : Rank) (i : Fin r.matrixRank) :
    ConstantExtension P r →ₐ[BaseField P] SplittingFunctionField P r :=
  (IsScalarTower.toAlgHom (BaseField P) (ConstantExtension P r)
      (SplittingFunctionField P r)).comp
    ((constantFrobenius P r).symm ^ (i : ℕ)).toAlgHom
theorem constantConjugateAlgHom_injective
    (P : BasePrime) (r : Rank) :
    Function.Injective (constantConjugateAlgHom P r) := by
  intro i j hij
  have hpowers :
      (constantFrobenius P r).symm ^ (i : ℕ) =
        (constantFrobenius P r).symm ^ (j : ℕ) := by
    apply AlgEquiv.ext
    intro c
    apply (algebraMap (ConstantExtension P r)
      (SplittingFunctionField P r)).injective
    exact DFunLike.congr_fun hij c
  apply Fin.ext
  apply pow_injOn_Iio_orderOf (x := (constantFrobenius P r).symm)
  · change (i : ℕ) < orderOf ((constantFrobenius P r)⁻¹)
    rw [orderOf_inv, constantFrobenius_order]
    exact i.isLt
  · change (j : ℕ) < orderOf ((constantFrobenius P r)⁻¹)
    rw [orderOf_inv, constantFrobenius_order]
    exact j.isLt
  · exact hpowers
theorem constantConjugateAlgHom_linearIndependent
    (P : BasePrime) (r : Rank) :
    LinearIndependent (SplittingFunctionField P r)
      (fun i : Fin r.matrixRank =>
        (constantConjugateAlgHom P r i).toLinearMap) := by
  exact (linearIndependent_algHom_toLinearMap
    (BaseField P) (ConstantExtension P r)
      (SplittingFunctionField P r)).comp
        (constantConjugateAlgHom P r)
        (constantConjugateAlgHom_injective P r)
noncomputable def constantBasisEvaluationLinearMap
    (P : BasePrime) (r : Rank) :
    (ConstantExtension P r →ₗ[BaseField P] SplittingFunctionField P r) →ₗ[
        SplittingFunctionField P r]
      (Fin r.matrixRank → SplittingFunctionField P r) where
  toFun f i := f (constantBasis P r i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
theorem constantBasisEvaluationLinearMap_injective
    (P : BasePrime) (r : Rank) :
    Function.Injective (constantBasisEvaluationLinearMap P r) := by
  intro f g hfg
  apply (constantBasis P r).ext
  intro i
  exact congrFun hfg i
noncomputable def constantConjugateEvaluationMatrix
    (P : BasePrime) (r : Rank) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r) :=
  fun i j => constantConjugateAlgHom P r i (constantBasis P r j)
theorem constantConjugateEvaluationMatrix_rows_linearIndependent
    (P : BasePrime) (r : Rank) :
    LinearIndependent (SplittingFunctionField P r)
      (constantConjugateEvaluationMatrix P r) := by
  have hmap := (constantConjugateAlgHom_linearIndependent P r).map'
    (constantBasisEvaluationLinearMap P r)
    (LinearMap.ker_eq_bot.mpr
      (constantBasisEvaluationLinearMap_injective P r))
  exact hmap
theorem constantConjugateEvaluationMatrix_det_ne_zero
    (P : BasePrime) (r : Rank) :
    (constantConjugateEvaluationMatrix P r).det ≠ 0 := by
  have hunit : IsUnit (constantConjugateEvaluationMatrix P r) :=
    Matrix.linearIndependent_rows_iff_isUnit.mp
      (constantConjugateEvaluationMatrix_rows_linearIndependent P r)
  exact (Matrix.isUnit_iff_isUnit_det _ |>.mp hunit).ne_zero
theorem constantMatrix_eq_diagonal_conjugateEvaluation
    (P : BasePrime) (r : Rank) (c : ConstantExtension P r) :
    constantMatrix P r c = Matrix.diagonal
      (fun i => constantConjugateAlgHom P r i c) := by
  ext i j
  simp [constantMatrix, constantConjugateAlgHom]
theorem span_constantMatrix_fixedBasis_eq_range_diagonal
    (P : BasePrime) (r : Rank) :
    Submodule.span (SplittingFunctionField P r)
        (Set.range (fun j : Fin r.matrixRank =>
          constantMatrix P r (constantBasis P r j))) =
      LinearMap.range (Matrix.diagonalLinearMap (Fin r.matrixRank)
        (SplittingFunctionField P r) (SplittingFunctionField P r)) := by
  let D := Matrix.diagonalLinearMap (Fin r.matrixRank)
    (SplittingFunctionField P r) (SplittingFunctionField P r)
  have hcols : LinearIndependent (SplittingFunctionField P r)
      (constantConjugateEvaluationMatrix P r).col :=
    Matrix.linearIndependent_cols_of_det_ne_zero
      (constantConjugateEvaluationMatrix_det_ne_zero P r)
  have hspan : Submodule.span (SplittingFunctionField P r)
      (Set.range (constantConjugateEvaluationMatrix P r).col) = ⊤ := by
    apply hcols.span_eq_top_of_card_eq_finrank
    simp
  have hfamily :
      (fun j : Fin r.matrixRank =>
        constantMatrix P r (constantBasis P r j)) =
      D ∘ (constantConjugateEvaluationMatrix P r).col := by
    funext j
    rw [constantMatrix_eq_diagonal_conjugateEvaluation]
    change Matrix.diagonal _ =
      Matrix.diagonal ((constantConjugateEvaluationMatrix P r).col j)
    congr 1
  rw [hfamily, Set.range_comp, ← Submodule.map_span, hspan,
    Submodule.map_top]
noncomputable def splittingCyclicBasisVector
    (P : BasePrime) (r : Rank)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r) :=
  constantMatrix P r (constantBasis P r p.1) *
    cyclicGeneratorMatrix P r ^ (p.2 : ℕ)
theorem diagonal_mul_cyclicGenerator_pow_mem_span_splittingCyclicBasis
    (P : BasePrime) (r : Rank)
    (v : Fin r.matrixRank → SplittingFunctionField P r)
    (k : Fin r.matrixRank) :
    Matrix.diagonal v * cyclicGeneratorMatrix P r ^ (k : ℕ) ∈
      Submodule.span (SplittingFunctionField P r)
        (Set.range (splittingCyclicBasisVector P r)) := by
  let target := Submodule.span (SplittingFunctionField P r)
    (Set.range (splittingCyclicBasisVector P r))
  have hDiagonal : Matrix.diagonal v ∈
      Submodule.span (SplittingFunctionField P r)
        (Set.range (fun j : Fin r.matrixRank =>
          constantMatrix P r (constantBasis P r j))) := by
    rw [span_constantMatrix_fixedBasis_eq_range_diagonal]
    exact ⟨v, rfl⟩
  refine Submodule.span_induction
    (p := fun D _ => D * cyclicGeneratorMatrix P r ^ (k : ℕ) ∈ target)
    ?basis ?zero ?add ?smul hDiagonal
  · intro D hD
    obtain ⟨j, rfl⟩ := hD
    exact Submodule.subset_span ⟨(j, k), rfl⟩
  · simp [target]
  · intro A B _ _ hA hB
    rw [add_mul]
    exact target.add_mem hA hB
  · intro a A _ hA
    rw [smul_mul_assoc]
    exact target.smul_mem a hA
theorem span_splittingCyclicBasisVector_eq_top
    (P : BasePrime) (r : Rank) :
    Submodule.span (SplittingFunctionField P r)
      (Set.range (splittingCyclicBasisVector P r)) = ⊤ := by
  apply top_unique
  intro A _
  cases r with
  | three =>
      simp only [Rank.matrixRank_three] at A ⊢
      let a := onePlusY P .three
      let Z : Matrix (Fin 3) (Fin 3) (SplittingFunctionField P .three) :=
        !![0, 0, a; 1, 0, 0; 0, 1, 0]
      let v0 : Fin 3 → SplittingFunctionField P .three :=
        ![A 0 0, A 1 1, A 2 2]
      let v1 : Fin 3 → SplittingFunctionField P .three :=
        ![a⁻¹ * A 0 2, A 1 0, A 2 1]
      let v2 : Fin 3 → SplittingFunctionField P .three :=
        ![a⁻¹ * A 0 1, a⁻¹ * A 1 2, A 2 0]
      have h0 := diagonal_mul_cyclicGenerator_pow_mem_span_splittingCyclicBasis
        P .three v0 (0 : Fin 3)
      have h1 := diagonal_mul_cyclicGenerator_pow_mem_span_splittingCyclicBasis
        P .three v1 (1 : Fin 3)
      have h2 := diagonal_mul_cyclicGenerator_pow_mem_span_splittingCyclicBasis
        P .three v2 (2 : Fin 3)
      have hsum := (Submodule.span (SplittingFunctionField P .three)
        (Set.range (splittingCyclicBasisVector P .three))).add_mem
          ((Submodule.span (SplittingFunctionField P .three)
            (Set.range (splittingCyclicBasisVector P .three))).add_mem h0 h1) h2
      have hdecomp : A = Matrix.diagonal v0 * Z ^ 0 +
          Matrix.diagonal v1 * Z ^ 1 + Matrix.diagonal v2 * Z ^ 2 := by
        dsimp [v0, v1, v2, Z, a]
        simp only [pow_zero, pow_one, pow_two]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_succ] <;>
          field_simp [onePlusY_ne_zero]
      rw [hdecomp]
      exact hsum
  | four =>
      simp only [Rank.matrixRank_four] at A ⊢
      let a := onePlusY P .four
      let Z : Matrix (Fin 4) (Fin 4) (SplittingFunctionField P .four) :=
        !![0, 0, 0, a; 1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0]
      let v0 : Fin 4 → SplittingFunctionField P .four :=
        ![A 0 0, A 1 1, A 2 2, A 3 3]
      let v1 : Fin 4 → SplittingFunctionField P .four :=
        ![a⁻¹ * A 0 3, A 1 0, A 2 1, A 3 2]
      let v2 : Fin 4 → SplittingFunctionField P .four :=
        ![a⁻¹ * A 0 2, a⁻¹ * A 1 3, A 2 0, A 3 1]
      let v3 : Fin 4 → SplittingFunctionField P .four :=
        ![a⁻¹ * A 0 1, a⁻¹ * A 1 2, a⁻¹ * A 2 3, A 3 0]
      have h0 := diagonal_mul_cyclicGenerator_pow_mem_span_splittingCyclicBasis
        P .four v0 (0 : Fin 4)
      have h1 := diagonal_mul_cyclicGenerator_pow_mem_span_splittingCyclicBasis
        P .four v1 (1 : Fin 4)
      have h2 := diagonal_mul_cyclicGenerator_pow_mem_span_splittingCyclicBasis
        P .four v2 (2 : Fin 4)
      have h3 := diagonal_mul_cyclicGenerator_pow_mem_span_splittingCyclicBasis
        P .four v3 (3 : Fin 4)
      let target := Submodule.span (SplittingFunctionField P .four)
        (Set.range (splittingCyclicBasisVector P .four))
      have hsum := target.add_mem
        (target.add_mem (target.add_mem h0 h1) h2) h3
      have hdecomp : A = Matrix.diagonal v0 * Z ^ 0 +
          Matrix.diagonal v1 * Z ^ 1 + Matrix.diagonal v2 * Z ^ 2 +
            Matrix.diagonal v3 * Z ^ 3 := by
        dsimp [v0, v1, v2, v3, Z, a]
        simp only [pow_zero, pow_one, pow_two, pow_three]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_succ] <;>
          field_simp [onePlusY_ne_zero]
      rw [hdecomp]
      exact hsum
theorem splittingCyclicBasisVector_linearIndependent
    (P : BasePrime) (r : Rank) :
    LinearIndependent (SplittingFunctionField P r)
      (splittingCyclicBasisVector P r) := by
  apply linearIndependent_of_top_le_span_of_card_eq_finrank
  · rw [span_splittingCyclicBasisVector_eq_top]
  · simp [Module.finrank_matrix]
noncomputable def splittingCyclicBasis
    (P : BasePrime) (r : Rank) :
    Module.Basis (Fin r.matrixRank × Fin r.matrixRank)
      (SplittingFunctionField P r)
      (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r)) :=
  Module.Basis.mk (splittingCyclicBasisVector_linearIndependent P r)
    (by rw [span_splittingCyclicBasisVector_eq_top])
@[simp]
theorem splittingCyclicBasis_apply
    (P : BasePrime) (r : Rank)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    splittingCyclicBasis P r p = splittingCyclicBasisVector P r p :=
  by simp [splittingCyclicBasis]
noncomputable def InfinityCyclicLattice (P : BasePrime) (r : Rank) :
    Submodule (InfinityCoefficientRing P r)
      (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r)) :=
  Submodule.span (InfinityCoefficientRing P r)
    (infinityCyclicBasisSet P r)
noncomputable instance infinityCyclicLattice_moduleFinite
    (P : BasePrime) (r : Rank) :
    Module.Finite (InfinityCoefficientRing P r)
      (InfinityCyclicLattice P r) :=
  Module.Finite.span_of_finite (InfinityCoefficientRing P r)
    (infinityCyclicBasisSet_finite P r)
theorem cyclicMonomial_mem_infinityCyclicLattice
    (P : BasePrime) (r : Rank) (c : ConstantExtension P r)
    (k : ℕ) (hk : k < r.matrixRank) :
    constantMatrix P r c * cyclicGeneratorMatrix P r ^ k ∈
      InfinityCyclicLattice P r :=
  Submodule.subset_span ⟨c, k, hk, rfl⟩
noncomputable def infinityCyclicFixedBasisVector
    (P : BasePrime) (r : Rank)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    InfinityCyclicLattice P r :=
  ⟨splittingCyclicBasisVector P r p,
    cyclicMonomial_mem_infinityCyclicLattice P r
      (constantBasis P r p.1) (p.2 : ℕ) p.2.isLt⟩
@[simp]
theorem infinityCyclicFixedBasisVector_coe
    (P : BasePrime) (r : Rank)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    (infinityCyclicFixedBasisVector P r p :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r)) =
      splittingCyclicBasisVector P r p :=
  rfl
theorem infinityCoefficientRing_smul_one_injective
    (P : BasePrime) (r : Rank) :
    Function.Injective (fun a : InfinityCoefficientRing P r =>
      a • (1 : SplittingFunctionField P r)) := by
  intro a b hab
  apply Subtype.ext
  simpa using hab
theorem splittingCyclicBasisVector_linearIndependent_over_infinityRing
    (P : BasePrime) (r : Rank) :
    LinearIndependent (InfinityCoefficientRing P r)
      (splittingCyclicBasisVector P r) :=
  (splittingCyclicBasisVector_linearIndependent P r).restrict_scalars
    (infinityCoefficientRing_smul_one_injective P r)
theorem infinityCyclicFixedBasisVector_linearIndependent
    (P : BasePrime) (r : Rank) :
    LinearIndependent (InfinityCoefficientRing P r)
      (infinityCyclicFixedBasisVector P r) := by
  apply LinearIndependent.of_comp (InfinityCyclicLattice P r).subtype
  exact splittingCyclicBasisVector_linearIndependent_over_infinityRing P r
theorem constantMatrix_baseField_smul
    (P : BasePrime) (r : Rank) (a : BaseField P)
    (c : ConstantExtension P r) :
    constantMatrix P r (a • c) =
      (algebraMap (BaseField P) (InfinityCoefficientRing P r) a) •
        constantMatrix P r c := by
  rw [constantMatrix_eq_diagonal_conjugateEvaluation]
  rw [constantMatrix_eq_diagonal_conjugateEvaluation]
  ext i j
  by_cases h : i = j <;> simp [Algebra.smul_def, h]
theorem cyclicMonomial_mem_span_splittingCyclicBasisVector
    (P : BasePrime) (r : Rank) (c : ConstantExtension P r)
    (k : ℕ) (hk : k < r.matrixRank) :
    constantMatrix P r c * cyclicGeneratorMatrix P r ^ k ∈
      Submodule.span (InfinityCoefficientRing P r)
        (Set.range (splittingCyclicBasisVector P r)) := by
  let k' : Fin r.matrixRank := ⟨k, hk⟩
  have hc :
      constantMatrix P r c * cyclicGeneratorMatrix P r ^ k =
        ∑ j, (algebraMap (BaseField P) (InfinityCoefficientRing P r)
          ((constantBasis P r).repr c j)) •
            splittingCyclicBasisVector P r (j, k') := by
    conv_lhs =>
      rw [← (constantBasis P r).sum_repr c]
    rw [← constantMatrixEmbedding_apply]
    rw [map_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [constantMatrixEmbedding_apply, constantMatrix_baseField_smul]
    rw [smul_mul_assoc]
    rfl
  rw [hc]
  apply Submodule.sum_mem
  intro j _
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨(j, k'), rfl⟩
theorem map_span_infinityCyclicFixedBasisVector
    (P : BasePrime) (r : Rank) :
    Submodule.map (InfinityCyclicLattice P r).subtype
        (Submodule.span (InfinityCoefficientRing P r)
          (Set.range (infinityCyclicFixedBasisVector P r))) =
      Submodule.span (InfinityCoefficientRing P r)
        (Set.range (splittingCyclicBasisVector P r)) := by
  rw [Submodule.map_span]
  congr 1
  ext X
  simp
theorem span_splittingCyclicBasisVector_eq_infinityCyclicLattice
    (P : BasePrime) (r : Rank) :
    Submodule.span (InfinityCoefficientRing P r)
        (Set.range (splittingCyclicBasisVector P r)) =
      InfinityCyclicLattice P r := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro X ⟨⟨j, k⟩, rfl⟩
    exact cyclicMonomial_mem_infinityCyclicLattice P r
      (constantBasis P r j) (k : ℕ) k.isLt
  · rw [InfinityCyclicLattice]
    apply Submodule.span_le.mpr
    intro X hX
    rcases hX with ⟨c, k, hk, rfl⟩
    exact cyclicMonomial_mem_span_splittingCyclicBasisVector P r c k hk
theorem span_infinityCyclicFixedBasisVector_eq_top
    (P : BasePrime) (r : Rank) :
    Submodule.span (InfinityCoefficientRing P r)
      (Set.range (infinityCyclicFixedBasisVector P r)) = ⊤ := by
  apply top_unique
  intro X _
  have hX : (X : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r)) ∈
      Submodule.span (InfinityCoefficientRing P r)
        (Set.range (splittingCyclicBasisVector P r)) := by
    rw [span_splittingCyclicBasisVector_eq_infinityCyclicLattice]
    exact X.property
  rw [← map_span_infinityCyclicFixedBasisVector] at hX
  rcases hX with ⟨Y, hY, hYX⟩
  have : Y = X := Subtype.ext hYX
  simpa [this] using hY
noncomputable def infinityCyclicBasis
    (P : BasePrime) (r : Rank) :
    Module.Basis (Fin r.matrixRank × Fin r.matrixRank)
      (InfinityCoefficientRing P r) (InfinityCyclicLattice P r) :=
  Module.Basis.mk (infinityCyclicFixedBasisVector_linearIndependent P r)
    (by rw [span_infinityCyclicFixedBasisVector_eq_top])
@[simp]
theorem infinityCyclicBasis_apply
    (P : BasePrime) (r : Rank)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    infinityCyclicBasis P r p = infinityCyclicFixedBasisVector P r p := by
  simp [infinityCyclicBasis]
theorem splittingCyclicBasis_repr_coe
    (P : BasePrime) (r : Rank) (X : InfinityCyclicLattice P r)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    (splittingCyclicBasis P r).repr X.1 p =
      algebraMap (InfinityCoefficientRing P r)
        (SplittingFunctionField P r) ((infinityCyclicBasis P r).repr X p) := by
  have h := congrArg Subtype.val ((infinityCyclicBasis P r).sum_repr X)
  have h' :
      (∑ q, (((infinityCyclicBasis P r).repr X q :
          InfinityCoefficientRing P r) : SplittingFunctionField P r) •
          splittingCyclicBasisVector P r q) = X.1 := by
    simp [infinityCyclicBasis_apply, infinityCyclicFixedBasisVector_coe] at h
    exact h
  have hp := congrArg ((splittingCyclicBasis P r).coord p) h'
  have hrepr (q : Fin r.matrixRank × Fin r.matrixRank) :
      (splittingCyclicBasis P r).coord p
          (splittingCyclicBasisVector P r q) = if q = p then 1 else 0 := by
    have hq := congrArg
      (fun f : (Fin r.matrixRank × Fin r.matrixRank) →₀
        SplittingFunctionField P r => f p)
      ((splittingCyclicBasis P r).repr_self q)
    simp only [splittingCyclicBasis_apply, Finsupp.single_apply] at hq
    exact hq
  simp only [map_sum, map_smul, smul_eq_mul] at hp
  simp_rw [hrepr] at hp
  simpa using hp.symm
def matrixTwoSidedMultiplicationLinearMap
    {K n : Type*} [Field K] [Fintype n] [DecidableEq n]
    (A B : Matrix n n K) : Matrix n n K →ₗ[K] Matrix n n K where
  toFun X := A * X * B
  map_add' X Y := by rw [mul_add, add_mul]
  map_smul' a X := by
    change A * (a • X) * B = a • (A * X * B)
    rw [mul_smul_comm, smul_mul_assoc]
@[simp]
theorem matrixTwoSidedMultiplicationLinearMap_apply
    {K n : Type*} [Field K] [Fintype n] [DecidableEq n]
    (A B X : Matrix n n K) :
    matrixTwoSidedMultiplicationLinearMap A B X = A * X * B :=
  rfl
theorem toMatrix_matrixTwoSidedMultiplicationLinearMap
    {K n : Type*} [Field K] [Fintype n] [DecidableEq n]
    (A B : Matrix n n K) :
    LinearMap.toMatrix (Matrix.stdBasis K n n) (Matrix.stdBasis K n n)
      (matrixTwoSidedMultiplicationLinearMap A B) =
        Matrix.kronecker A B.transpose := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp only [LinearMap.toMatrix_apply,
    matrixTwoSidedMultiplicationLinearMap_apply,
    Matrix.stdBasis_eq_single, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.transpose_apply]
  rw [show (Matrix.stdBasis K n n).repr
      (A * (Matrix.single k l (1 : K) : Matrix n n K) * B) (i, j) =
        (A * (Matrix.single k l (1 : K) : Matrix n n K) * B) i j by
      simp [Matrix.stdBasis]]
  rw [Matrix.mul_apply, Finset.sum_eq_single l]
  · simp
  · intro x _ hxl
    rw [Matrix.mul_single_apply_of_ne (1 : K) k l i x hxl A]
    simp
  · simp
theorem det_matrixTwoSidedMultiplicationLinearMap
    {K n : Type*} [Field K] [Fintype n] [DecidableEq n]
    (A B : Matrix n n K) :
    LinearMap.det (matrixTwoSidedMultiplicationLinearMap A B) =
      A.det ^ Fintype.card n * B.det ^ Fintype.card n := by
  rw [← LinearMap.det_toMatrix (Matrix.stdBasis K n n)]
  rw [toMatrix_matrixTwoSidedMultiplicationLinearMap]
  have h := Matrix.det_kronecker A B.transpose
  rw [Matrix.det_transpose] at h
  exact h
theorem det_matrixConjugationLinearMap
    {K n : Type*} [Field K] [Fintype n] [DecidableEq n]
    (g : (Matrix n n K)ˣ) :
    LinearMap.det (matrixTwoSidedMultiplicationLinearMap
      (g : Matrix n n K) (g⁻¹ : Matrix n n K)) = 1 := by
  rw [det_matrixTwoSidedMultiplicationLinearMap, ← mul_pow]
  have hdet : Matrix.det (g : Matrix n n K) *
      Matrix.det (g⁻¹ : Matrix n n K) = 1 := by
    rw [← Matrix.det_mul]
    simp
  rw [hdet, one_pow]
theorem Submodule.mem_of_map_mem_of_toMatrix_det_isUnit
    {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι R M) (f : M →ₗ[R] M) (N : Submodule R M)
    (hf : ∀ y, y ∈ N → f y ∈ N)
    (hdet : IsUnit (LinearMap.toMatrix b b f).det)
    {x : M} (hfx : f x ∈ N) : x ∈ N := by
  letI : Module.Free R M := Module.Free.of_basis b
  letI : Module.Finite R M := Module.Finite.of_basis b
  have hpow : ∀ (n : ℕ) {y : M}, y ∈ N → (f ^ n) y ∈ N := by
    intro n
    induction n with
    | zero =>
        intro y hy
        simpa using hy
    | succ n ih =>
        intro y hy
        simpa [pow_succ] using ih (hf y hy)
  have hpoly : ∀ (p : Polynomial R) {y : M},
      y ∈ N → Polynomial.aeval f p y ∈ N := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
        intro y hy
        rw [Polynomial.aeval_add]
        exact N.add_mem (hp hy) (hq hy)
    | monomial n a =>
        intro y hy
        rw [Polynomial.aeval_monomial]
        change a • (f ^ n) y ∈ N
        exact N.smul_mem a (hpow n hy)
  let q := f.charpoly.divX
  have hqfx : Polynomial.aeval f q (f x) ∈ N := hpoly q hfx
  have hdecomp := congrArg (Polynomial.aeval f)
    (Polynomial.divX_mul_X_add f.charpoly)
  have hcayley := LinearMap.aeval_self_charpoly f
  simp only [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C,
    hcayley] at hdecomp
  have hxzero := DFunLike.congr_fun hdecomp x
  have hc0x : f.charpoly.coeff 0 • x ∈ N := by
    have hneg := N.neg_mem hqfx
    convert hneg using 1
    change f.charpoly.coeff 0 • x = -Polynomial.aeval f q (f x)
    change Polynomial.aeval f q (f x) + f.charpoly.coeff 0 • x = 0 at hxzero
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact hxzero
  have hdet' : IsUnit (LinearMap.det f) := by
    rw [← LinearMap.det_toMatrix b]
    exact hdet
  have hc0 : IsUnit (f.charpoly.coeff 0) := by
    rw [LinearMap.det_eq_sign_charpoly_coeff] at hdet'
    exact (IsUnit.mul_iff.mp hdet').2
  rcases hc0 with ⟨u, hu⟩
  rw [← hu] at hc0x
  have := N.smul_mem (↑(u⁻¹) : R) hc0x
  simpa [smul_smul] using this
noncomputable def infinityConjugationLinearMap
    (P : BasePrime) (r : Rank)
    (g : Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (SplittingFunctionField P r)) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r) →ₗ[InfinityCoefficientRing P r]
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r) where
  toFun X :=
    (g : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r)) * X *
      ((g⁻¹ : Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (SplittingFunctionField P r)) :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (SplittingFunctionField P r))
  map_add' X Y := by
    rw [mul_add, add_mul]
  map_smul' a X := by
    change
      (g : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (SplittingFunctionField P r)) *
          ((a : SplittingFunctionField P r) • X) *
          (((g⁻¹ : Matrix.GeneralLinearGroup (Fin r.matrixRank)
              (SplittingFunctionField P r))) :
            Matrix (Fin r.matrixRank) (Fin r.matrixRank)
              (SplittingFunctionField P r)) = _
    rw [mul_smul_comm, smul_mul_assoc]
    rfl
def PreservesInfinityCyclicLattice
    (P : BasePrime) (r : Rank)
    (g : Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (SplittingFunctionField P r)) : Prop :=
  ∀ X, X ∈ InfinityCyclicLattice P r →
    infinityConjugationLinearMap P r g X ∈ InfinityCyclicLattice P r
@[simp]
theorem infinityConjugationLinearMap_one_apply
    (P : BasePrime) (r : Rank)
    (X : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r)) :
    infinityConjugationLinearMap P r 1 X = X := by
  simp [infinityConjugationLinearMap]
theorem infinityConjugationLinearMap_mul_apply
    (P : BasePrime) (r : Rank)
    (g h : Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (SplittingFunctionField P r))
    (X : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r)) :
    infinityConjugationLinearMap P r (g * h) X =
      infinityConjugationLinearMap P r g
        (infinityConjugationLinearMap P r h X) := by
  simp only [infinityConjugationLinearMap, LinearMap.coe_mk,
    AddHom.coe_mk, Units.val_mul, mul_inv_rev]
  noncomm_ring
theorem preservesInfinityCyclicLattice_one
    (P : BasePrime) (r : Rank) :
    PreservesInfinityCyclicLattice P r 1 := by
  intro X hX
  simpa using hX
theorem PreservesInfinityCyclicLattice.mul
    (P : BasePrime) (r : Rank)
    {g h : Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (SplittingFunctionField P r)}
    (hg : PreservesInfinityCyclicLattice P r g)
    (hh : PreservesInfinityCyclicLattice P r h) :
    PreservesInfinityCyclicLattice P r (g * h) := by
  intro X hX
  rw [infinityConjugationLinearMap_mul_apply]
  exact hg _ (hh X hX)
noncomputable def infinityLatticeEndomorphism
    (P : BasePrime) (r : Rank)
    (g : Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (SplittingFunctionField P r))
    (hg : PreservesInfinityCyclicLattice P r g) :
    InfinityCyclicLattice P r →ₗ[InfinityCoefficientRing P r]
      InfinityCyclicLattice P r where
  toFun X := ⟨infinityConjugationLinearMap P r g X.1, hg X.1 X.2⟩
  map_add' X Y := by
    apply Subtype.ext
    exact map_add (infinityConjugationLinearMap P r g) X.1 Y.1
  map_smul' a X := by
    apply Subtype.ext
    exact map_smul (infinityConjugationLinearMap P r g) a X.1
@[simp]
theorem infinityLatticeEndomorphism_coe
    (P : BasePrime) (r : Rank)
    (g : Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (SplittingFunctionField P r))
    (hg : PreservesInfinityCyclicLattice P r g)
    (X : InfinityCyclicLattice P r) :
    (infinityLatticeEndomorphism P r g hg X :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r)) =
      infinityConjugationLinearMap P r g X.1 :=
  rfl
theorem map_toMatrix_infinityLatticeEndomorphism
    (P : BasePrime) (r : Rank)
    (g : Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (SplittingFunctionField P r))
    (hg : PreservesInfinityCyclicLattice P r g) :
    (LinearMap.toMatrix (infinityCyclicBasis P r) (infinityCyclicBasis P r)
        (infinityLatticeEndomorphism P r g hg)).map
        (algebraMap (InfinityCoefficientRing P r)
          (SplittingFunctionField P r)) =
      LinearMap.toMatrix (splittingCyclicBasis P r) (splittingCyclicBasis P r)
        (matrixTwoSidedMultiplicationLinearMap
          (g : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (SplittingFunctionField P r))
          (g⁻¹ : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (SplittingFunctionField P r))) := by
  ext p q
  rw [Matrix.map_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply]
  have hcoord := splittingCyclicBasis_repr_coe P r
    (infinityLatticeEndomorphism P r g hg (infinityCyclicBasis P r q)) p
  simpa [matrixTwoSidedMultiplicationLinearMap_apply,
    infinityLatticeEndomorphism_coe, infinityConjugationLinearMap,
    infinityCyclicBasis_apply, infinityCyclicFixedBasisVector_coe,
    splittingCyclicBasis_apply] using hcoord.symm
theorem infinityLatticeEndomorphism_toMatrix_det
    (P : BasePrime) (r : Rank)
    (g : Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (SplittingFunctionField P r))
    (hg : PreservesInfinityCyclicLattice P r g) :
    (LinearMap.toMatrix (infinityCyclicBasis P r) (infinityCyclicBasis P r)
      (infinityLatticeEndomorphism P r g hg)).det = 1 := by
  apply Subtype.ext
  change algebraMap (InfinityCoefficientRing P r)
      (SplittingFunctionField P r) _ =
    algebraMap (InfinityCoefficientRing P r)
      (SplittingFunctionField P r) 1
  rw [map_one, RingHom.map_det]
  change ((LinearMap.toMatrix (infinityCyclicBasis P r)
      (infinityCyclicBasis P r) (infinityLatticeEndomorphism P r g hg)).map
        (algebraMap (InfinityCoefficientRing P r)
          (SplittingFunctionField P r))).det = 1
  rw [map_toMatrix_infinityLatticeEndomorphism]
  rw [LinearMap.det_toMatrix]
  exact det_matrixConjugationLinearMap g
theorem PreservesInfinityCyclicLattice.inv
    (P : BasePrime) (r : Rank)
    {g : Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (SplittingFunctionField P r)}
    (hg : PreservesInfinityCyclicLattice P r g) :
    PreservesInfinityCyclicLattice P r g⁻¹ := by
  intro X hX
  have hunit : IsUnit
      (LinearMap.toMatrix (infinityCyclicBasis P r) (infinityCyclicBasis P r)
        (infinityLatticeEndomorphism P r g hg)).det := by
    rw [infinityLatticeEndomorphism_toMatrix_det]
    exact isUnit_one
  let e : InfinityCyclicLattice P r ≃ₗ[InfinityCoefficientRing P r]
      InfinityCyclicLattice P r := LinearEquiv.ofIsUnitDet hunit
  let XL : InfinityCyclicLattice P r := ⟨X, hX⟩
  obtain ⟨Y, hY⟩ := e.surjective XL
  have hfY : infinityLatticeEndomorphism P r g hg Y = XL := by
    simpa [e] using hY
  have hAmbient := congrArg Subtype.val hfY
  have hInverse := congrArg (infinityConjugationLinearMap P r g⁻¹) hAmbient
  have hEq : Y.1 = infinityConjugationLinearMap P r g⁻¹ X := by
    simpa [← infinityConjugationLinearMap_mul_apply] using hInverse
  rw [← hEq]
  exact Y.property
noncomputable def InfinityLatticePreserverMonoid
    (P : BasePrime) (r : Rank) :
    Submonoid (Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (SplittingFunctionField P r)) where
  carrier := {g | PreservesInfinityCyclicLattice P r g}
  one_mem' := preservesInfinityCyclicLattice_one P r
  mul_mem' := fun hg hh => hg.mul P r hh
noncomputable def InfinityCyclicFiltration
    (P : BasePrime) (r : Rank) (bound : ℕ) :
    Submodule (InfinityCoefficientRing P r)
      (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r)) :=
  Submodule.span (InfinityCoefficientRing P r)
    {X | ∃ (c : ConstantExtension P r) (k : ℕ),
      k < bound ∧ k < r.matrixRank ∧
        X = constantMatrix P r c * cyclicGeneratorMatrix P r ^ k}
noncomputable def InfinityUniformizerMultiple
    (P : BasePrime) (r : Rank) :
    Submodule (InfinityCoefficientRing P r)
      (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r)) :=
  Submodule.span (InfinityCoefficientRing P r)
    {X | ∃ Y, Y ∈ InfinityCyclicLattice P r ∧
      X = (infinityUniformizer P r) • Y}
theorem infinityUniformizer_smul_mem_multiple
    (P : BasePrime) (r : Rank)
    {X : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r)}
    (hX : X ∈ InfinityCyclicLattice P r) :
    (infinityUniformizer P r) • X ∈
      InfinityUniformizerMultiple P r :=
  Submodule.subset_span ⟨X, hX, rfl⟩
def HasUpperUnipotentInfinityResidue
    (P : BasePrime) (r : Rank)
    (g : Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (SplittingFunctionField P r)) : Prop :=
  PreservesInfinityCyclicLattice P r g ∧
    ∀ (k : Fin r.matrixRank) (ζ : ConstantExtension P r),
      infinityConjugationLinearMap P r g
          (constantMatrix P r ζ * cyclicGeneratorMatrix P r ^ (k : ℕ)) -
          (constantMatrix P r ζ * cyclicGeneratorMatrix P r ^ (k : ℕ)) ∈
        InfinityCyclicFiltration P r (k : ℕ) ⊔
          InfinityUniformizerMultiple P r
theorem infinityCyclicFiltration_mono
    (P : BasePrime) (r : Rank) {a b : ℕ} (hab : a ≤ b) :
    InfinityCyclicFiltration P r a ≤ InfinityCyclicFiltration P r b := by
  apply Submodule.span_mono
  rintro X ⟨c, k, hka, hkr, rfl⟩
  exact ⟨c, k, lt_of_lt_of_le hka hab, hkr, rfl⟩
theorem HasUpperUnipotentInfinityResidue.deviation_mem_filtration
    (P : BasePrime) (r : Rank)
    {g : Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (SplittingFunctionField P r)}
    (hg : HasUpperUnipotentInfinityResidue P r g)
    (bound : ℕ)
    (X : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r))
    (hX : X ∈ InfinityCyclicFiltration P r bound) :
    infinityConjugationLinearMap P r g X - X ∈
      InfinityCyclicFiltration P r bound ⊔ InfinityUniformizerMultiple P r := by
  refine Submodule.span_induction
    (p := fun M _ => infinityConjugationLinearMap P r g M - M ∈
      InfinityCyclicFiltration P r bound ⊔ InfinityUniformizerMultiple P r)
    ?basis ?zero ?add ?smul hX
  · intro M hM
    obtain ⟨c, k, hkBound, hkRank, rfl⟩ := hM
    let kFin : Fin r.matrixRank := ⟨k, hkRank⟩
    have hk := hg.2 kFin c
    change infinityConjugationLinearMap P r g
          (constantMatrix P r c * cyclicGeneratorMatrix P r ^ k) -
        (constantMatrix P r c * cyclicGeneratorMatrix P r ^ k) ∈
      InfinityCyclicFiltration P r k ⊔ InfinityUniformizerMultiple P r at hk
    exact (sup_le_sup (infinityCyclicFiltration_mono P r
      (Nat.le_of_lt hkBound)) le_rfl) hk
  · change infinityConjugationLinearMap P r g 0 - 0 ∈ _
    simp
  · intro A B hA hB hdevA hdevB
    change infinityConjugationLinearMap P r g (A + B) - (A + B) ∈ _
    rw [map_add]
    have hadd := Submodule.add_mem
      (InfinityCyclicFiltration P r bound ⊔ InfinityUniformizerMultiple P r)
      hdevA hdevB
    convert hadd using 1
    abel
  · intro a A hA hdevA
    change infinityConjugationLinearMap P r g (a • A) - a • A ∈ _
    rw [map_smul, ← smul_sub]
    exact Submodule.smul_mem _ a hdevA
theorem PreservesInfinityCyclicLattice.map_mem_uniformizerMultiple
    (P : BasePrime) (r : Rank)
    {g : Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (SplittingFunctionField P r)}
    (hg : PreservesInfinityCyclicLattice P r g)
    (X : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r))
    (hX : X ∈ InfinityUniformizerMultiple P r) :
    infinityConjugationLinearMap P r g X ∈
      InfinityUniformizerMultiple P r := by
  refine Submodule.span_induction
    (p := fun M _ => infinityConjugationLinearMap P r g M ∈
      InfinityUniformizerMultiple P r)
    ?basis ?zero ?add ?smul hX
  · intro M hM
    obtain ⟨Y, hY, rfl⟩ := hM
    rw [map_smul]
    exact infinityUniformizer_smul_mem_multiple P r (hg Y hY)
  · change infinityConjugationLinearMap P r g 0 ∈ _
    simp
  · intro A B hA hB hmapA hmapB
    change infinityConjugationLinearMap P r g (A + B) ∈ _
    rw [map_add]
    exact Submodule.add_mem _ hmapA hmapB
  · intro a A hA hmapA
    change infinityConjugationLinearMap P r g (a • A) ∈ _
    rw [map_smul]
    exact Submodule.smul_mem _ a hmapA
theorem HasUpperUnipotentInfinityResidue.map_mem_filtration_sup
    (P : BasePrime) (r : Rank)
    {g : Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (SplittingFunctionField P r)}
    (hg : HasUpperUnipotentInfinityResidue P r g)
    (bound : ℕ)
    (X : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r))
    (hX : X ∈ InfinityCyclicFiltration P r bound ⊔
      InfinityUniformizerMultiple P r) :
    infinityConjugationLinearMap P r g X ∈
      InfinityCyclicFiltration P r bound ⊔
        InfinityUniformizerMultiple P r := by
  let target := InfinityCyclicFiltration P r bound ⊔
    InfinityUniformizerMultiple P r
  have hFiltration : InfinityCyclicFiltration P r bound ≤
      target.comap (infinityConjugationLinearMap P r g) := by
    intro Y hY
    have hdev := hg.deviation_mem_filtration P r bound Y hY
    have hYTarget : Y ∈ target := Submodule.mem_sup_left hY
    change infinityConjugationLinearMap P r g Y ∈ target
    have hadd := target.add_mem hYTarget hdev
    convert hadd using 1
    abel
  have hUniformizer : InfinityUniformizerMultiple P r ≤
      target.comap (infinityConjugationLinearMap P r g) := by
    intro Y hY
    exact Submodule.mem_sup_right
      (hg.1.map_mem_uniformizerMultiple P r Y hY)
  exact (sup_le hFiltration hUniformizer) hX
theorem hasUpperUnipotentInfinityResidue_one
    (P : BasePrime) (r : Rank) :
    HasUpperUnipotentInfinityResidue P r 1 := by
  refine ⟨preservesInfinityCyclicLattice_one P r, ?_⟩
  intro k ζ
  simp
theorem HasUpperUnipotentInfinityResidue.mul
    (P : BasePrime) (r : Rank)
    {g h : Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (SplittingFunctionField P r)}
    (hg : HasUpperUnipotentInfinityResidue P r g)
    (hh : HasUpperUnipotentInfinityResidue P r h) :
    HasUpperUnipotentInfinityResidue P r (g * h) := by
  refine ⟨hg.1.mul P r hh.1, ?_⟩
  intro k ζ
  let X := constantMatrix P r ζ * cyclicGeneratorMatrix P r ^ (k : ℕ)
  let target := InfinityCyclicFiltration P r (k : ℕ) ⊔
    InfinityUniformizerMultiple P r
  let D := infinityConjugationLinearMap P r h X - X
  have hD : D ∈ target := hh.2 k ζ
  have hgD : infinityConjugationLinearMap P r g D ∈ target :=
    hg.map_mem_filtration_sup P r (k : ℕ) D hD
  have hgX : infinityConjugationLinearMap P r g X - X ∈ target :=
    hg.2 k ζ
  have hsum := target.add_mem hgX hgD
  rw [infinityConjugationLinearMap_mul_apply]
  have hdecomp : infinityConjugationLinearMap P r h X = X + D := by
    change infinityConjugationLinearMap P r h X =
      X + (infinityConjugationLinearMap P r h X - X)
    abel
  rw [hdecomp, map_add]
  convert hsum using 1
  abel
theorem HasUpperUnipotentInfinityResidue.inv
    (P : BasePrime) (r : Rank)
    {g : Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (SplittingFunctionField P r)}
    (hg : HasUpperUnipotentInfinityResidue P r g) :
    HasUpperUnipotentInfinityResidue P r g⁻¹ := by
  have hginv := hg.1.inv P r
  refine ⟨hginv, ?_⟩
  intro k ζ
  let X := constantMatrix P r ζ * cyclicGeneratorMatrix P r ^ (k : ℕ)
  let target := InfinityCyclicFiltration P r (k : ℕ) ⊔
    InfinityUniformizerMultiple P r
  have hXL : X ∈ InfinityCyclicLattice P r :=
    cyclicMonomial_mem_infinityCyclicLattice P r ζ (k : ℕ) k.isLt
  let Y := infinityConjugationLinearMap P r g⁻¹ X
  have hYL : Y ∈ InfinityCyclicLattice P r := hginv X hXL
  let D := Y - X
  have hDL : D ∈ InfinityCyclicLattice P r :=
    (InfinityCyclicLattice P r).sub_mem hYL hXL
  let DL : InfinityCyclicLattice P r := ⟨D, hDL⟩
  let f := infinityLatticeEndomorphism P r g hg.1
  let N : Submodule (InfinityCoefficientRing P r)
      (InfinityCyclicLattice P r) :=
    target.comap (InfinityCyclicLattice P r).subtype
  have hfN : ∀ Z, Z ∈ N → f Z ∈ N := by
    intro Z hZ
    change infinityConjugationLinearMap P r g Z.1 ∈ target
    exact hg.map_mem_filtration_sup P r (k : ℕ) Z.1 hZ
  have hdet : IsUnit
      (LinearMap.toMatrix (infinityCyclicBasis P r) (infinityCyclicBasis P r)
        f).det := by
    dsimp [f]
    rw [infinityLatticeEndomorphism_toMatrix_det]
    exact isUnit_one
  have hdev := hg.2 k ζ
  have hneg : -(infinityConjugationLinearMap P r g X - X) ∈ target :=
    target.neg_mem hdev
  have hfDL : f DL ∈ N := by
    change infinityConjugationLinearMap P r g D ∈ target
    have hcomp : infinityConjugationLinearMap P r g Y = X := by
      dsimp [Y]
      simp [← infinityConjugationLinearMap_mul_apply]
    rw [show infinityConjugationLinearMap P r g D =
        infinityConjugationLinearMap P r g Y -
          infinityConjugationLinearMap P r g X by
      simp [D]]
    rw [hcomp]
    convert hneg using 1
    abel
  have hDN := Submodule.mem_of_map_mem_of_toMatrix_det_isUnit
    (infinityCyclicBasis P r) f N hfN hdet hfDL
  exact hDN
noncomputable def UpperUnipotentInfinityResidueMonoid
    (P : BasePrime) (r : Rank) :
    Submonoid (Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (SplittingFunctionField P r)) where
  carrier := {g | HasUpperUnipotentInfinityResidue P r g}
  one_mem' := hasUpperUnipotentInfinityResidue_one P r
  mul_mem' := fun hg hh => hg.mul P r hh
noncomputable def UpperUnipotentInfinityResidueSubgroup
    (P : BasePrime) (r : Rank) :
    Subgroup (Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (SplittingFunctionField P r)) where
  carrier := {g | HasUpperUnipotentInfinityResidue P r g}
  one_mem' := hasUpperUnipotentInfinityResidue_one P r
  mul_mem' := fun hg hh => hg.mul P r hh
  inv_mem' := fun hg => hg.inv P r
noncomputable def globalCompactNormalForm
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ) (j : ℕ) :
    Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (SplittingFunctionField P r) :=
  constantUnitMatrix P r u * cyclicGenerator P r ^ j
end QEC.Coding.HighDimensionalExpander.CartwrightSteger


