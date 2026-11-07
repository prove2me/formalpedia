-- Prove2me | Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_ResidueRepresentation
-- name    : QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_ResidueRepresentation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T12:33:07.53146+00:00
-- url     : https://prove2.me/theorems/18f5900b-91af-4618-9603-56bc2933264f
-- title:
--   Residue Representation
-- statement:
--   Definitions and structural lemmas for Residue Representation, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/ResidueRepresentation.lean

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_ResidueSelection
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Rank_two_le_matrixRank
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrix_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_frobeniusGL_pow_matrixRank
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueXAdjoinRootEquiv_root
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueYAdjoinRootEquiv_root
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueYMinpoly_natDegree
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_sourceYPolynomial_eq_pow_sub_one
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantUnitMatrix_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueXAdjoinRootEquiv_root
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueYAdjoinRootEquiv_root


set_option autoImplicit false
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
noncomputable def residueFrobeniusMatrix
    (P : BasePrime) (r : Rank) (level : Nat) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank) (ResidueField P r level) :=
  (frobeniusGL P r :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BaseField P)).map
    (algebraMap (BaseField P) (ResidueField P r level))
noncomputable def residueFrobeniusGL
    (P : BasePrime) (r : Rank) (level : Nat) :
    Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (ResidueField P r level) :=
  Matrix.GeneralLinearGroup.map
    (algebraMap (BaseField P) (ResidueField P r level))
    (frobeniusGL P r)
@[simp] theorem residueFrobeniusGL_coe
    (P : BasePrime) (r : Rank) (level : Nat) :
    (residueFrobeniusGL P r level :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (ResidueField P r level)) =
      residueFrobeniusMatrix P r level :=
  rfl
noncomputable def residueConstantMatrix
    (P : BasePrime) (r : Rank) (level : Nat)
    (c : ConstantExtension P r) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank) (ResidueField P r level) :=
  (constantRegularMatrix P r c).map
    (algebraMap (BaseField P) (ResidueField P r level))
theorem residueFrobeniusMatrix_pow_matrixRank
    (P : BasePrime) (r : Rank) (level : Nat) :
    residueFrobeniusMatrix P r level ^ r.matrixRank = 1 := by
  have hbase :
      (frobeniusGL P r :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BaseField P)) ^
          r.matrixRank = 1 := by
    rw [← Units.val_pow_eq_pow_val]
    exact congrArg Units.val (frobeniusGL_pow_matrixRank P r)
  rw [residueFrobeniusMatrix, ← Matrix.map_pow]
  rw [hbase]
  simp
theorem residueGamma_eq_pow_sub_one
    (P : BasePrime) (r : Rank) (level : Nat) :
    residueGamma P r level =
      (1 + residueAlpha P r level) ^ r.matrixRank - 1 := by
  rw [residueGamma, residueYPolynomial, Polynomial.eval_map,
    sourceYPolynomial_eq_pow_sub_one]
  simp
theorem residueAlpha_one_add_ne_zero
    (P : BasePrime) (r : Rank) (level : Nat) :
    1 + residueAlpha P r level ≠ 0 := by
  intro hzero
  have halpha : residueAlpha P r level = -1 := by
    exact eq_neg_of_add_eq_zero_right hzero
  have hgamma : residueGamma P r level = -1 := by
    rw [residueGamma_eq_pow_sub_one, halpha]
    have hdne : r.matrixRank ≠ 0 := by
      exact Nat.ne_of_gt
        (lt_of_lt_of_le (by norm_num) (Rank.two_le_matrixRank r))
    simp [hdne]
  have hinRange : residueGamma P r level ∈
      (algebraMap (BaseField P) (ResidueField P r level)).range := by
    refine ⟨-1, ?_⟩
    simp [hgamma]
  have hdegreeOne :
      (minpoly (BaseField P) (residueGamma P r level)).natDegree = 1 :=
    minpoly.natDegree_eq_one_iff.mpr hinRange
  have hdegreeFull := residueYMinpoly_natDegree P r level
  change (minpoly (BaseField P) (residueGamma P r level)).natDegree =
    r.residueExponent level at hdegreeFull
  rw [hdegreeOne] at hdegreeFull
  cases r <;>
    simp [Rank.residueExponent, Rank.matrixRank] at hdegreeFull <;> omega
theorem residueGamma_ne_zero
    (P : BasePrime) (r : Rank) (level : Nat) :
    residueGamma P r level ≠ 0 := by
  intro hzero
  have hinRange : residueGamma P r level ∈
      (algebraMap (BaseField P) (ResidueField P r level)).range := by
    refine ⟨0, ?_⟩
    simp [hzero]
  have hdegreeOne :
      (minpoly (BaseField P) (residueGamma P r level)).natDegree = 1 :=
    minpoly.natDegree_eq_one_iff.mpr hinRange
  have hdegreeFull := residueYMinpoly_natDegree P r level
  change (minpoly (BaseField P) (residueGamma P r level)).natDegree =
    r.residueExponent level at hdegreeFull
  rw [hdegreeOne] at hdegreeFull
  cases r <;>
    simp [Rank.residueExponent, Rank.matrixRank] at hdegreeFull <;> omega
theorem isUnit_one_sub_inv_of_pow_eq_one_add_smul_one
    {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n]
    (z : Matrix.GeneralLinearGroup n K) (d : Nat) (gamma : K)
    (hgamma : gamma ≠ 0)
    (hpow : (z : Matrix n n K) ^ d = (1 + gamma) • (1 : Matrix n n K)) :
    IsUnit
      ((1 : Matrix n n K) -
        (z⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K) := by
  let Z : Matrix n n K := z
  let Zi : Matrix n n K :=
    (z⁻¹ : Matrix.GeneralLinearGroup n K)
  let S : Matrix n n K := ∑ i ∈ Finset.range d, Z ^ i
  let B : Matrix n n K := 1 - Zi
  let C : Matrix n n K := 1 + gamma⁻¹ • S
  change IsUnit B
  have hZiZ : Zi * Z = 1 := by
    dsimp [Zi, Z]
    exact congrArg Units.val (inv_mul_cancel z)
  have hgeom : (Z - 1) * S = Z ^ d - 1 := by
    exact mul_geom_sum Z d
  have hpow' : Z ^ d - 1 = gamma • (1 : Matrix n n K) := by
    rw [hpow]
    simp [add_smul]
  have hBS : B * S = gamma • Zi := by
    calc
      B * S = Zi * ((Z - 1) * S) := by
        dsimp [B]
        symm
        rw [← mul_assoc, mul_sub, hZiZ, mul_one]
      _ = Zi * (Z ^ d - 1) := by rw [hgeom]
      _ = Zi * (gamma • (1 : Matrix n n K)) := by rw [hpow']
      _ = gamma • Zi := by
        rw [Matrix.mul_smul]
        simp
  have hBC : B * C = 1 := by
    calc
      B * C = B * (1 + gamma⁻¹ • S) := rfl
      _ = B + gamma⁻¹ • (B * S) := by
        rw [mul_add, mul_one, Matrix.mul_smul]
      _ = B + gamma⁻¹ • (gamma • Zi) := by rw [hBS]
      _ = 1 := by
        rw [smul_smul, inv_mul_cancel₀ hgamma, one_smul]
        simp [B]
  refine ⟨Units.mkOfMulEqOne B C hBC, ?_⟩
  exact Units.val_mkOfMulEqOne hBC
noncomputable def residueCyclicGeneratorMatrix
    (P : BasePrime) (r : Rank) (level : Nat) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank) (ResidueField P r level) :=
  (1 + residueAlpha P r level) • residueFrobeniusMatrix P r level
noncomputable def residueCyclicGeneratorGL
    (P : BasePrime) (r : Rank) (level : Nat) :
    Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (ResidueField P r level) :=
  Matrix.GeneralLinearGroup.scalar (Fin r.matrixRank)
      (Units.mk0 (1 + residueAlpha P r level)
        (residueAlpha_one_add_ne_zero P r level)) *
    residueFrobeniusGL P r level
@[simp] theorem residueCyclicGeneratorGL_coe
    (P : BasePrime) (r : Rank) (level : Nat) :
    (residueCyclicGeneratorGL P r level :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (ResidueField P r level)) =
      residueCyclicGeneratorMatrix P r level := by
  rw [residueCyclicGeneratorGL, residueCyclicGeneratorMatrix,
    Units.val_mul, residueFrobeniusGL_coe]
  change
    Matrix.scalar (Fin r.matrixRank) (1 + residueAlpha P r level) *
        residueFrobeniusMatrix P r level =
      (1 + residueAlpha P r level) • residueFrobeniusMatrix P r level
  rw [Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
theorem residueCyclicGeneratorMatrix_pow_matrixRank
    (P : BasePrime) (r : Rank) (level : Nat) :
    residueCyclicGeneratorMatrix P r level ^ r.matrixRank =
      (1 + residueGamma P r level) •
        (1 : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (ResidueField P r level)) := by
  rw [residueCyclicGeneratorMatrix, smul_pow,
    residueFrobeniusMatrix_pow_matrixRank]
  have hscalar :
      (1 + residueAlpha P r level) ^ r.matrixRank =
        1 + residueGamma P r level := by
    rw [residueGamma_eq_pow_sub_one]
    ring
  rw [hscalar]
noncomputable def residueBMatrix
    (P : BasePrime) (r : Rank) (level : Nat) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank) (ResidueField P r level) :=
  1 - ((residueCyclicGeneratorGL P r level)⁻¹ :
    Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (ResidueField P r level))
theorem residueBMatrix_isUnit
    (P : BasePrime) (r : Rank) (level : Nat) :
    IsUnit (residueBMatrix P r level) := by
  apply isUnit_one_sub_inv_of_pow_eq_one_add_smul_one
    (residueCyclicGeneratorGL P r level) r.matrixRank
    (residueGamma P r level) (residueGamma_ne_zero P r level)
  simpa only [residueCyclicGeneratorGL_coe] using
    residueCyclicGeneratorMatrix_pow_matrixRank P r level
noncomputable def residueBGL
    (P : BasePrime) (r : Rank) (level : Nat) :
    Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (ResidueField P r level) :=
  (residueBMatrix_isUnit P r level).unit
noncomputable def residueConstantGL
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : (ConstantExtension P r)ˣ) :
    Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (ResidueField P r level) :=
  Matrix.GeneralLinearGroup.map
      (algebraMap (BaseField P) (ResidueField P r level))
    (Units.map (constantRegularMatrix P r).toMonoidHom u)
noncomputable def residueCartwrightStegerGeneratorGL
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : (ConstantExtension P r)ˣ) :
    Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (ResidueField P r level) :=
  residueConstantGL P r level u * residueBGL P r level *
    (residueConstantGL P r level u)⁻¹
noncomputable def residueCartwrightStegerGenerator
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : (ConstantExtension P r)ˣ) :
    PGL P r level :=
  Matrix.ProjGenLinGroup.mk (residueCartwrightStegerGeneratorGL P r level u)
end QEC.Coding.HighDimensionalExpander.CartwrightSteger


