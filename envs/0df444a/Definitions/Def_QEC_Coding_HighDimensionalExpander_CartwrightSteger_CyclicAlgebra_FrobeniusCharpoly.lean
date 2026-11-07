-- Prove2me | Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_FrobeniusCharpoly
-- name    : QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_FrobeniusCharpoly
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T10:50:43.457995+00:00
-- url     : https://prove2.me/theorems/1633878a-eae5-46ec-a12d-e14e74d801ae
-- title:
--   Frobenius Charpoly
-- statement:
--   Definitions and structural lemmas for Frobenius Charpoly, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/FrobeniusCharpoly.lean

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Tactic
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantFrobenius_order
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrix_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantUnitMatrix_val


set_option autoImplicit false
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
abbrev ConstantGaloisGroup (P : BasePrime) (r : Rank) :=
  (ConstantExtension P r ≃ₐ[BaseField P] ConstantExtension P r)
noncomputable def frobeniusDifferenceLinearMap
    (P : BasePrime) (r : Rank) :
    ConstantExtension P r →ₗ[BaseField P] ConstantExtension P r :=
  LinearMap.id - (constantFrobenius P r).symm.toLinearEquiv.toLinearMap
noncomputable def frobeniusDifferenceRange
    (P : BasePrime) (r : Rank) :
    Submodule (BaseField P) (ConstantExtension P r) :=
  LinearMap.range (frobeniusDifferenceLinearMap P r)
noncomputable def constantMultiplicationLinearMap
    (P : BasePrime) (r : Rank) (a : ConstantExtension P r) :
    ConstantExtension P r →ₗ[BaseField P] ConstantExtension P r where
  toFun x := a * x
  map_add' x y := by simp [mul_add]
  map_smul' c x := by
    simp [Algebra.smul_def, mul_comm, mul_assoc]
@[simp]
theorem constantMultiplicationLinearMap_apply
    (P : BasePrime) (r : Rank)
    (a x : ConstantExtension P r) :
    constantMultiplicationLinearMap P r a x = a * x :=
  rfl
noncomputable def frobeniusPowerMap (P : BasePrime) (r : Rank) :
    Fin r.matrixRank → ConstantGaloisGroup P r :=
  fun i => constantFrobenius P r ^ i.val
theorem frobeniusPowerMap_injective (P : BasePrime) (r : Rank) :
    Function.Injective (frobeniusPowerMap P r) := by
  have aux : ∀ {i j : Fin r.matrixRank}, i.val ≤ j.val →
      frobeniusPowerMap P r i = frobeniusPowerMap P r j → i = j := by
    intro i j hle hij
    change constantFrobenius P r ^ i.val =
      constantFrobenius P r ^ j.val at hij
    have hpow : constantFrobenius P r ^ (j.val - i.val) = 1 := by
      apply mul_left_cancel (a := constantFrobenius P r ^ i.val)
      rw [← pow_add, Nat.add_comm, Nat.sub_add_cancel hle]
      rw [mul_one, hij]
    have hdvd : r.matrixRank ∣ j.val - i.val := by
      simpa [constantFrobenius_order P r] using
        (orderOf_dvd_of_pow_eq_one hpow)
    have hlt : j.val - i.val < r.matrixRank :=
      lt_of_le_of_lt (Nat.sub_le _ _) j.isLt
    have hzero : j.val - i.val = 0 :=
      Nat.eq_zero_of_dvd_of_lt hdvd hlt
    exact Fin.ext (Nat.le_antisymm hle (Nat.sub_eq_zero_iff_le.mp hzero))
  intro i j hij
  rcases le_total i.val j.val with hle | hle
  · exact aux hle hij
  · exact (aux hle hij.symm).symm
theorem frobeniusPowerMap_bijective (P : BasePrime) (r : Rank) :
    Function.Bijective (frobeniusPowerMap P r) := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨frobeniusPowerMap_injective P r, ?_⟩
  rw [Fintype.card_fin, Fintype.card_eq_nat_card,
    IsGalois.card_aut_eq_finrank]
  exact (GaloisField.finrank P.q
    (by cases r <;> norm_num : r.matrixRank ≠ 0)).symm
noncomputable def frobeniusPowerEquiv (P : BasePrime) (r : Rank) :
    Fin r.matrixRank ≃ ConstantGaloisGroup P r :=
  Equiv.ofBijective (frobeniusPowerMap P r)
    (frobeniusPowerMap_bijective P r)
noncomputable def frobeniusNormalBasis (P : BasePrime) (r : Rank) :
    Module.Basis (Fin r.matrixRank) (BaseField P) (ConstantExtension P r) :=
  (IsGalois.normalBasis (BaseField P) (ConstantExtension P r)).reindex
    (frobeniusPowerEquiv P r).symm
end QEC.Coding.HighDimensionalExpander.CartwrightSteger


