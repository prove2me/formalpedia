-- Prove2me | Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Core
-- name    : QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Core
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T10:46:17.018659+00:00
-- url     : https://prove2.me/theorems/1618c12b-62d5-47d9-b4ca-15d703ae90de
-- title:
--   Core
-- statement:
--   Definitions and structural lemmas for Core, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Order/Core.lean

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
import Mathlib.Tactic
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrix_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantUnitMatrix_val


set_option autoImplicit false
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
noncomputable def arithmeticRingToFunctionField (P : BasePrime) :
    ArithmeticRing P →+* FunctionField P :=
  IsLocalization.Away.lift
    (Polynomial.X * (1 + Polynomial.X) : PolynomialRing P)
    (S := ArithmeticRing P)
    (g := algebraMap (PolynomialRing P) (FunctionField P)) (by
      rw [isUnit_iff_ne_zero]
      apply RatFunc.algebraMap_ne_zero
      exact mul_ne_zero Polynomial.X_ne_zero (by
        intro hp
        have := congrArg (Polynomial.eval (0 : BaseField P)) hp
        simp at this))
@[simp] theorem arithmeticRingToFunctionField_algebraMap
    (P : BasePrime) (f : PolynomialRing P) :
    arithmeticRingToFunctionField P
        (algebraMap (PolynomialRing P) (ArithmeticRing P) f) =
      algebraMap (PolynomialRing P) (FunctionField P) f := by
  exact IsLocalization.Away.lift_eq _ _ _
noncomputable def arithmeticYInv (P : BasePrime) : ArithmeticRing P :=
  algebraMap (PolynomialRing P) (ArithmeticRing P) (1 + Polynomial.X) *
    IsLocalization.Away.invSelf
      (Polynomial.X * (1 + Polynomial.X) : PolynomialRing P)
theorem arithmeticRingToFunctionField_invSelf
    (P : BasePrime) :
    arithmeticRingToFunctionField P
        (IsLocalization.Away.invSelf
          (Polynomial.X * (1 + Polynomial.X) : PolynomialRing P)) =
      (algebraMap (PolynomialRing P) (FunctionField P)
        (Polynomial.X * (1 + Polynomial.X)))⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  have h := congrArg (arithmeticRingToFunctionField P)
    (IsLocalization.Away.mul_invSelf
      (S := ArithmeticRing P)
      (Polynomial.X * (1 + Polynomial.X) : PolynomialRing P))
  simpa [map_mul, arithmeticRingToFunctionField_algebraMap] using h
@[simp] theorem arithmeticRingToFunctionField_arithmeticYInv
    (P : BasePrime) :
    arithmeticRingToFunctionField P (arithmeticYInv P) =
      (RatFunc.X : FunctionField P)⁻¹ := by
  rw [arithmeticYInv, map_mul,
    arithmeticRingToFunctionField_algebraMap,
    arithmeticRingToFunctionField_invSelf]
  simp only [map_mul, map_add, map_one]
  have hOnePlus : (1 + RatFunc.X : FunctionField P) ≠ 0 := by
    have hpoly : (1 + Polynomial.X : PolynomialRing P) ≠ 0 := by
      intro hp
      have := congrArg (Polynomial.eval (0 : BaseField P)) hp
      simp at this
    simpa only [map_add, map_one, RatFunc.algebraMap_X] using
      (RatFunc.algebraMap_ne_zero hpoly)
  change (1 + RatFunc.X) * (RatFunc.X * (1 + RatFunc.X))⁻¹ =
    RatFunc.X⁻¹
  field_simp [RatFunc.X_ne_zero, hOnePlus]
noncomputable def arithmeticRingToSplittingFunctionField
    (P : BasePrime) (r : Rank) :
    ArithmeticRing P →+* SplittingFunctionField P r :=
  (functionFieldEmbedding P r).comp (arithmeticRingToFunctionField P)
theorem functionFieldEmbedding_X
    (P : BasePrime) (r : Rank) :
    functionFieldEmbedding P r (RatFunc.X : FunctionField P) =
      (RatFunc.X : SplittingFunctionField P r) := by
  rw [show (RatFunc.X : FunctionField P) =
      algebraMap (PolynomialRing P) (FunctionField P) Polynomial.X /
        algebraMap (PolynomialRing P) (FunctionField P) 1 by simp,
    show (RatFunc.X : SplittingFunctionField P r) =
      algebraMap (Polynomial (ConstantExtension P r))
          (SplittingFunctionField P r) Polynomial.X /
        algebraMap (Polynomial (ConstantExtension P r))
          (SplittingFunctionField P r) 1 by simp]
  unfold functionFieldEmbedding
  dsimp only
  rw [RatFunc.coe_mapRingHom_eq_coe_map]
  rw [RatFunc.map_apply_div]
  simp
@[simp] theorem arithmeticRingToSplittingFunctionField_arithmeticYInv
    (P : BasePrime) (r : Rank) :
    arithmeticRingToSplittingFunctionField P r (arithmeticYInv P) =
      (splittingY P r)⁻¹ := by
  rw [arithmeticRingToSplittingFunctionField,
    RingHom.comp_apply,
    arithmeticRingToFunctionField_arithmeticYInv, map_inv₀]
  rw [functionFieldEmbedding_X]
  rfl
noncomputable def arithmeticRingToSplitMatrix
    (P : BasePrime) (r : Rank) :
    ArithmeticRing P →+*
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r) :=
  (Matrix.scalar (Fin r.matrixRank)).comp
    (arithmeticRingToSplittingFunctionField P r)
noncomputable instance cartwrightStegerOrderAlgebra
    (P : BasePrime) (r : Rank) :
    Algebra (ArithmeticRing P)
      (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r)) :=
  { smul := fun a M => arithmeticRingToSplitMatrix P r a * M
    algebraMap := arithmeticRingToSplitMatrix P r
    commutes' := by
      intro a M
      change Matrix.scalar (Fin r.matrixRank)
          (arithmeticRingToSplittingFunctionField P r a) * M =
        M * Matrix.scalar (Fin r.matrixRank)
          (arithmeticRingToSplittingFunctionField P r a)
      exact Matrix.scalar_comm
        (arithmeticRingToSplittingFunctionField P r a)
        (fun b => Commute.all _ b) M
    smul_def' := by intros; rfl }
noncomputable def CartwrightStegerOrder (P : BasePrime) (r : Rank) :
    Subalgebra (ArithmeticRing P)
      (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r)) :=
  Algebra.adjoin (ArithmeticRing P)
    (Set.range (constantMatrix P r) ∪
      {cyclicGeneratorMatrix P r, cyclicGeneratorInverseMatrix P r})
theorem constantMatrix_mem_cartwrightStegerOrder
    (P : BasePrime) (r : Rank) (c : ConstantExtension P r) :
    constantMatrix P r c ∈ CartwrightStegerOrder P r := by
  apply Algebra.subset_adjoin
  exact Set.mem_union_left _ ⟨c, rfl⟩
theorem cyclicGeneratorMatrix_mem_cartwrightStegerOrder
    (P : BasePrime) (r : Rank) :
    cyclicGeneratorMatrix P r ∈ CartwrightStegerOrder P r := by
  apply Algebra.subset_adjoin
  exact Set.mem_union_right _ (Set.mem_insert _ _)
theorem cyclicGeneratorInverseMatrix_mem_cartwrightStegerOrder
    (P : BasePrime) (r : Rank) :
    cyclicGeneratorInverseMatrix P r ∈ CartwrightStegerOrder P r := by
  apply Algebra.subset_adjoin
  exact Set.mem_union_right _ (Set.mem_insert_iff.mpr (Or.inr rfl))
theorem cartwrightStegerBMatrix_mem_order
    (P : BasePrime) (r : Rank) :
    cartwrightStegerBMatrix P r ∈ CartwrightStegerOrder P r := by
  exact (CartwrightStegerOrder P r).sub_mem
    (CartwrightStegerOrder P r).one_mem
    (cyclicGeneratorInverseMatrix_mem_cartwrightStegerOrder P r)
@[simp] theorem algebraMap_arithmeticYInv
    (P : BasePrime) (r : Rank) :
    algebraMap (ArithmeticRing P)
        (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (SplittingFunctionField P r)) (arithmeticYInv P) =
      Matrix.scalar (Fin r.matrixRank) (splittingY P r)⁻¹ := by
  change arithmeticRingToSplitMatrix P r (arithmeticYInv P) = _
  rw [arithmeticRingToSplitMatrix, RingHom.comp_apply,
    arithmeticRingToSplittingFunctionField_arithmeticYInv]
theorem cartwrightStegerBInverseMatrix_mem_order
    (P : BasePrime) (r : Rank) :
    cartwrightStegerBInverseMatrix P r ∈
      CartwrightStegerOrder P r := by
  let S : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r) :=
    ∑ i ∈ Finset.range r.matrixRank, cyclicGeneratorMatrix P r ^ i
  have hS : S ∈ CartwrightStegerOrder P r := by
    apply (CartwrightStegerOrder P r).sum_mem
    intro i hi
    exact (CartwrightStegerOrder P r).pow_mem
      (cyclicGeneratorMatrix_mem_cartwrightStegerOrder P r) i
  have hsmul : (arithmeticYInv P) • S ∈
      CartwrightStegerOrder P r :=
    (CartwrightStegerOrder P r).smul_mem hS (arithmeticYInv P)
  have hscalar :
      (arithmeticYInv P) • S = (splittingY P r)⁻¹ • S := by
    rw [Algebra.smul_def, algebraMap_arithmeticYInv,
      Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
  rw [cartwrightStegerBInverseMatrix]
  exact (CartwrightStegerOrder P r).add_mem
    (CartwrightStegerOrder P r).one_mem (hscalar ▸ hsmul)
noncomputable def cartwrightStegerOrderB
    (P : BasePrime) (r : Rank) : (CartwrightStegerOrder P r)ˣ where
  val := ⟨cartwrightStegerBMatrix P r,
    cartwrightStegerBMatrix_mem_order P r⟩
  inv := ⟨cartwrightStegerBInverseMatrix P r,
    cartwrightStegerBInverseMatrix_mem_order P r⟩
  val_inv := Subtype.ext (cartwrightStegerB_mul_inverse P r)
  inv_val := Subtype.ext (cartwrightStegerB_inverse_mul P r)
noncomputable def constantOrderEmbedding
    (P : BasePrime) (r : Rank) :
    ConstantExtension P r →+* CartwrightStegerOrder P r where
  toFun c := ⟨constantMatrix P r c,
    constantMatrix_mem_cartwrightStegerOrder P r c⟩
  map_zero' := Subtype.ext (map_zero (constantMatrixEmbedding P r))
  map_one' := Subtype.ext (map_one (constantMatrixEmbedding P r))
  map_add' c d := Subtype.ext (map_add (constantMatrixEmbedding P r) c d)
  map_mul' c d := Subtype.ext (map_mul (constantMatrixEmbedding P r) c d)
noncomputable def constantOrderUnitHom
    (P : BasePrime) (r : Rank) :
    (ConstantExtension P r)ˣ →* (CartwrightStegerOrder P r)ˣ :=
  Units.map (constantOrderEmbedding P r).toMonoidHom
noncomputable def cartwrightStegerOrderGenerator
    (P : BasePrime) (r : Rank)
    (u : (ConstantExtension P r)ˣ) :
    (CartwrightStegerOrder P r)ˣ :=
  constantOrderUnitHom P r u * cartwrightStegerOrderB P r *
    (constantOrderUnitHom P r u)⁻¹
abbrev CartwrightStegerOrderProjectiveGroup
    (P : BasePrime) (r : Rank) :=
  (CartwrightStegerOrder P r)ˣ ⧸
    Subgroup.center ((CartwrightStegerOrder P r)ˣ)
noncomputable def CartwrightStegerOrderLattice
    (P : BasePrime) (r : Rank) :
    Subgroup (CartwrightStegerOrderProjectiveGroup P r) :=
  Subgroup.closure (Set.range fun u : ConstantProjectiveClass P r =>
    QuotientGroup.mk
      (cartwrightStegerOrderGenerator P r
        (constantClassRepresentative P r u)))
end QEC.Coding.HighDimensionalExpander.CartwrightSteger


