-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdelePlaceIncrement
-- name    : QEC_Coding_AlgebraicGeometry_Adeles_AdelePlaceIncrement
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:39:33.431544+00:00
-- url     : https://prove2.me/theorems/d2faa838-2160-4dd0-a48d-cdd3c25972b7
-- title:
--   Adele Place Increment
-- statement:
--   Definitions and structural lemmas for Adele Place Increment, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/AdelePlaceIncrement.lean

import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_Adele
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_PlaceIncrementDimension
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_valuation_uniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc WithZero
noncomputable section
namespace GlobalPlace
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (Polynomial k) F] [Algebra (RatFunc k) F]
variable [IsScalarTower (Polynomial k) (RatFunc k) F]
variable [IsScalarTower k (RatFunc k) F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable (RatFunc k) F]
variable [FiniteDimensional (RatFunc k) F]
theorem globalAdele_localParameterPower_valuation
    (P : GlobalPlace k F) (n : ℤ) :
    P.valuation (Differential.localParameterPower P n) = WithZero.exp (-n) := by
  rw [Differential.localParameterPower, Units.val_zpow_eq_zpow_val, map_zpow₀,
    Differential.localParameterUnit, Units.val_mk0,
    Differential.localParameter, P.valuation_uniformizer,
    ← WithZero.exp_zsmul]
  congr 1
  simp
noncomputable def globalAdeleLocalLeadingCoefficientValue
    (D : Divisor (GlobalPlace k F)) (P : GlobalPlace k F)
    (a : globalAdeleFilter (k := k) (F := F) (D + placeDivisor P)) :
    P.valuationRing :=
  ⟨Differential.localParameterPower P (D P + 1) *
      ((a.val : GlobalAdele (k := k) (F := F)).val P), by
    rw [mem_valuationRing_iff, map_mul,
      globalAdele_localParameterPower_valuation]
    have ha := a.property P
    simp only [Finsupp.add_apply, placeDivisor_apply] at ha
    calc
      WithZero.exp (-(D P + 1)) *
          P.valuation ((a.val : GlobalAdele (k := k) (F := F)).val P) ≤
          WithZero.exp (-(D P + 1)) * WithZero.exp (D P + 1) :=
        mul_le_mul_right ha _
      _ = 1 := by
        rw [← WithZero.exp_add]
        simp⟩
theorem globalAdeleLocalLeadingCoefficientValue_add
    (D : Divisor (GlobalPlace k F)) (P : GlobalPlace k F)
    (a b : globalAdeleFilter (k := k) (F := F) (D + placeDivisor P)) :
    globalAdeleLocalLeadingCoefficientValue D P (a + b) =
      globalAdeleLocalLeadingCoefficientValue D P a +
        globalAdeleLocalLeadingCoefficientValue D P b := by
  apply Subtype.ext
  change Differential.localParameterPower P (D P + 1) *
      (((a.val : GlobalAdele (k := k) (F := F)).val P) +
        ((b.val : GlobalAdele (k := k) (F := F)).val P)) = _
  exact mul_add _ _ _
theorem globalAdeleLocalLeadingCoefficientValue_smul
    (D : Divisor (GlobalPlace k F)) (P : GlobalPlace k F) (c : k)
    (a : globalAdeleFilter (k := k) (F := F) (D + placeDivisor P)) :
    globalAdeleLocalLeadingCoefficientValue D P (c • a) =
      constantsToValuationRing P c *
        globalAdeleLocalLeadingCoefficientValue D P a := by
  apply Subtype.ext
  calc
    ((globalAdeleLocalLeadingCoefficientValue D P (c • a) :
        P.valuationRing) : F) =
        Differential.localParameterPower P (D P + 1) *
          (algebraMap k F c *
            ((a.val : GlobalAdele (k := k) (F := F)).val P)) := by
      simp only [globalAdeleLocalLeadingCoefficientValue,
        Submodule.coe_smul, Pi.smul_apply, Algebra.smul_def]
    _ = algebraMap k F c *
        (Differential.localParameterPower P (D P + 1) *
          ((a.val : GlobalAdele (k := k) (F := F)).val P)) := by
      ring
    _ = ((constantsToValuationRing P c *
        globalAdeleLocalLeadingCoefficientValue D P a :
          P.valuationRing) : F) := rfl
noncomputable def globalAdeleLocalLeadingCoefficient
    (D : Divisor (GlobalPlace k F)) (P : GlobalPlace k F) :
    letI : Algebra k P.residueField := residueAlgebra P
    globalAdeleFilter (k := k) (F := F) (D + placeDivisor P) →ₗ[k]
      P.residueField := by
  letI : Algebra k P.residueField := residueAlgebra P
  refine
    { toFun := fun a => P.residue (globalAdeleLocalLeadingCoefficientValue D P a)
      map_add' := ?_
      map_smul' := ?_ }
  · intro a b
    rw [globalAdeleLocalLeadingCoefficientValue_add, map_add]
  · intro c a
    rw [globalAdeleLocalLeadingCoefficientValue_smul, map_mul]
    change constantsToResidue P c *
        P.residue (globalAdeleLocalLeadingCoefficientValue D P a) =
      algebraMap k P.residueField c *
        P.residue (globalAdeleLocalLeadingCoefficientValue D P a)
    rfl
end GlobalPlace
end
end QEC.Coding.AlgebraicGeometry


