-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_PlaceIncrement
-- name    : QEC_Coding_AlgebraicGeometry_RiemannRoch_PlaceIncrement
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:33:14.630829+00:00
-- url     : https://prove2.me/theorems/f85f86a4-dcc6-4b1e-8c8d-1758f232f633
-- title:
--   Place Increment
-- statement:
--   Definitions and structural lemmas for Place Increment, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/PlaceIncrement.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_ResidueProduct
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_PrincipalShift
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_mul
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_regularAt_iff_mem_valuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_regularAt_iff_order_nonnegative
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
namespace GlobalPlace
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (Polynomial k) F] [Algebra (RatFunc k) F]
variable [IsScalarTower (Polynomial k) (RatFunc k) F]
variable [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
noncomputable def placeDivisor (P : GlobalPlace k F) :
    Divisor (GlobalPlace k F) :=
  Finsupp.single P 1
@[simp]
theorem placeDivisor_apply (P : GlobalPlace k F) :
    placeDivisor P P = 1 := by
  classical
  simp [placeDivisor]
@[simp]
theorem placeDivisor_apply_of_ne (P Q : GlobalPlace k F) (hPQ : P ≠ Q) :
    placeDivisor P Q = 0 := by
  classical
  simp [placeDivisor, hPQ]
noncomputable def riemannRochPlaceIncrementSubmodule
    (G : Divisor (GlobalPlace k F)) (P : GlobalPlace k F) :
    Submodule k (riemannRochSubmodule (G + placeDivisor P)) :=
  (riemannRochSubmodule G).comap
    (riemannRochSubmodule (G + placeDivisor P)).subtype
theorem localParameterPower_valuation
    (P : GlobalPlace k F) (n : ℤ) :
    P.valuation (Differential.localParameterPower P n) = WithZero.exp (-n) := by
  rw [Differential.localParameterPower, Units.val_zpow_eq_zpow_val, map_zpow₀,
    Differential.localParameterUnit, Units.val_mk0,
    Differential.localParameter, P.valuation_uniformizer,
    ← WithZero.exp_zsmul]
  congr 1
  simp
theorem localParameterPower_order
    (P : GlobalPlace k F) (n : ℤ) :
    P.order (Differential.localParameterPower P n) = n := by
  rw [order, localParameterPower_valuation]
  simp
theorem localParameterPower_ne_zero
    (P : GlobalPlace k F) (n : ℤ) :
    Differential.localParameterPower P n ≠ 0 := by
  exact Units.ne_zero _
noncomputable def riemannRochPlaceLeadingCoefficientValue
    (G : Divisor (GlobalPlace k F)) (P : GlobalPlace k F)
    (x : riemannRochSubmodule (G + placeDivisor P)) : P.valuationRing :=
  ⟨Differential.localParameterPower P (G P + 1) * (x : F), by
    by_cases hx : (x : F) = 0
    · simp only [hx, mul_zero]
      exact P.valuationRing.zero_mem
    · apply (regularAt_iff_mem_valuationRing P _).mp
      apply (regularAt_iff_order_nonnegative P
        (mul_ne_zero (localParameterPower_ne_zero P (G P + 1)) hx)).mpr
      rw [order_mul P (localParameterPower_ne_zero P (G P + 1)) hx,
        localParameterPower_order]
      have hxP :=
        (mem_riemannRochSubmodule_iff_order_add_nonnegative
          (G + placeDivisor P) hx).mp x.property P
      simp only [Finsupp.add_apply, placeDivisor_apply] at hxP
      omega⟩
theorem riemannRochPlaceLeadingCoefficientValue_add
    (G : Divisor (GlobalPlace k F)) (P : GlobalPlace k F)
    (x y : riemannRochSubmodule (G + placeDivisor P)) :
    riemannRochPlaceLeadingCoefficientValue G P (x + y) =
      riemannRochPlaceLeadingCoefficientValue G P x +
        riemannRochPlaceLeadingCoefficientValue G P y := by
  apply Subtype.ext
  change Differential.localParameterPower P (G P + 1) *
      ((x : F) + (y : F)) =
    Differential.localParameterPower P (G P + 1) * (x : F) +
      Differential.localParameterPower P (G P + 1) * (y : F)
  exact mul_add _ _ _
theorem riemannRochPlaceLeadingCoefficientValue_smul
    (G : Divisor (GlobalPlace k F)) (P : GlobalPlace k F) (c : k)
    (x : riemannRochSubmodule (G + placeDivisor P)) :
    riemannRochPlaceLeadingCoefficientValue G P (c • x) =
      constantsToValuationRing P c *
        riemannRochPlaceLeadingCoefficientValue G P x := by
  apply Subtype.ext
  calc
    ((riemannRochPlaceLeadingCoefficientValue G P (c • x) :
        P.valuationRing) : F) =
        Differential.localParameterPower P (G P + 1) *
          (algebraMap k F c * (x : F)) := by
      simp only [riemannRochPlaceLeadingCoefficientValue,
        Submodule.coe_smul, Algebra.smul_def]
    _ = algebraMap k F c *
        (Differential.localParameterPower P (G P + 1) * (x : F)) := by
      ring
    _ = ((constantsToValuationRing P c *
        riemannRochPlaceLeadingCoefficientValue G P x :
          P.valuationRing) : F) := rfl
noncomputable def riemannRochPlaceLeadingCoefficient
    (G : Divisor (GlobalPlace k F)) (P : GlobalPlace k F) :
    letI : Algebra k P.residueField := residueAlgebra P
    riemannRochSubmodule (G + placeDivisor P) →ₗ[k] P.residueField := by
  letI : Algebra k P.residueField := residueAlgebra P
  refine
    { toFun := fun x => P.residue
        (riemannRochPlaceLeadingCoefficientValue G P x)
      map_add' := ?_
      map_smul' := ?_ }
  · intro x y
    rw [riemannRochPlaceLeadingCoefficientValue_add, map_add]
  · intro c x
    rw [riemannRochPlaceLeadingCoefficientValue_smul, map_mul]
    change constantsToResidue P c *
        P.residue (riemannRochPlaceLeadingCoefficientValue G P x) =
      algebraMap k P.residueField c *
        P.residue (riemannRochPlaceLeadingCoefficientValue G P x)
    rfl
end GlobalPlace
end QEC.Coding.AlgebraicGeometry


