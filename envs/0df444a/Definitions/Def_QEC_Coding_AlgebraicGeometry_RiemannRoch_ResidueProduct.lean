-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_ResidueProduct
-- name    : QEC_Coding_AlgebraicGeometry_RiemannRoch_ResidueProduct
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:37:34.841566+00:00
-- url     : https://prove2.me/theorems/a8eac2b3-a360-4b12-b8fd-5bdf62a427e4
-- title:
--   Residue Product
-- statement:
--   Definitions and structural lemmas for Residue Product, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/ResidueProduct.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Global_SimplePoleResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_ResidueProduct
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_PlaceIncrement
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_smul_mem_simplePoleDifferentialLattice_iff_order_add_neg_one
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_differentialDivisor_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_mul
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
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
open scoped Polynomial RatFunc
namespace Differential
open FunctionFieldDifferential
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (Polynomial k) F] [Algebra (RatFunc k) F]
variable [IsScalarTower (Polynomial k) (RatFunc k) F]
variable [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
noncomputable def riemannRochProductDifferential
    (omega : Differential k F) (homega : omega ≠ 0)
    (G : Divisor (GlobalPlace k F)) (P : GlobalPlace k F)
    (x : GlobalPlace.riemannRochSubmodule (G + P.placeDivisor))
    (y : GlobalPlace.riemannRochSubmodule
      (differentialDivisor (k := k) (F := F) omega homega - G)) :
    Differential k F :=
  ((x : F) * (y : F)) • omega
theorem riemannRochProductDifferential_isGlobalSimplePole
    (omega : Differential k F) (homega : omega ≠ 0)
    (G : Divisor (GlobalPlace k F)) (P : GlobalPlace k F)
    (x : GlobalPlace.riemannRochSubmodule (G + P.placeDivisor))
    (y : GlobalPlace.riemannRochSubmodule
      (differentialDivisor (k := k) (F := F) omega homega - G)) :
    IsGlobalSimplePole
      (riemannRochProductDifferential omega homega G P x y) := by
  intro Q
  by_cases hx : (x : F) = 0
  · simp only [riemannRochProductDifferential, hx, zero_mul, zero_smul]
    exact (simplePoleDifferentialLattice Q).zero_mem
  by_cases hy : (y : F) = 0
  · simp only [riemannRochProductDifferential, hy, mul_zero, zero_smul]
    exact (simplePoleDifferentialLattice Q).zero_mem
  have hxy : (x : F) * (y : F) ≠ 0 := mul_ne_zero hx hy
  apply (smul_mem_simplePoleDifferentialLattice_iff_order_add_neg_one
    (k := k) (F := F) Q ((x : F) * (y : F)) hxy omega homega).mpr
  rw [GlobalPlace.order_mul Q hx hy]
  have hxQ :=
    (GlobalPlace.mem_riemannRochSubmodule_iff_order_add_nonnegative
      (G + P.placeDivisor) hx).mp x.property Q
  have hyQ :=
    (GlobalPlace.mem_riemannRochSubmodule_iff_order_add_nonnegative
      (differentialDivisor (k := k) (F := F) omega homega - G) hy).mp
        y.property Q
  simp only [Finsupp.add_apply] at hxQ
  simp only [Finsupp.sub_apply, differentialDivisor_apply] at hyQ
  by_cases hQP : Q = P
  · subst Q
    rw [GlobalPlace.placeDivisor_apply] at hxQ
    omega
  · rw [GlobalPlace.placeDivisor_apply_of_ne P Q (Ne.symm hQP)] at hxQ
    omega
end Differential
end QEC.Coding.AlgebraicGeometry


