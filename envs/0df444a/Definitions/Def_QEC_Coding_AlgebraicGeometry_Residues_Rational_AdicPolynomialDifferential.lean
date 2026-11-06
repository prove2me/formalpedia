-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicPolynomialDifferential
-- name    : QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicPolynomialDifferential
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:32:27.16037+00:00
-- url     : https://prove2.me/theorems/75bef00a-7082-4bc5-99d8-29b263634a28
-- title:
--   Adic Polynomial Differential
-- statement:
--   Definitions and structural lemmas for Adic Polynomial Differential, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/AdicPolynomialDifferential.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_Residue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicResidue
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_differential_mem_localDifferentialLattice
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_localDifferentialLattice_le_simplePoleDifferentialLattice
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_differential_eq_functionFieldDerivation_smul_generator
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_rationalAdicPolynomialToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_none
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_some
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_rationalAdicPolynomialToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicResidueEquiv_mk
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_none
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_some
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


set_option autoImplicit false
open scoped Polynomial RatFunc
namespace QEC.Coding.AlgebraicGeometry
namespace Differential
open FunctionFieldDifferential
variable {k : Type*} [Field k] [Finite k]
theorem functionFieldDifferentialGenerator_mem_rationalAdic
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) :
    functionFieldDifferentialGenerator (k := k) (F := RatFunc k) ∈
      localDifferentialLattice (GlobalPlace.rationalAdic p) := by
  let x : (GlobalPlace.rationalAdic p).valuationRing :=
    GlobalPlace.rationalAdicPolynomialToValuationRing p Polynomial.X
  have hx := differential_mem_localDifferentialLattice
    (k := k) (F := RatFunc k) (GlobalPlace.rationalAdic p) x
  have hxValue : (x : RatFunc k) = RatFunc.X := by
    simp only [x, GlobalPlace.coe_rationalAdicPolynomialToValuationRing,
      RatFunc.algebraMap_X]
  have hX :
      functionFieldDerivation (k := k) (F := RatFunc k) RatFunc.X = 1 := by
    simpa using
      (functionFieldDerivation_apply_X (k := k) (F := RatFunc k))
  rw [hxValue, differential_eq_functionFieldDerivation_smul_generator,
    hX] at hx
  simpa using hx
noncomputable def rationalAdicPolynomialDifferential
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) (b : k[X]) :
    localDifferentialLattice (GlobalPlace.rationalAdic p) :=
  GlobalPlace.rationalAdicPolynomialToValuationRing p b •
    ⟨functionFieldDifferentialGenerator (k := k) (F := RatFunc k),
      functionFieldDifferentialGenerator_mem_rationalAdic p⟩
noncomputable def rationalAdicPolynomialDifferentialAtSimplePole
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) (b : k[X]) :
    simplePoleDifferentialLattice (GlobalPlace.rationalAdic p) :=
  ⟨rationalAdicPolynomialDifferential p b,
    localDifferentialLattice_le_simplePoleDifferentialLattice
      (k := k) (F := RatFunc k) (GlobalPlace.rationalAdic p)
      (rationalAdicPolynomialDifferential p b).property⟩
end Differential
end QEC.Coding.AlgebraicGeometry


