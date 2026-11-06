-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_SimpleFractionGlobalResidue
-- name    : QEC_Coding_AlgebraicGeometry_Residues_Rational_SimpleFractionGlobalResidue
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:40:54.883665+00:00
-- url     : https://prove2.me/theorems/591ceb63-3e84-433e-9b52-9fbcf21c5fb3
-- title:
--   Simple Fraction Global Residue
-- statement:
--   Definitions and structural lemmas for Simple Fraction Global Residue, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/SimpleFractionGlobalResidue.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicSimpleFractionResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_InfinitySimpleFractionResidue
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_coe_rationalAdicSimpleFractionAtSimplePole
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_coe_rationalInfinitySimpleFractionAtSimplePole
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_differential_mem_localDifferentialLattice
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_localDifferentialLattice_le_simplePoleDifferentialLattice
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_differential_eq_functionFieldDerivation_smul_generator
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_rationalAdicPolynomialToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicPolynomial_monic
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
theorem rationalAdicPolynomial_not_mem_of_ne
    (p q : IsDedekindDomain.HeightOneSpectrum k[X]) (hpq : p ≠ q) :
    GlobalPlace.rationalAdicPolynomial q ∉ p.asIdeal := by
  intro hmem
  apply hpq
  apply IsDedekindDomain.HeightOneSpectrum.ext
  have hle : q.asIdeal ≤ p.asIdeal := by
    rw [GlobalPlace.rationalAdic_asIdeal_eq_span q]
    exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hmem)
  exact (q.isMaximal.eq_of_le p.isPrime.ne_top hle).symm
theorem rationalAdicPolynomial_isUnit_of_ne
    (p q : IsDedekindDomain.HeightOneSpectrum k[X]) (hpq : p ≠ q) :
    IsUnit (GlobalPlace.rationalAdicPolynomialToValuationRing p
      (GlobalPlace.rationalAdicPolynomial q)) := by
  apply (Valuation.valuationSubring.integers
    (GlobalPlace.rationalAdic p).valuation).isUnit_iff_valuation_eq_one.mpr
  change (GlobalPlace.rationalAdic p).valuation
      ((GlobalPlace.rationalAdicPolynomialToValuationRing p
        (GlobalPlace.rationalAdicPolynomial q) :
          (GlobalPlace.rationalAdic p).valuationRing) : RatFunc k) = 1
  rw [GlobalPlace.coe_rationalAdicPolynomialToValuationRing]
  exact (p.valuation_eq_one_iff_notMem (K := RatFunc k)).mpr
    (rationalAdicPolynomial_not_mem_of_ne p q hpq)
noncomputable def rationalAdicSimpleFractionAwayCoefficient
    (p q : IsDedekindDomain.HeightOneSpectrum k[X]) (hpq : p ≠ q)
    (b : k[X]) : (GlobalPlace.rationalAdic p).valuationRing :=
  GlobalPlace.rationalAdicPolynomialToValuationRing p b *
    ↑((rationalAdicPolynomial_isUnit_of_ne p q hpq).unit⁻¹)
theorem coe_rationalAdicSimpleFractionAwayCoefficient
    (p q : IsDedekindDomain.HeightOneSpectrum k[X]) (hpq : p ≠ q)
    (b : k[X]) :
    ((rationalAdicSimpleFractionAwayCoefficient p q hpq b :
      (GlobalPlace.rationalAdic p).valuationRing) : RatFunc k) =
      algebraMap k[X] (RatFunc k) b /
        algebraMap k[X] (RatFunc k) (GlobalPlace.rationalAdicPolynomial q) := by
  unfold rationalAdicSimpleFractionAwayCoefficient
  rw [show
      (((GlobalPlace.rationalAdicPolynomialToValuationRing p b *
        ↑((rationalAdicPolynomial_isUnit_of_ne p q hpq).unit⁻¹) :
          (GlobalPlace.rationalAdic p).valuationRing) : RatFunc k)) =
        ((GlobalPlace.rationalAdicPolynomialToValuationRing p b :
          (GlobalPlace.rationalAdic p).valuationRing) : RatFunc k) *
          (((↑((rationalAdicPolynomial_isUnit_of_ne p q hpq).unit⁻¹) :
            (GlobalPlace.rationalAdic p).valuationRing)) : RatFunc k) by rfl]
  rw [GlobalPlace.coe_rationalAdicPolynomialToValuationRing]
  change algebraMap k[X] (RatFunc k) b *
      algebraMap (GlobalPlace.rationalAdic p).valuationRing (RatFunc k)
        (↑((rationalAdicPolynomial_isUnit_of_ne p q hpq).unit⁻¹) :
          (GlobalPlace.rationalAdic p).valuationRing) = _
  rw [map_units_inv (algebraMap
      (GlobalPlace.rationalAdic p).valuationRing (RatFunc k))
      (rationalAdicPolynomial_isUnit_of_ne p q hpq).unit,
    (rationalAdicPolynomial_isUnit_of_ne p q hpq).unit_spec]
  change algebraMap k[X] (RatFunc k) b *
      (((GlobalPlace.rationalAdicPolynomialToValuationRing p
        (GlobalPlace.rationalAdicPolynomial q) :
          (GlobalPlace.rationalAdic p).valuationRing) : RatFunc k))⁻¹ = _
  rw [GlobalPlace.coe_rationalAdicPolynomialToValuationRing, div_eq_mul_inv]
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
  have hX : functionFieldDerivation (k := k) (F := RatFunc k) RatFunc.X = 1 := by
    simpa using
      (functionFieldDerivation_apply_X (k := k) (F := RatFunc k))
  rw [hxValue, differential_eq_functionFieldDerivation_smul_generator,
    hX] at hx
  simpa using hx
theorem rationalAdicSimpleFraction_mem_localDifferentialLattice_of_ne
    (p q : IsDedekindDomain.HeightOneSpectrum k[X]) (hpq : p ≠ q)
    (b : k[X]) :
    ((rationalAdicSimpleFractionAtSimplePole q b :
      simplePoleDifferentialLattice (GlobalPlace.rationalAdic q)) :
        Differential k (RatFunc k)) ∈
      localDifferentialLattice (GlobalPlace.rationalAdic p) := by
  have hregular := (localDifferentialLattice (k := k) (F := RatFunc k)
    (GlobalPlace.rationalAdic p)).smul_mem
      (rationalAdicSimpleFractionAwayCoefficient p q hpq b)
      (functionFieldDifferentialGenerator_mem_rationalAdic p)
  change
    ((rationalAdicSimpleFractionAwayCoefficient p q hpq b :
      (GlobalPlace.rationalAdic p).valuationRing) : RatFunc k) •
        functionFieldDifferentialGenerator (k := k) (F := RatFunc k) ∈
      localDifferentialLattice (GlobalPlace.rationalAdic p) at hregular
  simpa only [coe_rationalAdicSimpleFractionAtSimplePole,
    coe_rationalAdicSimpleFractionAwayCoefficient] using hregular
theorem rationalAdicSimpleFraction_isGlobalSimplePole
    (q : IsDedekindDomain.HeightOneSpectrum k[X]) (b : k[X])
    (hb : b.degree < (GlobalPlace.rationalAdicPolynomial q).degree) :
    IsGlobalSimplePole (k := k) (F := RatFunc k)
      ((rationalAdicSimpleFractionAtSimplePole q b :
        simplePoleDifferentialLattice (GlobalPlace.rationalAdic q)) :
          Differential k (RatFunc k)) := by
  intro P
  obtain ⟨place, rfl⟩ := (GlobalPlace.rationalPlaceEquiv (k := k)).surjective P
  cases place with
  | none =>
      have hinfinity :=
        (rationalInfinitySimpleFractionAtSimplePole
          (GlobalPlace.rationalAdicPolynomial q) b
          (GlobalPlace.rationalAdicPolynomial_monic q) hb).property
      rw [GlobalPlace.rationalPlaceEquiv_apply_none,
        coe_rationalAdicSimpleFractionAtSimplePole]
      rw [coe_rationalInfinitySimpleFractionAtSimplePole] at hinfinity
      exact hinfinity
  | some p =>
      rw [GlobalPlace.rationalPlaceEquiv_apply_some]
      by_cases hpq : p = q
      · subst p
        exact (rationalAdicSimpleFractionAtSimplePole q b).property
      · exact localDifferentialLattice_le_simplePoleDifferentialLattice
          (k := k) (F := RatFunc k) (GlobalPlace.rationalAdic p)
          (rationalAdicSimpleFraction_mem_localDifferentialLattice_of_ne
            p q hpq b)
end Differential
end QEC.Coding.AlgebraicGeometry


