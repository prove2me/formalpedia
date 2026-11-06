-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicSimpleFractionResidue
-- name    : QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicSimpleFractionResidue
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:36:42.843925+00:00
-- url     : https://prove2.me/theorems/8d9c32b9-a515-4cfa-bdc9-eb06741480e9
-- title:
--   Adic Simple Fraction Residue
-- statement:
--   Definitions and structural lemmas for Adic Simple Fraction Residue, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/AdicSimpleFractionResidue.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Global_LogarithmicResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_ResidueProduct
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_EulerTrace
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_rationalAdicPolynomialToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicPolynomial_irreducible
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_rationalAdicPolynomialToValuationRing


set_option autoImplicit false
open scoped Polynomial RatFunc WithZero
namespace QEC.Coding.AlgebraicGeometry
namespace Differential
open FunctionFieldDifferential
variable {k : Type*} [Field k] [Finite k]
theorem rationalAdicPolynomial_derivative_ne_zero
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) :
    (GlobalPlace.rationalAdicPolynomial p).derivative ≠ 0 := by
  exact (Polynomial.separable_iff_derivative_ne_zero
    (GlobalPlace.rationalAdicPolynomial_irreducible p)).mp
      (PerfectField.separable_of_irreducible
        (GlobalPlace.rationalAdicPolynomial_irreducible p))
theorem rationalAdicPolynomial_derivative_not_mem
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) :
    (GlobalPlace.rationalAdicPolynomial p).derivative ∉ p.asIdeal := by
  rw [GlobalPlace.rationalAdic_asIdeal_eq_span p,
    Ideal.mem_span_singleton, Polynomial.dvd_derivative_iff]
  exact rationalAdicPolynomial_derivative_ne_zero p
theorem rationalAdicPolynomialDerivative_isUnit
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) :
    IsUnit (GlobalPlace.rationalAdicPolynomialToValuationRing p
      (GlobalPlace.rationalAdicPolynomial p).derivative) := by
  apply (Valuation.valuationSubring.integers
    (GlobalPlace.rationalAdic p).valuation).isUnit_iff_valuation_eq_one.mpr
  change (GlobalPlace.rationalAdic p).valuation
      ((GlobalPlace.rationalAdicPolynomialToValuationRing p
        (GlobalPlace.rationalAdicPolynomial p).derivative :
          (GlobalPlace.rationalAdic p).valuationRing) : RatFunc k) = 1
  rw [GlobalPlace.coe_rationalAdicPolynomialToValuationRing]
  exact (p.valuation_eq_one_iff_notMem (K := RatFunc k)).mpr
    (rationalAdicPolynomial_derivative_not_mem p)
noncomputable def rationalAdicRegularQuotient
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) (b : k[X]) :
    (GlobalPlace.rationalAdic p).valuationRing :=
  GlobalPlace.rationalAdicPolynomialToValuationRing p b *
    ↑((rationalAdicPolynomialDerivative_isUnit p).unit⁻¹)
theorem rationalAdicPolynomial_map_ne_zero
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) :
    algebraMap k[X] (RatFunc k) (GlobalPlace.rationalAdicPolynomial p) ≠ 0 :=
  RatFunc.algebraMap_ne_zero
    (GlobalPlace.rationalAdicPolynomial_irreducible p).ne_zero
noncomputable def rationalAdicSimpleFractionAtSimplePole
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) (b : k[X]) :
    simplePoleDifferentialLattice (GlobalPlace.rationalAdic p) :=
  rationalAdicRegularQuotient p b •
    logarithmicDifferentialAtSimplePole (k := k) (F := RatFunc k)
      (GlobalPlace.rationalAdic p)
      (algebraMap k[X] (RatFunc k) (GlobalPlace.rationalAdicPolynomial p))
      (rationalAdicPolynomial_map_ne_zero p)
end Differential
end QEC.Coding.AlgebraicGeometry


