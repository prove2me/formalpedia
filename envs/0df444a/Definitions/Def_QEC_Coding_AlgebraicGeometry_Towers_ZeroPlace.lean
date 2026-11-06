-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ZeroPlace
-- name    : QEC_Coding_AlgebraicGeometry_Towers_ZeroPlace
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:40:51.989937+00:00
-- url     : https://prove2.me/theorems/9c540c4b-ddc4-4e2c-82e0-5e41c3fe8ca7
-- title:
--   Zero Place
-- statement:
--   Definitions and structural lemmas for Zero Place, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ZeroPlace.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_BasePlaces
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicPolynomialLogarithmicResidue
import Mathlib.RingTheory.Polynomial.Quotient
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_coe_rationalAdicPolynomialDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_rationalAdicPolynomialToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicPolynomial_monic
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_none
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_some
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_regularAt_iff_mem_valuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.Differential.coe_rationalAdicPolynomialDifferential
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
open Polynomial
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
noncomputable def zeroBaseHeightOne :
    IsDedekindDomain.HeightOneSpectrum F256[X] := by
  have hprime : Prime (Polynomial.X : F256[X]) :=
    UniqueFactorizationMonoid.irreducible_iff_prime.mp Polynomial.irreducible_X
  have hspanPrime :
      (Ideal.span ({Polynomial.X} : Set F256[X])).IsPrime :=
    (Ideal.span_singleton_prime Polynomial.X_ne_zero).mpr hprime
  exact IsDedekindDomain.HeightOneSpectrum.ofPrime
    (Ideal.prime_of_isPrime
      (Ideal.span_singleton_eq_bot.not.mpr Polynomial.X_ne_zero)
      hspanPrime)
theorem zeroBaseHeightOne_asIdeal :
    zeroBaseHeightOne.asIdeal =
      Ideal.span ({Polynomial.X} : Set F256[X]) := by
  rfl
theorem zeroBaseRationalAdicPolynomial :
    GlobalPlace.rationalAdicPolynomial zeroBaseHeightOne =
      (Polynomial.X : F256[X]) := by
  apply Polynomial.eq_of_monic_of_associated
    (GlobalPlace.rationalAdicPolynomial_monic zeroBaseHeightOne)
    Polynomial.monic_X
  apply Ideal.span_singleton_eq_span_singleton.mp
  rw [← GlobalPlace.rationalAdic_asIdeal_eq_span]
  exact zeroBaseHeightOne_asIdeal
theorem zeroBaseAdjoinRootIdeal_eq :
    Ideal.span
        ({GlobalPlace.rationalAdicPolynomial zeroBaseHeightOne} : Set F256[X]) =
      Ideal.span ({Polynomial.X - Polynomial.C 0} : Set F256[X]) := by
  rw [zeroBaseRationalAdicPolynomial]
  simp
noncomputable def zeroBaseAdjoinRootEquiv :
    AdjoinRoot (GlobalPlace.rationalAdicPolynomial zeroBaseHeightOne) ≃ₐ[F256]
      F256 :=
  (Ideal.quotientEquivAlgOfEq F256 zeroBaseAdjoinRootIdeal_eq).trans
    (Polynomial.quotientSpanXSubCAlgEquiv 0)
theorem zeroBaseAdjoinRootEquiv_symm_apply (c : F256) :
    zeroBaseAdjoinRootEquiv.symm c =
      algebraMap F256
        (AdjoinRoot (GlobalPlace.rationalAdicPolynomial zeroBaseHeightOne)) c := by
  apply zeroBaseAdjoinRootEquiv.injective
  rw [zeroBaseAdjoinRootEquiv.apply_symm_apply,
    zeroBaseAdjoinRootEquiv.commutes]
  simp
noncomputable def zeroBaseResidueEquiv :
    F256 ≃+* GlobalPlace.residueField
      (GlobalPlace.rationalAdic zeroBaseHeightOne) :=
  zeroBaseAdjoinRootEquiv.symm.toRingEquiv.trans
    (GlobalPlace.rationalAdicResidueEquiv zeroBaseHeightOne)
theorem zeroBaseRationalAdicResidueEquiv_algebraMap (c : F256) :
    GlobalPlace.rationalAdicResidueEquiv zeroBaseHeightOne
        (algebraMap F256
          (AdjoinRoot (GlobalPlace.rationalAdicPolynomial zeroBaseHeightOne)) c) =
      GlobalPlace.constantsToResidue
        (GlobalPlace.rationalAdic zeroBaseHeightOne) c := by
  change (GlobalPlace.rationalAdic zeroBaseHeightOne).residue
      (GlobalPlace.rationalAdicPolynomialToValuationRing
        zeroBaseHeightOne (Polynomial.C c)) =
    (GlobalPlace.rationalAdic zeroBaseHeightOne).residue
      (GlobalPlace.constantsToValuationRing
        (GlobalPlace.rationalAdic zeroBaseHeightOne) c)
  apply congrArg (GlobalPlace.rationalAdic zeroBaseHeightOne).residue
  apply Subtype.ext
  simp only [GlobalPlace.coe_rationalAdicPolynomialToValuationRing,
    GlobalPlace.coe_constantsToValuationRing, RatFunc.algebraMap_C,
    RatFunc.algebraMap_eq_C]
theorem zeroBaseResidueEquiv_apply (c : F256) :
    zeroBaseResidueEquiv c =
      GlobalPlace.constantsToResidue
        (GlobalPlace.rationalAdic zeroBaseHeightOne) c := by
  change GlobalPlace.rationalAdicResidueEquiv zeroBaseHeightOne
      (zeroBaseAdjoinRootEquiv.symm c) = _
  rw [zeroBaseAdjoinRootEquiv_symm_apply]
  exact zeroBaseRationalAdicResidueEquiv_algebraMap c
noncomputable def zeroBaseRationalPlace :
    RationalPlace F256 (RatFunc F256) where
  place := GlobalPlace.rationalAdic zeroBaseHeightOne
  constantsEquiv := zeroBaseResidueEquiv
  constantsEquiv_apply := zeroBaseResidueEquiv_apply
theorem zeroBaseRationalPlace_X_regular :
    GlobalPlace.RegularAt zeroBaseRationalPlace.place RatFunc.X := by
  change GlobalPlace.RegularAt
    (GlobalPlace.rationalAdic zeroBaseHeightOne) RatFunc.X
  rw [GlobalPlace.regularAt_iff_mem_valuationRing]
  simpa only [GlobalPlace.coe_rationalAdicPolynomialToValuationRing,
    RatFunc.algebraMap_X] using
      (GlobalPlace.rationalAdicPolynomialToValuationRing
        zeroBaseHeightOne Polynomial.X).property
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


