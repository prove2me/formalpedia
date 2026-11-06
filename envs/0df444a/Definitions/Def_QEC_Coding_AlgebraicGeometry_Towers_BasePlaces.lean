-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_BasePlaces
-- name    : QEC_Coding_AlgebraicGeometry_Towers_BasePlaces
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:25:41.028552+00:00
-- url     : https://prove2.me/theorems/30554c61-1b95-40d7-8782-cc58716038d9
-- title:
--   Base Places
-- statement:
--   Definitions and structural lemmas for Base Places, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/BasePlaces.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_FixedFieldArtinSchreier
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicResidue
import Mathlib.RingTheory.Polynomial.Quotient
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
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_rationalAdicPolynomialToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicResidueEquiv_mk
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_none
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_some
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation


set_option autoImplicit false
open Polynomial
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
abbrev BasePoint := F256ˣ
noncomputable def basePolynomial (a : BasePoint) : F256[X] :=
  X - C (a : F256)
theorem basePolynomial_irreducible (a : BasePoint) :
    Irreducible (basePolynomial a) := by
  exact irreducible_X_sub_C (a : F256)
noncomputable def baseHeightOne (a : BasePoint) :
    IsDedekindDomain.HeightOneSpectrum F256[X] := by
  have hprime : Prime (basePolynomial a) :=
    UniqueFactorizationMonoid.irreducible_iff_prime.mp
      (basePolynomial_irreducible a)
  have hspanPrime : (Ideal.span ({basePolynomial a} : Set F256[X])).IsPrime :=
    (Ideal.span_singleton_prime (basePolynomial_irreducible a).ne_zero).mpr hprime
  exact IsDedekindDomain.HeightOneSpectrum.ofPrime
    (Ideal.prime_of_isPrime
      (Ideal.span_singleton_eq_bot.not.mpr
        (basePolynomial_irreducible a).ne_zero)
      hspanPrime)
theorem baseHeightOne_asIdeal (a : BasePoint) :
    (baseHeightOne a).asIdeal =
      Ideal.span ({X - C (a : F256)} : Set F256[X]) := by
  rfl
noncomputable def baseHeightOnePoint (a : BasePoint) :
    IsDedekindDomain.HeightOneSpectrum F256[X] :=
  baseHeightOne a
@[simp]
theorem baseHeightOnePoint_asIdeal (a : BasePoint) :
    (baseHeightOnePoint a).asIdeal =
      Ideal.span ({X - C (a : F256)} : Set F256[X]) := by
  exact baseHeightOne_asIdeal a
theorem baseRationalAdicPolynomial (a : BasePoint) :
    GlobalPlace.rationalAdicPolynomial (baseHeightOne a) =
      X - C (a : F256) := by
  apply Polynomial.eq_of_monic_of_associated
    (GlobalPlace.rationalAdicPolynomial_monic (baseHeightOne a))
    (monic_X_sub_C (a : F256))
  apply Ideal.span_singleton_eq_span_singleton.mp
  rw [← GlobalPlace.rationalAdic_asIdeal_eq_span]
  exact baseHeightOne_asIdeal a
theorem baseAdjoinRootIdeal_eq (a : BasePoint) :
    Ideal.span
        ({GlobalPlace.rationalAdicPolynomial (baseHeightOne a)} : Set F256[X]) =
      Ideal.span ({X - C (a : F256)} : Set F256[X]) := by
  rw [baseRationalAdicPolynomial]
noncomputable def baseAdjoinRootEquiv (a : BasePoint) :
    AdjoinRoot (GlobalPlace.rationalAdicPolynomial (baseHeightOne a)) ≃ₐ[F256]
      F256 :=
  (Ideal.quotientEquivAlgOfEq F256 (baseAdjoinRootIdeal_eq a)).trans
    (Polynomial.quotientSpanXSubCAlgEquiv (a : F256))
theorem baseAdjoinRootEquiv_symm_apply
    (a : BasePoint) (c : F256) :
    (baseAdjoinRootEquiv a).symm c =
      algebraMap F256
        (AdjoinRoot (GlobalPlace.rationalAdicPolynomial (baseHeightOne a))) c := by
  apply (baseAdjoinRootEquiv a).injective
  rw [(baseAdjoinRootEquiv a).apply_symm_apply,
    (baseAdjoinRootEquiv a).commutes]
  simp
noncomputable def baseResidueEquiv (a : BasePoint) :
    F256 ≃+* GlobalPlace.residueField
      (GlobalPlace.rationalAdic (baseHeightOne a)) :=
  (baseAdjoinRootEquiv a).symm.toRingEquiv.trans
    (GlobalPlace.rationalAdicResidueEquiv (baseHeightOne a))
theorem rationalAdicResidueEquiv_algebraMap
    (p : IsDedekindDomain.HeightOneSpectrum F256[X]) (c : F256) :
    GlobalPlace.rationalAdicResidueEquiv p
        (algebraMap F256
          (AdjoinRoot (GlobalPlace.rationalAdicPolynomial p)) c) =
      GlobalPlace.constantsToResidue (GlobalPlace.rationalAdic p) c := by
  change (GlobalPlace.rationalAdic p).residue
      (GlobalPlace.rationalAdicPolynomialToValuationRing p (Polynomial.C c)) =
    (GlobalPlace.rationalAdic p).residue
      (GlobalPlace.constantsToValuationRing (GlobalPlace.rationalAdic p) c)
  apply congrArg (GlobalPlace.rationalAdic p).residue
  apply Subtype.ext
  simp only [GlobalPlace.coe_rationalAdicPolynomialToValuationRing,
    GlobalPlace.coe_constantsToValuationRing, RatFunc.algebraMap_C,
    RatFunc.algebraMap_eq_C]
theorem baseResidueEquiv_apply (a : BasePoint) (c : F256) :
    baseResidueEquiv a c =
      GlobalPlace.constantsToResidue
        (GlobalPlace.rationalAdic (baseHeightOne a)) c := by
  change GlobalPlace.rationalAdicResidueEquiv (baseHeightOne a)
      ((baseAdjoinRootEquiv a).symm c) = _
  rw [baseAdjoinRootEquiv_symm_apply]
  exact rationalAdicResidueEquiv_algebraMap (baseHeightOne a) c
noncomputable def baseRationalPlace (a : BasePoint) :
    RationalPlace F256 (RatFunc F256) where
  place := GlobalPlace.rationalAdic (baseHeightOne a)
  constantsEquiv := baseResidueEquiv a
  constantsEquiv_apply := baseResidueEquiv_apply a
theorem baseRationalPlace_X_regular (a : BasePoint) :
    GlobalPlace.RegularAt (baseRationalPlace a).place RatFunc.X := by
  change GlobalPlace.RegularAt
    (GlobalPlace.rationalAdic (baseHeightOne a)) RatFunc.X
  rw [GlobalPlace.regularAt_iff_mem_valuationRing]
  simpa only [GlobalPlace.coe_rationalAdicPolynomialToValuationRing,
    RatFunc.algebraMap_X] using
      (GlobalPlace.rationalAdicPolynomialToValuationRing
        (baseHeightOne a) Polynomial.X).property
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


