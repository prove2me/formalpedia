-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicResidue
-- name    : QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicResidue
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:19:59.126302+00:00
-- url     : https://prove2.me/theorems/ed0d8f6b-990d-432a-bdee-978d914aa2b3
-- title:
--   Adic Residue
-- statement:
--   Definitions and structural lemmas for Adic Residue, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/AdicResidue.lean

import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RatFuncPlaceClassification
set_option autoImplicit false
open scoped Polynomial RatFunc
namespace QEC.Coding.AlgebraicGeometry
namespace GlobalPlace
variable {k : Type*} [Field k] [Finite k]
noncomputable local instance rationalAdicDecidableEq : DecidableEq k :=
  Classical.decEq k
noncomputable def rationalAdicPolynomial
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) : k[X] :=
  normalize (Submodule.IsPrincipal.generator p.asIdeal)
theorem rationalAdic_asIdeal_eq_span
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) :
    p.asIdeal = Ideal.span ({rationalAdicPolynomial p} : Set k[X]) := by
  rw [rationalAdicPolynomial]
  exact (Ideal.span_singleton_generator p.asIdeal).symm.trans
    (Ideal.span_singleton_eq_span_singleton.mpr (associated_normalize _))
noncomputable def rationalAdicLocalizationEquiv
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) :
    Localization.AtPrime p.asIdeal ≃+* (rationalAdic p).valuationRing := by
  let e₁ : Localization.AtPrime p.asIdeal ≃+*
      p.valuationSubringAtPrime (RatFunc k) :=
    (Localization.algEquiv p.asIdeal.primeCompl
      (p.valuationSubringAtPrime (RatFunc k))).toRingEquiv
  let hsub : (p.valuationSubringAtPrime (RatFunc k)).toSubring =
      (rationalAdic p).valuationRing.toSubring := by
    change (p.valuationSubringAtPrime (RatFunc k)).toSubring =
      (p.valuation (RatFunc k)).valuationSubring.toSubring
    exact congrArg ValuationSubring.toSubring
      p.valuationSubringAtPrime_eq_valuationSubring
  let e₂ : p.valuationSubringAtPrime (RatFunc k) ≃+*
      (rationalAdic p).valuationRing :=
    RingEquiv.subringCongr hsub
  exact e₁.trans e₂
noncomputable def rationalAdicPolynomialToValuationRing
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) :
    k[X] →+* (rationalAdic p).valuationRing :=
  (rationalAdicLocalizationEquiv p).toRingHom.comp
    (algebraMap k[X] (Localization.AtPrime p.asIdeal))
noncomputable def rationalAdicQuotientResidueEquiv
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) :
    (k[X] ⧸ p.asIdeal) ≃+* p.asIdeal.ResidueField :=
  RingEquiv.ofBijective (algebraMap (k[X] ⧸ p.asIdeal) p.asIdeal.ResidueField)
    p.asIdeal.bijective_algebraMap_quotient_residueField
noncomputable def rationalAdicResidueEquiv
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) :
    AdjoinRoot (rationalAdicPolynomial p) ≃+* (rationalAdic p).residueField :=
  (Ideal.quotEquivOfEq (rationalAdic_asIdeal_eq_span p).symm).trans
    ((rationalAdicQuotientResidueEquiv p).trans
      (IsLocalRing.ResidueField.mapEquiv (rationalAdicLocalizationEquiv p)))
end GlobalPlace
end QEC.Coding.AlgebraicGeometry


