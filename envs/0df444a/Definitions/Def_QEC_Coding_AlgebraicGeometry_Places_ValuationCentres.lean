-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ValuationCentres
-- name    : QEC_Coding_AlgebraicGeometry_Places_ValuationCentres
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:05:21.070531+00:00
-- url     : https://prove2.me/theorems/9221c575-fd68-4cfe-a08c-d3d8f6528728
-- title:
--   Valuation Centres
-- statement:
--   Definitions and structural lemmas for Valuation Centres, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/ValuationCentres.lean

import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.AlgebraicGeometry.StructureSheaf
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry.ValuationCentres
noncomputable section
def heightOneStalkValuationRingEquiv
    {K : Type*} [Field K] (R : Type*) [CommRing R] [IsDedekindDomain R]
    [Algebra R K] [IsFractionRing R K] (H : IsDedekindDomain.HeightOneSpectrum R) :
    (_root_.AlgebraicGeometry.Spec.structureSheaf R).presheaf.stalk
      (⟨H.asIdeal,H.isPrime⟩ : PrimeSpectrum R) ≃+* H.valuationSubringAtPrime K :=
by
  let p : PrimeSpectrum R := ⟨H.asIdeal,H.isPrime⟩
  letI : IsLocalization H.asIdeal.primeCompl
      ((_root_.AlgebraicGeometry.Spec.structureSheaf R).presheaf.stalk p) :=
    _root_.AlgebraicGeometry.StructureSheaf.IsLocalization.to_stalk R p
  exact (IsLocalization.algEquiv H.asIdeal.primeCompl _ _).toRingEquiv
end
end QEC.Coding.AlgebraicGeometry.ValuationCentres


