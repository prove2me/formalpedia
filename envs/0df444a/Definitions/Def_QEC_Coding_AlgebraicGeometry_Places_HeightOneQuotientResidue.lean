-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_HeightOneQuotientResidue
-- name    : QEC_Coding_AlgebraicGeometry_Places_HeightOneQuotientResidue
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T14:13:07.389206+00:00
-- url     : https://prove2.me/theorems/5d3e2df0-cee4-463f-a873-8b524d597570
-- title:
--   Height One Quotient Residue
-- statement:
--   Definitions and structural lemmas for Height One Quotient Residue, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/HeightOneQuotientResidue.lean

import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Localization.AtPrime.Basic
set_option autoImplicit false
namespace Valuation
noncomputable def residueFieldEquivOfEq {F : Type*} [Field F]
    (v w : Valuation F (WithZero (Multiplicative ℤ))) (h : v = w) :
    IsLocalRing.ResidueField v.valuationSubring ≃+*
      IsLocalRing.ResidueField w.valuationSubring := by
  cases h
  exact RingEquiv.refl _
end Valuation
namespace IsDedekindDomain.HeightOneSpectrum
noncomputable section
variable {R K : Type*} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]
noncomputable def quotientResidueEquivValuation
    (H : IsDedekindDomain.HeightOneSpectrum R) :
    (R ⧸ H.asIdeal) ≃+*
      IsLocalRing.ResidueField ((H.valuation K).valuationSubring) := by
  let e₁ : (R ⧸ H.asIdeal) ≃+*
      IsLocalRing.ResidueField (H.valuationSubringAtPrime K) :=
    IsLocalization.AtPrime.equivQuotMaximalIdeal H.asIdeal
      (H.valuationSubringAtPrime K)
  let e₂ : H.valuationSubringAtPrime K ≃+*
      (H.valuation K).valuationSubring := by
    rw [H.valuationSubringAtPrime_eq_valuationSubring]
  exact e₁.trans (IsLocalRing.ResidueField.mapEquiv e₂)
end
end IsDedekindDomain.HeightOneSpectrum


