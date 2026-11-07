-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCoprimeModularReduction
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalCoprimeModularReduction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T02:17:05.301509+00:00
-- url     : https://prove2.me/theorems/5f705e85-4622-4af0-bb74-5ae8727940e7
-- title:
--   LPSOriginal Coprime Modular Reduction
-- statement:
--   Definitions and structural lemmas for LPSOriginal Coprime Modular Reduction, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCoprimeModularReduction.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCosetCuspSeries
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalAnalyticCuspLocalization
set_option autoImplicit false
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
namespace QEC.Coding.TannerLiftedProduct
noncomputable section
attribute [local instance] lpsOriginalLevelPhasePrime_isMaximal
attribute [local instance] lpsOriginalLevelPhaseResidue_field
def lpsOriginalAnalyticCosetBranch
    (N : ℕ) (hN : 0 < N) (x : LPSOriginalCuspIndex N) :
    lpsOriginalAnalyticCuspLaurentRing :=
  lpsOriginalAnalyticCuspAffineBranch (lpsOriginalCosetCuspWitness N hN x).1.val
    (lpsOriginalCosetCuspWitness N hN x).1.property
    (lpsOriginalCosetCuspWitness N hN x).2.val
def lpsOriginalAnalyticLevelCoefficientEval (N : ℕ) (hN : 0 < N) :
    Polynomial ℤ →+* lpsOriginalAnalyticCuspLaurentRing :=
  Polynomial.eval₂RingHom (Int.castRingHom lpsOriginalAnalyticCuspLaurentRing)
    (lpsOriginalAnalyticCuspAffineBranch N hN 0)
def lpsOriginalIntegralLevelCoefficientEval (N : ℕ) (hN : 0 < N) :
    Polynomial ℤ →+* lpsOriginalCuspSeriesRing (lpsOriginalLevelPhaseRing N) :=
  Polynomial.eval₂RingHom (Int.castRingHom _)
    (lpsOriginalCuspJWidth (lpsOriginalLevelPhaseRing N) N hN.ne')
def lpsOriginalResidueLevelCoefficientEval
    (N : ℕ) (hN : 0 < N) (p : ℕ) (hp : p.Prime) :
    Polynomial ℤ →+* lpsOriginalCuspSeriesRing (LPSOriginalLevelPhaseResidue N hN p hp) :=
  Polynomial.eval₂RingHom (Int.castRingHom _)
    (lpsOriginalCuspJWidth (LPSOriginalLevelPhaseResidue N hN p hp) N hN.ne')
local instance lpsOriginalFieldCuspSeries_domain
    (K : Type*) [Field K] : IsDomain (lpsOriginalCuspSeriesRing K) :=
  Localization.Away.isDomain PowerSeries.X_ne_zero
def lpsOriginalFieldLevelJPolynomialEval
    (K : Type*) [Field K] (N : ℕ) (hN : 0 < N) :
    Polynomial K →+* lpsOriginalCuspSeriesRing K :=
  Polynomial.eval₂RingHom
    ((algebraMap (PowerSeries K) (lpsOriginalCuspSeriesRing K)).comp PowerSeries.C)
    (lpsOriginalCuspJWidth K N hN.ne')
def lpsOriginalModularPolynomialModFraction
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] :
    Polynomial (FractionRing (Polynomial (ZMod p))) :=
  (lpsOriginalIntegerPolynomial N hN).map
    ((algebraMap (Polynomial (ZMod p)) (FractionRing (Polynomial (ZMod p)))).comp
      (Polynomial.mapRingHom (Int.castRingHom (ZMod p))))
end
end QEC.Coding.TannerLiftedProduct


