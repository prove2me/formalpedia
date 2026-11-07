-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCosetCuspSeries
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalCosetCuspSeries
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T00:10:34.106579+00:00
-- url     : https://prove2.me/theorems/7b64ca19-21a1-45f0-8f84-ecb9e18ab475
-- title:
--   LPSOriginal Coset Cusp Series
-- statement:
--   Definitions and structural lemmas for LPSOriginal Coset Cusp Series, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCosetCuspSeries.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspPhaseResidue
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspSeriesReduction
set_option autoImplicit false
open Complex Filter Topology
open scoped UpperHalfPlane MatrixGroups
namespace QEC.Coding.TannerLiftedProduct
noncomputable section
attribute [local instance] lpsOriginalLevelPhasePrime_isMaximal
attribute [local instance] lpsOriginalLevelPhaseResidue_field
def lpsOriginalPhaseCuspNumerator
    (R : Type*) [CommRing R] (N m : ℕ) (hm : m ≠ 0) (ζ : R) : PowerSeries R :=
  PowerSeries.C (ζ^(N-1)) * PowerSeries.expand m hm
    (PowerSeries.rescale ζ (lpsOriginalCuspJNumerator R))
def lpsOriginalPhaseCuspSeries
    (R : Type*) [CommRing R] (N m : ℕ) (hm : m ≠ 0) (ζ : R) :
    lpsOriginalCuspSeriesRing R :=
  (IsLocalization.Away.invSelf (S := lpsOriginalCuspSeriesRing R)
    (PowerSeries.X : PowerSeries R))^m *
    algebraMap (PowerSeries R) (lpsOriginalCuspSeriesRing R)
      (lpsOriginalPhaseCuspNumerator R N m hm ζ)
lemma lpsOriginalCosetCuspData_slope_pos
    (N : ℕ) (hN : 0 < N) (x : LPSOriginalCuspIndex N) :
    0 < (lpsOriginalCosetCuspData N hN x).1 :=
  (lpsOriginalCosetCuspWitness N hN x).1.property
def lpsOriginalCosetIntegralCuspSeries
    (N : ℕ) (hN : 0 < N) (x : LPSOriginalCuspIndex N) :
    lpsOriginalCuspSeriesRing (lpsOriginalLevelPhaseRing N) :=
  lpsOriginalPhaseCuspSeries (lpsOriginalLevelPhaseRing N) N
    (lpsOriginalCosetCuspData N hN x).1
    (lpsOriginalCosetCuspData_slope_pos N hN x).ne'
    (lpsOriginalCosetPhaseElement N hN x)
def lpsOriginalCosetResidueCuspSeries
    (N : ℕ) (hN : 0 < N) (p : ℕ) (hp : p.Prime)
    (x : LPSOriginalCuspIndex N) :
    lpsOriginalCuspSeriesRing (LPSOriginalLevelPhaseResidue N hN p hp) :=
  lpsOriginalPhaseCuspSeries (LPSOriginalLevelPhaseResidue N hN p hp) N
    (lpsOriginalCosetCuspData N hN x).1
    (lpsOriginalCosetCuspData_slope_pos N hN x).ne'
    (Ideal.Quotient.mk (lpsOriginalLevelPhasePrime N hN p hp)
      (lpsOriginalCosetPhaseElement N hN x))
end
end QEC.Coding.TannerLiftedProduct


